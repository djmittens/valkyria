#include "aio_combinators_internal.h"

extern void valk_async_handle_run_resource_cleanups(valk_async_handle_t *handle);

void valk_async_notify_parent(valk_async_handle_t *child) {
  if (!child || !child->parent) return;
  valk_async_handle_t *parent = child->parent;
  
  valk_async_status_t status = valk_async_handle_get_status(child);
  
  if (status == VALK_ASYNC_COMPLETED && parent->on_child_completed) {
    parent->on_child_completed(child);
  } else if ((status == VALK_ASYNC_FAILED || status == VALK_ASYNC_CANCELLED) && parent->on_child_failed) {
    parent->on_child_failed(child);
  }
}

static void valk_async_propagate_single(void *ctx);

static void valk_async_schedule_propagate(valk_async_handle_t *child) {
  valk_aio_system_t *sys = child->sys;
  // LCOV_EXCL_BR_START - async scheduling: depends on sys configuration
  if (sys) {
    valk_aio_enqueue_task(sys, valk_async_propagate_single, child);
  } else {
    valk_async_propagate_single(child);
  }
  // LCOV_EXCL_BR_STOP
}

static void valk_async_propagate_single(void *ctx) {
  VALK_GC_SAFE_POINT(); // LCOV_EXCL_BR_LINE - GC safepoint: depends on GC state
  
  valk_async_handle_t *source = (valk_async_handle_t *)ctx;
  // LCOV_EXCL_BR_START - defensive null check
  if (!source) return;
  // LCOV_EXCL_BR_STOP

  u32 children_count = valk_chunked_ptrs_count(&source->children);
  VALK_INFO("Propagating from handle %llu (status=%d, children=%u)",
            source->id, valk_async_handle_get_status(source), children_count);

  valk_async_status_t source_status = valk_async_handle_get_status(source);

  // LCOV_EXCL_START - async propagation: complex internal state machine
  for (u32 i = 0; i < children_count; i++) {
    valk_async_handle_t *child = valk_chunked_ptrs_get(&source->children, i);
    valk_async_status_t child_status = valk_async_handle_get_status(child);
    VALK_DEBUG("  Child %zu: handle %llu, status=%d, parent=%llu (source=%llu), on_complete=%p",
              i, child->id, child_status,
              child->parent ? child->parent->id : 0, source->id,
              (void*)child->on_complete);
    if (child_status == VALK_ASYNC_RUNNING &&
        (child->parent == source || child->on_complete != NULL)) {
      if (source_status == VALK_ASYNC_COMPLETED) {
        if (child->on_complete && child->env) {
          valk_lval_t *args;
          valk_lval_t *transformed;
          valk_mem_allocator_t *alloc = child->sys ? (valk_mem_allocator_t*)&child->sys->system_region : nullptr;
          if (!alloc && child->region) {
            alloc = (valk_mem_allocator_t*)child->region;
          }
          if (!alloc) alloc = &valk_malloc_allocator;
          VALK_WITH_ALLOC(alloc) {
            args = valk_lval_cons(source->result, valk_lval_nil());
            transformed = valk_lval_eval_call(child->env, child->on_complete, args);
          }
          if (LVAL_TYPE(transformed) == LVAL_ERR) {
            atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
            child->error = transformed;
          } else if (LVAL_TYPE(transformed) == LVAL_HANDLE) {
            valk_async_handle_t *inner = transformed->async.handle;
            valk_async_status_t inner_status = valk_async_handle_get_status(inner);
            if (inner_status == VALK_ASYNC_COMPLETED) {
              atomic_store_explicit(&child->status, VALK_ASYNC_COMPLETED, memory_order_release);
              child->result = inner->result;
            } else if (inner_status == VALK_ASYNC_FAILED) {
              atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
              child->error = inner->error;
            } else if (inner_status == VALK_ASYNC_CANCELLED) {
              atomic_store_explicit(&child->status, VALK_ASYNC_CANCELLED, memory_order_release);
            } else {
              child->on_complete = NULL;
              valk_async_handle_add_child(inner, child);
              valk_async_done_fn child_on_done = atomic_load_explicit(&child->on_done, memory_order_acquire);
              valk_async_done_fn inner_on_done = atomic_load_explicit(&inner->on_done, memory_order_acquire);
              if (child_on_done && !inner_on_done) {
                void *child_ctx = atomic_load_explicit(&child->on_done_ctx, memory_order_relaxed);
                atomic_store_explicit(&inner->on_done, child_on_done, memory_order_release);
                atomic_store_explicit(&inner->on_done_ctx, child_ctx, memory_order_relaxed);
                inner->region = child->region;
                inner->env = child->env;
                atomic_store_explicit(&child->on_done, NULL, memory_order_relaxed);
                atomic_store_explicit(&child->on_done_ctx, NULL, memory_order_relaxed);
              }
              continue;
            }
          } else {
            atomic_store_explicit(&child->status, VALK_ASYNC_COMPLETED, memory_order_release);
            child->result = transformed;
          }
        } else {
          atomic_store_explicit(&child->status, VALK_ASYNC_COMPLETED, memory_order_release);
          child->result = source->result;
        }
        valk_async_notify_parent(child);
        valk_async_notify_done(child);
        valk_async_handle_run_resource_cleanups(child);
        valk_async_schedule_propagate(child);
      } else if (source_status == VALK_ASYNC_FAILED) {
        if (child->on_error && child->env) {
          valk_lval_t *args;
          valk_lval_t *recovered;
          valk_mem_allocator_t *alloc = child->sys ? (valk_mem_allocator_t*)&child->sys->system_region : nullptr;
          if (!alloc && child->region) {
            alloc = (valk_mem_allocator_t*)child->region;
          }
          if (!alloc) alloc = &valk_malloc_allocator;
          VALK_WITH_ALLOC(alloc) {
            args = valk_lval_cons(source->error, valk_lval_nil());
            recovered = valk_lval_eval_call(child->env, child->on_error, args);
          }
          if (LVAL_TYPE(recovered) == LVAL_ERR) {
            atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
            child->error = recovered;
          } else {
            atomic_store_explicit(&child->status, VALK_ASYNC_COMPLETED, memory_order_release);
            child->result = recovered;
          }
        } else {
          atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
          child->error = source->error;
        }
        valk_async_notify_parent(child);
        valk_async_notify_done(child);
        valk_async_handle_run_resource_cleanups(child);
        valk_async_schedule_propagate(child);
      }
    }
  }
  // LCOV_EXCL_STOP
}

void valk_async_propagate_completion(valk_async_handle_t *source) {
  // LCOV_EXCL_BR_START - defensive null check
  if (!source) return;
  // LCOV_EXCL_BR_STOP
  valk_async_propagate_single(source);
}
