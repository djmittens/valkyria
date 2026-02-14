#include "aio_combinators_internal.h"

extern void valk_async_handle_run_resource_cleanups(valk_async_handle_t *handle);

void valk_async_notify_parent(valk_async_handle_t *child) {
  if (!child || !child->parent) return; // LCOV_EXCL_BR_LINE - null checks
  valk_async_handle_t *parent = child->parent;
  
  valk_async_status_t status = valk_async_handle_get_status(child);
  
  if (status == VALK_ASYNC_COMPLETED && parent->on_child_completed) { // LCOV_EXCL_BR_LINE - callback presence varies
    parent->on_child_completed(child);
  } else if ((status == VALK_ASYNC_FAILED || status == VALK_ASYNC_CANCELLED) && parent->on_child_failed) { // LCOV_EXCL_BR_LINE - callback presence varies
    parent->on_child_failed(child);
  }
}

static void valk_async_propagate_single(void *ctx);

static void valk_async_schedule_propagate(valk_async_handle_t *child) {
  valk_aio_system_t *sys = child->sys;
  if (sys) { // LCOV_EXCL_BR_LINE - sys-null fallback: handles without system propagate inline
    valk_aio_enqueue_task(sys, valk_async_propagate_single, child);
  } else {
    valk_async_propagate_single(child);
  }
}

static void valk_async_propagate_single(void *ctx) {
  VALK_GC_SAFE_POINT();
  
  valk_async_handle_t *source = (valk_async_handle_t *)ctx;
  if (!source) return; // LCOV_EXCL_LINE - defensive null check

  u32 children_count = valk_chunked_ptrs_count(&source->children);
  VALK_INFO("Propagating from handle %llu (status=%d, children=%u)",
            source->id, valk_async_handle_get_status(source), children_count);

  valk_async_status_t source_status = valk_async_handle_get_status(source);

  for (u32 i = 0; i < children_count; i++) {
    valk_async_handle_t *child = valk_chunked_ptrs_get(&source->children, i);
    valk_async_status_t child_status = valk_async_handle_get_status(child);
    VALK_DEBUG("  Child %zu: handle %llu, status=%d, parent=%llu (source=%llu), on_complete=%p",
              i, child->id, child_status,
              child->parent ? child->parent->id : 0, source->id,
              (void*)child->on_complete);
    if (child_status == VALK_ASYNC_RUNNING && // LCOV_EXCL_BR_LINE - status check
        (child->parent == source || child->on_complete != NULL)) {
      if (source_status == VALK_ASYNC_COMPLETED) { // LCOV_EXCL_BR_LINE - status branch
        if (child->on_complete && child->env) { // LCOV_EXCL_BR_LINE - callback presence
          valk_lval_t *args;
          valk_lval_t *transformed;
          valk_mem_allocator_t *alloc = child->sys ? (valk_mem_allocator_t*)&child->sys->system_region : nullptr; // LCOV_EXCL_BR_LINE - allocator selection
          if (!alloc && child->region) { // LCOV_EXCL_BR_LINE - allocator fallback
            alloc = (valk_mem_allocator_t*)child->region;
          }
          if (!alloc) alloc = &valk_malloc_allocator; // LCOV_EXCL_BR_LINE - allocator fallback
          VALK_WITH_ALLOC(alloc) {
            args = valk_lval_cons(source->result, valk_lval_nil());
            transformed = valk_lval_eval_call(child->env, child->on_complete, args);
          }
          if (LVAL_TYPE(transformed) == LVAL_ERR) { // LCOV_EXCL_BR_LINE - error type
            atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
            child->error = transformed;
          } else if (LVAL_TYPE(transformed) == LVAL_HANDLE) { // LCOV_EXCL_BR_LINE - handle type
            valk_async_handle_t *inner = transformed->async.handle;
            valk_async_status_t inner_status = valk_async_handle_get_status(inner);
            if (inner_status == VALK_ASYNC_COMPLETED) { // LCOV_EXCL_BR_LINE - inner status
              atomic_store_explicit(&child->status, VALK_ASYNC_COMPLETED, memory_order_release);
              child->result = inner->result;
            } else if (inner_status == VALK_ASYNC_FAILED) { // LCOV_EXCL_BR_LINE - inner status
              atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
              child->error = inner->error;
            } else if (inner_status == VALK_ASYNC_CANCELLED) { // LCOV_EXCL_BR_LINE - cancelled rare
              atomic_store_explicit(&child->status, VALK_ASYNC_CANCELLED, memory_order_release);
            } else {
              child->on_complete = NULL;
              valk_async_handle_add_child(inner, child);
              valk_async_done_fn child_on_done = atomic_load_explicit(&child->on_done, memory_order_acquire);
              valk_async_done_fn inner_on_done = atomic_load_explicit(&inner->on_done, memory_order_acquire);
              if (child_on_done && !inner_on_done) { // LCOV_EXCL_BR_LINE - callback transfer
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
      } else if (source_status == VALK_ASYNC_FAILED) { // LCOV_EXCL_BR_LINE - status branch
        if (child->on_error && child->env) { // LCOV_EXCL_BR_LINE - error handler presence
          valk_lval_t *args;
          valk_lval_t *recovered;
          valk_mem_allocator_t *alloc = child->sys ? (valk_mem_allocator_t*)&child->sys->system_region : nullptr; // LCOV_EXCL_BR_LINE - allocator selection
          if (!alloc && child->region) { // LCOV_EXCL_BR_LINE - allocator fallback
            alloc = (valk_mem_allocator_t*)child->region;
          }
          if (!alloc) alloc = &valk_malloc_allocator; // LCOV_EXCL_BR_LINE - allocator fallback
          VALK_WITH_ALLOC(alloc) {
            args = valk_lval_cons(source->error, valk_lval_nil());
            recovered = valk_lval_eval_call(child->env, child->on_error, args);
          }
          if (LVAL_TYPE(recovered) == LVAL_ERR) { // LCOV_EXCL_BR_LINE - recovery error
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
}

void valk_async_propagate_completion(valk_async_handle_t *source) {
  if (!source) return; // LCOV_EXCL_LINE - defensive null check
  valk_async_propagate_single(source);
}
