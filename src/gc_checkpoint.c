#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>

extern void evac_ctx_init(valk_evacuation_ctx_t* ctx);
extern void evac_ctx_free(valk_evacuation_ctx_t* ctx);
extern valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
extern void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);
extern valk_lval_t* evac_worklist_pop(valk_evacuation_ctx_t* ctx);
extern void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
extern void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
extern void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);

// LCOV_EXCL_START - evacuation checkpoint requires active eval stack from evaluator
static inline void evac_value_and_process_env(valk_evacuation_ctx_t* ctx, valk_lval_t** ptr) {
  valk_lval_t* val = *ptr;
  if (val == nullptr) return;
  valk_lval_t* new_val = valk_evacuate_value(ctx, val);
  if (new_val != val) {
    *ptr = new_val;
  } else if (LVAL_TYPE(val) == LVAL_FUN && val->fun.builtin == nullptr && val->fun.env != nullptr) {
    valk_evacuate_env(ctx, val->fun.env);
  }
}

static void evac_checkpoint_eval_stack(valk_evacuation_ctx_t* ctx) {
  if (valk_thread_ctx.eval_stack == nullptr) return;

  valk_eval_stack_t* stack = (valk_eval_stack_t*)valk_thread_ctx.eval_stack;
  for (u64 i = 0; i < stack->count; i++) {
    valk_cont_frame_t* frame = &stack->frames[i];
    switch (frame->kind) {
      case CONT_EVAL_ARGS:
        evac_value_and_process_env(ctx, &frame->eval_args.func);
        evac_value_and_process_env(ctx, &frame->eval_args.remaining);
        break;
      case CONT_COLLECT_ARG:
        evac_value_and_process_env(ctx, &frame->collect_arg.func);
        evac_value_and_process_env(ctx, &frame->collect_arg.remaining);
        for (u64 j = 0; j < frame->collect_arg.count; j++) {
          evac_value_and_process_env(ctx, &frame->collect_arg.args[j]);
        }
        break;
      case CONT_IF_BRANCH:
        evac_value_and_process_env(ctx, &frame->if_branch.true_branch);
        evac_value_and_process_env(ctx, &frame->if_branch.false_branch);
        break;
      case CONT_DO_NEXT:
        evac_value_and_process_env(ctx, &frame->do_next.remaining);
        break;
      case CONT_SELECT_CHECK:
        evac_value_and_process_env(ctx, &frame->select_check.result_expr);
        evac_value_and_process_env(ctx, &frame->select_check.remaining);
        evac_value_and_process_env(ctx, &frame->select_check.original_args);
        break;
      case CONT_BODY_NEXT:
        evac_value_and_process_env(ctx, &frame->body_next.remaining);
        break;
      case CONT_CTX_DEADLINE:
        evac_value_and_process_env(ctx, &frame->ctx_deadline.body);
        break;
      case CONT_CTX_WITH:
        evac_value_and_process_env(ctx, &frame->ctx_with.value_expr);
        evac_value_and_process_env(ctx, &frame->ctx_with.body);
        break;
      default:
        break;
    }
  }

  evac_value_and_process_env(ctx, &valk_thread_ctx.eval_expr);
  evac_value_and_process_env(ctx, &valk_thread_ctx.eval_value);
}
// LCOV_EXCL_STOP

static void valk_checkpoint_request_stw(void) {
  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  // LCOV_EXCL_BR_START - CAS race: another thread may have changed phase
  if (!atomic_compare_exchange_strong(&valk_sys->phase, &expected,
                                       VALK_GC_PHASE_CHECKPOINT_REQUESTED)) {
  // LCOV_EXCL_BR_STOP
    return;
  }

  u64 num_threads = atomic_load(&valk_sys->threads_registered);
  if (num_threads <= 1) {
    atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);
    return;
  }

  if (valk_sys->barrier_initialized) {
    valk_barrier_reset(&valk_sys->barrier, num_threads);
  } else {
    valk_barrier_init(&valk_sys->barrier, num_threads);
    valk_sys->barrier_initialized = true;
  }

  valk_system_wake_threads(valk_sys);

  valk_barrier_wait(&valk_sys->barrier);
}

static void valk_checkpoint_release_stw(void) {
  valk_gc_phase_e phase = atomic_load(&valk_sys->phase);
  if (phase != VALK_GC_PHASE_CHECKPOINT_REQUESTED) return;

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);

  valk_barrier_wait(&valk_sys->barrier);
}

// LCOV_EXCL_BR_START - checkpoint null checks and iteration
void valk_checkpoint(valk_mem_arena_t* scratch, valk_gc_heap_t* heap,
                     valk_lenv_t* root_env) {
  if (scratch == nullptr || heap == nullptr) {
    VALK_WARN("Checkpoint called with nullptr scratch or heap");
    return;
  }

  VALK_DEBUG("Checkpoint starting, scratch offset=%llu", (unsigned long long)scratch->offset);

  valk_checkpoint_request_stw();

  valk_evacuation_ctx_t ctx = {
    .scratch = scratch,
    .heap = heap,
    .worklist = nullptr,
    .worklist_count = 0,
    .worklist_capacity = 0,
    .evacuated = nullptr,
    .evacuated_count = 0,
    .evacuated_capacity = 0,
    .values_copied = 0,
    .bytes_copied = 0,
    .pointers_fixed = 0,
  };

  evac_ctx_init(&ctx);

  VALK_DEBUG("Checkpoint Phase 1: Starting evacuation from scratch arena");
  if (root_env != nullptr) {
    valk_evacuate_env(&ctx, root_env);
  }

  evac_checkpoint_eval_stack(&ctx);

  while (ctx.worklist_count > 0) {
    valk_lval_t* v = evac_worklist_pop(&ctx);
    valk_evacuate_children(&ctx, v);
  }

  VALK_DEBUG("Checkpoint Phase 1: Evacuated %zu values (%zu bytes)",
             ctx.values_copied, ctx.bytes_copied);

  for (u64 i = 0; i < ctx.evacuated_count; i++) {
    valk_fix_pointers(&ctx, ctx.evacuated[i]);
  }

  if (root_env != nullptr) {
    valk_fix_env_pointers(&ctx, root_env);
  }

  VALK_DEBUG("Checkpoint Phase 2: Fixed %zu pointers", ctx.pointers_fixed);

  atomic_fetch_add_explicit(&scratch->stats.num_checkpoints, 1, memory_order_relaxed);
  atomic_fetch_add_explicit(&scratch->stats.bytes_evacuated, ctx.bytes_copied, memory_order_relaxed);
  atomic_fetch_add_explicit(&scratch->stats.values_evacuated, ctx.values_copied, memory_order_relaxed);

  heap->stats.evacuations_from_scratch += ctx.values_copied;
  heap->stats.evacuation_bytes += ctx.bytes_copied;
  heap->stats.evacuation_pointer_fixups += ctx.pointers_fixed;

  VALK_INFO("Checkpoint: evacuated %zu values (%zu bytes), fixed %zu pointers",
            ctx.values_copied, ctx.bytes_copied, ctx.pointers_fixed);

  valk_mem_arena_reset(scratch);

  evac_ctx_free(&ctx);

  valk_checkpoint_release_stw();
}
// LCOV_EXCL_BR_STOP
