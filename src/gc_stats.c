#include "gc.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <uv.h>
#ifdef __linux__
#include <dirent.h>
#endif

// ============================================================================
// GC Runtime Metrics Export
// ============================================================================

void valk_gc_get_runtime_metrics(valk_gc_malloc_heap_t* heap,
                                  u64* cycles, u64* pause_us_total,
                                  u64* pause_us_max, sz* reclaimed,
                                  sz* heap_used, sz* heap_total) {
  if (!heap) return;

  if (cycles) *cycles = atomic_load(&heap->runtime_metrics.cycles_total);
  if (pause_us_total) *pause_us_total = atomic_load(&heap->runtime_metrics.pause_us_total);
  if (pause_us_max) *pause_us_max = atomic_load(&heap->runtime_metrics.pause_us_max);
  if (reclaimed) *reclaimed = atomic_load(&heap->runtime_metrics.reclaimed_bytes_total);

  if (heap_used) *heap_used = valk_gc_heap2_used_bytes(heap);
  if (heap_total) *heap_total = heap->hard_limit;
}

sz valk_gc_get_allocated_bytes_total(valk_gc_malloc_heap_t* heap) {
  if (!heap) return 0;
  return atomic_load(&heap->runtime_metrics.allocated_bytes_total);
}

u8 valk_gc_get_last_efficiency(valk_gc_malloc_heap_t* heap) {
  if (!heap) return 0;
  sz before = atomic_load(&heap->runtime_metrics.last_heap_before_gc);
  sz reclaimed = atomic_load(&heap->runtime_metrics.last_reclaimed);
  if (before == 0) return 0;
  sz pct = (reclaimed * 100) / before;
  return (u8)(pct > 100 ? 100 : pct);
}

void valk_gc_get_survival_histogram(valk_gc_malloc_heap_t* heap,
                                     u64* gen_0, u64* gen_1_5,
                                     u64* gen_6_20, u64* gen_21_plus) {
  if (!heap) return;
  if (gen_0) *gen_0 = atomic_load(&heap->runtime_metrics.survival_gen_0);
  if (gen_1_5) *gen_1_5 = atomic_load(&heap->runtime_metrics.survival_gen_1_5);
  if (gen_6_20) *gen_6_20 = atomic_load(&heap->runtime_metrics.survival_gen_6_20);
  if (gen_21_plus) *gen_21_plus = atomic_load(&heap->runtime_metrics.survival_gen_21_plus);
}

void valk_gc_get_pause_histogram(valk_gc_malloc_heap_t* heap,
                                  u64* pause_0_1ms, u64* pause_1_5ms,
                                  u64* pause_5_10ms, u64* pause_10_16ms,
                                  u64* pause_16ms_plus) {
  if (!heap) return;
  if (pause_0_1ms) *pause_0_1ms = atomic_load(&heap->runtime_metrics.pause_0_1ms);
  if (pause_1_5ms) *pause_1_5ms = atomic_load(&heap->runtime_metrics.pause_1_5ms);
  if (pause_5_10ms) *pause_5_10ms = atomic_load(&heap->runtime_metrics.pause_5_10ms);
  if (pause_10_16ms) *pause_10_16ms = atomic_load(&heap->runtime_metrics.pause_10_16ms);
  if (pause_16ms_plus) *pause_16ms_plus = atomic_load(&heap->runtime_metrics.pause_16ms_plus);
}

void valk_gc_get_fragmentation(valk_gc_malloc_heap_t* heap, valk_fragmentation_t* out) {
  if (!heap || !out) return;
  memset(out, 0, sizeof(*out));

  out->heap_allocated = valk_gc_heap2_used_bytes(heap);
  out->heap_limit = heap->hard_limit;
  out->heap_peak = atomic_load(&heap->stats.peak_usage);
}

// ============================================================================
// GC Statistics Printing (heap2)
// ============================================================================

void valk_gc_malloc_print_stats(valk_gc_malloc_heap_t* heap) {
  if (heap == nullptr) return;

  valk_gc_stats2_t stats;
  valk_gc_heap2_get_stats(heap, &stats);

  fprintf(stderr, "\n=== GC Heap Statistics ===\n");
  u8 usage_pct = valk_gc_heap_usage_pct(heap);
  fprintf(stderr, "Heap usage:       %u%% (threshold: %u%%, hard limit: %zu bytes)\n",
          usage_pct, heap->gc_threshold_pct, heap->hard_limit);
  fprintf(stderr, "Used bytes:       %zu bytes\n", stats.used_bytes);
  fprintf(stderr, "Committed bytes:  %zu bytes\n", stats.committed_bytes);
  fprintf(stderr, "Large objects:    %zu bytes\n", stats.large_object_bytes);
  fprintf(stderr, "Peak usage:       %zu bytes\n", atomic_load(&heap->stats.peak_usage));
  fprintf(stderr, "Collections:      %llu\n", (unsigned long long)stats.collections);
  fprintf(stderr, "Emergency GCs:    %llu\n", (unsigned long long)heap->stats.emergency_collections);

  fprintf(stderr, "--- Per-Class Usage ---\n");
  // LCOV_EXCL_START - conditional output formatting for debug/diagnostic use
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    if (stats.class_total_slots[c] > 0) {
      u64 pct = (stats.class_used_slots[c] * 100) / stats.class_total_slots[c];
      fprintf(stderr, "  Class %d (%4u B): %llu / %llu slots (%llu%%)\n",
              c, valk_gc_size_classes[c],
              (unsigned long long)stats.class_used_slots[c], (unsigned long long)stats.class_total_slots[c], (unsigned long long)pct);
    }
  }

  if (heap->stats.evacuations_from_scratch > 0) {
    fprintf(stderr, "--- Evacuation Stats ---\n");
    fprintf(stderr, "Values evacuated: %llu\n", (unsigned long long)heap->stats.evacuations_from_scratch);
    fprintf(stderr, "Bytes evacuated:  %zu\n", heap->stats.evacuation_bytes);
    fprintf(stderr, "Pointers fixed:   %llu\n", (unsigned long long)heap->stats.evacuation_pointer_fixups);
  }
  // LCOV_EXCL_STOP
  fprintf(stderr, "=========================\n\n");
}

void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, FILE* out) {
  if (out == nullptr) out = stderr;

  fprintf(out, "\n=== Memory Statistics ===\n");

  if (scratch != nullptr) {
    double usage = (double)scratch->offset / scratch->capacity * 100.0;
    u64 overflow_fallbacks = atomic_load_explicit(&scratch->stats.overflow_fallbacks, memory_order_relaxed);
    fprintf(out, "Scratch Arena:\n");
    fprintf(out, "  Usage:       %.1f%% (%zu / %zu bytes)\n",
            usage, scratch->offset, scratch->capacity);
    fprintf(out, "  High Water:  %zu bytes\n",
            atomic_load_explicit(&scratch->stats.high_water_mark, memory_order_relaxed));
    fprintf(out, "  Allocations: %llu\n",
            (unsigned long long)atomic_load_explicit(&scratch->stats.total_allocations, memory_order_relaxed));
    fprintf(out, "  Resets:      %llu\n",
            (unsigned long long)atomic_load_explicit(&scratch->stats.num_resets, memory_order_relaxed));
    fprintf(out, "  Checkpoints: %llu\n",
            (unsigned long long)atomic_load_explicit(&scratch->stats.num_checkpoints, memory_order_relaxed));
    if (overflow_fallbacks > 0) {
      fprintf(out, "  Overflows:   %llu (%zu bytes)\n",
              (unsigned long long)overflow_fallbacks,
              atomic_load_explicit(&scratch->stats.overflow_bytes, memory_order_relaxed));
    }
    fprintf(out, "\n");
  }

  if (heap != nullptr) {
    valk_gc_stats2_t stats;
    valk_gc_heap2_get_stats(heap, &stats);

    double usage = (double)stats.used_bytes / heap->hard_limit * 100.0;
    fprintf(out, "GC Heap (heap2):\n");
    fprintf(out, "  Usage:       %.1f%% (%zu / %zu bytes)\n",
            usage, stats.used_bytes, heap->hard_limit);
    fprintf(out, "  Committed:   %zu bytes\n", stats.committed_bytes);
    fprintf(out, "  Large objs:  %zu bytes\n", stats.large_object_bytes);
    fprintf(out, "  Collections: %llu\n", (unsigned long long)stats.collections);
    fprintf(out, "  Reclaimed:   %zu bytes total\n",
            stats.bytes_reclaimed_total);
  }

  fprintf(out, "=========================\n\n");
}

// ============================================================================
// Memory Snapshot for REPL Eval Tracking
// ============================================================================

void valk_repl_mem_take_snapshot(valk_gc_malloc_heap_t* heap, valk_mem_arena_t* scratch,
                                 valk_repl_mem_snapshot_t* out) {
  if (!out) return;
  memset(out, 0, sizeof(*out));

  if (heap) {
    out->heap_used_bytes = valk_gc_heap2_used_bytes(heap);
    out->lval_count = 0;
    out->lenv_count = 0;
  }

  if (scratch) {
    out->scratch_used_bytes = scratch->offset;
  }
}

void valk_repl_mem_snapshot_delta(valk_repl_mem_snapshot_t* before, valk_repl_mem_snapshot_t* after,
                                  i64* heap_delta, i64* scratch_delta,
                                  i64* lval_delta, i64* lenv_delta) {
  if (!before || !after) return;
  if (heap_delta) *heap_delta = (i64)after->heap_used_bytes - (i64)before->heap_used_bytes;
  if (scratch_delta) *scratch_delta = (i64)after->scratch_used_bytes - (i64)before->scratch_used_bytes;
  if (lval_delta) *lval_delta = (i64)after->lval_count - (i64)before->lval_count;
  if (lenv_delta) *lenv_delta = (i64)after->lenv_count - (i64)before->lenv_count;
}

// ============================================================================
// REPL Eval Delta Tracking (for dashboard REPL profile)
// ============================================================================

static valk_repl_eval_delta_t g_repl_eval_delta = {0};
static bool g_repl_eval_delta_valid = false;

bool valk_repl_get_last_eval_delta(valk_repl_eval_delta_t* out) {
  if (!out || !g_repl_eval_delta_valid) return false;
  *out = g_repl_eval_delta;
  return true;
}

void valk_repl_set_eval_delta(i64 heap, i64 scratch, i64 lval, i64 lenv) {
  g_repl_eval_delta.heap_delta = heap;
  g_repl_eval_delta.scratch_delta = scratch;
  g_repl_eval_delta.lval_delta = lval;
  g_repl_eval_delta.lenv_delta = lenv;
  g_repl_eval_delta.eval_count++;
  g_repl_eval_delta_valid = true;
}

// ============================================================================
// Diagnostic Dump for Debugging Hangs
// ============================================================================

static const char *valk_gc_phase_name(valk_gc_phase_e phase) {
  switch (phase) {
    case VALK_GC_PHASE_IDLE: return "IDLE";
    case VALK_GC_PHASE_STW_REQUESTED: return "STW_REQUESTED";
    case VALK_GC_PHASE_CHECKPOINT_REQUESTED: return "CHECKPOINT_REQUESTED";
    case VALK_GC_PHASE_MARKING: return "MARKING";
    case VALK_GC_PHASE_SWEEPING: return "SWEEPING";
    default: return "UNKNOWN";
  }
}

void valk_diag_dump_on_timeout(void) {
  valk_gc_phase_e phase = atomic_load(&valk_gc_coord.phase);
  u64 registered = atomic_load(&valk_gc_coord.threads_registered);
  u64 paused = atomic_load(&valk_gc_coord.threads_paused);

  fprintf(stderr, "\n");
  fprintf(stderr, "╔══════════════════════════════════════════════════════════════╗\n");
  fprintf(stderr, "║  TIMEOUT DIAGNOSTIC DUMP                                     ║\n");
  fprintf(stderr, "╚══════════════════════════════════════════════════════════════╝\n");
  fprintf(stderr, "\n");

  fprintf(stderr, "=== GC Coordinator State ===\n");
  fprintf(stderr, "  phase:              %s (%d)\n", valk_gc_phase_name(phase), phase);
  fprintf(stderr, "  threads_registered: %llu\n", (unsigned long long)registered);
  fprintf(stderr, "  threads_paused:     %llu\n", (unsigned long long)paused);
  fprintf(stderr, "  barrier_init:       %s\n", valk_gc_coord.barrier_initialized ? "yes" : "no");
  fprintf(stderr, "\n");

  if (phase != VALK_GC_PHASE_IDLE) {
    fprintf(stderr, "  *** GC is NOT idle - possible deadlock in GC coordination ***\n");
    if (paused < registered) {
      fprintf(stderr, "  *** Waiting for %llu threads to reach safe point ***\n",
              (unsigned long long)(registered - paused));
    }
    fprintf(stderr, "\n");
  }

  fprintf(stderr, "=== Registered Threads ===\n");
  for (u64 i = 0; i < VALK_GC_MAX_THREADS && i < 16; i++) {
    if (valk_gc_coord.threads[i].active) {
      valk_thread_context_t *tc = valk_gc_coord.threads[i].ctx;
      fprintf(stderr, "  [%llu] pthread=%lu active=yes",
              (unsigned long long)i,
              (unsigned long)valk_gc_coord.threads[i].thread_id);
      if (tc) {
        fprintf(stderr, " gc_id=%llu", (unsigned long long)tc->gc_thread_id);
      }
      fprintf(stderr, "\n");
    }
  }
  fprintf(stderr, "\n");

  fprintf(stderr, "=== Current Thread Context ===\n");
  fprintf(stderr, "  gc_registered:   %s\n", valk_thread_ctx.gc_registered ? "yes" : "no");
  fprintf(stderr, "  gc_thread_id:    %llu\n", (unsigned long long)valk_thread_ctx.gc_thread_id);
  fprintf(stderr, "  root_stack_cnt:  %zu\n", valk_thread_ctx.root_stack_count);
  fprintf(stderr, "\n");

#ifdef __linux__
  fprintf(stderr, "=== Thread Stacks (from /proc) ===\n");
  char path[64];
  snprintf(path, sizeof(path), "/proc/%d/task", getpid());
  DIR *dir = opendir(path);
  if (dir) {
    struct dirent *ent;
    while ((ent = readdir(dir)) != nullptr) {
      if (ent->d_name[0] == '.') continue;
      char stack_path[128];
      snprintf(stack_path, sizeof(stack_path), "/proc/%d/task/%s/stack", getpid(), ent->d_name);
      FILE *f = fopen(stack_path, "r");
      if (f) {
        fprintf(stderr, "--- Thread %s ---\n", ent->d_name);
        char line[256];
        int lines = 0;
        while (fgets(line, sizeof(line), f) && lines < 10) {
          fprintf(stderr, "  %s", line);
          lines++;
        }
        fclose(f);
      }
    }
    closedir(dir);
  }
  fprintf(stderr, "\n");
#endif

  fprintf(stderr, "=== Likely Cause ===\n");
  if (phase == VALK_GC_PHASE_STW_REQUESTED || phase == VALK_GC_PHASE_CHECKPOINT_REQUESTED) {
    fprintf(stderr, "  GC/checkpoint requested but not all threads reached safe point.\n");
    fprintf(stderr, "  A thread may be stuck in a long-running operation without\n");
    fprintf(stderr, "  calling VALK_GC_SAFE_POINT().\n");
  } else if (phase == VALK_GC_PHASE_MARKING || phase == VALK_GC_PHASE_SWEEPING) {
    fprintf(stderr, "  GC is in progress. Threads may be stuck at a barrier.\n");
    fprintf(stderr, "  Check barrier_wait calls in gc.c.\n");
  } else {
    fprintf(stderr, "  GC is idle. Hang may be in application logic:\n");
    fprintf(stderr, "  - Event loop waiting for I/O that never arrives\n");
    fprintf(stderr, "  - Deadlock in application mutex\n");
    fprintf(stderr, "  - Infinite loop in user code\n");
  }
  fprintf(stderr, "\n");

  fflush(stderr);
}
