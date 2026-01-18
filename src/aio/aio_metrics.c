// src/aio_metrics.c - AIO metrics implementation
#include "aio_metrics.h"
#include "aio_metrics_v2.h"
#include "memory.h"
#include "gc.h"
#include "parser.h"
#include "common.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>

void valk_event_loop_metrics_get(uv_loop_t* loop, valk_event_loop_metrics_t* out) {
  if (!loop || !out) return;

  memset(out, 0, sizeof(*out));

  uv_metrics_t metrics;
  if (uv_metrics_info(loop, &metrics) == 0) {
    out->loop_count = metrics.loop_count;
    out->events = metrics.events;
    out->events_waiting = metrics.events_waiting;
  }

  out->idle_time_us = uv_metrics_idle_time(loop) / 1000;
}

void valk_vm_metrics_collect(valk_vm_metrics_t* out,
                              valk_gc_malloc_heap_t* heap,
                              struct uv_loop_s* loop) {
  if (!out) return;
  memset(out, 0, sizeof(*out));

  if (heap) {
    sz reclaimed, heap_used, heap_total;
    valk_gc_get_runtime_metrics(heap,
      &out->gc_cycles, &out->gc_pause_us_total, &out->gc_pause_us_max,
      &reclaimed, &heap_used, &heap_total);
    out->gc_reclaimed_bytes = reclaimed;
    out->gc_heap_used = heap_used;
    out->gc_heap_total = heap_total;
    out->gc_allocated_bytes = valk_gc_get_allocated_bytes_total(heap);
    out->gc_efficiency_pct = valk_gc_get_last_efficiency(heap);

    valk_gc_stats2_t gc_stats;
    valk_gc_heap2_get_stats(heap, &gc_stats);
    out->gc_large_object_bytes = gc_stats.large_object_bytes;
    for (int i = 0; i < VALK_VM_SIZE_CLASSES; i++) {
      out->size_class_used[i] = gc_stats.class_used_slots[i];
      out->size_class_total[i] = gc_stats.class_total_slots[i];
    }

    valk_gc_get_pause_histogram(heap,
      &out->pause_0_1ms, &out->pause_1_5ms, &out->pause_5_10ms,
      &out->pause_10_16ms, &out->pause_16ms_plus);

    valk_gc_get_survival_histogram(heap,
      &out->survival_gen_0, &out->survival_gen_1_5,
      &out->survival_gen_6_20, &out->survival_gen_21_plus);
  }

  valk_eval_metrics_get(
    &out->eval_total, &out->function_calls, &out->builtin_calls,
    &out->stack_depth_max, &out->closures_created, &out->env_lookups);

  if (loop) {
    valk_event_loop_metrics_t loop_m;
    valk_event_loop_metrics_get(loop, &loop_m);
    out->loop_count = loop_m.loop_count;
    out->events_processed = loop_m.events;
    out->idle_time_us = loop_m.idle_time_us;
  }
}

char* valk_vm_metrics_to_json(const valk_vm_metrics_t* m,
                               valk_mem_allocator_t* alloc) {
  if (!m) return nullptr;

  u64 buf_size = 4096;
  char* buf = alloc ? valk_mem_allocator_alloc(alloc, buf_size) : malloc(buf_size);
  if (!buf) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  char* p = buf;
  char* end = buf + buf_size;
  int n;

  double heap_util = m->gc_heap_total > 0
    ? 100.0 * (double)m->gc_heap_used / (double)m->gc_heap_total
    : 0.0;

  n = snprintf(p, end - p,
    "{\"gc\":{\"cycles_total\":%llu,\"pause_us_total\":%llu,\"pause_us_max\":%llu,"
    "\"pause_ms_avg\":%.3f,\"reclaimed_bytes_total\":%llu,\"heap_used_bytes\":%llu,"
    "\"heap_total_bytes\":%llu,\"heap_utilization_pct\":%.2f,\"large_object_bytes\":%llu,",
    (unsigned long long)m->gc_cycles,
    (unsigned long long)m->gc_pause_us_total,
    (unsigned long long)m->gc_pause_us_max,
    m->gc_cycles > 0 ? (double)m->gc_pause_us_total / m->gc_cycles / 1000.0 : 0.0,
    (unsigned long long)m->gc_reclaimed_bytes,
    (unsigned long long)m->gc_heap_used,
    (unsigned long long)m->gc_heap_total,
    heap_util,
    (unsigned long long)m->gc_large_object_bytes);
  if (n < 0 || p + n >= end) goto truncated;
  p += n;

  static const u16 sizes[] = {16, 32, 64, 128, 256, 512, 1024, 2048, 4096};
  n = snprintf(p, end - p, "\"size_classes\":[");
  if (n < 0 || p + n >= end) goto truncated;
  p += n;

  for (int i = 0; i < VALK_VM_SIZE_CLASSES; i++) {
    n = snprintf(p, end - p, "%s{\"size\":%u,\"used\":%llu,\"total\":%llu}",
      i > 0 ? "," : "",
      sizes[i],
      (unsigned long long)m->size_class_used[i],
      (unsigned long long)m->size_class_total[i]);
    if (n < 0 || p + n >= end) goto truncated;
    p += n;
  }

  n = snprintf(p, end - p,
    "],\"pause_histogram\":{\"0_1ms\":%llu,\"1_5ms\":%llu,\"5_10ms\":%llu,"
    "\"10_16ms\":%llu,\"16ms_plus\":%llu},",
    (unsigned long long)m->pause_0_1ms,
    (unsigned long long)m->pause_1_5ms,
    (unsigned long long)m->pause_5_10ms,
    (unsigned long long)m->pause_10_16ms,
    (unsigned long long)m->pause_16ms_plus);
  if (n < 0 || p + n >= end) goto truncated;
  p += n;

  n = snprintf(p, end - p,
    "\"survival\":{\"gen_0\":%llu,\"gen_1_5\":%llu,\"gen_6_20\":%llu,\"gen_21_plus\":%llu}},",
    (unsigned long long)m->survival_gen_0,
    (unsigned long long)m->survival_gen_1_5,
    (unsigned long long)m->survival_gen_6_20,
    (unsigned long long)m->survival_gen_21_plus);
  if (n < 0 || p + n >= end) goto truncated;
  p += n;

  n = snprintf(p, end - p,
    "\"interpreter\":{\"evals_total\":%llu,\"function_calls\":%llu,\"builtin_calls\":%llu,"
    "\"stack_depth_max\":%u,\"closures_created\":%llu,\"env_lookups\":%llu},"
    "\"event_loop\":{\"iterations\":%llu,\"events_processed\":%llu,"
    "\"idle_time_us\":%llu,\"idle_time_pct\":%.2f}}",
    (unsigned long long)m->eval_total,
    (unsigned long long)m->function_calls,
    (unsigned long long)m->builtin_calls,
    m->stack_depth_max,
    (unsigned long long)m->closures_created,
    (unsigned long long)m->env_lookups,
    (unsigned long long)m->loop_count,
    (unsigned long long)m->events_processed,
    (unsigned long long)m->idle_time_us,
    0.0);
  if (n < 0 || p + n >= end) goto truncated;

  return buf;

truncated:
  if (!alloc) free(buf);
  return nullptr;
}

char* valk_vm_metrics_to_json_compact(const valk_vm_metrics_t* m,
                                       valk_mem_allocator_t* alloc) {
  if (!m) return nullptr;

  u64 buf_size = 512;
  char* buf = alloc ? valk_mem_allocator_alloc(alloc, buf_size) : malloc(buf_size);
  if (!buf) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  double heap_util = m->gc_heap_total > 0
    ? 100.0 * (double)m->gc_heap_used / (double)m->gc_heap_total
    : 0.0;

  int n = snprintf(buf, buf_size,
    "{\"gc\":{\"heap_used\":%llu,\"heap_pct\":%.1f,\"cycles\":%llu},"
    "\"interp\":{\"evals\":%llu,\"calls\":%llu,\"builtins\":%llu},"
    "\"loop\":{\"iters\":%llu,\"events\":%llu}}",
    (unsigned long long)m->gc_heap_used,
    heap_util,
    (unsigned long long)m->gc_cycles,
    (unsigned long long)m->eval_total,
    (unsigned long long)m->function_calls,
    (unsigned long long)m->builtin_calls,
    (unsigned long long)m->loop_count,
    (unsigned long long)m->events_processed);

  if (n < 0 || (u64)n >= buf_size) {
    if (!alloc) free(buf);
    return nullptr;
  }

  return buf;
}

char* valk_vm_metrics_to_prometheus(const valk_vm_metrics_t* m,
                                     valk_mem_allocator_t* alloc) {
  if (!m) return nullptr;

  u64 buf_size = 4096;
  char* buf = alloc ? valk_mem_allocator_alloc(alloc, buf_size) : malloc(buf_size);
  if (!buf) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  double heap_util_ratio = m->gc_heap_total > 0
    ? (double)m->gc_heap_used / (double)m->gc_heap_total
    : 0.0;

  int written = snprintf(buf, buf_size,
    "# HELP valk_gc_cycles_total Total garbage collection cycles\n"
    "# TYPE valk_gc_cycles_total counter\n"
    "valk_gc_cycles_total %llu\n"
    "\n"
    "# HELP valk_gc_pause_seconds_total Total GC pause time in seconds\n"
    "# TYPE valk_gc_pause_seconds_total counter\n"
    "valk_gc_pause_seconds_total %.6f\n"
    "\n"
    "# HELP valk_gc_pause_seconds_max Maximum single GC pause in seconds\n"
    "# TYPE valk_gc_pause_seconds_max gauge\n"
    "valk_gc_pause_seconds_max %.6f\n"
    "\n"
    "# HELP valk_gc_reclaimed_bytes_total Total bytes reclaimed by GC\n"
    "# TYPE valk_gc_reclaimed_bytes_total counter\n"
    "valk_gc_reclaimed_bytes_total %llu\n"
    "\n"
    "# HELP valk_gc_heap_used_bytes Current heap memory in use\n"
    "# TYPE valk_gc_heap_used_bytes gauge\n"
    "valk_gc_heap_used_bytes %llu\n"
    "\n"
    "# HELP valk_gc_heap_total_bytes Total heap capacity\n"
    "# TYPE valk_gc_heap_total_bytes gauge\n"
    "valk_gc_heap_total_bytes %llu\n"
    "\n"
    "# HELP valk_gc_heap_utilization_ratio Heap utilization as ratio (0.0-1.0)\n"
    "# TYPE valk_gc_heap_utilization_ratio gauge\n"
    "valk_gc_heap_utilization_ratio %.6f\n"
    "\n"
    "# HELP valk_eval_total Total expression evaluations\n"
    "# TYPE valk_eval_total counter\n"
    "valk_eval_total %llu\n"
    "\n"
    "# HELP valk_function_calls_total User function invocations\n"
    "# TYPE valk_function_calls_total counter\n"
    "valk_function_calls_total %llu\n"
    "\n"
    "# HELP valk_builtin_calls_total Builtin function invocations\n"
    "# TYPE valk_builtin_calls_total counter\n"
    "valk_builtin_calls_total %llu\n"
    "\n"
    "# HELP valk_stack_depth_max Peak call stack depth\n"
    "# TYPE valk_stack_depth_max gauge\n"
    "valk_stack_depth_max %u\n"
    "\n"
    "# HELP valk_closures_created_total Lambda closures created\n"
    "# TYPE valk_closures_created_total counter\n"
    "valk_closures_created_total %llu\n"
    "\n"
    "# HELP valk_env_lookups_total Symbol resolution lookups\n"
    "# TYPE valk_env_lookups_total counter\n"
    "valk_env_lookups_total %llu\n"
    "\n"
    "# HELP valk_loop_iterations_total Event loop iterations\n"
    "# TYPE valk_loop_iterations_total counter\n"
    "valk_loop_iterations_total %llu\n"
    "\n"
    "# HELP valk_events_processed_total Events processed by event loop\n"
    "# TYPE valk_events_processed_total counter\n"
    "valk_events_processed_total %llu\n"
    "\n"
    "# HELP valk_loop_idle_seconds_total Time spent idle in event loop\n"
    "# TYPE valk_loop_idle_seconds_total counter\n"
    "valk_loop_idle_seconds_total %.6f\n",
    m->gc_cycles,
    (double)m->gc_pause_us_total / 1e6,
    (double)m->gc_pause_us_max / 1e6,
    m->gc_reclaimed_bytes,
    m->gc_heap_used,
    m->gc_heap_total,
    heap_util_ratio,
    m->eval_total,
    m->function_calls,
    m->builtin_calls,
    m->stack_depth_max,
    m->closures_created,
    m->env_lookups,
    m->loop_count,
    m->events_processed,
    (double)m->idle_time_us / 1e6
  );

  (void)written;
  return buf;
}

valk_aio_metrics_state_t* valk_aio_metrics_state_new(
    u64 arenas_total,
    u64 tcp_buffers_total,
    u64 queue_capacity,
    const char* loop_name) {
  valk_aio_metrics_state_t* state = calloc(1, sizeof(valk_aio_metrics_state_t));
  if (!state) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  state->gc_heap = nullptr;
  state->scratch_arena = nullptr;

  valk_aio_metrics_v2_t* m_v2 = calloc(1, sizeof(valk_aio_metrics_v2_t));
  if (m_v2 && valk_aio_metrics_v2_init(m_v2, loop_name)) {
    state->metrics_v2 = m_v2;
  } else {
    free(m_v2);
    state->metrics_v2 = nullptr;
  }

  valk_aio_system_stats_v2_t* s_v2 = calloc(1, sizeof(valk_aio_system_stats_v2_t));
  if (s_v2 && valk_aio_system_stats_v2_init(s_v2, loop_name, arenas_total, tcp_buffers_total, queue_capacity)) {
    state->system_stats_v2 = s_v2;
  } else {
    free(s_v2);
    state->system_stats_v2 = nullptr;
  }

  return state;
}

void valk_aio_metrics_state_free(valk_aio_metrics_state_t* state) {
  if (state) {
    free(state->metrics_v2);
    free(state->system_stats_v2);
    free(state);
  }
}
