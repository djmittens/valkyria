// src/aio_metrics.h - AIO metrics collection
// V2 registry-based metrics are the canonical source for HTTP/AIO metrics.
// This header provides:
// - VM metrics types and functions (GC, interpreter, event loop)
// - Metrics state container
#ifndef VALK_AIO_METRICS_H
#define VALK_AIO_METRICS_H

#include "types.h"
#include "memory.h"
#include "gc.h"

typedef struct valk_aio_metrics_v2 valk_aio_metrics_v2_t;
typedef struct valk_aio_system_stats_v2 valk_aio_system_stats_v2_t;

struct uv_loop_s;

#define VALK_VM_SIZE_CLASSES 9

typedef struct {
  u64 gc_cycles;
  u64 gc_pause_us_total;
  u64 gc_pause_us_max;
  u64 gc_reclaimed_bytes;
  u64 gc_allocated_bytes;
  u8 gc_efficiency_pct;
  u64 gc_heap_used;
  u64 gc_heap_total;
  u64 gc_large_object_bytes;

  u64 size_class_used[VALK_VM_SIZE_CLASSES];
  u64 size_class_total[VALK_VM_SIZE_CLASSES];

  u64 pause_0_1ms;
  u64 pause_1_5ms;
  u64 pause_5_10ms;
  u64 pause_10_16ms;
  u64 pause_16ms_plus;

  u64 survival_gen_0;
  u64 survival_gen_1_5;
  u64 survival_gen_6_20;
  u64 survival_gen_21_plus;

  u64 eval_total;
  u64 function_calls;
  u64 builtin_calls;
  u32 stack_depth_max;
  u64 closures_created;
  u64 env_lookups;

  u64 loop_count;
  u64 events_processed;
  u64 idle_time_us;
} valk_vm_metrics_t;

void valk_vm_metrics_collect(valk_vm_metrics_t* out,
                              valk_gc_malloc_heap_t* heap,
                              struct uv_loop_s* loop);

char* valk_vm_metrics_to_json(const valk_vm_metrics_t* m,
                               valk_mem_allocator_t* alloc);

char* valk_vm_metrics_to_json_compact(const valk_vm_metrics_t* m,
                                       valk_mem_allocator_t* alloc);

char* valk_vm_metrics_to_prometheus(const valk_vm_metrics_t* m,
                                     valk_mem_allocator_t* alloc);

typedef struct {
  u64 loop_count;
  u64 events;
  u64 events_waiting;
  u64 idle_time_us;
} valk_event_loop_metrics_t;

void valk_event_loop_metrics_get(struct uv_loop_s* loop, valk_event_loop_metrics_t* out);

typedef struct valk_aio_metrics_state {
  valk_gc_malloc_heap_t *gc_heap;
  valk_mem_arena_t *scratch_arena;
  void *metrics_v2;
  void *system_stats_v2;
} valk_aio_metrics_state_t;

valk_aio_metrics_state_t* valk_aio_metrics_state_new(
    u64 arenas_total,
    u64 tcp_buffers_total,
    u64 queue_capacity,
    const char* loop_name);

void valk_aio_metrics_state_free(valk_aio_metrics_state_t* state);

#define VALK_METRICS_IF(sys) if ((sys) && (sys)->metrics_state)
#define VALK_METRICS_GET(sys) ((sys)->metrics_state)
#define VALK_METRICS_V2(sys) ((valk_aio_metrics_v2_t*)(sys)->metrics_state->metrics_v2)
#define VALK_SYSTEM_STATS_V2(sys) ((valk_aio_system_stats_v2_t*)(sys)->metrics_state->system_stats_v2)

#endif // VALK_AIO_METRICS_H
