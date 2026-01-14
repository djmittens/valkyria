#pragma once

#include "memory.h"

#define valk_arc_retain(ref)                                                  \
  ({                                                                          \
    u64 __old = __atomic_fetch_add(&(ref)->refcount, 1, __ATOMIC_RELEASE); \
    valk_capture_trace(VALK_TRACE_ACQUIRE, __old + 1, ref);                   \
    (ref);                                                                    \
  })

#define valk_arc_release(ref)                                               \
  do {                                                                      \
    u64 old = __atomic_fetch_sub(&(ref)->refcount, 1, __ATOMIC_RELEASE); \
    valk_capture_trace(VALK_TRACE_RELEASE, old - 1, ref);                   \
    if (old == 1) {                                                         \
      if ((ref)->free) {                                                    \
        valk_arc_trace_report_print(ref);                                   \
        (ref)->free(ref);                                                   \
      } else if ((ref)->allocator) {                                        \
        valk_mem_allocator_free((ref)->allocator, (ref));                   \
      }                                                                     \
    }                                                                       \
  } while (0)

typedef enum { VALK_SUC, VALK_ERR } valk_res_t;

typedef struct valk_arc_box {
  valk_res_t type;
  u64 refcount;
  valk_mem_allocator_t *allocator;
#ifdef VALK_ARC_DEBUG
  valk_arc_trace_info traces[VALK_ARC_TRACE_MAX];
  u64 nextTrace;
#endif
  void (*free)(struct valk_arc_box *);
  u64 capacity;
  void *item;
} valk_arc_box;

valk_arc_box *valk_arc_box_new(valk_res_t type, u64 capacity);
void valk_arc_box_init(valk_arc_box *self, valk_res_t type, u64 capacity);
valk_arc_box *valk_arc_box_err(const char *msg);
