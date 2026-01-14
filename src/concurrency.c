#include "concurrency.h"

#include "common.h"
#include "memory.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define __assert_thread_safe_allocator()                                    \
  do {                                                                      \
    static valk_mem_allocator_e supported[] = {                             \
        VALK_ALLOC_MALLOC, VALK_ALLOC_SLAB, VALK_ALLOC_ARENA};              \
    bool found = 0;                                                         \
    for (u64 i = 0; i < sizeof(supported) / sizeof(supported[0]); ++i) { \
      if (supported[i] == valk_thread_ctx.allocator->type) {                \
        found = 1;                                                          \
      }                                                                     \
    }                                                                       \
    VALK_ASSERT(                                                            \
        found, "Current context is not thread safe: %s",                    \
        valk_mem_allocator_e_to_string(valk_thread_ctx.allocator->type));   \
  } while (0)

valk_arc_box *valk_arc_box_new(valk_res_t type, u64 capacity) {
  valk_arc_box *res = valk_mem_alloc(sizeof(valk_arc_box) + capacity);
  valk_arc_box_init(res, type, capacity);
  __assert_thread_safe_allocator();
  res->allocator = valk_thread_ctx.allocator;
  return res;
}

void valk_arc_box_init(valk_arc_box *self, valk_res_t type, u64 capacity) {
  memset(self, 0, sizeof(valk_arc_box) + capacity);
  self->type = type;
  self->refcount = 1;
  self->capacity = capacity;
  self->item = &((char *)self)[sizeof(valk_arc_box)];
  self->allocator = nullptr;
  self->free = nullptr;
  valk_capture_trace(VALK_TRACE_NEW, 1, self);
}

valk_arc_box *valk_arc_box_err(const char *msg) {
  int len = strlen(msg);
  valk_arc_box *res = valk_mem_alloc(sizeof(valk_arc_box) + len + 1);
  valk_arc_box_init(res, VALK_ERR, len + 1);
  strncpy(res->item, msg, len);
  return res;
}
