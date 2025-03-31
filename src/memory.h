#pragma once

#include <stdint.h>
#include <stdio.h>

#define VALK_WITH_CTX(_ctx_)                                                   \
  for (struct {                                                                \
         int exec;                                                             \
         valk_thread_context_t old_ctx;                                        \
       } __ctx = {1, valk_thread_ctx};                                         \
       __ctx.exec; valk_thread_ctx = __ctx.old_ctx)                            \
    for (valk_thread_ctx = (_ctx_); __ctx.exec; __ctx.exec = 0)


typedef struct {
  size_t capacity;
  size_t count;
  void *items;
} valk_buffer_t;

void valk_alloc_buffer(valk_buffer_t *buf, size_t capacity);

typedef enum {
  VALK_ALLOC_MALLOC,
  VALK_ALLOC_ARENA,
} valk_mem_allocator_e;

typedef struct {
  valk_mem_allocator_e allocType;
  // TODO(networking): use valk_buffer_t for this 
  void *heap;
  void *(*alloc)(void *heap, size_t bytes);
  void (*free)(void *heap, void *ptr);
} valk_thread_context_t;

extern __thread valk_thread_context_t valk_thread_ctx;

static inline void *valk_mem_alloc(size_t bytes) {
  return valk_thread_ctx.alloc(valk_thread_ctx.heap, bytes);
}

static inline void valk_mem_free(void *ptr) {
  printf("Freeing %p\n", ptr);
  valk_thread_ctx.free(valk_thread_ctx.heap, ptr);
}

void valk_mem_init_malloc();
