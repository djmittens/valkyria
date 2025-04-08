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

void valk_buffer_alloc(valk_buffer_t *buf, size_t capacity);
void valk_buffer_append(valk_buffer_t *buf, void *bytes, size_t len);
int valk_buffer_is_full(valk_buffer_t *buf);

typedef struct {
  size_t handle;
  // size_t size; // todo(networking): i should add this to the layout if i need
  // it. i dont think this will ever be useful tho, so save a few bytes of
  // overhead
  char data[];
} valk_slab_item_t;

typedef struct {
  size_t itemSize;
  size_t numItems;
  size_t numFree;
  // Memory layout
  // [sizeof(size_t) * numSlabs | freeList]
  // [sizeof(valk_slab_t + (size_t * numSlabs)) * capacity | slabs]
  void *heap;
} valk_slab_t;

void valk_slab_alloc_init(valk_slab_t *self, size_t itemSize, size_t numItems);

void *valk_slab_alloc_reset(valk_slab_t *self, size_t safePoint);
void *valk_slab_alloc_free(valk_slab_t *self);

valk_slab_item_t *valk_slab_alloc_aquire(valk_slab_t *self);

void valk_slab_alloc_release(valk_slab_t *self, valk_slab_item_t *item);
void valk_slab_alloc_release_ptr(valk_slab_t *self, void *data);

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
