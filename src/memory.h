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

#define VALK_WITH_ALLOC(_alloc_)                                               \
  for (struct {                                                                \
         int exec;                                                             \
         void *old_alloc;                                                      \
       } __ctx = {1, valk_thread_ctx.allocator};                               \
       __ctx.exec; valk_thread_ctx.allocator = __ctx.old_alloc)                \
    for (valk_thread_ctx.allocator = (_alloc_); __ctx.exec; __ctx.exec = 0)

#define valk_mem_alloc(__bytes)                                                \
  valk_mem_allocator_alloc(valk_thread_ctx.allocator, (__bytes))

#define valk_mem_realloc(__ptr, __new_size)                                    \
  valk_mem_allocator_realloc(valk_thread_ctx.allocator, (__ptr), (__new_size))

#define valk_mem_calloc(__num, __size)                                         \
  valk_mem_allocator_calloc(valk_thread_ctx.allocator, (__num), (__size))

#define valk_mem_free(__ptr)                                                   \
  valk_mem_allocator_free(valk_thread_ctx.allocator, __ptr)

/// generic helper, same as Linux kernel’s container_of
/// @return the ptr of the right type
#define valk_container_of(ptr, type, member)                                   \
  ((type *)((char *)(ptr) - offsetof(type, member)))

typedef enum {
  VALK_ALLOC_NULL,
  VALK_ALLOC_MALLOC,
  VALK_ALLOC_ARENA,
  VALK_ALLOC_SLAB,
} valk_mem_allocator_e;

char *valk_mem_allocator_e_to_string(valk_mem_allocator_e self);

typedef struct {
  valk_mem_allocator_e type;
} valk_mem_allocator_t;

typedef struct {
  size_t capacity;
  size_t count;
  void *items;
} valk_buffer_t;

void valk_buffer_alloc(valk_buffer_t *buf, size_t capacity);
void valk_buffer_append(valk_buffer_t *buf, void *bytes, size_t len);
int valk_buffer_is_full(valk_buffer_t *buf);

typedef struct valk_slab_item_t {
  size_t handle;
  _Atomic(struct valk_slab_item_t *) next;
  // size_t size; // todo(networking): i should add this to the layout if i need
  // it. i dont think this will ever be useful tho, so save a few bytes of
  // overhead
  uint8_t data[];
} valk_slab_item_t;

typedef struct { // extends valk_mem_allocator_t;
  valk_mem_allocator_e type;
  size_t itemSize;
  size_t numItems;
  _Atomic size_t numFree;
  // treiber list top
  _Atomic(valk_slab_item_t *) top;
  // Memory layout
  // [sizeof(size_t) * numSlabs | freeList]
  // [sizeof(valk_slab_t + (size_t * numSlabs)) * capacity | slabs]
  _Atomic uint8_t heap[];
} valk_slab_t;

valk_slab_t *valk_slab_new(size_t itemSize, size_t numItems);
void valk_slab_init(valk_slab_t *self, size_t itemSize, size_t numItems);

void valk_slab_free(valk_slab_t *self);

/// @brief estimate the amount of bytes that are needed to contain the entire
/// slab
/// @return the total size that should be allocated, to initialize slab
size_t valk_slab_size(size_t itemSize, size_t numItems);

/// @brief estimate the the total chunk size in bytes of each item in the array
///
/// this is useful in cases where one would want to iterate over the chunks or
/// perhaps access a chunk at a particular offset
/// @param itemSize the concrete size of item without padding or headers
/// @return the actual size of the the item in memory including padding and
/// headers
size_t valk_slab_item_stride(size_t itemSize);

valk_slab_item_t *valk_slab_aquire(valk_slab_t *self);

void valk_slab_release(valk_slab_t *self, valk_slab_item_t *item);
void valk_slab_release_ptr(valk_slab_t *self, void *data);

typedef struct { // extends valk_mem_allocator_t;
  valk_mem_allocator_e type;
  size_t capacity;
  size_t offset;
  uint8_t heap[];
} valk_mem_arena_t;

void valk_mem_arena_init(valk_mem_arena_t *self, size_t capacity);
void valk_mem_arena_reset(valk_mem_arena_t *self);
void *valk_mem_arena_alloc(valk_mem_arena_t *self, size_t bytes);

typedef struct {
  valk_mem_allocator_t *allocator;
} valk_thread_context_t;

extern __thread valk_thread_context_t valk_thread_ctx;

void *valk_mem_allocator_alloc(valk_mem_allocator_t *self, size_t bytes);
void *valk_mem_allocator_realloc(valk_mem_allocator_t *self, void *ptr,
                                 size_t new_size);
void *valk_mem_allocator_calloc(valk_mem_allocator_t *self, size_t num,
                                size_t size);
void valk_mem_allocator_free(valk_mem_allocator_t *self, void *ptr);

void valk_mem_init_malloc();
