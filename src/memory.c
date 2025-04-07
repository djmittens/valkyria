#include "memory.h"
#include "common.h"
#include <stdlib.h>
#include <string.h>

__thread valk_thread_context_t valk_thread_ctx = {0};

static void *__valk_mem_malloc(void *heap, size_t bytes) {
  UNUSED(heap);
  return malloc(bytes);
}

static void __valk_mem_malloc_free(void *heap, void *ptr) {
  UNUSED(heap);
  free(ptr);
}

void valk_mem_init_malloc() {
  valk_thread_ctx.allocType = VALK_ALLOC_MALLOC;
  valk_thread_ctx.heap = NULL;
  valk_thread_ctx.alloc = __valk_mem_malloc;
  valk_thread_ctx.free = __valk_mem_malloc_free;
}

/// ARENA ALLOCATOR
typedef struct {
  size_t offset;
  size_t capacity;
  void *data;
} valk_mem_arena_t;

static void *__valk_mem_arena(void *heap, size_t bytes) {}

static void __valk_mem_arena_free(void *heap, void *ptr) {
  UNUSED(heap);
  UNUSED(ptr);
  // Frees are disabled for arenas
}

void valk_buffer_alloc(valk_buffer_t *buf, size_t capacity) {
  buf->capacity = capacity;
  buf->count = 0;
  // TODO(networking): use mmap with page aligned shit for this instead
  buf->items = valk_mem_alloc(capacity);
}

void valk_buffer_append(valk_buffer_t *buf, void *bytes, size_t len) {
  VALK_ASSERT(
      buf->capacity > (buf->count + len),
      "Buffer too small !!!  capacity [%ld] :: count [%ld] :: new bytes [%ld]",
      buf->capacity, buf->count, len);
  memcpy(&((char *)buf->items)[buf->count], bytes, len);
  buf->count += len;
}

int valk_buffer_is_full(valk_buffer_t *buf) {
  return (buf->capacity - buf->count) < 1;
}
