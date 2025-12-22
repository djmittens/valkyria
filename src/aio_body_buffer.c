#include "aio_body_buffer.h"
#include <string.h>

#define INITIAL_CAPACITY 4096
#define GROWTH_FACTOR 2

void valk_body_buffer_init(valk_body_buffer_t *bb, valk_mem_arena_t *arena) {
  bb->arena = arena;
  bb->data = nullptr;
  bb->len = 0;
  bb->capacity = 0;
}

static bool grow_buffer(valk_body_buffer_t *bb, size_t needed) {
  size_t new_capacity = bb->capacity == 0 ? INITIAL_CAPACITY : bb->capacity;
  while (new_capacity < needed) {
    new_capacity *= GROWTH_FACTOR;
  }

  uint8_t *new_data = valk_mem_arena_alloc(bb->arena, new_capacity);
  if (!new_data) {
    return false;
  }

  if (bb->data && bb->len > 0) {
    memcpy(new_data, bb->data, bb->len);
  }

  bb->data = new_data;
  bb->capacity = new_capacity;
  return true;
}

bool valk_body_buffer_append(valk_body_buffer_t *bb, const valk_body_chunk_t *chunk) {
  if (!chunk || !chunk->data || chunk->len == 0) {
    return true;
  }
  return valk_body_buffer_append_bytes(bb, chunk->data, chunk->len);
}

bool valk_body_buffer_append_bytes(valk_body_buffer_t *bb, const uint8_t *data, size_t len) {
  if (!data || len == 0) {
    return true;
  }

  size_t needed = bb->len + len;
  if (needed > bb->capacity) {
    if (!grow_buffer(bb, needed)) {
      return false;
    }
  }

  memcpy(bb->data + bb->len, data, len);
  bb->len += len;
  return true;
}

const uint8_t *valk_body_buffer_get(const valk_body_buffer_t *bb, size_t *len) {
  if (len) {
    *len = bb->len;
  }
  if (bb->len == 0) {
    return nullptr;
  }
  return bb->data;
}

void valk_body_buffer_reset(valk_body_buffer_t *bb) {
  bb->len = 0;
}

size_t valk_body_buffer_remaining(const valk_body_buffer_t *bb, size_t max_body_size) {
  if (bb->len >= max_body_size) {
    return 0;
  }
  return max_body_size - bb->len;
}
