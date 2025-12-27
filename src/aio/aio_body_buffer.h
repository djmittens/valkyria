#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include "../memory.h"
#include "aio_body_view.h"

typedef struct valk_body_buffer {
  valk_mem_arena_t *arena;
  uint8_t *data;
  size_t len;
  size_t capacity;
} valk_body_buffer_t;

void valk_body_buffer_init(valk_body_buffer_t *bb, valk_mem_arena_t *arena);

bool valk_body_buffer_append(valk_body_buffer_t *bb, const valk_body_chunk_t *chunk);

bool valk_body_buffer_append_bytes(valk_body_buffer_t *bb, const uint8_t *data, size_t len);

const uint8_t *valk_body_buffer_get(const valk_body_buffer_t *bb, size_t *len);

void valk_body_buffer_reset(valk_body_buffer_t *bb);

size_t valk_body_buffer_remaining(const valk_body_buffer_t *bb, size_t max_body_size);
