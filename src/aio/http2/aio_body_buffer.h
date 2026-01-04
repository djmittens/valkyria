#pragma once
#include "types.h"

#include <stddef.h>
#include <stdbool.h>
#include "memory.h"
#include "aio_body_view.h"

typedef struct valk_body_buffer {
  valk_mem_arena_t *arena;
  u8 *data;
  u64 len;
  u64 capacity;
} valk_body_buffer_t;

void valk_body_buffer_init(valk_body_buffer_t *bb, valk_mem_arena_t *arena);

bool valk_body_buffer_append(valk_body_buffer_t *bb, const valk_body_chunk_t *chunk);

bool valk_body_buffer_append_bytes(valk_body_buffer_t *bb, const u8 *data, u64 len);

const u8 *valk_body_buffer_get(const valk_body_buffer_t *bb, u64 *len);

void valk_body_buffer_reset(valk_body_buffer_t *bb);

u64 valk_body_buffer_remaining(const valk_body_buffer_t *bb, u64 max_body_size);
