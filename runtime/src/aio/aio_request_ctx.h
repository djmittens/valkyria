#pragma once

#include "types.h"
#include "memory.h"
#include <uv.h>

struct valk_lval_t;
struct valk_mem_allocator;

#define VALK_NO_DEADLINE 0

typedef struct valk_request_ctx {
  u64 trace_id;
  u64 span_id;
  u64 parent_span_id;
  u64 deadline_us;
  struct valk_lval_t *locals;
  valk_mem_allocator_t *allocator;
} valk_request_ctx_t;

static inline u64 valk_time_now_us(void) {
  return uv_hrtime() / 1000;
}

static inline u64 valk_time_now_ms(void) {
  return uv_hrtime() / 1000000;
}

static inline bool valk_request_ctx_has_deadline(valk_request_ctx_t *ctx) {
  return ctx && ctx->deadline_us != VALK_NO_DEADLINE;
}

static inline bool valk_request_ctx_deadline_exceeded(valk_request_ctx_t *ctx) {
  if (!ctx || ctx->deadline_us == VALK_NO_DEADLINE) return false;
  return valk_time_now_us() > ctx->deadline_us;
}

static inline u64 valk_request_ctx_remaining_us(valk_request_ctx_t *ctx) {
  if (!ctx || ctx->deadline_us == VALK_NO_DEADLINE) return UINT64_MAX;
  u64 now = valk_time_now_us();
  if (now >= ctx->deadline_us) return 0;
  return ctx->deadline_us - now;
}

static inline u64 valk_request_ctx_remaining_ms(valk_request_ctx_t *ctx) {
  u64 remaining_us = valk_request_ctx_remaining_us(ctx);
  if (remaining_us == UINT64_MAX) return UINT64_MAX;
  return remaining_us / 1000;
}

u64 valk_trace_id_generate(void);
u64 valk_span_id_generate(void);

valk_request_ctx_t *valk_request_ctx_new(valk_mem_allocator_t *allocator);

valk_request_ctx_t *valk_request_ctx_copy(valk_request_ctx_t *src, valk_mem_allocator_t *allocator);

valk_request_ctx_t *valk_request_ctx_with_deadline(valk_request_ctx_t *parent, u64 deadline_us, valk_mem_allocator_t *allocator);

valk_request_ctx_t *valk_request_ctx_with_timeout(valk_request_ctx_t *parent, u64 timeout_ms, valk_mem_allocator_t *allocator);

valk_request_ctx_t *valk_request_ctx_new_span(valk_request_ctx_t *parent, valk_mem_allocator_t *allocator);

valk_request_ctx_t *valk_request_ctx_with_local(valk_request_ctx_t *parent, struct valk_lval_t *key, struct valk_lval_t *value, valk_mem_allocator_t *allocator);

struct valk_lval_t *valk_request_ctx_get_local(valk_request_ctx_t *ctx, struct valk_lval_t *key);
