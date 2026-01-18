#include "aio_request_ctx.h"
#include "parser.h"
#include <string.h>

static _Atomic u64 g_trace_id_counter = 1;
static _Atomic u64 g_span_id_counter = 1;

u64 valk_trace_id_generate(void) {
  u64 counter = atomic_fetch_add(&g_trace_id_counter, 1);
  u64 time_component = valk_time_now_us() & 0xFFFFFFFF00000000ULL;
  return time_component | (counter & 0xFFFFFFFF);
}

u64 valk_span_id_generate(void) {
  u64 counter = atomic_fetch_add(&g_span_id_counter, 1);
  u64 time_component = (valk_time_now_us() >> 10) & 0xFFFFFF0000000000ULL;
  return time_component | (counter & 0xFFFFFFFFFF);
}

valk_request_ctx_t *valk_request_ctx_new(valk_mem_allocator_t *allocator) {
  valk_request_ctx_t *ctx = valk_mem_allocator_alloc(allocator, sizeof(valk_request_ctx_t));
  if (!ctx) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  ctx->trace_id = valk_trace_id_generate();
  ctx->span_id = valk_span_id_generate();
  ctx->parent_span_id = 0;
  ctx->deadline_us = VALK_NO_DEADLINE;
  ctx->locals = nullptr;
  ctx->allocator = allocator;
  return ctx;
}

valk_request_ctx_t *valk_request_ctx_copy(valk_request_ctx_t *src, valk_mem_allocator_t *allocator) {
  if (!src) return valk_request_ctx_new(allocator);

  valk_request_ctx_t *ctx = valk_mem_allocator_alloc(allocator, sizeof(valk_request_ctx_t));
  if (!ctx) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  *ctx = *src;
  ctx->allocator = allocator;
  return ctx;
}

valk_request_ctx_t *valk_request_ctx_with_deadline(valk_request_ctx_t *parent, u64 deadline_us, valk_mem_allocator_t *allocator) {
  valk_request_ctx_t *ctx = valk_request_ctx_copy(parent, allocator);
  if (!ctx) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  if (ctx->deadline_us == VALK_NO_DEADLINE || deadline_us < ctx->deadline_us) {
    ctx->deadline_us = deadline_us;
  }
  return ctx;
}

valk_request_ctx_t *valk_request_ctx_with_timeout(valk_request_ctx_t *parent, u64 timeout_ms, valk_mem_allocator_t *allocator) {
  u64 deadline_us = valk_time_now_us() + (timeout_ms * 1000);
  return valk_request_ctx_with_deadline(parent, deadline_us, allocator);
}

valk_request_ctx_t *valk_request_ctx_new_span(valk_request_ctx_t *parent, valk_mem_allocator_t *allocator) {
  valk_request_ctx_t *ctx = valk_mem_allocator_alloc(allocator, sizeof(valk_request_ctx_t));
  if (!ctx) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  if (parent) {
    ctx->trace_id = parent->trace_id;
    ctx->parent_span_id = parent->span_id;
    ctx->deadline_us = parent->deadline_us;
    ctx->locals = parent->locals;
  } else {
    ctx->trace_id = valk_trace_id_generate();
    ctx->parent_span_id = 0;
    ctx->deadline_us = VALK_NO_DEADLINE;
    ctx->locals = nullptr;
  }

  ctx->span_id = valk_span_id_generate();
  ctx->allocator = allocator;
  return ctx;
}

valk_request_ctx_t *valk_request_ctx_with_local(valk_request_ctx_t *parent, valk_lval_t *key, valk_lval_t *value, valk_mem_allocator_t *allocator) {
  valk_request_ctx_t *ctx = valk_request_ctx_copy(parent, allocator);
  if (!ctx) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  valk_lval_t *pair = valk_lval_cons(key, value);
  ctx->locals = valk_lval_cons(pair, ctx->locals);
  return ctx;
}

valk_lval_t *valk_request_ctx_get_local(valk_request_ctx_t *ctx, valk_lval_t *key) {
  if (!ctx || !ctx->locals || !key) return nullptr;

  valk_lval_t *curr = ctx->locals;
  while (curr && LVAL_TYPE(curr) == LVAL_CONS) {
    valk_lval_t *pair = curr->cons.head;
    if (pair && LVAL_TYPE(pair) == LVAL_CONS) {
      valk_lval_t *k = pair->cons.head;
      if (k && LVAL_TYPE(k) == LVAL_TYPE(key)) {
        if (LVAL_TYPE(k) == LVAL_SYM && strcmp(k->str, key->str) == 0) {
          return pair->cons.tail;
        }
        if (LVAL_TYPE(k) == LVAL_STR && strcmp(k->str, key->str) == 0) {
          return pair->cons.tail;
        }
        if (LVAL_TYPE(k) == LVAL_NUM && k->num == key->num) {
          return pair->cons.tail;
        }
      }
    }
    curr = curr->cons.tail;
  }
  return nullptr;
}
