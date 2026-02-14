#include "aio_internal.h"
#include "aio_request_ctx.h"

static valk_request_ctx_t *get_current_request_ctx(void) {
  return valk_thread_ctx.request_ctx;
}

static valk_lval_t *valk_builtin_ctx_deadline(valk_lenv_t *e, valk_lval_t *a) {
  (void)e;
  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("ctx/deadline: expected 0 arguments");
  }

  valk_request_ctx_t *ctx = get_current_request_ctx();
  if (!ctx || ctx->deadline_us == VALK_NO_DEADLINE) {
    return valk_lval_nil();
  }

  u64 remaining_ms = valk_request_ctx_remaining_ms(ctx);
  return valk_lval_num((long)remaining_ms);
}

static valk_lval_t *valk_builtin_ctx_deadline_exceeded(valk_lenv_t *e, valk_lval_t *a) {
  (void)e;
  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("ctx/deadline-exceeded?: expected 0 arguments");
  }

  valk_request_ctx_t *ctx = get_current_request_ctx();
  if (valk_request_ctx_deadline_exceeded(ctx)) {
    return valk_lval_sym(":true");
  }
  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_ctx_get(valk_lenv_t *e, valk_lval_t *a) {
  (void)e;
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("ctx/get: expected 1 argument (key)");
  }

  valk_lval_t *key = valk_lval_list_nth(a, 0);
  valk_request_ctx_t *ctx = get_current_request_ctx();
  if (!ctx) {
    return valk_lval_nil();
  }

  valk_lval_t *val = valk_request_ctx_get_local(ctx, key);
  return val ? val : valk_lval_nil();
}

static valk_lval_t *valk_builtin_ctx_locals(valk_lenv_t *e, valk_lval_t *a) {
  (void)e;
  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("ctx/locals: expected 0 arguments");
  }

  valk_request_ctx_t *ctx = get_current_request_ctx();
  if (!ctx || !ctx->locals) {
    return valk_lval_nil();
  }

  return ctx->locals;
}

static valk_lval_t *valk_builtin_trace_id(valk_lenv_t *e, valk_lval_t *a) {
  (void)e;
  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("trace/id: expected 0 arguments");
  }

  valk_request_ctx_t *ctx = get_current_request_ctx();
  if (!ctx || ctx->trace_id == 0) {
    return valk_lval_nil();
  }

  return valk_lval_num((long)ctx->trace_id);
}

static valk_lval_t *valk_builtin_trace_span(valk_lenv_t *e, valk_lval_t *a) {
  (void)e;
  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("trace/span: expected 0 arguments");
  }

  valk_request_ctx_t *ctx = get_current_request_ctx();
  if (!ctx || ctx->span_id == 0) {
    return valk_lval_nil();
  }

  return valk_lval_num((long)ctx->span_id);
}

static valk_lval_t *valk_builtin_trace_parent_span(valk_lenv_t *e, valk_lval_t *a) {
  (void)e;
  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("trace/parent-span: expected 0 arguments");
  }

  valk_request_ctx_t *ctx = get_current_request_ctx();
  if (!ctx || ctx->parent_span_id == 0) {
    return valk_lval_nil();
  }

  return valk_lval_num((long)ctx->parent_span_id);
}

void valk_register_ctx_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "ctx/deadline", valk_builtin_ctx_deadline);
  valk_lenv_put_builtin(env, "ctx/deadline-exceeded?", valk_builtin_ctx_deadline_exceeded);
  valk_lenv_put_builtin(env, "ctx/get", valk_builtin_ctx_get);
  valk_lenv_put_builtin(env, "ctx/locals", valk_builtin_ctx_locals);

  valk_lenv_put_builtin(env, "trace/id", valk_builtin_trace_id);
  valk_lenv_put_builtin(env, "trace/span", valk_builtin_trace_span);
  valk_lenv_put_builtin(env, "trace/parent-span", valk_builtin_trace_parent_span);
}
