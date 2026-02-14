#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"
#include "../../src/aio/aio_request_ctx.h"

extern void valk_register_ctx_builtins(valk_lenv_t *env);

static valk_lenv_t *create_test_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_register_ctx_builtins(env);
  return env;
}

static valk_lval_t *call_builtin(valk_lenv_t *env, const char *name, valk_lval_t *args) {
  valk_lval_t *sym = valk_lval_sym(name);
  valk_lval_t *fun = valk_lval_eval(env, sym);
  if (LVAL_TYPE(fun) == LVAL_ERR) {
    return fun;
  }
  return valk_lval_eval_call(env, fun, args);
}

void test_ctx_deadline_no_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "ctx/deadline", args);
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

void test_ctx_deadline_no_deadline(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.deadline_us = VALK_NO_DEADLINE};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "ctx/deadline", args);
    ASSERT_LVAL_TYPE(result, LVAL_NIL);
  }

  VALK_PASS();
}

void test_ctx_deadline_with_deadline(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t *ctx = valk_request_ctx_with_timeout(nullptr, 5000, &valk_malloc_allocator);

  VALK_WITH_REQUEST_CTX(ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "ctx/deadline", args);
    ASSERT_LVAL_TYPE(result, LVAL_NUM);
    ASSERT_TRUE(result->num > 0 && result->num <= 5000);
  }

  free(ctx);
  VALK_PASS();
}

void test_ctx_deadline_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "ctx/deadline", args);
  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 0 arguments");

  VALK_PASS();
}

void test_ctx_deadline_exceeded_no_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "ctx/deadline-exceeded?", args);
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

void test_ctx_deadline_exceeded_no_deadline(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.deadline_us = VALK_NO_DEADLINE};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "ctx/deadline-exceeded?", args);
    ASSERT_LVAL_TYPE(result, LVAL_NIL);
  }

  VALK_PASS();
}

void test_ctx_deadline_exceeded_false(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.deadline_us = valk_time_now_us() + 5000000};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "ctx/deadline-exceeded?", args);
    ASSERT_LVAL_TYPE(result, LVAL_NIL);
  }

  VALK_PASS();
}

void test_ctx_deadline_exceeded_true(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.deadline_us = valk_time_now_us() - 1000};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "ctx/deadline-exceeded?", args);
    ASSERT_LVAL_TYPE(result, LVAL_SYM);
    ASSERT_STR_EQ(result->str, ":true");
  }

  VALK_PASS();
}

void test_ctx_deadline_exceeded_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "ctx/deadline-exceeded?", args);
  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 0 arguments");

  VALK_PASS();
}

void test_ctx_get_no_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_sym(":key")}, 1);
  valk_lval_t *result = call_builtin(env, "ctx/get", args);
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

void test_ctx_get_key_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.locals = nullptr};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_sym(":key")}, 1);
    valk_lval_t *result = call_builtin(env, "ctx/get", args);
    ASSERT_LVAL_TYPE(result, LVAL_NIL);
  }

  VALK_PASS();
}

void test_ctx_get_key_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t *ctx = valk_request_ctx_new(&valk_malloc_allocator);
  valk_lval_t *key = valk_lval_sym(":user-id");
  valk_lval_t *value = valk_lval_num(42);
  ctx = valk_request_ctx_with_local(ctx, key, value, &valk_malloc_allocator);

  VALK_WITH_REQUEST_CTX(ctx) {
    valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_sym(":user-id")}, 1);
    valk_lval_t *result = call_builtin(env, "ctx/get", args);
    ASSERT_LVAL_TYPE(result, LVAL_NUM);
    ASSERT_EQ(result->num, 42);
  }

  free(ctx);
  VALK_PASS();
}

void test_ctx_get_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "ctx/get", args);
  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_ctx_get_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_sym(":key1"),
    valk_lval_sym(":key2")
  }, 2);
  valk_lval_t *result = call_builtin(env, "ctx/get", args);
  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_ctx_locals_no_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "ctx/locals", args);
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

void test_ctx_locals_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.locals = nullptr};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "ctx/locals", args);
    ASSERT_LVAL_TYPE(result, LVAL_NIL);
  }

  VALK_PASS();
}

void test_ctx_locals_non_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t *ctx = valk_request_ctx_new(&valk_malloc_allocator);
  valk_lval_t *key = valk_lval_sym(":user-id");
  valk_lval_t *value = valk_lval_num(42);
  ctx = valk_request_ctx_with_local(ctx, key, value, &valk_malloc_allocator);

  VALK_WITH_REQUEST_CTX(ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "ctx/locals", args);
    ASSERT_LVAL_TYPE(result, LVAL_CONS);
  }

  free(ctx);
  VALK_PASS();
}

void test_ctx_locals_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "ctx/locals", args);
  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 0 arguments");

  VALK_PASS();
}

void test_trace_id_no_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "trace/id", args);
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

void test_trace_id_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.trace_id = 0};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "trace/id", args);
    ASSERT_LVAL_TYPE(result, LVAL_NIL);
  }

  VALK_PASS();
}

void test_trace_id_non_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.trace_id = 12345};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "trace/id", args);
    ASSERT_LVAL_TYPE(result, LVAL_NUM);
    ASSERT_EQ(result->num, 12345);
  }

  VALK_PASS();
}

void test_trace_id_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "trace/id", args);
  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 0 arguments");

  VALK_PASS();
}

void test_trace_span_no_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "trace/span", args);
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

void test_trace_span_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.span_id = 0};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "trace/span", args);
    ASSERT_LVAL_TYPE(result, LVAL_NIL);
  }

  VALK_PASS();
}

void test_trace_span_non_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.span_id = 67890};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "trace/span", args);
    ASSERT_LVAL_TYPE(result, LVAL_NUM);
    ASSERT_EQ(result->num, 67890);
  }

  VALK_PASS();
}

void test_trace_span_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "trace/span", args);
  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 0 arguments");

  VALK_PASS();
}

void test_trace_parent_span_no_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "trace/parent-span", args);
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

void test_trace_parent_span_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.parent_span_id = 0};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "trace/parent-span", args);
    ASSERT_LVAL_TYPE(result, LVAL_NIL);
  }

  VALK_PASS();
}

void test_trace_parent_span_non_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t ctx = {.parent_span_id = 11111};

  VALK_WITH_REQUEST_CTX(&ctx) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = call_builtin(env, "trace/parent-span", args);
    ASSERT_LVAL_TYPE(result, LVAL_NUM);
    ASSERT_EQ(result->num, 11111);
  }

  VALK_PASS();
}

void test_trace_parent_span_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "trace/parent-span", args);
  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 0 arguments");

  VALK_PASS();
}

void test_trace_with_new_span(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_request_ctx_t *parent = valk_request_ctx_new(&valk_malloc_allocator);
  valk_request_ctx_t *child = valk_request_ctx_new_span(parent, &valk_malloc_allocator);

  VALK_WITH_REQUEST_CTX(child) {
    valk_lval_t *args = valk_lval_nil();

    valk_lval_t *trace_id = call_builtin(env, "trace/id", args);
    ASSERT_LVAL_TYPE(trace_id, LVAL_NUM);
    ASSERT_EQ(trace_id->num, (long)parent->trace_id);

    valk_lval_t *span_id = call_builtin(env, "trace/span", args);
    ASSERT_LVAL_TYPE(span_id, LVAL_NUM);
    ASSERT_EQ(span_id->num, (long)child->span_id);

    valk_lval_t *parent_span = call_builtin(env, "trace/parent-span", args);
    ASSERT_LVAL_TYPE(parent_span, LVAL_NUM);
    ASSERT_EQ(parent_span->num, (long)parent->span_id);
  }

  free(parent);
  free(child);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_ctx_deadline_no_ctx", test_ctx_deadline_no_ctx);
  valk_testsuite_add_test(suite, "test_ctx_deadline_no_deadline", test_ctx_deadline_no_deadline);
  valk_testsuite_add_test(suite, "test_ctx_deadline_with_deadline", test_ctx_deadline_with_deadline);
  valk_testsuite_add_test(suite, "test_ctx_deadline_wrong_args", test_ctx_deadline_wrong_args);
  valk_testsuite_add_test(suite, "test_ctx_deadline_exceeded_no_ctx", test_ctx_deadline_exceeded_no_ctx);
  valk_testsuite_add_test(suite, "test_ctx_deadline_exceeded_no_deadline", test_ctx_deadline_exceeded_no_deadline);
  valk_testsuite_add_test(suite, "test_ctx_deadline_exceeded_false", test_ctx_deadline_exceeded_false);
  valk_testsuite_add_test(suite, "test_ctx_deadline_exceeded_true", test_ctx_deadline_exceeded_true);
  valk_testsuite_add_test(suite, "test_ctx_deadline_exceeded_wrong_args", test_ctx_deadline_exceeded_wrong_args);
  valk_testsuite_add_test(suite, "test_ctx_get_no_ctx", test_ctx_get_no_ctx);
  valk_testsuite_add_test(suite, "test_ctx_get_key_not_found", test_ctx_get_key_not_found);
  valk_testsuite_add_test(suite, "test_ctx_get_key_found", test_ctx_get_key_found);
  valk_testsuite_add_test(suite, "test_ctx_get_wrong_args", test_ctx_get_wrong_args);
  valk_testsuite_add_test(suite, "test_ctx_get_too_many_args", test_ctx_get_too_many_args);
  valk_testsuite_add_test(suite, "test_ctx_locals_no_ctx", test_ctx_locals_no_ctx);
  valk_testsuite_add_test(suite, "test_ctx_locals_empty", test_ctx_locals_empty);
  valk_testsuite_add_test(suite, "test_ctx_locals_non_empty", test_ctx_locals_non_empty);
  valk_testsuite_add_test(suite, "test_ctx_locals_wrong_args", test_ctx_locals_wrong_args);
  valk_testsuite_add_test(suite, "test_trace_id_no_ctx", test_trace_id_no_ctx);
  valk_testsuite_add_test(suite, "test_trace_id_zero", test_trace_id_zero);
  valk_testsuite_add_test(suite, "test_trace_id_non_zero", test_trace_id_non_zero);
  valk_testsuite_add_test(suite, "test_trace_id_wrong_args", test_trace_id_wrong_args);
  valk_testsuite_add_test(suite, "test_trace_span_no_ctx", test_trace_span_no_ctx);
  valk_testsuite_add_test(suite, "test_trace_span_zero", test_trace_span_zero);
  valk_testsuite_add_test(suite, "test_trace_span_non_zero", test_trace_span_non_zero);
  valk_testsuite_add_test(suite, "test_trace_span_wrong_args", test_trace_span_wrong_args);
  valk_testsuite_add_test(suite, "test_trace_parent_span_no_ctx", test_trace_parent_span_no_ctx);
  valk_testsuite_add_test(suite, "test_trace_parent_span_zero", test_trace_parent_span_zero);
  valk_testsuite_add_test(suite, "test_trace_parent_span_non_zero", test_trace_parent_span_non_zero);
  valk_testsuite_add_test(suite, "test_trace_parent_span_wrong_args", test_trace_parent_span_wrong_args);
  valk_testsuite_add_test(suite, "test_trace_with_new_span", test_trace_with_new_span);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
