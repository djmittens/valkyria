#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"

#ifdef VALK_METRICS_ENABLED
#include "../../src/aio/aio_sse.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void valk_register_sse_builtins(valk_lenv_t *env);

static valk_lenv_t *create_test_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_register_sse_builtins(env);
  return env;
}

static valk_sse_stream_t *create_test_stream(void) {
  valk_sse_stream_t *stream = calloc(1, sizeof(valk_sse_stream_t));
  stream->state = VALK_SSE_OPEN;
  stream->queue_max = 100;
  stream->pending_capacity = 4096;
  stream->pending_data = malloc(stream->pending_capacity);
  stream->data_deferred = false;
  return stream;
}

static void free_test_stream(valk_sse_stream_t *stream) {
  if (!stream) return;
  valk_sse_event_t *event = stream->queue_head;
  while (event) {
    valk_sse_event_t *next = event->next;
    free(event);
    event = next;
  }
  if (stream->pending_data) free(stream->pending_data);
  free(stream);
}

static valk_lval_t *call_builtin(valk_lenv_t *env, const char *name, valk_lval_t *args) {
  valk_lval_t *sym = valk_lval_sym(name);
  valk_lval_t *fun = valk_lval_eval(env, sym);
  if (LVAL_TYPE(fun) == LVAL_ERR) {
    return fun;
  }
  return valk_lval_eval_call(env, fun, args);
}

void test_sse_open_no_context(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "sse/open", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_sse_open_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("not-a-ctx")
  }, 1);
  valk_lval_t *result = call_builtin(env, "sse/open", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "http request context");

  VALK_PASS();
}

void test_sse_send_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2-3 arguments");

  VALK_PASS();
}

void test_sse_send_one_arg(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("data")
  }, 1);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2-3 arguments");

  VALK_PASS();
}

void test_sse_send_four_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("a"),
    valk_lval_str("b"),
    valk_lval_str("c"),
    valk_lval_str("d")
  }, 4);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2-3 arguments");

  VALK_PASS();
}

void test_sse_send_wrong_stream_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("not-a-stream"),
    valk_lval_str("data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_send_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    fake_ref,
    valk_lval_str("data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_send_event_type_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("sse_stream", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    fake_ref,
    valk_lval_num(42),
    valk_lval_str("data")
  }, 3);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_send_data_wrong_type_2_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("sse_stream", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    fake_ref,
    valk_lval_num(42)
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_send_data_wrong_type_3_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("sse_stream", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    fake_ref,
    valk_lval_str("event_type"),
    valk_lval_num(42)
  }, 3);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_close_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "sse/close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_sse_close_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("not-a-stream")
  }, 1);
  valk_lval_t *result = call_builtin(env, "sse/close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_close_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){fake_ref}, 1);
  valk_lval_t *result = call_builtin(env, "sse/close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_writable_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "sse/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_sse_writable_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("not-a-stream")
  }, 1);
  valk_lval_t *result = call_builtin(env, "sse/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_writable_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){fake_ref}, 1);
  valk_lval_t *result = call_builtin(env, "sse/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_on_drain_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "sse/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  VALK_PASS();
}

void test_sse_on_drain_one_arg(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("stream")
  }, 1);
  valk_lval_t *result = call_builtin(env, "sse/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  VALK_PASS();
}

void test_sse_on_drain_wrong_stream_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *callback = valk_lval_lambda(valk_lenv_empty(), valk_lval_nil(), valk_lval_nil());
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("not-a-stream"),
    callback
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_on_drain_wrong_callback_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("sse_stream", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    fake_ref,
    valk_lval_str("not-a-function")
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be a function");

  VALK_PASS();
}

void test_sse_on_drain_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", NULL, NULL);
  valk_lval_t *callback = valk_lval_lambda(valk_lenv_empty(), valk_lval_nil(), valk_lval_nil());
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    fake_ref,
    callback
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_builtins_registered(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *sym = valk_lval_sym("sse/open");
  valk_lval_t *val = valk_lval_eval(env, sym);
  ASSERT_LVAL_TYPE(val, LVAL_FUN);

  sym = valk_lval_sym("sse/send");
  val = valk_lval_eval(env, sym);
  ASSERT_LVAL_TYPE(val, LVAL_FUN);

  sym = valk_lval_sym("sse/close");
  val = valk_lval_eval(env, sym);
  ASSERT_LVAL_TYPE(val, LVAL_FUN);

  sym = valk_lval_sym("sse/writable?");
  val = valk_lval_eval(env, sym);
  ASSERT_LVAL_TYPE(val, LVAL_FUN);

  sym = valk_lval_sym("sse/on-drain");
  val = valk_lval_eval(env, sym);
  ASSERT_LVAL_TYPE(val, LVAL_FUN);

  VALK_PASS();
}

void test_sse_send_null_stream_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *null_ref = valk_lval_ref("sse_stream", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    null_ref,
    valk_lval_str("data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  VALK_PASS();
}

void test_sse_close_null_stream_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *null_ref = valk_lval_ref("sse_stream", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){null_ref}, 1);
  valk_lval_t *result = call_builtin(env, "sse/close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_writable_null_stream_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *null_ref = valk_lval_ref("sse_stream", NULL, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){null_ref}, 1);
  valk_lval_t *result = call_builtin(env, "sse/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_send_with_valid_stream_2_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_sse_stream_t *stream = create_test_stream();

  valk_lval_t *stream_ref = valk_lval_ref("sse_stream", stream, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    stream_ref,
    valk_lval_str("test data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  VALK_TEST_ASSERT(result->num == 9, "Should return data length (9)");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_with_valid_stream_3_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_sse_stream_t *stream = create_test_stream();

  valk_lval_t *stream_ref = valk_lval_ref("sse_stream", stream, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    stream_ref,
    valk_lval_str("custom_event"),
    valk_lval_str("event payload")
  }, 3);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  VALK_TEST_ASSERT(result->num == 13, "Should return data length (13)");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_backpressure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_sse_stream_t *stream = create_test_stream();
  stream->queue_len = 100;
  stream->queue_max = 100;

  valk_lval_t *stream_ref = valk_lval_ref("sse_stream", stream, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    stream_ref,
    valk_lval_str("data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "backpressure");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_close_with_valid_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_sse_stream_t *stream = create_test_stream();

  valk_lval_t *stream_ref = valk_lval_ref("sse_stream", stream, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){stream_ref}, 1);
  valk_lval_t *result = call_builtin(env, "sse/close", args);

  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

void test_sse_writable_with_valid_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_sse_stream_t *stream = create_test_stream();

  valk_lval_t *stream_ref = valk_lval_ref("sse_stream", stream, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){stream_ref}, 1);
  valk_lval_t *result = call_builtin(env, "sse/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_SYM);
  VALK_TEST_ASSERT(strcmp(result->str, "true") == 0, "Empty queue should be writable");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_writable_full_queue(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_sse_stream_t *stream = create_test_stream();
  stream->queue_len = 100;
  stream->queue_max = 100;

  valk_lval_t *stream_ref = valk_lval_ref("sse_stream", stream, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){stream_ref}, 1);
  valk_lval_t *result = call_builtin(env, "sse/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_SYM);
  VALK_TEST_ASSERT(strcmp(result->str, "false") == 0, "Full queue should not be writable");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_on_drain_null_stream_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();

  valk_lval_t *null_ref = valk_lval_ref("sse_stream", NULL, NULL);
  valk_lval_t *callback = valk_lval_lambda(valk_lenv_empty(), valk_lval_nil(), valk_lval_nil());
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    null_ref,
    callback
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "SSE stream handle");

  VALK_PASS();
}

void test_sse_send_3_args_event_type_not_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_sse_stream_t *stream = create_test_stream();

  valk_lval_t *stream_ref = valk_lval_ref("sse_stream", stream, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    stream_ref,
    valk_lval_num(42),
    valk_lval_str("data")
  }, 3);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "event-type must be a string");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_3_args_data_not_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_sse_stream_t *stream = create_test_stream();

  valk_lval_t *stream_ref = valk_lval_ref("sse_stream", stream, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    stream_ref,
    valk_lval_str("event_type"),
    valk_lval_num(42)
  }, 3);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "data must be a string");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_2_args_data_not_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_sse_stream_t *stream = create_test_stream();

  valk_lval_t *stream_ref = valk_lval_ref("sse_stream", stream, NULL);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    stream_ref,
    valk_lval_num(42)
  }, 2);
  valk_lval_t *result = call_builtin(env, "sse/send", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "data must be a string");

  free_test_stream(stream);
  VALK_PASS();
}

#else

void test_sse_builtins_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("SSE builtins tests require VALK_METRICS_ENABLED");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_sse_open_no_context", test_sse_open_no_context);
  valk_testsuite_add_test(suite, "test_sse_open_wrong_args", test_sse_open_wrong_args);
  valk_testsuite_add_test(suite, "test_sse_send_no_args", test_sse_send_no_args);
  valk_testsuite_add_test(suite, "test_sse_send_one_arg", test_sse_send_one_arg);
  valk_testsuite_add_test(suite, "test_sse_send_four_args", test_sse_send_four_args);
  valk_testsuite_add_test(suite, "test_sse_send_wrong_stream_type", test_sse_send_wrong_stream_type);
  valk_testsuite_add_test(suite, "test_sse_send_wrong_ref_type", test_sse_send_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_sse_send_event_type_wrong_type", test_sse_send_event_type_wrong_type);
  valk_testsuite_add_test(suite, "test_sse_send_data_wrong_type_2_args", test_sse_send_data_wrong_type_2_args);
  valk_testsuite_add_test(suite, "test_sse_send_data_wrong_type_3_args", test_sse_send_data_wrong_type_3_args);
  valk_testsuite_add_test(suite, "test_sse_close_no_args", test_sse_close_no_args);
  valk_testsuite_add_test(suite, "test_sse_close_wrong_type", test_sse_close_wrong_type);
  valk_testsuite_add_test(suite, "test_sse_close_wrong_ref_type", test_sse_close_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_sse_writable_no_args", test_sse_writable_no_args);
  valk_testsuite_add_test(suite, "test_sse_writable_wrong_type", test_sse_writable_wrong_type);
  valk_testsuite_add_test(suite, "test_sse_writable_wrong_ref_type", test_sse_writable_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_sse_on_drain_no_args", test_sse_on_drain_no_args);
  valk_testsuite_add_test(suite, "test_sse_on_drain_one_arg", test_sse_on_drain_one_arg);
  valk_testsuite_add_test(suite, "test_sse_on_drain_wrong_stream_type", test_sse_on_drain_wrong_stream_type);
  valk_testsuite_add_test(suite, "test_sse_on_drain_wrong_callback_type", test_sse_on_drain_wrong_callback_type);
  valk_testsuite_add_test(suite, "test_sse_on_drain_wrong_ref_type", test_sse_on_drain_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_sse_builtins_registered", test_sse_builtins_registered);
  valk_testsuite_add_test(suite, "test_sse_send_null_stream_ref", test_sse_send_null_stream_ref);
  valk_testsuite_add_test(suite, "test_sse_close_null_stream_ref", test_sse_close_null_stream_ref);
  valk_testsuite_add_test(suite, "test_sse_writable_null_stream_ref", test_sse_writable_null_stream_ref);
  valk_testsuite_add_test(suite, "test_sse_send_with_valid_stream_2_args", test_sse_send_with_valid_stream_2_args);
  valk_testsuite_add_test(suite, "test_sse_send_with_valid_stream_3_args", test_sse_send_with_valid_stream_3_args);
  valk_testsuite_add_test(suite, "test_sse_send_backpressure", test_sse_send_backpressure);
  valk_testsuite_add_test(suite, "test_sse_close_with_valid_stream", test_sse_close_with_valid_stream);
  valk_testsuite_add_test(suite, "test_sse_writable_with_valid_stream", test_sse_writable_with_valid_stream);
  valk_testsuite_add_test(suite, "test_sse_writable_full_queue", test_sse_writable_full_queue);
  valk_testsuite_add_test(suite, "test_sse_on_drain_null_stream_ref", test_sse_on_drain_null_stream_ref);
  valk_testsuite_add_test(suite, "test_sse_send_3_args_event_type_not_string", test_sse_send_3_args_event_type_not_string);
  valk_testsuite_add_test(suite, "test_sse_send_3_args_data_not_string", test_sse_send_3_args_data_not_string);
  valk_testsuite_add_test(suite, "test_sse_send_2_args_data_not_string", test_sse_send_2_args_data_not_string);
#else
  valk_testsuite_add_test(suite, "test_sse_builtins_disabled", test_sse_builtins_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
