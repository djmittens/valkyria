#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"
#include "../../src/gc.h"
#include "../../src/aio/http2/stream/aio_stream_body.h"
#include "../../src/aio/aio_internal.h"

extern void valk_register_stream_builtins(valk_lenv_t *env);

static valk_lenv_t *create_test_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_register_stream_builtins(env);
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

static valk_stream_body_t *create_test_body(valk_aio_handle_t *conn, i32 stream_id) {
  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->id = (u64)stream_id;
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = stream_id;
  body->next = nullptr;
  body->bytes_sent = 0;
  body->last_activity_ms = 0;
  body->idle_timeout_ms = 0;
  body->queue_max = 16;
  body->queue_len = 0;
  body->lisp_on_drain_handle = (valk_handle_t){0};
  body->lisp_on_close_handle = (valk_handle_t){0};
  return body;
}

static void free_test_body(valk_stream_body_t *body) {
  free(body);
}

static valk_aio_handle_t *create_test_conn(void) {
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = 0xBA1CADA1;
  conn->http.stream_bodies = nullptr;
  conn->http.session = nullptr;
  return conn;
}

static void free_test_conn(valk_aio_handle_t *conn) {
  free(conn);
}

static valk_lval_t *make_stream_body_ref(valk_stream_body_t *body) {
  return valk_lval_ref("stream_body", body, nullptr);
}

void test_stream_write_wrong_arg_count_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "stream/write", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  VALK_PASS();
}

void test_stream_write_wrong_arg_count_one(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/write", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_write_invalid_body_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_num(42),
    valk_lval_str("data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/write", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}

void test_stream_write_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *wrong_ref = valk_lval_ref("other_type", nullptr, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    wrong_ref,
    valk_lval_str("data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/write", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}

void test_stream_write_data_not_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_stream_body_ref(body),
    valk_lval_num(123)
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/write", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be a string");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_writable_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "stream/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_stream_writable_invalid_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_EQ(result->num, 0);

  VALK_PASS();
}

void test_stream_writable_closed_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSED;

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_EQ(result->num, 0);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_writable_closing_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSING;

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_EQ(result->num, 0);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_writable_open_body_no_session(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_OPEN;
  body->queue_len = 0;
  body->queue_max = 16;
  body->session = nullptr;

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/writable?", args);

  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_EQ(result->num, 0);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_close_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "stream/close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_stream_close_invalid_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}

void test_stream_close_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_OPEN;

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/close", args);

  ASSERT_LVAL_TYPE(result, LVAL_NIL);
  ASSERT_EQ(body->state, VALK_STREAM_CLOSING);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_on_drain_wrong_arg_count_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "stream/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  VALK_PASS();
}

void test_stream_on_drain_wrong_arg_count_one(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_on_drain_invalid_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_num(42),
    valk_lval_str("not a function")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}

void test_stream_on_drain_callback_not_function(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_stream_body_ref(body),
    valk_lval_str("not a function")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be a function");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_on_close_wrong_arg_count_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "stream/on-close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  VALK_PASS();
}

void test_stream_on_close_wrong_arg_count_one(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/on-close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_on_close_invalid_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_num(42),
    valk_lval_str("not a function")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/on-close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}

void test_stream_on_close_callback_not_function(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_stream_body_ref(body),
    valk_lval_str("not a function")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/on-close", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be a function");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_set_timeout_wrong_arg_count_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "stream/set-timeout", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  VALK_PASS();
}

void test_stream_set_timeout_wrong_arg_count_one(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/set-timeout", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_set_timeout_invalid_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_num(42),
    valk_lval_num(5000)
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/set-timeout", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}

void test_stream_set_timeout_not_number(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_stream_body_ref(body),
    valk_lval_str("not a number")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/set-timeout", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be a number");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_set_timeout_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  valk_lval_t *body_ref = make_stream_body_ref(body);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    body_ref,
    valk_lval_num(5000)
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/set-timeout", args);

  ASSERT_LVAL_TYPE(result, LVAL_REF);
  ASSERT_EQ(body->idle_timeout_ms, 5000);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_cancel_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "stream/cancel", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_stream_cancel_invalid_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/cancel", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}

void test_stream_id_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "stream/id", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_stream_id_invalid_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/id", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}

void test_stream_id_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 42);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/id", args);

  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_EQ(result->num, 42);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_open_wrong_arg_count_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "stream/open", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1-2 arguments");

  VALK_PASS();
}

void test_stream_open_wrong_arg_count_three(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_num(1),
    valk_lval_num(2),
    valk_lval_num(3)
  }, 3);
  valk_lval_t *result = call_builtin(env, "stream/open", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1-2 arguments");

  VALK_PASS();
}

void test_stream_open_first_arg_not_request(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/open", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be http request");

  VALK_PASS();
}

void test_stream_open_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *wrong_ref = valk_lval_ref("stream_body", nullptr, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){wrong_ref}, 1);
  valk_lval_t *result = call_builtin(env, "stream/open", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be http request");

  VALK_PASS();
}

void test_get_stream_body_null_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_nil()}, 1);
  valk_lval_t *result = call_builtin(env, "stream/id", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}

void test_get_stream_body_wrong_type_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *ref_with_wrong_type = valk_lval_ref("other_type", (void *)0x1234, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){ref_with_wrong_type}, 1);
  valk_lval_t *result = call_builtin(env, "stream/id", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be stream body handle");

  VALK_PASS();
}


void test_stream_on_drain_success_with_runtime(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);

  valk_lval_t *formals = valk_lval_nil();
  valk_lval_t *fn_body = valk_lval_num(42);
  valk_lval_t *callback = valk_lval_lambda(env, formals, fn_body);

  valk_lval_t *body_ref = make_stream_body_ref(body);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){body_ref, callback}, 2);
  valk_lval_t *result = call_builtin(env, "stream/on-drain", args);

  ASSERT_LVAL_TYPE(result, LVAL_REF);
  ASSERT_TRUE(body->lisp_on_drain_handle.generation > 0);
  ASSERT_EQ(body->callback_env, env);

  valk_handle_release(&valk_global_handle_table, body->lisp_on_drain_handle);
  free_test_body(body);
  free_test_conn(conn);
  valk_runtime_shutdown();

  VALK_PASS();
}

void test_stream_on_drain_replaces_existing(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);

  valk_lval_t *formals = valk_lval_nil();
  valk_lval_t *fn_body = valk_lval_num(1);
  valk_lval_t *callback1 = valk_lval_lambda(env, formals, fn_body);

  valk_lval_t *body_ref = make_stream_body_ref(body);
  valk_lval_t *args1 = valk_lval_list((valk_lval_t*[]){body_ref, callback1}, 2);
  call_builtin(env, "stream/on-drain", args1);

  u32 old_generation = body->lisp_on_drain_handle.generation;

  valk_lval_t *fn_body2 = valk_lval_num(2);
  valk_lval_t *callback2 = valk_lval_lambda(env, formals, fn_body2);
  valk_lval_t *args2 = valk_lval_list((valk_lval_t*[]){body_ref, callback2}, 2);
  call_builtin(env, "stream/on-drain", args2);

  ASSERT_TRUE(body->lisp_on_drain_handle.generation > old_generation);

  valk_handle_release(&valk_global_handle_table, body->lisp_on_drain_handle);
  free_test_body(body);
  free_test_conn(conn);
  valk_runtime_shutdown();

  VALK_PASS();
}

void test_stream_on_close_success_with_runtime(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);

  valk_lval_t *formals = valk_lval_nil();
  valk_lval_t *fn_body = valk_lval_num(42);
  valk_lval_t *callback = valk_lval_lambda(env, formals, fn_body);

  valk_lval_t *body_ref = make_stream_body_ref(body);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){body_ref, callback}, 2);
  valk_lval_t *result = call_builtin(env, "stream/on-close", args);

  ASSERT_LVAL_TYPE(result, LVAL_REF);
  ASSERT_TRUE(body->lisp_on_close_handle.generation > 0);
  ASSERT_EQ(body->callback_env, env);

  valk_handle_release(&valk_global_handle_table, body->lisp_on_close_handle);
  free_test_body(body);
  free_test_conn(conn);
  valk_runtime_shutdown();

  VALK_PASS();
}

void test_stream_on_close_replaces_existing(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);

  valk_lval_t *formals = valk_lval_nil();
  valk_lval_t *fn_body = valk_lval_num(1);
  valk_lval_t *callback1 = valk_lval_lambda(env, formals, fn_body);

  valk_lval_t *body_ref = make_stream_body_ref(body);
  valk_lval_t *args1 = valk_lval_list((valk_lval_t*[]){body_ref, callback1}, 2);
  call_builtin(env, "stream/on-close", args1);

  u32 old_generation = body->lisp_on_close_handle.generation;

  valk_lval_t *fn_body2 = valk_lval_num(2);
  valk_lval_t *callback2 = valk_lval_lambda(env, formals, fn_body2);
  valk_lval_t *args2 = valk_lval_list((valk_lval_t*[]){body_ref, callback2}, 2);
  call_builtin(env, "stream/on-close", args2);

  ASSERT_TRUE(body->lisp_on_close_handle.generation > old_generation);

  valk_handle_release(&valk_global_handle_table, body->lisp_on_close_handle);
  free_test_body(body);
  free_test_conn(conn);
  valk_runtime_shutdown();

  VALK_PASS();
}

void test_stream_cancel_already_closed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSED;

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/cancel", args);

  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_cancel_no_session(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->session = nullptr;

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_stream_body_ref(body)}, 1);
  valk_lval_t *result = call_builtin(env, "stream/cancel", args);

  ASSERT_LVAL_TYPE(result, LVAL_NIL);
  ASSERT_EQ(body->state, VALK_STREAM_CLOSING);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_write_body_closed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSED;

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_stream_body_ref(body),
    valk_lval_str("test data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/write", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "failed with code -1");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_write_body_closing(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSING;

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_stream_body_ref(body),
    valk_lval_str("test data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/write", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "failed with code -1");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_stream_write_queue_full(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->queue_len = body->queue_max;

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_stream_body_ref(body),
    valk_lval_str("test data")
  }, 2);
  valk_lval_t *result = call_builtin(env, "stream/write", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "queue full");

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_stream_write_wrong_arg_count_zero", test_stream_write_wrong_arg_count_zero);
  valk_testsuite_add_test(suite, "test_stream_write_wrong_arg_count_one", test_stream_write_wrong_arg_count_one);
  valk_testsuite_add_test(suite, "test_stream_write_invalid_body_ref", test_stream_write_invalid_body_ref);
  valk_testsuite_add_test(suite, "test_stream_write_wrong_ref_type", test_stream_write_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_stream_write_data_not_string", test_stream_write_data_not_string);

  valk_testsuite_add_test(suite, "test_stream_writable_wrong_arg_count", test_stream_writable_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_stream_writable_invalid_body", test_stream_writable_invalid_body);
  valk_testsuite_add_test(suite, "test_stream_writable_closed_body", test_stream_writable_closed_body);
  valk_testsuite_add_test(suite, "test_stream_writable_closing_body", test_stream_writable_closing_body);
  valk_testsuite_add_test(suite, "test_stream_writable_open_body_no_session", test_stream_writable_open_body_no_session);

  valk_testsuite_add_test(suite, "test_stream_close_wrong_arg_count", test_stream_close_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_stream_close_invalid_body", test_stream_close_invalid_body);
  valk_testsuite_add_test(suite, "test_stream_close_success", test_stream_close_success);

  valk_testsuite_add_test(suite, "test_stream_on_drain_wrong_arg_count_zero", test_stream_on_drain_wrong_arg_count_zero);
  valk_testsuite_add_test(suite, "test_stream_on_drain_wrong_arg_count_one", test_stream_on_drain_wrong_arg_count_one);
  valk_testsuite_add_test(suite, "test_stream_on_drain_invalid_body", test_stream_on_drain_invalid_body);
  valk_testsuite_add_test(suite, "test_stream_on_drain_callback_not_function", test_stream_on_drain_callback_not_function);

  valk_testsuite_add_test(suite, "test_stream_on_close_wrong_arg_count_zero", test_stream_on_close_wrong_arg_count_zero);
  valk_testsuite_add_test(suite, "test_stream_on_close_wrong_arg_count_one", test_stream_on_close_wrong_arg_count_one);
  valk_testsuite_add_test(suite, "test_stream_on_close_invalid_body", test_stream_on_close_invalid_body);
  valk_testsuite_add_test(suite, "test_stream_on_close_callback_not_function", test_stream_on_close_callback_not_function);

  valk_testsuite_add_test(suite, "test_stream_set_timeout_wrong_arg_count_zero", test_stream_set_timeout_wrong_arg_count_zero);
  valk_testsuite_add_test(suite, "test_stream_set_timeout_wrong_arg_count_one", test_stream_set_timeout_wrong_arg_count_one);
  valk_testsuite_add_test(suite, "test_stream_set_timeout_invalid_body", test_stream_set_timeout_invalid_body);
  valk_testsuite_add_test(suite, "test_stream_set_timeout_not_number", test_stream_set_timeout_not_number);
  valk_testsuite_add_test(suite, "test_stream_set_timeout_success", test_stream_set_timeout_success);

  valk_testsuite_add_test(suite, "test_stream_cancel_wrong_arg_count", test_stream_cancel_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_stream_cancel_invalid_body", test_stream_cancel_invalid_body);

  valk_testsuite_add_test(suite, "test_stream_id_wrong_arg_count", test_stream_id_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_stream_id_invalid_body", test_stream_id_invalid_body);
  valk_testsuite_add_test(suite, "test_stream_id_success", test_stream_id_success);

  valk_testsuite_add_test(suite, "test_stream_open_wrong_arg_count_zero", test_stream_open_wrong_arg_count_zero);
  valk_testsuite_add_test(suite, "test_stream_open_wrong_arg_count_three", test_stream_open_wrong_arg_count_three);
  valk_testsuite_add_test(suite, "test_stream_open_first_arg_not_request", test_stream_open_first_arg_not_request);
  valk_testsuite_add_test(suite, "test_stream_open_wrong_ref_type", test_stream_open_wrong_ref_type);

  valk_testsuite_add_test(suite, "test_get_stream_body_null_ref", test_get_stream_body_null_ref);
  valk_testsuite_add_test(suite, "test_get_stream_body_wrong_type_string", test_get_stream_body_wrong_type_string);

  valk_testsuite_add_test(suite, "test_stream_on_drain_success_with_runtime", test_stream_on_drain_success_with_runtime);
  valk_testsuite_add_test(suite, "test_stream_on_drain_replaces_existing", test_stream_on_drain_replaces_existing);
  valk_testsuite_add_test(suite, "test_stream_on_close_success_with_runtime", test_stream_on_close_success_with_runtime);
  valk_testsuite_add_test(suite, "test_stream_on_close_replaces_existing", test_stream_on_close_replaces_existing);

  valk_testsuite_add_test(suite, "test_stream_cancel_already_closed", test_stream_cancel_already_closed);
  valk_testsuite_add_test(suite, "test_stream_cancel_no_session", test_stream_cancel_no_session);

  valk_testsuite_add_test(suite, "test_stream_write_body_closed", test_stream_write_body_closed);
  valk_testsuite_add_test(suite, "test_stream_write_body_closing", test_stream_write_body_closing);
  valk_testsuite_add_test(suite, "test_stream_write_queue_full", test_stream_write_queue_full);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
