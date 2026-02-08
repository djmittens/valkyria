#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"
#include "../../src/aio/aio_internal.h"

extern void valk_register_http_request_builtins(valk_lenv_t *env);

static valk_lenv_t *create_test_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_register_http_request_builtins(env);
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

static valk_lval_t *make_request_ref(valk_http2_server_request_t *req) {
  return valk_lval_ref("http_request", req, nullptr);
}

static valk_http2_server_request_t *create_test_request(void) {
  valk_http2_server_request_t *req = calloc(1, sizeof(valk_http2_server_request_t));
  req->method = "POST";
  req->path = "/api/test";
  req->authority = "localhost:8080";
  req->scheme = "https";
  req->stream_id = 42;
  req->headers.count = 0;
  req->headers.capacity = 0;
  req->headers.items = nullptr;
  req->body = nullptr;
  req->bodyLen = 0;
  return req;
}

static void add_header(valk_http2_server_request_t *req, const char *name, const char *value) {
  if (req->headers.count >= req->headers.capacity) {
    u64 new_cap = req->headers.capacity == 0 ? 4 : req->headers.capacity * 2;
    req->headers.items = realloc(req->headers.items, new_cap * sizeof(struct valk_http2_header_t));
    req->headers.capacity = new_cap;
  }
  struct valk_http2_header_t *h = &req->headers.items[req->headers.count++];
  h->name = (u8 *)strdup(name);
  h->value = (u8 *)strdup(value);
  h->nameLen = strlen(name);
  h->valueLen = strlen(value);
}

static void free_request(valk_http2_server_request_t *req) {
  for (u64 i = 0; i < req->headers.count; i++) {
    free(req->headers.items[i].name);
    free(req->headers.items[i].value);
  }
  free(req->headers.items);
  free(req);
}

void test_req_method_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/method", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "POST");

  free_request(req);
  VALK_PASS();
}

void test_req_method_null_method(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  req->method = nullptr;
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/method", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "GET");

  free_request(req);
  VALK_PASS();
}

void test_req_method_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "req/method", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_req_method_not_request(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "req/method", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be http request");

  VALK_PASS();
}

void test_req_path_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/path", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "/api/test");

  free_request(req);
  VALK_PASS();
}

void test_req_path_null_path(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  req->path = nullptr;
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/path", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "/");

  free_request(req);
  VALK_PASS();
}

void test_req_path_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "req/path", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_req_authority_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/authority", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "localhost:8080");

  free_request(req);
  VALK_PASS();
}

void test_req_authority_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  req->authority = nullptr;
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/authority", args);

  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  free_request(req);
  VALK_PASS();
}

void test_req_authority_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "req/authority", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_req_scheme_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/scheme", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "https");

  free_request(req);
  VALK_PASS();
}

void test_req_scheme_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  req->scheme = nullptr;
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/scheme", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "https");

  free_request(req);
  VALK_PASS();
}

void test_req_scheme_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "req/scheme", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_req_headers_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/headers", args);

  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  free_request(req);
  VALK_PASS();
}

void test_req_headers_with_headers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  add_header(req, "content-type", "application/json");
  add_header(req, "x-custom", "value");

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/headers", args);

  ASSERT_LVAL_TYPE(result, LVAL_QEXPR);
  ASSERT_EQ(valk_lval_list_count(result), 2);

  valk_lval_t *first = valk_lval_list_nth(result, 0);
  ASSERT_LVAL_TYPE(first, LVAL_QEXPR);
  ASSERT_EQ(valk_lval_list_count(first), 2);
  ASSERT_STR_EQ(valk_lval_list_nth(first, 0)->str, "content-type");
  ASSERT_STR_EQ(valk_lval_list_nth(first, 1)->str, "application/json");

  free_request(req);
  VALK_PASS();
}

void test_req_headers_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "req/headers", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_req_header_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  add_header(req, "content-type", "application/json");

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_request_ref(req),
    valk_lval_str("content-type")
  }, 2);
  valk_lval_t *result = call_builtin(env, "req/header", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "application/json");

  free_request(req);
  VALK_PASS();
}

void test_req_header_case_insensitive(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  add_header(req, "Content-Type", "text/plain");

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_request_ref(req),
    valk_lval_str("content-type")
  }, 2);
  valk_lval_t *result = call_builtin(env, "req/header", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "text/plain");

  free_request(req);
  VALK_PASS();
}

void test_req_header_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  add_header(req, "content-type", "application/json");

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_request_ref(req),
    valk_lval_str("x-missing")
  }, 2);
  valk_lval_t *result = call_builtin(env, "req/header", args);

  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  free_request(req);
  VALK_PASS();
}

void test_req_header_wrong_args_count(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/header", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 2 arguments");

  free_request(req);
  VALK_PASS();
}

void test_req_header_wrong_name_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    make_request_ref(req),
    valk_lval_num(42)
  }, 2);
  valk_lval_t *result = call_builtin(env, "req/header", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be string");

  free_request(req);
  VALK_PASS();
}

void test_req_body_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/body", args);

  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  free_request(req);
  VALK_PASS();
}

void test_req_body_with_content(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  req->body = (u8 *)strdup("{\"test\":true}");
  req->bodyLen = strlen("{\"test\":true}");

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/body", args);

  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "{\"test\":true}");

  free((void *)req->body);
  free_request(req);
  VALK_PASS();
}

void test_req_body_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "req/body", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_req_stream_id(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_http2_server_request_t *req = create_test_request();
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){make_request_ref(req)}, 1);
  valk_lval_t *result = call_builtin(env, "req/stream-id", args);

  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_EQ(result->num, 42);

  free_request(req);
  VALK_PASS();
}

void test_req_stream_id_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "req/stream-id", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "expected 1 argument");

  VALK_PASS();
}

void test_req_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *wrong_ref = valk_lval_ref("other_type", nullptr, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){wrong_ref}, 1);
  valk_lval_t *result = call_builtin(env, "req/method", args);

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "must be http request");

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_req_method_success", test_req_method_success);
  valk_testsuite_add_test(suite, "test_req_method_null_method", test_req_method_null_method);
  valk_testsuite_add_test(suite, "test_req_method_wrong_args", test_req_method_wrong_args);
  valk_testsuite_add_test(suite, "test_req_method_not_request", test_req_method_not_request);
  valk_testsuite_add_test(suite, "test_req_path_success", test_req_path_success);
  valk_testsuite_add_test(suite, "test_req_path_null_path", test_req_path_null_path);
  valk_testsuite_add_test(suite, "test_req_path_wrong_args", test_req_path_wrong_args);
  valk_testsuite_add_test(suite, "test_req_authority_success", test_req_authority_success);
  valk_testsuite_add_test(suite, "test_req_authority_null", test_req_authority_null);
  valk_testsuite_add_test(suite, "test_req_authority_wrong_args", test_req_authority_wrong_args);
  valk_testsuite_add_test(suite, "test_req_scheme_success", test_req_scheme_success);
  valk_testsuite_add_test(suite, "test_req_scheme_null", test_req_scheme_null);
  valk_testsuite_add_test(suite, "test_req_scheme_wrong_args", test_req_scheme_wrong_args);
  valk_testsuite_add_test(suite, "test_req_headers_empty", test_req_headers_empty);
  valk_testsuite_add_test(suite, "test_req_headers_with_headers", test_req_headers_with_headers);
  valk_testsuite_add_test(suite, "test_req_headers_wrong_args", test_req_headers_wrong_args);
  valk_testsuite_add_test(suite, "test_req_header_found", test_req_header_found);
  valk_testsuite_add_test(suite, "test_req_header_case_insensitive", test_req_header_case_insensitive);
  valk_testsuite_add_test(suite, "test_req_header_not_found", test_req_header_not_found);
  valk_testsuite_add_test(suite, "test_req_header_wrong_args_count", test_req_header_wrong_args_count);
  valk_testsuite_add_test(suite, "test_req_header_wrong_name_type", test_req_header_wrong_name_type);
  valk_testsuite_add_test(suite, "test_req_body_null", test_req_body_null);
  valk_testsuite_add_test(suite, "test_req_body_with_content", test_req_body_with_content);
  valk_testsuite_add_test(suite, "test_req_body_wrong_args", test_req_body_wrong_args);
  valk_testsuite_add_test(suite, "test_req_stream_id", test_req_stream_id);
  valk_testsuite_add_test(suite, "test_req_stream_id_wrong_args", test_req_stream_id_wrong_args);
  valk_testsuite_add_test(suite, "test_req_wrong_ref_type", test_req_wrong_ref_type);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
