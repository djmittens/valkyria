#include "../testing.h"
#include "../../test/fakes/nghttp2_fake/nghttp2_fake.h"
#include "../../test/fakes/nghttp2_fake/nghttp2_fake_control.h"
#include <string.h>

static nghttp2_session *g_session = NULL;
static int g_begin_headers_count = 0;
static int g_header_count = 0;
static int32_t g_last_stream_id = 0;

static void reset_state(void) {
  if (g_session) {
    nghttp2_session_del(g_session);
    g_session = NULL;
  }
  g_begin_headers_count = 0;
  g_header_count = 0;
  g_last_stream_id = 0;
}

static int on_begin_headers(nghttp2_session *session, const nghttp2_frame *frame,
                            void *user_data) {
  (void)session;
  (void)user_data;
  g_begin_headers_count++;
  g_last_stream_id = frame->hd.stream_id;
  return 0;
}

static int on_header(nghttp2_session *session, const nghttp2_frame *frame,
                     const uint8_t *name, size_t namelen,
                     const uint8_t *value, size_t valuelen,
                     uint8_t flags, void *user_data) {
  (void)session;
  (void)frame;
  (void)name;
  (void)namelen;
  (void)value;
  (void)valuelen;
  (void)flags;
  (void)user_data;
  g_header_count++;
  return 0;
}

void test_session_new(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  
  int r = nghttp2_session_server_new(&g_session, cbs, NULL);
  ASSERT_EQ(r, 0);
  ASSERT_TRUE(g_session != NULL);
  
  nghttp2_session_callbacks_del(cbs);
  
  VALK_PASS();
}

void test_session_client_new(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  
  int r = nghttp2_session_client_new(&g_session, cbs, NULL);
  ASSERT_EQ(r, 0);
  ASSERT_TRUE(g_session != NULL);
  
  nghttp2_session_callbacks_del(cbs);
  
  VALK_PASS();
}

void test_inject_request(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  nghttp2_session_callbacks_set_on_begin_headers_callback(cbs, on_begin_headers);
  nghttp2_session_callbacks_set_on_header_callback(cbs, on_header);
  
  nghttp2_session_server_new(&g_session, cbs, NULL);
  nghttp2_session_callbacks_del(cbs);
  
  int32_t stream_id = nghttp2_fake_inject_request(
    g_session, "GET", "/test",
    NULL, 0, NULL, 0);
  
  ASSERT_TRUE(stream_id > 0);
  ASSERT_EQ(g_begin_headers_count, 1);
  ASSERT_EQ(g_header_count, 3);
  ASSERT_EQ(g_last_stream_id, stream_id);
  
  VALK_PASS();
}

void test_stream_user_data(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  nghttp2_session_server_new(&g_session, cbs, NULL);
  nghttp2_session_callbacks_del(cbs);
  
  int test_data = 42;
  int r = nghttp2_session_set_stream_user_data(g_session, 1, &test_data);
  ASSERT_EQ(r, 0);
  
  int *retrieved = nghttp2_session_get_stream_user_data(g_session, 1);
  ASSERT_EQ(retrieved, &test_data);
  ASSERT_EQ(*retrieved, 42);
  
  VALK_PASS();
}

void test_submit_response(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  nghttp2_session_server_new(&g_session, cbs, NULL);
  nghttp2_session_callbacks_del(cbs);
  
  int32_t stream_id = nghttp2_fake_inject_request(
    g_session, "GET", "/test", NULL, 0, NULL, 0);
  
  nghttp2_nv nva[] = {
    {(uint8_t *)":status", (uint8_t *)"200", 7, 3, 0},
    {(uint8_t *)"content-type", (uint8_t *)"text/plain", 12, 10, 0},
  };
  
  int r = nghttp2_submit_response(g_session, stream_id, nva, 2, NULL);
  ASSERT_EQ(r, 0);
  
  nghttp2_fake_response_t resp;
  bool found = nghttp2_fake_get_response(g_session, stream_id, &resp);
  ASSERT_TRUE(found);
  ASSERT_EQ(resp.status_code, 200);
  ASSERT_EQ(resp.nheaders, 2);
  
  VALK_PASS();
}

void test_stream_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  nghttp2_session_server_new(&g_session, cbs, NULL);
  nghttp2_session_callbacks_del(cbs);
  
  ASSERT_EQ(nghttp2_fake_stream_count(g_session), 0);
  
  nghttp2_fake_inject_request(g_session, "GET", "/test1", NULL, 0, NULL, 0);
  ASSERT_EQ(nghttp2_fake_stream_count(g_session), 1);
  
  nghttp2_fake_inject_request(g_session, "GET", "/test2", NULL, 0, NULL, 0);
  ASSERT_EQ(nghttp2_fake_stream_count(g_session), 2);
  
  VALK_PASS();
}

void test_rst_stream(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  nghttp2_session_server_new(&g_session, cbs, NULL);
  nghttp2_session_callbacks_del(cbs);
  
  int32_t stream_id = nghttp2_fake_inject_request(
    g_session, "GET", "/test", NULL, 0, NULL, 0);
  
  nghttp2_nv nva[] = {
    {(uint8_t *)":status", (uint8_t *)"200", 7, 3, 0},
  };
  nghttp2_submit_response(g_session, stream_id, nva, 1, NULL);
  
  nghttp2_submit_rst_stream(g_session, 0, stream_id, 0);
  
  nghttp2_fake_response_t resp;
  nghttp2_fake_get_response(g_session, stream_id, &resp);
  ASSERT_TRUE(resp.closed);
  
  VALK_PASS();
}

void test_want_write(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  nghttp2_session_server_new(&g_session, cbs, NULL);
  nghttp2_session_callbacks_del(cbs);
  
  ASSERT_FALSE(nghttp2_session_want_write(g_session));
  
  int32_t stream_id = nghttp2_fake_inject_request(
    g_session, "GET", "/test", NULL, 0, NULL, 0);
  
  nghttp2_nv nva[] = {
    {(uint8_t *)":status", (uint8_t *)"200", 7, 3, 0},
  };
  nghttp2_submit_response(g_session, stream_id, nva, 1, NULL);
  
  ASSERT_TRUE(nghttp2_session_want_write(g_session));
  
  VALK_PASS();
}

void test_reset(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  nghttp2_session_server_new(&g_session, cbs, NULL);
  nghttp2_session_callbacks_del(cbs);
  
  nghttp2_fake_inject_request(g_session, "GET", "/test1", NULL, 0, NULL, 0);
  nghttp2_fake_inject_request(g_session, "GET", "/test2", NULL, 0, NULL, 0);
  
  ASSERT_EQ(nghttp2_fake_stream_count(g_session), 2);
  
  nghttp2_fake_reset(g_session);
  
  ASSERT_EQ(nghttp2_fake_stream_count(g_session), 0);
  
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  
  valk_testsuite_add_test(suite, "session_new", test_session_new);
  valk_testsuite_add_test(suite, "session_client_new", test_session_client_new);
  valk_testsuite_add_test(suite, "inject_request", test_inject_request);
  valk_testsuite_add_test(suite, "stream_user_data", test_stream_user_data);
  valk_testsuite_add_test(suite, "submit_response", test_submit_response);
  valk_testsuite_add_test(suite, "stream_count", test_stream_count);
  valk_testsuite_add_test(suite, "rst_stream", test_rst_stream);
  valk_testsuite_add_test(suite, "want_write", test_want_write);
  valk_testsuite_add_test(suite, "reset", test_reset);
  
  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  
  reset_state();
  
  return result;
}
