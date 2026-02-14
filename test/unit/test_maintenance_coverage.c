#include "../testing.h"
#include "../../src/aio/aio_internal.h"
#include "../../src/aio/system/aio_maintenance.h"
#include "../../src/aio/http2/aio_http2_conn_fsm.h"
#include <string.h>

extern const valk_aio_ops_t valk_aio_ops_test;

static valk_aio_handle_t *create_mock_conn(valk_aio_system_t *sys) {
  valk_aio_handle_t *h = calloc(1, sizeof(valk_aio_handle_t));
  h->magic = VALK_AIO_HANDLE_MAGIC;
  h->kind = VALK_HNDL_HTTP_CONN;
  h->http.state = VALK_CONN_ESTABLISHED;
  h->sys = sys;
  return h;
}

static void link_handle(valk_aio_system_t *sys, valk_aio_handle_t *h) {
  h->next = sys->liveHandles.next;
  h->prev = &sys->liveHandles;
  if (sys->liveHandles.next) {
    sys->liveHandles.next->prev = h;
  }
  sys->liveHandles.next = h;
}

static void free_mock_conn(valk_aio_handle_t *h) {
  free(h);
}

void test_connection_timeout_triggers_when_idle_exceeded(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  memset(&sys, 0, sizeof(sys));
  sys.ops = &valk_aio_ops_test;
  sys.config.connection_idle_timeout_ms = 1000;
  sys.liveHandles.next = &sys.liveHandles;
  sys.liveHandles.prev = &sys.liveHandles;

  valk_aio_handle_t *conn = create_mock_conn(&sys);
  conn->http.last_activity_ms = 5000;
  link_handle(&sys, conn);

  valk_maintenance_check_connection_timeouts(&sys, 7000);

  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_mock_conn(conn);
  VALK_PASS();
}

void test_connection_timeout_skipped_when_timeout_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  memset(&sys, 0, sizeof(sys));
  sys.ops = &valk_aio_ops_test;
  sys.config.connection_idle_timeout_ms = 0;
  sys.liveHandles.next = &sys.liveHandles;
  sys.liveHandles.prev = &sys.liveHandles;

  valk_aio_handle_t *conn = create_mock_conn(&sys);
  conn->http.last_activity_ms = 1000;
  link_handle(&sys, conn);

  valk_maintenance_check_connection_timeouts(&sys, 99999999);

  ASSERT_EQ(conn->http.state, VALK_CONN_ESTABLISHED);

  free_mock_conn(conn);
  VALK_PASS();
}

void test_connection_timeout_skipped_when_not_idle_enough(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  memset(&sys, 0, sizeof(sys));
  sys.ops = &valk_aio_ops_test;
  sys.config.connection_idle_timeout_ms = 5000;
  sys.liveHandles.next = &sys.liveHandles;
  sys.liveHandles.prev = &sys.liveHandles;

  valk_aio_handle_t *conn = create_mock_conn(&sys);
  conn->http.last_activity_ms = 1000;
  link_handle(&sys, conn);

  valk_maintenance_check_connection_timeouts(&sys, 3000);

  ASSERT_EQ(conn->http.state, VALK_CONN_ESTABLISHED);

  free_mock_conn(conn);
  VALK_PASS();
}

void test_connection_timeout_skipped_for_non_http_conn(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  memset(&sys, 0, sizeof(sys));
  sys.ops = &valk_aio_ops_test;
  sys.config.connection_idle_timeout_ms = 1000;
  sys.liveHandles.next = &sys.liveHandles;
  sys.liveHandles.prev = &sys.liveHandles;

  valk_aio_handle_t *conn = create_mock_conn(&sys);
  conn->kind = VALK_HNDL_TIMER;
  conn->http.last_activity_ms = 1000;
  link_handle(&sys, conn);

  valk_maintenance_check_connection_timeouts(&sys, 9999999);

  free_mock_conn(conn);
  VALK_PASS();
}

void test_connection_timeout_skipped_when_last_activity_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  memset(&sys, 0, sizeof(sys));
  sys.ops = &valk_aio_ops_test;
  sys.config.connection_idle_timeout_ms = 1000;
  sys.liveHandles.next = &sys.liveHandles;
  sys.liveHandles.prev = &sys.liveHandles;

  valk_aio_handle_t *conn = create_mock_conn(&sys);
  conn->http.last_activity_ms = 0;
  link_handle(&sys, conn);

  valk_maintenance_check_connection_timeouts(&sys, 9999999);

  ASSERT_EQ(conn->http.state, VALK_CONN_ESTABLISHED);

  free_mock_conn(conn);
  VALK_PASS();
}

void test_orphaned_stream_check_with_stream_bodies(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  memset(&sys, 0, sizeof(sys));
  sys.ops = &valk_aio_ops_test;
  sys.liveHandles.next = &sys.liveHandles;
  sys.liveHandles.prev = &sys.liveHandles;

  valk_aio_handle_t *conn = create_mock_conn(&sys);
  conn->http.session = (nghttp2_session *)0x1;
  
  valk_stream_body_t body;
  memset(&body, 0, sizeof(body));
  body.state = VALK_STREAM_CLOSED;
  body.conn = conn;
  conn->http.stream_bodies = &body;
  
  link_handle(&sys, conn);

  valk_maintenance_check_orphaned_streams(&sys);

  free_mock_conn(conn);
  VALK_PASS();
}

void test_orphaned_stream_check_skips_non_established(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  memset(&sys, 0, sizeof(sys));
  sys.ops = &valk_aio_ops_test;
  sys.liveHandles.next = &sys.liveHandles;
  sys.liveHandles.prev = &sys.liveHandles;

  valk_aio_handle_t *conn = create_mock_conn(&sys);
  conn->http.state = VALK_CONN_HANDSHAKING;
  conn->http.stream_bodies = (valk_stream_body_t *)0x1;
  link_handle(&sys, conn);

  valk_maintenance_check_orphaned_streams(&sys);

  free_mock_conn(conn);
  VALK_PASS();
}

void test_orphaned_stream_check_skips_no_bodies(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  memset(&sys, 0, sizeof(sys));
  sys.ops = &valk_aio_ops_test;
  sys.liveHandles.next = &sys.liveHandles;
  sys.liveHandles.prev = &sys.liveHandles;

  valk_aio_handle_t *conn = create_mock_conn(&sys);
  conn->http.stream_bodies = nullptr;
  link_handle(&sys, conn);

  valk_maintenance_check_orphaned_streams(&sys);

  free_mock_conn(conn);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "connection_timeout_triggers_when_idle_exceeded",
    test_connection_timeout_triggers_when_idle_exceeded);
  valk_testsuite_add_test(suite, "connection_timeout_skipped_when_timeout_disabled",
    test_connection_timeout_skipped_when_timeout_disabled);
  valk_testsuite_add_test(suite, "connection_timeout_skipped_when_not_idle_enough",
    test_connection_timeout_skipped_when_not_idle_enough);
  valk_testsuite_add_test(suite, "connection_timeout_skipped_for_non_http_conn",
    test_connection_timeout_skipped_for_non_http_conn);
  valk_testsuite_add_test(suite, "connection_timeout_skipped_when_last_activity_zero",
    test_connection_timeout_skipped_when_last_activity_zero);
  valk_testsuite_add_test(suite, "orphaned_stream_check_with_stream_bodies",
    test_orphaned_stream_check_with_stream_bodies);
  valk_testsuite_add_test(suite, "orphaned_stream_check_skips_non_established",
    test_orphaned_stream_check_skips_non_established);
  valk_testsuite_add_test(suite, "orphaned_stream_check_skips_no_bodies",
    test_orphaned_stream_check_skips_no_bodies);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
