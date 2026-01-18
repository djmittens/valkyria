#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/http2/aio_http2_conn_fsm.h"
#include "../../src/aio/aio_internal.h"

#include <stdlib.h>

static valk_aio_handle_t *create_test_conn(void) {
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  return conn;
}

static void free_test_conn(valk_aio_handle_t *conn) {
  free(conn);
}

void test_state_str_valid(VALK_TEST_ARGS()) {
  VALK_TEST();
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_INIT), "INIT");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_HANDSHAKING), "HANDSHAKING");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_ESTABLISHED), "ESTABLISHED");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_GOAWAY_SENT), "GOAWAY_SENT");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_DRAINING), "DRAINING");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_CLOSING), "CLOSING");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_CLOSED), "CLOSED");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_ERROR), "ERROR");
  VALK_PASS();
}

void test_state_str_invalid(VALK_TEST_ARGS()) {
  VALK_TEST();
  ASSERT_STR_EQ(valk_conn_state_str(-1), "UNKNOWN");
  ASSERT_STR_EQ(valk_conn_state_str(100), "UNKNOWN");
  VALK_PASS();
}

void test_event_str_valid(VALK_TEST_ARGS()) {
  VALK_TEST();
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_START_HANDSHAKE), "START_HANDSHAKE");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_HANDSHAKE_COMPLETE), "HANDSHAKE_COMPLETE");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_HANDSHAKE_FAILED), "HANDSHAKE_FAILED");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_SEND_GOAWAY), "SEND_GOAWAY");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_GOAWAY_ACKED), "GOAWAY_ACKED");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_STREAMS_DRAINED), "STREAMS_DRAINED");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_CLOSE), "CLOSE");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_CLOSED), "CLOSED");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_ERROR), "ERROR");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_TIMEOUT), "TIMEOUT");
  VALK_PASS();
}

void test_event_str_invalid(VALK_TEST_ARGS()) {
  VALK_TEST();
  ASSERT_STR_EQ(valk_conn_event_str(-1), "UNKNOWN");
  ASSERT_STR_EQ(valk_conn_event_str(100), "UNKNOWN");
  VALK_PASS();
}

void test_is_closing_or_closed(VALK_TEST_ARGS()) {
  VALK_TEST();
  ASSERT_FALSE(valk_conn_is_closing_or_closed(VALK_CONN_INIT));
  ASSERT_FALSE(valk_conn_is_closing_or_closed(VALK_CONN_HANDSHAKING));
  ASSERT_FALSE(valk_conn_is_closing_or_closed(VALK_CONN_ESTABLISHED));
  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_GOAWAY_SENT));
  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_DRAINING));
  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_CLOSING));
  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_CLOSED));
  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_ERROR));
  VALK_PASS();
}

void test_init_state_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_conn_init_state(nullptr);
  VALK_PASS();
}

void test_init_state(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.state = VALK_CONN_ERROR;

  valk_conn_init_state(conn);

  ASSERT_EQ(conn->http.state, VALK_CONN_INIT);
  ASSERT_GT(conn->http.diag.state_change_time, 0);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  bool changed = valk_conn_transition(nullptr, VALK_CONN_EVT_START_HANDSHAKE);
  ASSERT_FALSE(changed);
  VALK_PASS();
}

void test_transition_init_start_handshake(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_START_HANDSHAKE);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_HANDSHAKING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_init_handshake_complete(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_HANDSHAKE_COMPLETE);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_ESTABLISHED);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_init_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_CLOSE);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_init_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_ERROR);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_ERROR);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_init_no_change(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_GOAWAY_ACKED);

  ASSERT_FALSE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_INIT);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_handshaking_complete(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_HANDSHAKING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_HANDSHAKE_COMPLETE);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_ESTABLISHED);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_handshaking_failed(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_HANDSHAKING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_HANDSHAKE_FAILED);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_ERROR);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_handshaking_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_HANDSHAKING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_CLOSE);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_handshaking_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_HANDSHAKING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_ERROR);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_ERROR);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_handshaking_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_HANDSHAKING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_TIMEOUT);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_established_send_goaway(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_ESTABLISHED;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_SEND_GOAWAY);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_GOAWAY_SENT);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_established_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_ESTABLISHED;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_CLOSE);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_established_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_ESTABLISHED;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_ERROR);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_ERROR);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_established_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_ESTABLISHED;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_TIMEOUT);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_goaway_sent_acked(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_GOAWAY_SENT;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_GOAWAY_ACKED);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_DRAINING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_goaway_sent_streams_drained(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_GOAWAY_SENT;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_STREAMS_DRAINED);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_goaway_sent_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_GOAWAY_SENT;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_CLOSE);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_goaway_sent_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_GOAWAY_SENT;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_ERROR);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_ERROR);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_goaway_sent_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_GOAWAY_SENT;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_TIMEOUT);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_draining_streams_drained(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_DRAINING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_STREAMS_DRAINED);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_draining_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_DRAINING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_CLOSE);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_draining_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_DRAINING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_ERROR);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_ERROR);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_draining_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_DRAINING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_TIMEOUT);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_closing_closed(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_CLOSING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_CLOSED);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSED);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_closing_no_change(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_CLOSING;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_ERROR);

  ASSERT_FALSE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_closed_no_change(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_CLOSED;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_ERROR);

  ASSERT_FALSE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSED);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_error_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_ERROR;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_CLOSE);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_error_closed(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_ERROR;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_CLOSED);

  ASSERT_TRUE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSED);

  free_test_conn(conn);
  VALK_PASS();
}

void test_transition_error_no_change(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_conn_init_state(conn);
  conn->http.state = VALK_CONN_ERROR;

  bool changed = valk_conn_transition(conn, VALK_CONN_EVT_TIMEOUT);

  ASSERT_FALSE(changed);
  ASSERT_EQ(conn->http.state, VALK_CONN_ERROR);

  free_test_conn(conn);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_state_str_valid", test_state_str_valid);
  valk_testsuite_add_test(suite, "test_state_str_invalid", test_state_str_invalid);
  valk_testsuite_add_test(suite, "test_event_str_valid", test_event_str_valid);
  valk_testsuite_add_test(suite, "test_event_str_invalid", test_event_str_invalid);
  valk_testsuite_add_test(suite, "test_is_closing_or_closed", test_is_closing_or_closed);

  valk_testsuite_add_test(suite, "test_init_state_null", test_init_state_null);
  valk_testsuite_add_test(suite, "test_init_state", test_init_state);

  valk_testsuite_add_test(suite, "test_transition_null", test_transition_null);
  valk_testsuite_add_test(suite, "test_transition_init_start_handshake", test_transition_init_start_handshake);
  valk_testsuite_add_test(suite, "test_transition_init_handshake_complete", test_transition_init_handshake_complete);
  valk_testsuite_add_test(suite, "test_transition_init_close", test_transition_init_close);
  valk_testsuite_add_test(suite, "test_transition_init_error", test_transition_init_error);
  valk_testsuite_add_test(suite, "test_transition_init_no_change", test_transition_init_no_change);

  valk_testsuite_add_test(suite, "test_transition_handshaking_complete", test_transition_handshaking_complete);
  valk_testsuite_add_test(suite, "test_transition_handshaking_failed", test_transition_handshaking_failed);
  valk_testsuite_add_test(suite, "test_transition_handshaking_close", test_transition_handshaking_close);
  valk_testsuite_add_test(suite, "test_transition_handshaking_error", test_transition_handshaking_error);
  valk_testsuite_add_test(suite, "test_transition_handshaking_timeout", test_transition_handshaking_timeout);

  valk_testsuite_add_test(suite, "test_transition_established_send_goaway", test_transition_established_send_goaway);
  valk_testsuite_add_test(suite, "test_transition_established_close", test_transition_established_close);
  valk_testsuite_add_test(suite, "test_transition_established_error", test_transition_established_error);
  valk_testsuite_add_test(suite, "test_transition_established_timeout", test_transition_established_timeout);

  valk_testsuite_add_test(suite, "test_transition_goaway_sent_acked", test_transition_goaway_sent_acked);
  valk_testsuite_add_test(suite, "test_transition_goaway_sent_streams_drained", test_transition_goaway_sent_streams_drained);
  valk_testsuite_add_test(suite, "test_transition_goaway_sent_close", test_transition_goaway_sent_close);
  valk_testsuite_add_test(suite, "test_transition_goaway_sent_error", test_transition_goaway_sent_error);
  valk_testsuite_add_test(suite, "test_transition_goaway_sent_timeout", test_transition_goaway_sent_timeout);

  valk_testsuite_add_test(suite, "test_transition_draining_streams_drained", test_transition_draining_streams_drained);
  valk_testsuite_add_test(suite, "test_transition_draining_close", test_transition_draining_close);
  valk_testsuite_add_test(suite, "test_transition_draining_error", test_transition_draining_error);
  valk_testsuite_add_test(suite, "test_transition_draining_timeout", test_transition_draining_timeout);

  valk_testsuite_add_test(suite, "test_transition_closing_closed", test_transition_closing_closed);
  valk_testsuite_add_test(suite, "test_transition_closing_no_change", test_transition_closing_no_change);

  valk_testsuite_add_test(suite, "test_transition_closed_no_change", test_transition_closed_no_change);

  valk_testsuite_add_test(suite, "test_transition_error_close", test_transition_error_close);
  valk_testsuite_add_test(suite, "test_transition_error_closed", test_transition_error_closed);
  valk_testsuite_add_test(suite, "test_transition_error_no_change", test_transition_error_no_change);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
