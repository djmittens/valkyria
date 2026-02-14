#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/http2/stream/aio_stream_body.h"
#include "../../src/aio/aio_internal.h"

#include <unistd.h>
#include <uv.h>

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
  body->max_session_ms = 0;
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

void test_register_null_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_register(nullptr);
  VALK_PASS();
}

void test_register_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_t body = {.conn = nullptr};
  valk_stream_body_register(&body);
  VALK_PASS();
}

void test_register_single_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);

  valk_stream_body_register(body);

  ASSERT_EQ(conn->http.stream_bodies, body);
  ASSERT_NULL(body->next);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_register_multiple_bodies(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body1 = create_test_body(conn, 1);
  valk_stream_body_t *body2 = create_test_body(conn, 3);
  valk_stream_body_t *body3 = create_test_body(conn, 5);

  valk_stream_body_register(body1);
  valk_stream_body_register(body2);
  valk_stream_body_register(body3);

  ASSERT_EQ(conn->http.stream_bodies, body3);
  ASSERT_EQ(body3->next, body2);
  ASSERT_EQ(body2->next, body1);
  ASSERT_NULL(body1->next);

  free_test_body(body1);
  free_test_body(body2);
  free_test_body(body3);
  free_test_conn(conn);
  VALK_PASS();
}

void test_unregister_null_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_unregister(nullptr);
  VALK_PASS();
}

void test_unregister_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_t body = {.conn = nullptr};
  valk_stream_body_unregister(&body);
  VALK_PASS();
}

void test_unregister_single_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);

  conn->http.stream_bodies = body;
  valk_stream_body_unregister(body);

  ASSERT_NULL(conn->http.stream_bodies);
  ASSERT_NULL(body->next);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_unregister_head_of_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body1 = create_test_body(conn, 1);
  valk_stream_body_t *body2 = create_test_body(conn, 3);
  valk_stream_body_t *body3 = create_test_body(conn, 5);

  body3->next = body2;
  body2->next = body1;
  conn->http.stream_bodies = body3;

  valk_stream_body_unregister(body3);

  ASSERT_EQ(conn->http.stream_bodies, body2);
  ASSERT_NULL(body3->next);

  free_test_body(body1);
  free_test_body(body2);
  free_test_body(body3);
  free_test_conn(conn);
  VALK_PASS();
}

void test_unregister_middle_of_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body1 = create_test_body(conn, 1);
  valk_stream_body_t *body2 = create_test_body(conn, 3);
  valk_stream_body_t *body3 = create_test_body(conn, 5);

  body3->next = body2;
  body2->next = body1;
  conn->http.stream_bodies = body3;

  valk_stream_body_unregister(body2);

  ASSERT_EQ(conn->http.stream_bodies, body3);
  ASSERT_EQ(body3->next, body1);
  ASSERT_NULL(body2->next);

  free_test_body(body1);
  free_test_body(body2);
  free_test_body(body3);
  free_test_conn(conn);
  VALK_PASS();
}

void test_unregister_tail_of_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body1 = create_test_body(conn, 1);
  valk_stream_body_t *body2 = create_test_body(conn, 3);
  valk_stream_body_t *body3 = create_test_body(conn, 5);

  body3->next = body2;
  body2->next = body1;
  conn->http.stream_bodies = body3;

  valk_stream_body_unregister(body1);

  ASSERT_EQ(conn->http.stream_bodies, body3);
  ASSERT_EQ(body3->next, body2);
  ASSERT_NULL(body2->next);
  ASSERT_NULL(body1->next);

  free_test_body(body1);
  free_test_body(body2);
  free_test_body(body3);
  free_test_conn(conn);
  VALK_PASS();
}

void test_unregister_not_in_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body1 = create_test_body(conn, 1);
  valk_stream_body_t *body_not_in_list = create_test_body(conn, 99);

  conn->http.stream_bodies = body1;

  valk_stream_body_unregister(body_not_in_list);

  ASSERT_EQ(conn->http.stream_bodies, body1);

  free_test_body(body1);
  free_test_body(body_not_in_list);
  free_test_conn(conn);
  VALK_PASS();
}

void test_close_by_stream_id_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_close_by_stream_id(nullptr, 1);
  VALK_PASS();
}

void test_close_by_stream_id_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_close_by_stream_id(conn, 1);
  ASSERT_NULL(conn->http.stream_bodies);
  free_test_conn(conn);
  VALK_PASS();
}

void test_close_by_stream_id_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSED;
  conn->http.stream_bodies = body;

  valk_stream_body_close_by_stream_id(conn, 999);

  ASSERT_EQ(body->state, VALK_STREAM_CLOSED);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_close_all_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_close_all(nullptr);
  VALK_PASS();
}

void test_close_all_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_close_all(conn);
  ASSERT_NULL(conn->http.stream_bodies);
  free_test_conn(conn);
  VALK_PASS();
}

void test_get_bytes_sent_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  u64 bytes = valk_stream_body_get_bytes_sent(nullptr, 1);
  ASSERT_EQ(bytes, 0);
  VALK_PASS();
}

void test_get_bytes_sent_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  u64 bytes = valk_stream_body_get_bytes_sent(conn, 1);
  ASSERT_EQ(bytes, 0);
  free_test_conn(conn);
  VALK_PASS();
}

void test_get_bytes_sent_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->bytes_sent = 1000;
  conn->http.stream_bodies = body;

  u64 bytes = valk_stream_body_get_bytes_sent(conn, 999);
  ASSERT_EQ(bytes, 0);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_get_bytes_sent_found(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->bytes_sent = 12345;
  conn->http.stream_bodies = body;

  u64 bytes = valk_stream_body_get_bytes_sent(conn, 1);
  ASSERT_EQ(bytes, 12345);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_get_bytes_sent_multiple_bodies(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body1 = create_test_body(conn, 1);
  valk_stream_body_t *body2 = create_test_body(conn, 3);
  valk_stream_body_t *body3 = create_test_body(conn, 5);

  body1->bytes_sent = 100;
  body2->bytes_sent = 200;
  body3->bytes_sent = 300;

  body3->next = body2;
  body2->next = body1;
  conn->http.stream_bodies = body3;

  ASSERT_EQ(valk_stream_body_get_bytes_sent(conn, 1), 100);
  ASSERT_EQ(valk_stream_body_get_bytes_sent(conn, 3), 200);
  ASSERT_EQ(valk_stream_body_get_bytes_sent(conn, 5), 300);
  ASSERT_EQ(valk_stream_body_get_bytes_sent(conn, 999), 0);

  free_test_body(body1);
  free_test_body(body2);
  free_test_body(body3);
  free_test_conn(conn);
  VALK_PASS();
}

void test_check_orphaned_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_check_orphaned(nullptr);
  VALK_PASS();
}

void test_check_orphaned_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = nullptr;
  valk_stream_body_check_orphaned(conn);
  free_test_conn(conn);
  VALK_PASS();
}

void test_check_orphaned_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = (nghttp2_session *)0x1;
  valk_stream_body_check_orphaned(conn);
  ASSERT_NULL(conn->http.stream_bodies);
  free_test_conn(conn);
  VALK_PASS();
}

void test_check_orphaned_closed_body_skipped(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = (nghttp2_session *)0x1;
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSED;
  conn->http.stream_bodies = body;

  valk_stream_body_check_orphaned(conn);

  ASSERT_EQ(body->state, VALK_STREAM_CLOSED);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_check_orphaned_closing_body_skipped(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = (nghttp2_session *)0x1;
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSING;
  conn->http.stream_bodies = body;

  valk_stream_body_check_orphaned(conn);

  ASSERT_EQ(body->state, VALK_STREAM_CLOSING);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_set_idle_timeout_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_set_idle_timeout(nullptr, 5000);
  VALK_PASS();
}

void test_set_idle_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);

  valk_stream_body_set_idle_timeout(body, 5000);
  ASSERT_EQ(body->idle_timeout_ms, 5000);

  valk_stream_body_set_idle_timeout(body, 0);
  ASSERT_EQ(body->idle_timeout_ms, 0);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_touch_activity_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_touch_activity(nullptr);
  VALK_PASS();
}

void test_touch_activity(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->last_activity_ms = 0;

  valk_stream_body_touch_activity(body);
  ASSERT_GT(body->last_activity_ms, 0);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_is_idle_expired_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  bool expired = valk_stream_body_is_idle_expired(nullptr);
  ASSERT_FALSE(expired);
  VALK_PASS();
}

void test_is_idle_expired_zero_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->idle_timeout_ms = 0;
  body->last_activity_ms = 0;

  bool expired = valk_stream_body_is_idle_expired(body);
  ASSERT_FALSE(expired);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_is_idle_expired_not_expired(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->idle_timeout_ms = 10000;
  valk_stream_body_touch_activity(body);

  bool expired = valk_stream_body_is_idle_expired(body);
  ASSERT_FALSE(expired);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_cancel_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  int rv = valk_stream_body_cancel(nullptr, 0);
  ASSERT_EQ(rv, -1);
  VALK_PASS();
}

void test_cancel_already_closed(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSED;

  int rv = valk_stream_body_cancel(body, 0);
  ASSERT_EQ(rv, 0);
  ASSERT_EQ(body->state, VALK_STREAM_CLOSED);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_is_idle_expired_actual_expired(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->idle_timeout_ms = 1;
  body->last_activity_ms = 0;

  usleep(2000);

  bool expired = valk_stream_body_is_idle_expired(body);
  ASSERT_TRUE(expired);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_set_max_session_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_set_max_session(nullptr, 5000);
  VALK_PASS();
}

void test_set_max_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);

  valk_stream_body_set_max_session(body, 1800000);
  ASSERT_EQ(body->max_session_ms, 1800000);

  valk_stream_body_set_max_session(body, 0);
  ASSERT_EQ(body->max_session_ms, 0);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_is_session_expired_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  bool expired = valk_stream_body_is_session_expired(nullptr);
  ASSERT_FALSE(expired);
  VALK_PASS();
}

void test_is_session_expired_zero_max(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->max_session_ms = 0;
  body->created_at_ms = 0;

  bool expired = valk_stream_body_is_session_expired(body);
  ASSERT_FALSE(expired);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_is_session_expired_not_expired(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->max_session_ms = 10000;
  body->created_at_ms = uv_hrtime() / 1000000;

  bool expired = valk_stream_body_is_session_expired(body);
  ASSERT_FALSE(expired);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_is_session_expired_actual_expired(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->max_session_ms = 1;
  body->created_at_ms = 0;

  usleep(2000);

  bool expired = valk_stream_body_is_session_expired(body);
  ASSERT_TRUE(expired);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_write_null_data(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);

  int rv = valk_stream_body_write(body, nullptr, 10);
  ASSERT_EQ(rv, -1);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_write_closed_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSED;

  int rv = valk_stream_body_write(body, "test", 4);
  ASSERT_EQ(rv, -1);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_write_closing_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSING;

  int rv = valk_stream_body_write(body, "test", 4);
  ASSERT_EQ(rv, -1);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_write_queue_full(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->queue_max = 5;
  body->queue_len = 5;

  int rv = valk_stream_body_write(body, "test", 4);
  ASSERT_EQ(rv, -2);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_writable_closed_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSED;

  bool writable = valk_stream_body_writable(body);
  ASSERT_FALSE(writable);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_writable_closing_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSING;

  bool writable = valk_stream_body_writable(body);
  ASSERT_FALSE(writable);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_queue_len_with_items(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->queue_len = 42;

  u64 len = valk_stream_body_queue_len(body);
  ASSERT_EQ(len, 42);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_close_null_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_close(nullptr);
  VALK_PASS();
}

void test_close_already_closed(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSED;

  valk_stream_body_close(body);
  ASSERT_EQ(body->state, VALK_STREAM_CLOSED);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_close_already_closing(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_CLOSING;

  valk_stream_body_close(body);
  ASSERT_EQ(body->state, VALK_STREAM_CLOSING);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_free_null_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_stream_body_free(nullptr);
  VALK_PASS();
}

void test_writable_null_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  bool writable = valk_stream_body_writable(nullptr);
  ASSERT_FALSE(writable);
  VALK_PASS();
}

void test_writable_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_OPEN;
  body->session = nullptr;

  bool writable = valk_stream_body_writable(body);
  ASSERT_FALSE(writable);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

void test_queue_len_null_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  u64 len = valk_stream_body_queue_len(nullptr);
  ASSERT_EQ(len, 0);
  VALK_PASS();
}

void test_cancel_no_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_stream_body_t *body = create_test_body(conn, 1);
  body->state = VALK_STREAM_OPEN;
  body->session = nullptr;

  int rv = valk_stream_body_cancel(body, NGHTTP2_CANCEL);
  ASSERT_EQ(rv, 0);

  free_test_body(body);
  free_test_conn(conn);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_register_null_body", test_register_null_body);
  valk_testsuite_add_test(suite, "test_register_null_conn", test_register_null_conn);
  valk_testsuite_add_test(suite, "test_register_single_body", test_register_single_body);
  valk_testsuite_add_test(suite, "test_register_multiple_bodies", test_register_multiple_bodies);

  valk_testsuite_add_test(suite, "test_unregister_null_body", test_unregister_null_body);
  valk_testsuite_add_test(suite, "test_unregister_null_conn", test_unregister_null_conn);
  valk_testsuite_add_test(suite, "test_unregister_single_body", test_unregister_single_body);
  valk_testsuite_add_test(suite, "test_unregister_head_of_list", test_unregister_head_of_list);
  valk_testsuite_add_test(suite, "test_unregister_middle_of_list", test_unregister_middle_of_list);
  valk_testsuite_add_test(suite, "test_unregister_tail_of_list", test_unregister_tail_of_list);
  valk_testsuite_add_test(suite, "test_unregister_not_in_list", test_unregister_not_in_list);

  valk_testsuite_add_test(suite, "test_close_by_stream_id_null_conn", test_close_by_stream_id_null_conn);
  valk_testsuite_add_test(suite, "test_close_by_stream_id_empty_list", test_close_by_stream_id_empty_list);
  valk_testsuite_add_test(suite, "test_close_by_stream_id_not_found", test_close_by_stream_id_not_found);

  valk_testsuite_add_test(suite, "test_close_all_null_conn", test_close_all_null_conn);
  valk_testsuite_add_test(suite, "test_close_all_empty_list", test_close_all_empty_list);

  valk_testsuite_add_test(suite, "test_get_bytes_sent_null_conn", test_get_bytes_sent_null_conn);
  valk_testsuite_add_test(suite, "test_get_bytes_sent_empty_list", test_get_bytes_sent_empty_list);
  valk_testsuite_add_test(suite, "test_get_bytes_sent_not_found", test_get_bytes_sent_not_found);
  valk_testsuite_add_test(suite, "test_get_bytes_sent_found", test_get_bytes_sent_found);
  valk_testsuite_add_test(suite, "test_get_bytes_sent_multiple_bodies", test_get_bytes_sent_multiple_bodies);

  valk_testsuite_add_test(suite, "test_check_orphaned_null_conn", test_check_orphaned_null_conn);
  valk_testsuite_add_test(suite, "test_check_orphaned_null_session", test_check_orphaned_null_session);
  valk_testsuite_add_test(suite, "test_check_orphaned_empty_list", test_check_orphaned_empty_list);
  valk_testsuite_add_test(suite, "test_check_orphaned_closed_body_skipped", test_check_orphaned_closed_body_skipped);
  valk_testsuite_add_test(suite, "test_check_orphaned_closing_body_skipped", test_check_orphaned_closing_body_skipped);

  valk_testsuite_add_test(suite, "test_set_idle_timeout_null", test_set_idle_timeout_null);
  valk_testsuite_add_test(suite, "test_set_idle_timeout", test_set_idle_timeout);
  valk_testsuite_add_test(suite, "test_touch_activity_null", test_touch_activity_null);
  valk_testsuite_add_test(suite, "test_touch_activity", test_touch_activity);
  valk_testsuite_add_test(suite, "test_is_idle_expired_null", test_is_idle_expired_null);
  valk_testsuite_add_test(suite, "test_is_idle_expired_zero_timeout", test_is_idle_expired_zero_timeout);
  valk_testsuite_add_test(suite, "test_is_idle_expired_not_expired", test_is_idle_expired_not_expired);
  valk_testsuite_add_test(suite, "test_cancel_null", test_cancel_null);
  valk_testsuite_add_test(suite, "test_cancel_already_closed", test_cancel_already_closed);

  valk_testsuite_add_test(suite, "test_is_idle_expired_actual_expired", test_is_idle_expired_actual_expired);
  valk_testsuite_add_test(suite, "test_set_max_session_null", test_set_max_session_null);
  valk_testsuite_add_test(suite, "test_set_max_session", test_set_max_session);
  valk_testsuite_add_test(suite, "test_is_session_expired_null", test_is_session_expired_null);
  valk_testsuite_add_test(suite, "test_is_session_expired_zero_max", test_is_session_expired_zero_max);
  valk_testsuite_add_test(suite, "test_is_session_expired_not_expired", test_is_session_expired_not_expired);
  valk_testsuite_add_test(suite, "test_is_session_expired_actual_expired", test_is_session_expired_actual_expired);
  valk_testsuite_add_test(suite, "test_write_null_data", test_write_null_data);
  valk_testsuite_add_test(suite, "test_write_closed_body", test_write_closed_body);
  valk_testsuite_add_test(suite, "test_write_closing_body", test_write_closing_body);
  valk_testsuite_add_test(suite, "test_write_queue_full", test_write_queue_full);
  valk_testsuite_add_test(suite, "test_writable_closed_body", test_writable_closed_body);
  valk_testsuite_add_test(suite, "test_writable_closing_body", test_writable_closing_body);
  valk_testsuite_add_test(suite, "test_queue_len_with_items", test_queue_len_with_items);
  valk_testsuite_add_test(suite, "test_close_null_body", test_close_null_body);
  valk_testsuite_add_test(suite, "test_close_already_closed", test_close_already_closed);
  valk_testsuite_add_test(suite, "test_close_already_closing", test_close_already_closing);
  valk_testsuite_add_test(suite, "test_free_null_body", test_free_null_body);
  valk_testsuite_add_test(suite, "test_writable_null_body", test_writable_null_body);
  valk_testsuite_add_test(suite, "test_writable_null_session", test_writable_null_session);
  valk_testsuite_add_test(suite, "test_queue_len_null_body", test_queue_len_null_body);
  valk_testsuite_add_test(suite, "test_cancel_no_session", test_cancel_no_session);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
