#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"
#include "../../src/aio/http2/aio_http2_session.h"
#include "../../src/aio/http2/aio_http2_conn.h"
#include "../../src/aio/aio_internal.h"
#include "../../src/aio/aio_ops.h"
#include "../../src/aio/http2/aio_ssl.h"

#include <stdlib.h>

static valk_aio_system_t *create_test_system(void) {
  valk_aio_system_t *sys = calloc(1, sizeof(valk_aio_system_t));
  sys->ops = &valk_aio_ops_test;
  sys->config.max_concurrent_streams = 100;
  sys->config.arena_size = 64 * 1024;
  sys->config.max_servers = 8;
  sys->port_strs = calloc(sys->config.max_servers, 8);
  sys->metrics_state = calloc(1, sizeof(valk_aio_metrics_state_t));
  sys->metrics_state->metrics_v2 = calloc(1, 256);
  sys->metrics_state->system_stats_v2 = calloc(1, 256);
  return sys;
}

static void free_test_system(valk_aio_system_t *sys) {
  free(sys->port_strs);
  free(sys->metrics_state->metrics_v2);
  free(sys->metrics_state->system_stats_v2);
  free(sys->metrics_state);
  free(sys);
}

static valk_aio_handle_t *create_test_conn(valk_aio_system_t *sys) {
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->kind = VALK_HNDL_HTTP_CONN;
  conn->http.state = VALK_CONN_ESTABLISHED;
  conn->sys = sys;
  conn->http.active_arena_head = UINT32_MAX;
  valk_conn_io_init(&conn->http.io, HTTP_SLAB_ITEM_SIZE);
  return conn;
}

// --- byte_body_cb tests ---

void test_byte_body_cb_full_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  const char *body = "Hello, World!";
  u64 body_len = strlen(body);

  http_body_source_t src = {
    .body = body,
    .body_len = body_len,
    .offset = 0,
    .needs_free = false
  };

  nghttp2_data_source ds = { .ptr = &src };
  u8 buf[256];
  u32 data_flags = 0;

  nghttp2_ssize result = valk_http2_byte_body_cb(
      nullptr, 1, buf, sizeof(buf), &data_flags, &ds, nullptr);

  ASSERT_EQ(result, (nghttp2_ssize)body_len);
  ASSERT_TRUE(data_flags & NGHTTP2_DATA_FLAG_EOF);
  ASSERT_EQ(memcmp(buf, body, body_len), 0);
  VALK_PASS();
}

void test_byte_body_cb_chunked(VALK_TEST_ARGS()) {
  VALK_TEST();
  const char *body = "Hello, World!";
  u64 body_len = strlen(body);

  http_body_source_t src = {
    .body = body,
    .body_len = body_len,
    .offset = 0,
    .needs_free = false
  };

  nghttp2_data_source ds = { .ptr = &src };
  u8 buf[5];
  u32 data_flags = 0;

  nghttp2_ssize r1 = valk_http2_byte_body_cb(
      nullptr, 1, buf, sizeof(buf), &data_flags, &ds, nullptr);
  ASSERT_EQ(r1, 5);
  ASSERT_FALSE(data_flags & NGHTTP2_DATA_FLAG_EOF);

  nghttp2_ssize r2 = valk_http2_byte_body_cb(
      nullptr, 1, buf, sizeof(buf), &data_flags, &ds, nullptr);
  ASSERT_EQ(r2, 5);
  ASSERT_FALSE(data_flags & NGHTTP2_DATA_FLAG_EOF);

  nghttp2_ssize r3 = valk_http2_byte_body_cb(
      nullptr, 1, buf, sizeof(buf), &data_flags, &ds, nullptr);
  ASSERT_EQ(r3, 3);
  ASSERT_TRUE(data_flags & NGHTTP2_DATA_FLAG_EOF);
  VALK_PASS();
}

void test_byte_body_cb_needs_free(VALK_TEST_ARGS()) {
  VALK_TEST();
  http_body_source_t *src = malloc(sizeof(http_body_source_t));
  src->body = "data";
  src->body_len = 4;
  src->offset = 0;
  src->needs_free = true;

  nghttp2_data_source ds = { .ptr = src };
  u8 buf[256];
  u32 data_flags = 0;

  nghttp2_ssize result = valk_http2_byte_body_cb(
      nullptr, 1, buf, sizeof(buf), &data_flags, &ds, nullptr);
  ASSERT_EQ(result, 4);
  ASSERT_TRUE(data_flags & NGHTTP2_DATA_FLAG_EOF);
  // src was freed by the callback since needs_free=true
  VALK_PASS();
}

// --- qexpr_get tests ---

void test_qexpr_get_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *num = valk_lval_num(42);
  valk_lval_t *result = valk_http2_qexpr_get(num, ":status");
  ASSERT_NULL(result);
  VALK_PASS();
}

void test_qexpr_get_found(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *items[] = {
    valk_lval_sym(":status"), valk_lval_str("200"),
    valk_lval_sym(":body"), valk_lval_str("hello")
  };
  valk_lval_t *qexpr = valk_lval_qlist(items, 4);

  valk_lval_t *status = valk_http2_qexpr_get(qexpr, ":status");
  ASSERT_NOT_NULL(status);
  ASSERT_LVAL_STR(status, "200");

  valk_lval_t *body = valk_http2_qexpr_get(qexpr, ":body");
  ASSERT_NOT_NULL(body);
  ASSERT_LVAL_STR(body, "hello");
  VALK_PASS();
}

void test_qexpr_get_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *items[] = {
    valk_lval_sym(":status"), valk_lval_str("200")
  };
  valk_lval_t *qexpr = valk_lval_qlist(items, 2);

  valk_lval_t *result = valk_http2_qexpr_get(qexpr, ":body");
  ASSERT_NULL(result);
  VALK_PASS();
}

// --- session_valid / connection_closing tests ---

void test_session_valid_matching(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  nghttp2_session *fake_session = (nghttp2_session *)0x12345;
  conn->http.session = fake_session;

  bool valid = valk_aio_http_session_valid(conn, fake_session);
  ASSERT_TRUE(valid);

  free(conn);
  VALK_PASS();
}

void test_session_valid_mismatch(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.session = (nghttp2_session *)0x12345;

  bool valid = valk_aio_http_session_valid(conn, (void *)0x99999);
  ASSERT_FALSE(valid);

  free(conn);
  VALK_PASS();
}

void test_session_valid_null_handle(VALK_TEST_ARGS()) {
  VALK_TEST();
  bool valid = valk_aio_http_session_valid(nullptr, (void *)0x1);
  ASSERT_FALSE(valid);
  VALK_PASS();
}

void test_session_valid_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  bool valid = valk_aio_http_session_valid(conn, nullptr);
  ASSERT_FALSE(valid);
  free(conn);
  VALK_PASS();
}

void test_connection_closing_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  bool closing = valk_aio_http_connection_closing(nullptr);
  ASSERT_TRUE(closing);
  VALK_PASS();
}

void test_connection_closing_established(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->http.state = VALK_CONN_ESTABLISHED;

  bool closing = valk_aio_http_connection_closing(conn);
  ASSERT_FALSE(closing);

  free(conn);
  VALK_PASS();
}

void test_connection_closing_closing_state(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->http.state = VALK_CONN_CLOSING;

  bool closing = valk_aio_http_connection_closing(conn);
  ASSERT_TRUE(closing);

  free(conn);
  VALK_PASS();
}

void test_connection_closing_closed_state(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->http.state = VALK_CONN_CLOSED;

  bool closing = valk_aio_http_connection_closing(conn);
  ASSERT_TRUE(closing);

  free(conn);
  VALK_PASS();
}

// --- stream_reset / submit_goaway tests (need real nghttp2 session) ---

void test_stream_reset_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  int rv = valk_http2_stream_reset(nullptr, 1, NGHTTP2_CANCEL);
  ASSERT_EQ(rv, -1);
  VALK_PASS();
}

void test_stream_reset_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->http.session = nullptr;

  int rv = valk_http2_stream_reset(conn, 1, NGHTTP2_CANCEL);
  ASSERT_EQ(rv, -1);

  free(conn);
  VALK_PASS();
}

void test_stream_reset_with_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  int rv = valk_http2_stream_reset(conn, 1, NGHTTP2_CANCEL);
  ASSERT_EQ(rv, 0);

  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  free(conn);
  VALK_PASS();
}

void test_submit_goaway_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  int rv = valk_http2_submit_goaway(nullptr, NGHTTP2_NO_ERROR);
  ASSERT_EQ(rv, -1);
  VALK_PASS();
}

void test_submit_goaway_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->http.session = nullptr;

  int rv = valk_http2_submit_goaway(conn, NGHTTP2_NO_ERROR);
  ASSERT_EQ(rv, -1);

  free(conn);
  VALK_PASS();
}

void test_submit_goaway_with_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  int rv = valk_http2_submit_goaway(conn, NGHTTP2_NO_ERROR);
  ASSERT_EQ(rv, 0);

  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  free(conn);
  VALK_PASS();
}

// --- release_stream_arena tests ---

void test_release_stream_arena_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_http2_release_stream_arena(nullptr, 1);
  VALK_PASS();
}

void test_release_stream_arena_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->http.session = nullptr;
  valk_http2_release_stream_arena(conn, 1);
  free(conn);
  VALK_PASS();
}

void test_release_stream_arena_null_server(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->http.session = (nghttp2_session *)0x1;
  conn->http.server = nullptr;
  valk_http2_release_stream_arena(conn, 1);
  free(conn);
  VALK_PASS();
}

void test_release_stream_arena_no_stream_data(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  valk_aio_handle_t *conn = create_test_conn(sys);
  valk_aio_http_server *srv = calloc(1, sizeof(valk_aio_http_server));
  srv->sys = sys;
  conn->http.server = srv;

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  valk_http2_release_stream_arena(conn, 999);

  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  free(srv);
  free(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_release_stream_arena_with_valid_arena(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->httpStreamArenas = valk_slab_new(sizeof(valk_mem_arena_t) + 64 * 1024, 4);
  valk_aio_handle_t *conn = create_test_conn(sys);
  valk_aio_http_server *srv = calloc(1, sizeof(valk_aio_http_server));
  srv->sys = sys;
  conn->http.server = srv;

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_callbacks_set_on_begin_headers_callback(callbacks, valk_http2_on_begin_headers_callback);
  nghttp2_session_callbacks_set_on_header_callback(callbacks, valk_http2_on_header_callback);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  // Simulate a request arriving: feed HEADERS frame
  // We need to get stream user data set up, which happens in on_begin_headers
  // Feed a proper HTTP/2 client connection preface + HEADERS frame
  static const u8 client_preface[] = "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";
  nghttp2_session_mem_recv2(conn->http.session, client_preface, sizeof(client_preface) - 1);

  // Build a SETTINGS frame (required before HEADERS)
  u8 settings_frame[] = {
    0x00, 0x00, 0x00,  // length = 0
    0x04,              // type = SETTINGS
    0x00,              // flags = 0
    0x00, 0x00, 0x00, 0x00  // stream 0
  };
  nghttp2_session_mem_recv2(conn->http.session, settings_frame, sizeof(settings_frame));

  // Build a HEADERS frame for stream 1
  // Use nghttp2 deflater to create proper HPACK headers
  nghttp2_hd_deflater *deflater;
  nghttp2_hd_deflate_new(&deflater, 4096);

  nghttp2_nv headers[] = {
    {(u8 *)":method", (u8 *)"GET", 7, 3, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":scheme", (u8 *)"https", 7, 5, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":path", (u8 *)"/test", 5, 5, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":authority", (u8 *)"localhost", 10, 9, NGHTTP2_NV_FLAG_NONE},
  };

  u8 hdr_buf[1024];
  ssize_t hdr_len = nghttp2_hd_deflate_hd(deflater, hdr_buf, sizeof(hdr_buf),
                                            headers, 4);
  ASSERT_GT(hdr_len, 0);

  // Build HEADERS frame: length(3) + type(1) + flags(1) + stream_id(4) + payload
  u8 frame_buf[1024];
  frame_buf[0] = (hdr_len >> 16) & 0xff;
  frame_buf[1] = (hdr_len >> 8) & 0xff;
  frame_buf[2] = hdr_len & 0xff;
  frame_buf[3] = 0x01; // HEADERS
  frame_buf[4] = 0x05; // END_STREAM | END_HEADERS
  frame_buf[5] = 0x00;
  frame_buf[6] = 0x00;
  frame_buf[7] = 0x00;
  frame_buf[8] = 0x01; // stream 1
  memcpy(frame_buf + 9, hdr_buf, hdr_len);

  nghttp2_session_mem_recv2(conn->http.session, frame_buf, 9 + hdr_len);

  // Now stream 1 should have user data set
  valk_http2_server_request_t *req = nghttp2_session_get_stream_user_data(
      conn->http.session, 1);

  if (req && valk_arena_ref_valid(req->arena_ref)) {
    // Release the arena via the function we're testing
    valk_http2_release_stream_arena(conn, 1);
    // Verify arena was released
    ASSERT_FALSE(valk_arena_ref_valid(req->arena_ref));
  }

  nghttp2_hd_deflate_del(deflater);
  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  free(srv);
  free(conn);
  valk_slab_free(sys->httpStreamArenas);
  free_test_system(sys);
  VALK_PASS();
}

// --- remove_from_active_arenas tests ---

void test_remove_from_active_arenas_head(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->httpStreamArenas = valk_slab_new(sizeof(valk_mem_arena_t) + 64 * 1024, 4);
  valk_aio_handle_t *conn = create_test_conn(sys);
  valk_aio_http_server *srv = calloc(1, sizeof(valk_aio_http_server));
  srv->sys = sys;
  conn->http.server = srv;

  // Acquire two arenas and link them
  valk_slab_item_t *item1 = valk_slab_aquire(sys->httpStreamArenas);
  valk_slab_item_t *item2 = valk_slab_aquire(sys->httpStreamArenas);
  u32 slot1 = (u32)(item1->handle & 0xFFFFFFFF);
  u32 slot2 = (u32)(item2->handle & 0xFFFFFFFF);

  // Init arenas so we can get request structs
  valk_mem_arena_t *arena1 = (valk_mem_arena_t *)item1->data;
  valk_mem_arena_t *arena2 = (valk_mem_arena_t *)item2->data;
  valk_mem_arena_init(arena1, sys->config.arena_size);
  valk_mem_arena_init(arena2, sys->config.arena_size);

  // Allocate request from each arena
  valk_http2_server_request_t *req1;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena1) {
    req1 = valk_mem_alloc(sizeof(valk_http2_server_request_t));
    memset(req1, 0, sizeof(*req1));
    req1->arena_ref.slab_item = item1;
    req1->arena_ref.slot = slot1;
    req1->next_arena_slot = slot2;
  }

  valk_http2_server_request_t *req2;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena2) {
    req2 = valk_mem_alloc(sizeof(valk_http2_server_request_t));
    memset(req2, 0, sizeof(*req2));
    req2->arena_ref.slab_item = item2;
    req2->arena_ref.slot = slot2;
    req2->next_arena_slot = UINT32_MAX;
  }

  conn->http.active_arena_head = slot1;

  // Remove the head
  valk_http2_remove_from_active_arenas(conn, slot1);
  ASSERT_EQ(conn->http.active_arena_head, slot2);

  valk_slab_release(sys->httpStreamArenas, item1);
  valk_slab_release(sys->httpStreamArenas, item2);
  valk_slab_free(sys->httpStreamArenas);
  free(srv);
  free(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_remove_from_active_arenas_middle(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->httpStreamArenas = valk_slab_new(sizeof(valk_mem_arena_t) + 64 * 1024, 4);
  valk_aio_handle_t *conn = create_test_conn(sys);
  valk_aio_http_server *srv = calloc(1, sizeof(valk_aio_http_server));
  srv->sys = sys;
  conn->http.server = srv;

  valk_slab_item_t *item1 = valk_slab_aquire(sys->httpStreamArenas);
  valk_slab_item_t *item2 = valk_slab_aquire(sys->httpStreamArenas);
  valk_slab_item_t *item3 = valk_slab_aquire(sys->httpStreamArenas);
  u32 slot1 = (u32)(item1->handle & 0xFFFFFFFF);
  u32 slot2 = (u32)(item2->handle & 0xFFFFFFFF);
  u32 slot3 = (u32)(item3->handle & 0xFFFFFFFF);

  valk_mem_arena_t *arena1 = (valk_mem_arena_t *)item1->data;
  valk_mem_arena_t *arena2 = (valk_mem_arena_t *)item2->data;
  valk_mem_arena_t *arena3 = (valk_mem_arena_t *)item3->data;
  valk_mem_arena_init(arena1, sys->config.arena_size);
  valk_mem_arena_init(arena2, sys->config.arena_size);
  valk_mem_arena_init(arena3, sys->config.arena_size);

  valk_http2_server_request_t *req1;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena1) {
    req1 = valk_mem_alloc(sizeof(valk_http2_server_request_t));
    memset(req1, 0, sizeof(*req1));
    req1->arena_ref.slab_item = item1;
    req1->arena_ref.slot = slot1;
    req1->next_arena_slot = slot2;
  }

  valk_http2_server_request_t *req2;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena2) {
    req2 = valk_mem_alloc(sizeof(valk_http2_server_request_t));
    memset(req2, 0, sizeof(*req2));
    req2->arena_ref.slab_item = item2;
    req2->arena_ref.slot = slot2;
    req2->next_arena_slot = slot3;
  }

  valk_http2_server_request_t *req3;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena3) {
    req3 = valk_mem_alloc(sizeof(valk_http2_server_request_t));
    memset(req3, 0, sizeof(*req3));
    req3->arena_ref.slab_item = item3;
    req3->arena_ref.slot = slot3;
    req3->next_arena_slot = UINT32_MAX;
  }

  conn->http.active_arena_head = slot1;

  // Remove the middle element
  valk_http2_remove_from_active_arenas(conn, slot2);
  ASSERT_EQ(conn->http.active_arena_head, slot1);
  ASSERT_EQ(req1->next_arena_slot, slot3);

  valk_slab_release(sys->httpStreamArenas, item1);
  valk_slab_release(sys->httpStreamArenas, item2);
  valk_slab_release(sys->httpStreamArenas, item3);
  valk_slab_free(sys->httpStreamArenas);
  free(srv);
  free(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- client_on_header_cb tests ---

static ssize_t __test_send_cb(nghttp2_session *session, const u8 *data,
                              size_t length, int flags, void *user_data) {
  UNUSED(session); UNUSED(data); UNUSED(flags); UNUSED(user_data);
  return (ssize_t)length;
}

void test_client_on_header_cb_status(VALK_TEST_ARGS()) {
  VALK_TEST();
  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_callbacks_set_on_header_callback(callbacks, valk_http2_client_on_header_cb);
  nghttp2_session_callbacks_set_send_callback(callbacks, __test_send_cb);

  nghttp2_session *session;
  nghttp2_session_client_new(&session, callbacks, nullptr);

  nghttp2_nv req_hdrs[] = {
    {(u8 *)":method", (u8 *)"GET", 7, 3, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":scheme", (u8 *)"https", 7, 5, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":path", (u8 *)"/", 5, 1, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":authority", (u8 *)"localhost", 10, 9, NGHTTP2_NV_FLAG_NONE},
  };

  valk_http2_response_t *res = calloc(1, sizeof(valk_http2_response_t));
  res->headers.items = calloc(8, sizeof(struct valk_http2_header_t));
  res->headers.count = 0;
  res->headers.capacity = 8;

  typedef struct {
    u64 streamid;
    void *req;
    valk_http2_response_t *res;
    void *handle;
  } client_reqres_t;

  client_reqres_t *reqres = calloc(1, sizeof(client_reqres_t));
  reqres->res = res;

  i32 stream_id = nghttp2_submit_request2(session, nullptr, req_hdrs, 4, nullptr, reqres);
  ASSERT_GT(stream_id, 0);

  // Actually send to create the stream in nghttp2's internal state
  nghttp2_session_send(session);

  nghttp2_frame frame;
  memset(&frame, 0, sizeof(frame));
  frame.hd.type = NGHTTP2_HEADERS;
  frame.hd.stream_id = stream_id;

  int rv = valk_http2_client_on_header_cb(session, &frame,
    (u8 *)":status", 7, (u8 *)"200", 3, 0, nullptr);
  ASSERT_EQ(rv, 0);
  ASSERT_NOT_NULL(res->status);
  ASSERT_STR_EQ(res->status, "200");

  rv = valk_http2_client_on_header_cb(session, &frame,
    (u8 *)"content-type", 12, (u8 *)"text/plain", 10, 0, nullptr);
  ASSERT_EQ(rv, 0);
  ASSERT_EQ(res->headers.count, 1);
  ASSERT_EQ(memcmp(res->headers.items[0].name, "content-type", 12), 0);
  ASSERT_EQ(memcmp(res->headers.items[0].value, "text/plain", 10), 0);

  free((void *)res->status);
  for (u64 i = 0; i < res->headers.count; i++) {
    free(res->headers.items[i].name);
    free(res->headers.items[i].value);
  }
  free(res->headers.items);
  free(res);
  free(reqres);
  nghttp2_session_del(session);
  nghttp2_session_callbacks_del(callbacks);
  VALK_PASS();
}

void test_client_on_header_cb_grows_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();
  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_callbacks_set_send_callback(callbacks, __test_send_cb);
  nghttp2_session *session;
  nghttp2_session_client_new(&session, callbacks, nullptr);

  valk_http2_response_t *res = calloc(1, sizeof(valk_http2_response_t));
  res->headers.items = nullptr;
  res->headers.count = 0;
  res->headers.capacity = 0;

  typedef struct {
    u64 streamid;
    void *req;
    valk_http2_response_t *res;
    void *handle;
  } client_reqres_t;

  client_reqres_t *reqres = calloc(1, sizeof(client_reqres_t));
  reqres->res = res;

  nghttp2_nv req_hdrs[] = {
    {(u8 *)":method", (u8 *)"GET", 7, 3, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":scheme", (u8 *)"https", 7, 5, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":path", (u8 *)"/", 5, 1, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":authority", (u8 *)"localhost", 10, 9, NGHTTP2_NV_FLAG_NONE},
  };
  i32 stream_id = nghttp2_submit_request2(session, nullptr, req_hdrs, 4, nullptr, reqres);

  nghttp2_session_send(session);

  nghttp2_frame frame;
  memset(&frame, 0, sizeof(frame));
  frame.hd.type = NGHTTP2_HEADERS;
  frame.hd.stream_id = stream_id;

  int rv = valk_http2_client_on_header_cb(session, &frame,
    (u8 *)"x-header-1", 10, (u8 *)"value1", 6, 0, nullptr);
  ASSERT_EQ(rv, 0);
  ASSERT_EQ(res->headers.count, 1);
  ASSERT_GE(res->headers.capacity, 1);

  for (u64 i = 0; i < res->headers.count; i++) {
    free(res->headers.items[i].name);
    free(res->headers.items[i].value);
  }
  free(res->headers.items);
  free(res);
  free(reqres);
  nghttp2_session_del(session);
  nghttp2_session_callbacks_del(callbacks);
  VALK_PASS();
}

// --- release_stream_arena with backpressure ---

void test_release_stream_arena_backpressure_exit(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->httpStreamArenas = valk_slab_new(sizeof(valk_mem_arena_t) + 64 * 1024, 4);
  valk_aio_handle_t *conn = create_test_conn(sys);
  valk_aio_http_server *srv = calloc(1, sizeof(valk_aio_http_server));
  srv->sys = sys;
  conn->http.server = srv;

  SSL_CTX *ssl_ctx = SSL_CTX_new(TLS_server_method());
  valk_aio_ssl_accept(&conn->http.io.ssl, ssl_ctx);

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_callbacks_set_on_begin_headers_callback(callbacks, valk_http2_on_begin_headers_callback);
  nghttp2_session_callbacks_set_on_header_callback(callbacks, valk_http2_on_header_callback);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  static const u8 client_preface[] = "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";
  nghttp2_session_mem_recv2(conn->http.session, client_preface, sizeof(client_preface) - 1);

  u8 settings_frame[] = {
    0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00
  };
  nghttp2_session_mem_recv2(conn->http.session, settings_frame, sizeof(settings_frame));

  nghttp2_hd_deflater *deflater;
  nghttp2_hd_deflate_new(&deflater, 4096);
  nghttp2_nv headers[] = {
    {(u8 *)":method", (u8 *)"GET", 7, 3, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":scheme", (u8 *)"https", 7, 5, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":path", (u8 *)"/test", 5, 5, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":authority", (u8 *)"localhost", 10, 9, NGHTTP2_NV_FLAG_NONE},
  };
  u8 hdr_buf[1024];
  ssize_t hdr_len = nghttp2_hd_deflate_hd(deflater, hdr_buf, sizeof(hdr_buf), headers, 4);
  ASSERT_GT(hdr_len, 0);

  u8 frame_buf[1024];
  frame_buf[0] = (hdr_len >> 16) & 0xff;
  frame_buf[1] = (hdr_len >> 8) & 0xff;
  frame_buf[2] = hdr_len & 0xff;
  frame_buf[3] = 0x01;
  frame_buf[4] = 0x05;
  frame_buf[5] = 0x00;
  frame_buf[6] = 0x00;
  frame_buf[7] = 0x00;
  frame_buf[8] = 0x01;
  memcpy(frame_buf + 9, hdr_buf, hdr_len);
  nghttp2_session_mem_recv2(conn->http.session, frame_buf, 9 + hdr_len);

  valk_http2_server_request_t *req = nghttp2_session_get_stream_user_data(
      conn->http.session, 1);

  if (req && valk_arena_ref_valid(req->arena_ref)) {
    conn->http.arena_backpressure = true;
    valk_http2_release_stream_arena(conn, 1);
    ASSERT_FALSE(valk_arena_ref_valid(req->arena_ref));
    ASSERT_FALSE(conn->http.arena_backpressure);
  }

  nghttp2_hd_deflate_del(deflater);
  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  valk_aio_ssl_free(&conn->http.io.ssl);
  SSL_CTX_free(ssl_ctx);
  free(srv);
  free(conn);
  valk_slab_free(sys->httpStreamArenas);
  free_test_system(sys);
  VALK_PASS();
}

// --- on_frame_recv_callback: GOAWAY frame ---

void test_on_frame_recv_goaway(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  valk_aio_handle_t *conn = create_test_conn(sys);

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  nghttp2_frame frame;
  memset(&frame, 0, sizeof(frame));
  frame.hd.type = NGHTTP2_GOAWAY;
  frame.hd.stream_id = 0;

  int rv = valk_http2_on_frame_recv_callback(conn->http.session, &frame, conn);
  ASSERT_EQ(rv, 0);

  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  free(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- on_frame_recv_callback: RST_STREAM frame ---

void test_on_frame_recv_rst_stream(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  valk_aio_handle_t *conn = create_test_conn(sys);

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  nghttp2_frame frame;
  memset(&frame, 0, sizeof(frame));
  frame.hd.type = NGHTTP2_RST_STREAM;
  frame.hd.stream_id = 1;
  frame.rst_stream.error_code = NGHTTP2_CANCEL;

  int rv = valk_http2_on_frame_recv_callback(conn->http.session, &frame, conn);
  ASSERT_EQ(rv, 0);

  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  free(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- on_frame_recv_callback: HEADERS with no stream user data ---

void test_on_frame_recv_headers_no_stream_data(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  valk_aio_handle_t *conn = create_test_conn(sys);
  valk_aio_http_server *srv = calloc(1, sizeof(valk_aio_http_server));
  srv->sys = sys;
  conn->http.server = srv;

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  nghttp2_frame frame;
  memset(&frame, 0, sizeof(frame));
  frame.hd.type = NGHTTP2_HEADERS;
  frame.hd.stream_id = 1;
  frame.headers.cat = NGHTTP2_HCAT_REQUEST;

  int rv = valk_http2_on_frame_recv_callback(conn->http.session, &frame, conn);
  ASSERT_EQ(rv, 0);

  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  free(srv);
  free(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- on_begin_headers: arena pool exhausted sends 503 ---

void test_on_begin_headers_arena_exhausted(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->httpStreamArenas = valk_slab_new(sizeof(valk_mem_arena_t) + 64 * 1024, 1);
  valk_aio_handle_t *conn = create_test_conn(sys);
  valk_aio_http_server *srv = calloc(1, sizeof(valk_aio_http_server));
  srv->sys = sys;
  conn->http.server = srv;

  valk_slab_item_t *item = valk_slab_aquire(sys->httpStreamArenas);
  ASSERT_NOT_NULL(item);

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_callbacks_set_on_begin_headers_callback(callbacks, valk_http2_on_begin_headers_callback);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  static const u8 client_preface[] = "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";
  nghttp2_session_mem_recv2(conn->http.session, client_preface, sizeof(client_preface) - 1);

  u8 settings_frame[] = {
    0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00
  };
  nghttp2_session_mem_recv2(conn->http.session, settings_frame, sizeof(settings_frame));

  nghttp2_hd_deflater *deflater;
  nghttp2_hd_deflate_new(&deflater, 4096);
  nghttp2_nv headers[] = {
    {(u8 *)":method", (u8 *)"GET", 7, 3, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":scheme", (u8 *)"https", 7, 5, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":path", (u8 *)"/test", 5, 5, NGHTTP2_NV_FLAG_NONE},
    {(u8 *)":authority", (u8 *)"localhost", 10, 9, NGHTTP2_NV_FLAG_NONE},
  };
  u8 hdr_buf[1024];
  ssize_t hdr_len = nghttp2_hd_deflate_hd(deflater, hdr_buf, sizeof(hdr_buf), headers, 4);
  ASSERT_GT(hdr_len, 0);

  u8 frame_buf[1024];
  frame_buf[0] = (hdr_len >> 16) & 0xff;
  frame_buf[1] = (hdr_len >> 8) & 0xff;
  frame_buf[2] = hdr_len & 0xff;
  frame_buf[3] = 0x01;
  frame_buf[4] = 0x05;
  frame_buf[5] = 0x00;
  frame_buf[6] = 0x00;
  frame_buf[7] = 0x00;
  frame_buf[8] = 0x01;
  memcpy(frame_buf + 9, hdr_buf, hdr_len);
  nghttp2_session_mem_recv2(conn->http.session, frame_buf, 9 + hdr_len);

  ASSERT_TRUE(conn->http.arena_backpressure);
  ASSERT_EQ(conn->http.active_streams, 0);

  nghttp2_hd_deflate_del(deflater);
  valk_slab_release(sys->httpStreamArenas, item);
  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  free(srv);
  free(conn);
  valk_slab_free(sys->httpStreamArenas);
  free_test_system(sys);
  VALK_PASS();
}

// --- on_frame_recv_callback: non-matching frame type (passthrough) ---

void test_on_frame_recv_passthrough(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  valk_aio_handle_t *conn = create_test_conn(sys);

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  nghttp2_frame frame;
  memset(&frame, 0, sizeof(frame));
  frame.hd.type = NGHTTP2_SETTINGS;
  frame.hd.stream_id = 0;

  int rv = valk_http2_on_frame_recv_callback(conn->http.session, &frame, conn);
  ASSERT_EQ(rv, 0);

  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  free(conn);
  free_test_system(sys);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_byte_body_cb_full_body", test_byte_body_cb_full_body);
  valk_testsuite_add_test(suite, "test_byte_body_cb_chunked", test_byte_body_cb_chunked);
  valk_testsuite_add_test(suite, "test_byte_body_cb_needs_free", test_byte_body_cb_needs_free);

  valk_testsuite_add_test(suite, "test_qexpr_get_wrong_type", test_qexpr_get_wrong_type);
  valk_testsuite_add_test(suite, "test_qexpr_get_found", test_qexpr_get_found);
  valk_testsuite_add_test(suite, "test_qexpr_get_not_found", test_qexpr_get_not_found);

  valk_testsuite_add_test(suite, "test_session_valid_matching", test_session_valid_matching);
  valk_testsuite_add_test(suite, "test_session_valid_mismatch", test_session_valid_mismatch);
  valk_testsuite_add_test(suite, "test_session_valid_null_handle", test_session_valid_null_handle);
  valk_testsuite_add_test(suite, "test_session_valid_null_session", test_session_valid_null_session);

  valk_testsuite_add_test(suite, "test_connection_closing_null", test_connection_closing_null);
  valk_testsuite_add_test(suite, "test_connection_closing_established", test_connection_closing_established);
  valk_testsuite_add_test(suite, "test_connection_closing_closing_state", test_connection_closing_closing_state);
  valk_testsuite_add_test(suite, "test_connection_closing_closed_state", test_connection_closing_closed_state);

  valk_testsuite_add_test(suite, "test_stream_reset_null_conn", test_stream_reset_null_conn);
  valk_testsuite_add_test(suite, "test_stream_reset_null_session", test_stream_reset_null_session);
  valk_testsuite_add_test(suite, "test_stream_reset_with_session", test_stream_reset_with_session);

  valk_testsuite_add_test(suite, "test_submit_goaway_null_conn", test_submit_goaway_null_conn);
  valk_testsuite_add_test(suite, "test_submit_goaway_null_session", test_submit_goaway_null_session);
  valk_testsuite_add_test(suite, "test_submit_goaway_with_session", test_submit_goaway_with_session);

  valk_testsuite_add_test(suite, "test_release_stream_arena_null_conn", test_release_stream_arena_null_conn);
  valk_testsuite_add_test(suite, "test_release_stream_arena_null_session", test_release_stream_arena_null_session);
  valk_testsuite_add_test(suite, "test_release_stream_arena_null_server", test_release_stream_arena_null_server);
  valk_testsuite_add_test(suite, "test_release_stream_arena_no_stream_data", test_release_stream_arena_no_stream_data);
  valk_testsuite_add_test(suite, "test_release_stream_arena_with_valid_arena", test_release_stream_arena_with_valid_arena);

  valk_testsuite_add_test(suite, "test_remove_from_active_arenas_head", test_remove_from_active_arenas_head);
  valk_testsuite_add_test(suite, "test_remove_from_active_arenas_middle", test_remove_from_active_arenas_middle);

  valk_testsuite_add_test(suite, "test_client_on_header_cb_status", test_client_on_header_cb_status);
  valk_testsuite_add_test(suite, "test_client_on_header_cb_grows_capacity", test_client_on_header_cb_grows_capacity);

  valk_testsuite_add_test(suite, "test_release_stream_arena_backpressure_exit", test_release_stream_arena_backpressure_exit);
  valk_testsuite_add_test(suite, "test_on_frame_recv_goaway", test_on_frame_recv_goaway);
  valk_testsuite_add_test(suite, "test_on_frame_recv_rst_stream", test_on_frame_recv_rst_stream);
  valk_testsuite_add_test(suite, "test_on_frame_recv_headers_no_stream_data", test_on_frame_recv_headers_no_stream_data);
  valk_testsuite_add_test(suite, "test_on_begin_headers_arena_exhausted", test_on_begin_headers_arena_exhausted);
  valk_testsuite_add_test(suite, "test_on_frame_recv_passthrough", test_on_frame_recv_passthrough);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
