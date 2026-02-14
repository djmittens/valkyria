#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/http2/aio_http2_conn.h"
#include "../../src/aio/aio_internal.h"
#include "../../src/aio/aio_ops.h"

#include <nghttp2/nghttp2.h>
#include <stdlib.h>

static valk_aio_handle_t *create_test_conn(void) {
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->kind = VALK_HNDL_HTTP_CONN;
  conn->http.state = VALK_CONN_ESTABLISHED;
  conn->http.backpressure = false;
  conn->http.backpressure_next = nullptr;
  conn->http.backpressure_start_time = 0;
  conn->http.session = nullptr;
  conn->http.arena_backpressure = false;
  conn->http.active_streams = 0;
  valk_conn_io_init(&conn->http.io, HTTP_SLAB_ITEM_SIZE);
  return conn;
}

static void free_test_conn(valk_aio_handle_t *conn) {
  free(conn);
}

static valk_aio_system_t *create_test_system(void) {
  valk_aio_system_t *sys = calloc(1, sizeof(valk_aio_system_t));
  sys->ops = &valk_aio_ops_test;
  sys->config.min_buffers_per_conn = 4;
  sys->config.max_concurrent_streams = 100;
  return sys;
}

static void free_test_system(valk_aio_system_t *sys) {
  free(sys);
}

void test_backpressure_try_resume_one_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_http2_backpressure_try_resume_one(nullptr);
  VALK_PASS();
}

void test_backpressure_try_resume_one_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 10);
  valk_backpressure_list_init(&sys->backpressure, 100, 5000);

  valk_http2_backpressure_try_resume_one(sys);

  ASSERT_NULL(sys->backpressure.head);
  ASSERT_EQ(sys->backpressure.size, 0);

  valk_slab_free(sys->tcpBufferSlab);
  free_test_system(sys);
  VALK_PASS();
}

void test_write_buf_acquire_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->sys = nullptr;

  bool result = valk_http2_conn_write_buf_acquire(conn);
  ASSERT_FALSE(result);

  free_test_conn(conn);
  VALK_PASS();
}

void test_write_buf_acquire_null_slab(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = nullptr;
  conn->sys = sys;

  bool result = valk_http2_conn_write_buf_acquire(conn);
  ASSERT_FALSE(result);

  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_write_buf_acquire_success(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 4);
  conn->sys = sys;

  bool result = valk_http2_conn_write_buf_acquire(conn);
  ASSERT_TRUE(result);
  ASSERT_NOT_NULL(conn->http.io.write_buf);

  valk_conn_io_free(&conn->http.io, sys->tcpBufferSlab);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_write_buf_data_no_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();

  u8 *data = valk_http2_conn_write_buf_data(conn);
  ASSERT_NULL(data);

  free_test_conn(conn);
  VALK_PASS();
}

void test_write_buf_data_with_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 4);
  conn->sys = sys;

  valk_http2_conn_write_buf_acquire(conn);
  u8 *data = valk_http2_conn_write_buf_data(conn);
  ASSERT_NOT_NULL(data);

  valk_conn_io_free(&conn->http.io, sys->tcpBufferSlab);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_write_buf_available_no_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();

  u64 available = valk_http2_conn_write_buf_available(conn);
  ASSERT_EQ(available, 0);

  free_test_conn(conn);
  VALK_PASS();
}

void test_write_buf_available_with_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 4);
  conn->sys = sys;

  valk_http2_conn_write_buf_acquire(conn);
  u64 available = valk_http2_conn_write_buf_available(conn);
  ASSERT_EQ(available, HTTP_SLAB_ITEM_SIZE);

  valk_conn_io_free(&conn->http.io, sys->tcpBufferSlab);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_write_buf_append_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->sys = nullptr;

  u8 data[] = {1, 2, 3, 4, 5};
  u64 appended = valk_http2_conn_write_buf_append(conn, data, sizeof(data));
  ASSERT_EQ(appended, 0);

  free_test_conn(conn);
  VALK_PASS();
}

void test_write_buf_append_null_slab(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = nullptr;
  conn->sys = sys;

  u8 data[] = {1, 2, 3, 4, 5};
  u64 appended = valk_http2_conn_write_buf_append(conn, data, sizeof(data));
  ASSERT_EQ(appended, 0);

  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_write_buf_append_success(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 4);
  conn->sys = sys;

  valk_http2_conn_write_buf_acquire(conn);

  u8 data[] = {1, 2, 3, 4, 5};
  u64 appended = valk_http2_conn_write_buf_append(conn, data, sizeof(data));
  ASSERT_EQ(appended, sizeof(data));
  ASSERT_EQ(conn->http.io.write_pos, sizeof(data));

  u64 remaining = valk_http2_conn_write_buf_available(conn);
  ASSERT_EQ(remaining, HTTP_SLAB_ITEM_SIZE - sizeof(data));

  valk_conn_io_free(&conn->http.io, sys->tcpBufferSlab);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_flush_frames_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_buffer_t buf = {.items = nullptr, .count = 0, .capacity = 1024};
  u64 result = valk_http2_flush_frames(&buf, nullptr);
  ASSERT_EQ(result, 0);
  VALK_PASS();
}

void test_flush_frames_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = nullptr;

  valk_buffer_t buf = {.items = nullptr, .count = 0, .capacity = 1024};
  u64 result = valk_http2_flush_frames(&buf, conn);
  ASSERT_EQ(result, 0);

  free_test_conn(conn);
  VALK_PASS();
}

void test_enter_arena_backpressure_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_http2_enter_arena_backpressure(nullptr);
  VALK_PASS();
}

void test_enter_arena_backpressure_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = nullptr;

  valk_http2_enter_arena_backpressure(conn);

  ASSERT_FALSE(conn->http.arena_backpressure);

  free_test_conn(conn);
  VALK_PASS();
}

void test_enter_arena_backpressure_already_backpressured(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = (nghttp2_session *)0x1;
  conn->http.arena_backpressure = true;

  valk_http2_enter_arena_backpressure(conn);

  ASSERT_TRUE(conn->http.arena_backpressure);

  free_test_conn(conn);
  VALK_PASS();
}

void test_exit_arena_backpressure_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_http2_exit_arena_backpressure(nullptr);
  VALK_PASS();
}

void test_exit_arena_backpressure_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = nullptr;
  conn->http.arena_backpressure = true;

  valk_http2_exit_arena_backpressure(conn);

  ASSERT_TRUE(conn->http.arena_backpressure);

  free_test_conn(conn);
  VALK_PASS();
}

void test_exit_arena_backpressure_not_backpressured(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = (nghttp2_session *)0x1;
  conn->http.arena_backpressure = false;

  valk_http2_exit_arena_backpressure(conn);

  ASSERT_FALSE(conn->http.arena_backpressure);

  free_test_conn(conn);
  VALK_PASS();
}

void test_exit_arena_backpressure_null_server(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = (nghttp2_session *)0x1;
  conn->http.arena_backpressure = true;
  conn->http.server = nullptr;

  valk_http2_exit_arena_backpressure(conn);

  ASSERT_TRUE(conn->http.arena_backpressure);

  free_test_conn(conn);
  VALK_PASS();
}

void test_conn_on_disconnect_null_handler(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  conn->sys = sys;
  conn->http.session = nullptr;
  conn->http.httpHandler = nullptr;
  conn->http.server = nullptr;
  conn->http.stream_bodies = nullptr;
  conn->http.state = VALK_CONN_CLOSING;

  valk_backpressure_list_init(&sys->backpressure, 100, 5000);

  valk_http2_conn_on_disconnect(conn);

  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSED);
  ASSERT_FALSE(conn->http.backpressure);

  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_conn_tcp_read_impl_closing_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.state = VALK_CONN_CLOSING;

  valk_http2_conn_tcp_read_impl(conn, 100, "test data");

  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSING);

  free_test_conn(conn);
  VALK_PASS();
}

void test_conn_tcp_read_impl_closed_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.state = VALK_CONN_CLOSED;

  valk_http2_conn_tcp_read_impl(conn, 100, "test data");

  ASSERT_EQ(conn->http.state, VALK_CONN_CLOSED);

  free_test_conn(conn);
  VALK_PASS();
}

void test_flush_pending_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_http2_flush_pending(nullptr);
  VALK_PASS();
}

void test_continue_pending_send_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_http2_continue_pending_send(nullptr);
  VALK_PASS();
}

void test_continue_pending_send_null_session(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.session = nullptr;

  valk_http2_continue_pending_send(conn);

  free_test_conn(conn);
  VALK_PASS();
}

void test_alloc_callback_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  uv_handle_t handle = {.data = nullptr};
  uv_buf_t buf = {.base = (char *)0x1234, .len = 1000};

  valk_http2_conn_alloc_callback(&handle, 1024, &buf);

  ASSERT_NULL(buf.base);
  ASSERT_EQ(buf.len, 0);

  VALK_PASS();
}

void test_alloc_callback_wrong_magic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->magic = 0xDEADBEEF;

  uv_handle_t handle = {.data = conn};
  uv_buf_t buf = {.base = (char *)0x1234, .len = 1000};

  valk_http2_conn_alloc_callback(&handle, 1024, &buf);

  ASSERT_NULL(buf.base);
  ASSERT_EQ(buf.len, 0);

  free_test_conn(conn);
  VALK_PASS();
}

void test_alloc_callback_wrong_kind(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  conn->kind = VALK_HNDL_TCP;

  uv_handle_t handle = {.data = conn};
  uv_buf_t buf = {.base = (char *)0x1234, .len = 1000};

  valk_http2_conn_alloc_callback(&handle, 1024, &buf);

  ASSERT_NULL(buf.base);
  ASSERT_EQ(buf.len, 0);

  free_test_conn(conn);
  VALK_PASS();
}

void test_alloc_callback_existing_read_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 4);
  conn->sys = sys;

  valk_conn_io_read_buf_acquire(&conn->http.io, sys->tcpBufferSlab);
  ASSERT_NOT_NULL(conn->http.io.read_buf);

  uv_handle_t handle = {.data = conn};
  uv_buf_t buf = {.base = nullptr, .len = 0};

  valk_http2_conn_alloc_callback(&handle, 1024, &buf);

  ASSERT_NOT_NULL(buf.base);
  ASSERT_EQ(buf.len, HTTP_SLAB_ITEM_SIZE);

  valk_conn_io_free(&conn->http.io, sys->tcpBufferSlab);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_alloc_callback_acquire_new_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 4);
  conn->sys = sys;

  ASSERT_NULL(conn->http.io.read_buf);

  uv_handle_t handle = {.data = conn};
  uv_buf_t buf = {.base = nullptr, .len = 0};

  valk_http2_conn_alloc_callback(&handle, 1024, &buf);

  ASSERT_NOT_NULL(buf.base);
  ASSERT_EQ(buf.len, HTTP_SLAB_ITEM_SIZE);
  ASSERT_NOT_NULL(conn->http.io.read_buf);

  valk_conn_io_free(&conn->http.io, sys->tcpBufferSlab);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

void test_alloc_callback_slab_exhausted(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 2);
  conn->sys = sys;

  valk_slab_aquire(sys->tcpBufferSlab);
  valk_slab_aquire(sys->tcpBufferSlab);
  ASSERT_EQ(valk_slab_available(sys->tcpBufferSlab), 0);

  uv_handle_t handle = {.data = conn};
  uv_buf_t buf = {.base = (char *)0x1234, .len = 1000};

  valk_http2_conn_alloc_callback(&handle, 1024, &buf);

  ASSERT_NULL(buf.base);
  ASSERT_EQ(buf.len, 0);

  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- backpressure resume with actual conn (exercises __vtable_read_start) ---

void test_backpressure_try_resume_one_with_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 10);
  valk_backpressure_list_init(&sys->backpressure, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  conn->sys = sys;
  conn->uv.tcp.user_data = conn;

  valk_backpressure_list_add(&sys->backpressure, conn, 0);
  ASSERT_EQ(sys->backpressure.size, 1);
  ASSERT_TRUE(conn->http.backpressure);

  valk_http2_backpressure_try_resume_one(sys);

  ASSERT_FALSE(conn->http.backpressure);
  ASSERT_EQ(sys->backpressure.size, 0);

  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- vtable_alloc_cb + vtable_read_cb via inject_data after resume ---

void test_vtable_read_path_via_inject_data(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 10);
  valk_backpressure_list_init(&sys->backpressure, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  conn->sys = sys;
  conn->uv.tcp.user_data = conn;
  conn->http.state = VALK_CONN_ESTABLISHED;

  valk_backpressure_list_add(&sys->backpressure, conn, 0);
  valk_http2_backpressure_try_resume_one(sys);

  conn->http.state = VALK_CONN_CLOSING;
  valk_test_tcp_inject_data(&conn->uv.tcp, "test", 4);

  ASSERT_NOT_NULL(conn->http.io.read_buf);

  valk_conn_io_free(&conn->http.io, sys->tcpBufferSlab);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- vtable_alloc_cb existing read_buf path ---

void test_vtable_alloc_cb_existing_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 10);
  valk_backpressure_list_init(&sys->backpressure, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  conn->sys = sys;
  conn->uv.tcp.user_data = conn;
  conn->http.state = VALK_CONN_ESTABLISHED;

  valk_backpressure_list_add(&sys->backpressure, conn, 0);
  valk_http2_backpressure_try_resume_one(sys);

  conn->http.state = VALK_CONN_CLOSING;
  valk_test_tcp_inject_data(&conn->uv.tcp, "first", 5);
  ASSERT_NOT_NULL(conn->http.io.read_buf);

  valk_test_tcp_inject_data(&conn->uv.tcp, "second", 6);

  valk_conn_io_free(&conn->http.io, sys->tcpBufferSlab);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- vtable_alloc_cb slab exhausted ---

void test_vtable_alloc_cb_slab_exhausted(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 4);
  valk_backpressure_list_init(&sys->backpressure, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  conn->sys = sys;
  conn->uv.tcp.user_data = conn;
  conn->http.state = VALK_CONN_ESTABLISHED;

  valk_backpressure_list_add(&sys->backpressure, conn, 0);
  valk_http2_backpressure_try_resume_one(sys);
  ASSERT_FALSE(conn->http.backpressure);

  void *s1 = valk_slab_aquire(sys->tcpBufferSlab);
  void *s2 = valk_slab_aquire(sys->tcpBufferSlab);
  void *s3 = valk_slab_aquire(sys->tcpBufferSlab);
  void *s4 = valk_slab_aquire(sys->tcpBufferSlab);
  ASSERT_EQ(valk_slab_available(sys->tcpBufferSlab), 0);

  conn->http.state = VALK_CONN_CLOSING;
  valk_test_tcp_inject_data(&conn->uv.tcp, "data", 4);
  ASSERT_NULL(conn->http.io.read_buf);

  valk_slab_release(sys->tcpBufferSlab, s1);
  valk_slab_release(sys->tcpBufferSlab, s2);
  valk_slab_release(sys->tcpBufferSlab, s3);
  valk_slab_release(sys->tcpBufferSlab, s4);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- vtable_alloc_cb invalid conn ---

void test_vtable_alloc_cb_invalid_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 10);
  valk_backpressure_list_init(&sys->backpressure, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  conn->sys = sys;
  conn->uv.tcp.user_data = conn;
  conn->http.state = VALK_CONN_ESTABLISHED;

  valk_backpressure_list_add(&sys->backpressure, conn, 0);
  valk_http2_backpressure_try_resume_one(sys);
  ASSERT_FALSE(conn->http.backpressure);

  conn->magic = 0;

  valk_test_tcp_inject_data(&conn->uv.tcp, "data", 4);
  ASSERT_NULL(conn->http.io.read_buf);

  conn->magic = VALK_AIO_HANDLE_MAGIC;
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- flush_complete with backpressure exercises resume path ---

void test_flush_complete_resumes_backpressure(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 10);
  valk_backpressure_list_init(&sys->backpressure, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  conn->sys = sys;
  conn->uv.tcp.user_data = conn;
  conn->http.state = VALK_CONN_ESTABLISHED;
  conn->http.backpressure = true;

  nghttp2_session_callbacks *callbacks;
  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_server_new(&conn->http.session, callbacks, conn);

  valk_backpressure_list_add(&sys->backpressure, conn, 0);

  bool acquired = valk_http2_conn_write_buf_acquire(conn);
  ASSERT_TRUE(acquired);

  u8 *write_data = valk_http2_conn_write_buf_data(conn);
  ASSERT_NOT_NULL(write_data);
  memcpy(write_data, "HTTP/2 data", 11);
  conn->http.io.write_pos = 11;

  valk_http2_conn_write_buf_flush(conn);

  ASSERT_FALSE(conn->http.backpressure);

  nghttp2_session_del(conn->http.session);
  nghttp2_session_callbacks_del(callbacks);
  valk_conn_io_free(&conn->http.io, sys->tcpBufferSlab);
  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

// --- tcp_read_impl with null buffer triggers backpressure ---

void test_tcp_read_impl_null_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->tcpBufferSlab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 10);
  valk_backpressure_list_init(&sys->backpressure, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  conn->sys = sys;
  conn->uv.tcp.user_data = conn;

  valk_http2_conn_tcp_read_impl(conn, 0, nullptr);

  ASSERT_TRUE(conn->http.backpressure);
  ASSERT_EQ(sys->backpressure.size, 1);

  valk_slab_free(sys->tcpBufferSlab);
  free_test_conn(conn);
  free_test_system(sys);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_backpressure_try_resume_one_null_sys", test_backpressure_try_resume_one_null_sys);
  valk_testsuite_add_test(suite, "test_backpressure_try_resume_one_empty_list", test_backpressure_try_resume_one_empty_list);

  valk_testsuite_add_test(suite, "test_write_buf_acquire_null_sys", test_write_buf_acquire_null_sys);
  valk_testsuite_add_test(suite, "test_write_buf_acquire_null_slab", test_write_buf_acquire_null_slab);
  valk_testsuite_add_test(suite, "test_write_buf_acquire_success", test_write_buf_acquire_success);

  valk_testsuite_add_test(suite, "test_write_buf_data_no_buf", test_write_buf_data_no_buf);
  valk_testsuite_add_test(suite, "test_write_buf_data_with_buf", test_write_buf_data_with_buf);

  valk_testsuite_add_test(suite, "test_write_buf_available_no_buf", test_write_buf_available_no_buf);
  valk_testsuite_add_test(suite, "test_write_buf_available_with_buf", test_write_buf_available_with_buf);

  valk_testsuite_add_test(suite, "test_write_buf_append_null_sys", test_write_buf_append_null_sys);
  valk_testsuite_add_test(suite, "test_write_buf_append_null_slab", test_write_buf_append_null_slab);
  valk_testsuite_add_test(suite, "test_write_buf_append_success", test_write_buf_append_success);

  valk_testsuite_add_test(suite, "test_flush_frames_null_conn", test_flush_frames_null_conn);
  valk_testsuite_add_test(suite, "test_flush_frames_null_session", test_flush_frames_null_session);

  valk_testsuite_add_test(suite, "test_enter_arena_backpressure_null_conn", test_enter_arena_backpressure_null_conn);
  valk_testsuite_add_test(suite, "test_enter_arena_backpressure_null_session", test_enter_arena_backpressure_null_session);
  valk_testsuite_add_test(suite, "test_enter_arena_backpressure_already_backpressured", test_enter_arena_backpressure_already_backpressured);

  valk_testsuite_add_test(suite, "test_exit_arena_backpressure_null_conn", test_exit_arena_backpressure_null_conn);
  valk_testsuite_add_test(suite, "test_exit_arena_backpressure_null_session", test_exit_arena_backpressure_null_session);
  valk_testsuite_add_test(suite, "test_exit_arena_backpressure_not_backpressured", test_exit_arena_backpressure_not_backpressured);
  valk_testsuite_add_test(suite, "test_exit_arena_backpressure_null_server", test_exit_arena_backpressure_null_server);

  valk_testsuite_add_test(suite, "test_conn_on_disconnect_null_handler", test_conn_on_disconnect_null_handler);

  valk_testsuite_add_test(suite, "test_conn_tcp_read_impl_closing_conn", test_conn_tcp_read_impl_closing_conn);
  valk_testsuite_add_test(suite, "test_conn_tcp_read_impl_closed_conn", test_conn_tcp_read_impl_closed_conn);

  valk_testsuite_add_test(suite, "test_flush_pending_null_conn", test_flush_pending_null_conn);
  valk_testsuite_add_test(suite, "test_continue_pending_send_null_conn", test_continue_pending_send_null_conn);
  valk_testsuite_add_test(suite, "test_continue_pending_send_null_session", test_continue_pending_send_null_session);

  valk_testsuite_add_test(suite, "test_alloc_callback_null_conn", test_alloc_callback_null_conn);
  valk_testsuite_add_test(suite, "test_alloc_callback_wrong_magic", test_alloc_callback_wrong_magic);
  valk_testsuite_add_test(suite, "test_alloc_callback_wrong_kind", test_alloc_callback_wrong_kind);
  valk_testsuite_add_test(suite, "test_alloc_callback_existing_read_buf", test_alloc_callback_existing_read_buf);
  valk_testsuite_add_test(suite, "test_alloc_callback_acquire_new_buf", test_alloc_callback_acquire_new_buf);
  valk_testsuite_add_test(suite, "test_alloc_callback_slab_exhausted", test_alloc_callback_slab_exhausted);

  valk_testsuite_add_test(suite, "test_backpressure_try_resume_one_with_conn", test_backpressure_try_resume_one_with_conn);
  valk_testsuite_add_test(suite, "test_vtable_read_path_via_inject_data", test_vtable_read_path_via_inject_data);
  valk_testsuite_add_test(suite, "test_vtable_alloc_cb_existing_buf", test_vtable_alloc_cb_existing_buf);
  valk_testsuite_add_test(suite, "test_vtable_alloc_cb_slab_exhausted_vtable", test_vtable_alloc_cb_slab_exhausted);
  valk_testsuite_add_test(suite, "test_vtable_alloc_cb_invalid_conn", test_vtable_alloc_cb_invalid_conn);
  valk_testsuite_add_test(suite, "test_flush_complete_resumes_backpressure", test_flush_complete_resumes_backpressure);
  valk_testsuite_add_test(suite, "test_tcp_read_impl_null_buffer", test_tcp_read_impl_null_buffer);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
