#include <stdlib.h>
#include <string.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/aio_internal.h"
#include "aio/aio_handle_diag.h"
#include "common.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

typedef struct {
  int connectedCount;
  int disconnectedCount;
} test_srv_state_t;

static void cb_onConnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  test_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->connectedCount, 1, __ATOMIC_RELAXED);
}

static void cb_onDisconnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  test_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->disconnectedCount, 1, __ATOMIC_RELAXED);
}

static void cb_onHeader(void *arg, valk_aio_handle_t *conn, u64 stream, char *name,
                 char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

static void cb_onBody(void *arg, valk_aio_handle_t *conn, u64 stream, u8 flags,
               valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}

void test_get_tcp_buffer_slab_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_aio_get_tcp_buffer_slab(nullptr);
  ASSERT_NULL(slab);

  VALK_PASS();
}

void test_get_handle_slab_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_aio_get_handle_slab(nullptr);
  ASSERT_NULL(slab);

  VALK_PASS();
}

void test_get_stream_arenas_slab_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_aio_get_stream_arenas_slab(nullptr);
  ASSERT_NULL(slab);

  VALK_PASS();
}

void test_get_http_servers_slab_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_aio_get_http_servers_slab(nullptr);
  ASSERT_NULL(slab);

  VALK_PASS();
}

void test_get_http_clients_slab_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_aio_get_http_clients_slab(nullptr);
  ASSERT_NULL(slab);

  VALK_PASS();
}

void test_get_handle_diag_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_handle_diag_t diag;
  bool ok = valk_aio_get_handle_diag(nullptr, 0, &diag);
  ASSERT_FALSE(ok);

  VALK_PASS();
}

void test_get_handle_diag_null_out(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  bool ok = valk_aio_get_handle_diag(sys, 0, nullptr);
  ASSERT_FALSE(ok);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_get_handle_kind_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(nullptr, 0);
  ASSERT_EQ(kind, VALK_DIAG_HNDL_EMPTY);

  VALK_PASS();
}

void test_get_slabs_with_active_system(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_slab_t *tcp_slab = valk_aio_get_tcp_buffer_slab(sys);
  ASSERT_NOT_NULL(tcp_slab);

  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  ASSERT_NOT_NULL(handle_slab);

  valk_slab_t *arena_slab = valk_aio_get_stream_arenas_slab(sys);
  ASSERT_NOT_NULL(arena_slab);

  valk_slab_t *server_slab = valk_aio_get_http_servers_slab(sys);
  ASSERT_NOT_NULL(server_slab);

  valk_slab_t *client_slab = valk_aio_get_http_clients_slab(sys);
  ASSERT_NOT_NULL(client_slab);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_get_handle_kind_out_of_bounds(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(sys, 999999);
  ASSERT_EQ(kind, VALK_DIAG_HNDL_EMPTY);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_get_handle_diag_out_of_bounds(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_handle_diag_t diag;
  bool ok = valk_aio_get_handle_diag(sys, 999999, &diag);
  ASSERT_FALSE(ok);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_handle_kind_with_connection(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  test_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(server_result);
  int port = valk_aio_http2_server_get_port(srv);

  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);

  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  ASSERT_NOT_NULL(handle_slab);

  int found_http = 0;
  int found_empty = 0;
  for (u64 i = 0; i < handle_slab->numItems && i < 100; i++) {
    valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(sys, i);
    if (kind == VALK_DIAG_HNDL_HTTP_CONN || kind == VALK_DIAG_HNDL_TCP) {
      found_http++;
    } else if (kind == VALK_DIAG_HNDL_EMPTY) {
      found_empty++;
    }
  }

  ASSERT_GT(found_http + found_empty, 0);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_owner_register_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  u16 idx = valk_owner_register(nullptr, "test", 1, (void*)0x1234);
  ASSERT_EQ(idx, UINT16_MAX);

  VALK_PASS();
}

void test_owner_register_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  u16 idx = valk_owner_register(sys, "test_owner", 1, (void*)0x1234);
  ASSERT_NE(idx, UINT16_MAX);

  const char *name = valk_owner_get_name(sys, idx);
  ASSERT_NOT_NULL(name);
  ASSERT_STR_EQ(name, "test_owner");

  u64 count = valk_owner_get_count(sys);
  ASSERT_GT(count, 0);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_owner_get_name_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *name = valk_owner_get_name(nullptr, 0);
  ASSERT_NULL(name);

  VALK_PASS();
}

void test_owner_get_name_out_of_bounds(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  const char *name = valk_owner_get_name(sys, UINT16_MAX);
  ASSERT_NULL(name);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_owner_get_count_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  u64 count = valk_owner_get_count(nullptr);
  ASSERT_EQ(count, 0);

  VALK_PASS();
}

void test_handle_kind_with_timer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);

  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  ASSERT_NOT_NULL(handle_slab);

  bool found_timer = false;
  for (u64 i = 0; i < handle_slab->numItems && i < 100; i++) {
    valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(sys, i);
    if (kind == VALK_DIAG_HNDL_TIMER) {
      found_timer = true;
      break;
    }
  }
  ASSERT_TRUE(found_timer);

  valk_aio_timer_close(timer, NULL);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_get_tcp_buffer_slab_null", test_get_tcp_buffer_slab_null);
  valk_testsuite_add_test(suite, "test_get_handle_slab_null", test_get_handle_slab_null);
  valk_testsuite_add_test(suite, "test_get_stream_arenas_slab_null", test_get_stream_arenas_slab_null);
  valk_testsuite_add_test(suite, "test_get_http_servers_slab_null", test_get_http_servers_slab_null);
  valk_testsuite_add_test(suite, "test_get_http_clients_slab_null", test_get_http_clients_slab_null);
  valk_testsuite_add_test(suite, "test_get_handle_diag_null_sys", test_get_handle_diag_null_sys);
  valk_testsuite_add_test(suite, "test_get_handle_diag_null_out", test_get_handle_diag_null_out);
  valk_testsuite_add_test(suite, "test_get_handle_kind_null", test_get_handle_kind_null);
  valk_testsuite_add_test(suite, "test_get_slabs_with_active_system", test_get_slabs_with_active_system);
  valk_testsuite_add_test(suite, "test_get_handle_kind_out_of_bounds", test_get_handle_kind_out_of_bounds);
  valk_testsuite_add_test(suite, "test_get_handle_diag_out_of_bounds", test_get_handle_diag_out_of_bounds);
  valk_testsuite_add_test(suite, "test_handle_kind_with_connection", test_handle_kind_with_connection);
  valk_testsuite_add_test(suite, "test_owner_register_null", test_owner_register_null);
  valk_testsuite_add_test(suite, "test_owner_register_success", test_owner_register_success);
  valk_testsuite_add_test(suite, "test_owner_get_name_null", test_owner_get_name_null);
  valk_testsuite_add_test(suite, "test_owner_get_name_out_of_bounds", test_owner_get_name_out_of_bounds);
  valk_testsuite_add_test(suite, "test_owner_get_count_null", test_owner_get_count_null);
  valk_testsuite_add_test(suite, "test_handle_kind_with_timer", test_handle_kind_with_timer);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
