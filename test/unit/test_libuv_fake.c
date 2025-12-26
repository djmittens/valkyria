#include "../testing.h"
#include "../../test/fakes/libuv_fake/uv_fake.h"
#include "../../test/fakes/libuv_fake/uv_fake_control.h"
#include <string.h>

static uv_loop_t test_loop;
static int g_callback_count = 0;
static uv_timer_t *g_last_timer = NULL;

static void reset_state(void) {
  uv_loop_init(&test_loop);
  uv_fake_reset(&test_loop);
  g_callback_count = 0;
  g_last_timer = NULL;
}

static void timer_cb(uv_timer_t *timer) {
  g_last_timer = timer;
  g_callback_count++;
}

void test_loop_init(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  uv_loop_t loop;
  int r = uv_loop_init(&loop);
  ASSERT_EQ(r, 0);
  ASSERT_EQ(loop.time, 0);
  ASSERT_FALSE(loop.running);
  
  VALK_PASS();
}

void test_timer_init(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  uv_timer_t timer;
  int r = uv_timer_init(&test_loop, &timer);
  ASSERT_EQ(r, 0);
  ASSERT_EQ(timer.loop, &test_loop);
  ASSERT_EQ(timer.type, UV_TIMER);
  ASSERT_FALSE(timer.active);
  
  VALK_PASS();
}

void test_timer_fires_at_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  uv_timer_t timer;
  uv_timer_init(&test_loop, &timer);
  uv_timer_start(&timer, timer_cb, 1000, 0);
  
  ASSERT_EQ(g_callback_count, 0);
  
  uv_fake_time_advance(&test_loop, 500);
  ASSERT_EQ(g_callback_count, 0);
  
  uv_fake_time_advance(&test_loop, 500);
  ASSERT_EQ(g_callback_count, 1);
  ASSERT_EQ(g_last_timer, &timer);
  
  uv_fake_time_advance(&test_loop, 1000);
  ASSERT_EQ(g_callback_count, 1);
  
  VALK_PASS();
}

void test_timer_repeats(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  uv_timer_t timer;
  uv_timer_init(&test_loop, &timer);
  uv_timer_start(&timer, timer_cb, 100, 100);
  
  uv_fake_time_advance(&test_loop, 350);
  ASSERT_EQ(g_callback_count, 3);
  
  VALK_PASS();
}

void test_timer_stop(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  uv_timer_t timer;
  uv_timer_init(&test_loop, &timer);
  uv_timer_start(&timer, timer_cb, 100, 100);
  
  uv_fake_time_advance(&test_loop, 100);
  ASSERT_EQ(g_callback_count, 1);
  
  uv_timer_stop(&timer);
  
  uv_fake_time_advance(&test_loop, 100);
  ASSERT_EQ(g_callback_count, 1);
  
  VALK_PASS();
}

void test_now_and_hrtime(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  ASSERT_EQ(uv_now(&test_loop), 0);
  ASSERT_EQ(uv_hrtime(), 0);
  
  uv_fake_time_advance(&test_loop, 500);
  
  ASSERT_EQ(uv_now(&test_loop), 500);
  ASSERT_EQ(uv_hrtime(), 500 * 1000000ULL);
  
  VALK_PASS();
}

void test_tcp_init(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  uv_tcp_t tcp;
  int r = uv_tcp_init(&test_loop, &tcp);
  ASSERT_EQ(r, 0);
  ASSERT_EQ(tcp.loop, &test_loop);
  ASSERT_EQ(tcp.type, UV_TCP);
  
  VALK_PASS();
}

void test_tcp_bind_listen(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  uv_tcp_t server;
  uv_tcp_init(&test_loop, &server);
  
  struct sockaddr_in addr;
  uv_ip4_addr("127.0.0.1", 8080, &addr);
  
  int r = uv_tcp_bind(&server, (struct sockaddr *)&addr, 0);
  ASSERT_EQ(r, 0);
  ASSERT_TRUE(server.bound);
  
  static int conn_count = 0;
  conn_count = 0;
  
  r = uv_listen((uv_stream_t *)&server, 128, (uv_connection_cb)NULL);
  ASSERT_EQ(r, 0);
  ASSERT_TRUE(server.listening);
  
  VALK_PASS();
}

static int g_conn_count = 0;

static void on_connection(uv_stream_t *server, int status) {
  (void)server;
  (void)status;
  g_conn_count++;
}

void test_tcp_accept(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  g_conn_count = 0;
  
  uv_tcp_t server;
  uv_tcp_init(&test_loop, &server);
  
  struct sockaddr_in addr;
  uv_ip4_addr("127.0.0.1", 8080, &addr);
  uv_tcp_bind(&server, (struct sockaddr *)&addr, 0);
  uv_listen((uv_stream_t *)&server, 128, on_connection);
  
  uv_tcp_t fake_client;
  memset(&fake_client, 0, sizeof(fake_client));
  
  uv_fake_inject_connection(&server, &fake_client);
  ASSERT_EQ(g_conn_count, 1);
  
  uv_tcp_t accepted;
  int r = uv_accept((uv_stream_t *)&server, (uv_stream_t *)&accepted);
  ASSERT_EQ(r, 0);
  
  VALK_PASS();
}

static char g_read_buf[1024];
static ssize_t g_read_len = 0;

static void on_alloc(uv_handle_t *handle, size_t suggested_size, uv_buf_t *buf) {
  (void)handle;
  (void)suggested_size;
  buf->base = g_read_buf;
  buf->len = sizeof(g_read_buf);
}

static void on_read(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
  (void)stream;
  (void)buf;
  g_read_len = nread;
}

void test_tcp_read_inject(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  memset(g_read_buf, 0, sizeof(g_read_buf));
  g_read_len = 0;
  
  uv_tcp_t tcp;
  uv_tcp_init(&test_loop, &tcp);
  
  uv_read_start((uv_stream_t *)&tcp, on_alloc, on_read);
  
  const char *test_data = "Hello, World!";
  uv_fake_inject_read_data(&tcp, test_data, strlen(test_data));
  
  ASSERT_EQ(g_read_len, (ssize_t)strlen(test_data));
  ASSERT_EQ(memcmp(g_read_buf, test_data, strlen(test_data)), 0);
  
  VALK_PASS();
}

void test_tcp_write_capture(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  uv_tcp_t tcp;
  uv_tcp_init(&test_loop, &tcp);
  
  const char *data1 = "Hello";
  const char *data2 = "World";
  
  uv_buf_t bufs[2] = {
    uv_buf_init((char *)data1, 5),
    uv_buf_init((char *)data2, 5),
  };
  
  uv_write_t req;
  uv_write(&req, (uv_stream_t *)&tcp, bufs, 2, NULL);
  
  char captured[64];
  size_t len = uv_fake_get_written_data(&tcp, captured, sizeof(captured));
  ASSERT_EQ(len, 10);
  ASSERT_EQ(memcmp(captured, "HelloWorld", 10), 0);
  
  VALK_PASS();
}

void test_loop_alive(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  ASSERT_FALSE(uv_loop_alive(&test_loop));
  
  uv_timer_t timer;
  uv_timer_init(&test_loop, &timer);
  uv_timer_start(&timer, timer_cb, 100, 0);
  
  ASSERT_TRUE(uv_loop_alive(&test_loop));
  
  uv_fake_time_advance(&test_loop, 100);
  
  ASSERT_FALSE(uv_loop_alive(&test_loop));
  
  VALK_PASS();
}

void test_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  uv_timer_t timer;
  uv_timer_init(&test_loop, &timer);
  uv_timer_start(&timer, timer_cb, 100, 100);
  
  ASSERT_FALSE(uv_is_closing((uv_handle_t *)&timer));
  
  uv_close((uv_handle_t *)&timer, NULL);
  
  ASSERT_TRUE(uv_is_closing((uv_handle_t *)&timer));
  
  uv_fake_time_advance(&test_loop, 100);
  ASSERT_EQ(g_callback_count, 0);
  
  VALK_PASS();
}

void test_timer_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  
  ASSERT_EQ(uv_fake_timer_count(&test_loop), 0);
  
  uv_timer_t timer1, timer2;
  uv_timer_init(&test_loop, &timer1);
  uv_timer_init(&test_loop, &timer2);
  
  uv_timer_start(&timer1, timer_cb, 100, 0);
  ASSERT_EQ(uv_fake_timer_count(&test_loop), 1);
  
  uv_timer_start(&timer2, timer_cb, 200, 0);
  ASSERT_EQ(uv_fake_timer_count(&test_loop), 2);
  
  uv_fake_time_advance(&test_loop, 100);
  ASSERT_EQ(uv_fake_timer_count(&test_loop), 1);
  
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  
  valk_testsuite_add_test(suite, "loop_init", test_loop_init);
  valk_testsuite_add_test(suite, "timer_init", test_timer_init);
  valk_testsuite_add_test(suite, "timer_fires_at_timeout", test_timer_fires_at_timeout);
  valk_testsuite_add_test(suite, "timer_repeats", test_timer_repeats);
  valk_testsuite_add_test(suite, "timer_stop", test_timer_stop);
  valk_testsuite_add_test(suite, "now_and_hrtime", test_now_and_hrtime);
  valk_testsuite_add_test(suite, "tcp_init", test_tcp_init);
  valk_testsuite_add_test(suite, "tcp_bind_listen", test_tcp_bind_listen);
  valk_testsuite_add_test(suite, "tcp_accept", test_tcp_accept);
  valk_testsuite_add_test(suite, "tcp_read_inject", test_tcp_read_inject);
  valk_testsuite_add_test(suite, "tcp_write_capture", test_tcp_write_capture);
  valk_testsuite_add_test(suite, "loop_alive", test_loop_alive);
  valk_testsuite_add_test(suite, "close", test_close);
  valk_testsuite_add_test(suite, "timer_count", test_timer_count);
  
  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  
  return result;
}
