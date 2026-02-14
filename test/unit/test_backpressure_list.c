#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/http2/overload/aio_overload_backpressure.h"
#include "../../src/aio/aio_internal.h"
#include "../../src/aio/aio_ops.h"

#include <stdlib.h>

static valk_aio_handle_t *create_test_conn(void) {
  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.backpressure = false;
  conn->http.backpressure_next = nullptr;
  conn->http.backpressure_start_time = 0;
  conn->http.state = VALK_CONN_ESTABLISHED;
  return conn;
}

static void free_test_conn(valk_aio_handle_t *conn) {
  free(conn);
}

static valk_aio_system_t *create_test_system(void) {
  valk_aio_system_t *sys = calloc(1, sizeof(valk_aio_system_t));
  sys->ops = &valk_aio_ops_test;
  return sys;
}

static void free_test_system(valk_aio_system_t *sys) {
  free(sys);
}

void test_init_null_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_init(nullptr, 100, 5000);
  VALK_PASS();
}

void test_init_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  ASSERT_NULL(list.head);
  ASSERT_EQ(list.size, 0);
  ASSERT_EQ(list.max_size, 100);
  ASSERT_EQ(list.timeout_ms, 5000);

  VALK_PASS();
}

void test_init_zero_values(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 0, 0);

  ASSERT_NULL(list.head);
  ASSERT_EQ(list.size, 0);
  ASSERT_EQ(list.max_size, 0);
  ASSERT_EQ(list.timeout_ms, 0);

  VALK_PASS();
}

void test_add_null_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  bool added = valk_backpressure_list_add(nullptr, conn, 1000);
  ASSERT_FALSE(added);
  free_test_conn(conn);
  VALK_PASS();
}

void test_add_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  bool added = valk_backpressure_list_add(&list, nullptr, 1000);
  ASSERT_FALSE(added);
  VALK_PASS();
}

void test_add_single_connection(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_aio_handle_t *conn = create_test_conn();

  bool added = valk_backpressure_list_add(&list, conn, 1000);

  ASSERT_TRUE(added);
  ASSERT_EQ(list.size, 1);
  ASSERT_EQ(list.head, conn);
  ASSERT_TRUE(conn->http.backpressure);
  ASSERT_EQ(conn->http.backpressure_start_time, 1000);
  ASSERT_NULL(conn->http.backpressure_next);

  free_test_conn(conn);
  VALK_PASS();
}

void test_add_multiple_connections(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_handle_t *conn3 = create_test_conn();

  valk_backpressure_list_add(&list, conn1, 1000);
  valk_backpressure_list_add(&list, conn2, 2000);
  valk_backpressure_list_add(&list, conn3, 3000);

  ASSERT_EQ(list.size, 3);
  ASSERT_EQ(list.head, conn3);
  ASSERT_EQ(conn3->http.backpressure_next, conn2);
  ASSERT_EQ(conn2->http.backpressure_next, conn1);
  ASSERT_NULL(conn1->http.backpressure_next);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_conn(conn3);
  VALK_PASS();
}

void test_add_already_backpressured(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_aio_handle_t *conn = create_test_conn();

  bool added1 = valk_backpressure_list_add(&list, conn, 1000);
  ASSERT_TRUE(added1);
  ASSERT_EQ(list.size, 1);

  bool added2 = valk_backpressure_list_add(&list, conn, 2000);
  ASSERT_TRUE(added2);
  ASSERT_EQ(list.size, 1);
  ASSERT_EQ(conn->http.backpressure_start_time, 1000);

  free_test_conn(conn);
  VALK_PASS();
}

void test_add_queue_full(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 2, 5000);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_handle_t *conn3 = create_test_conn();

  ASSERT_TRUE(valk_backpressure_list_add(&list, conn1, 1000));
  ASSERT_TRUE(valk_backpressure_list_add(&list, conn2, 2000));
  ASSERT_FALSE(valk_backpressure_list_add(&list, conn3, 3000));

  ASSERT_EQ(list.size, 2);
  ASSERT_FALSE(conn3->http.backpressure);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_conn(conn3);
  VALK_PASS();
}

void test_remove_null_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *conn = create_test_conn();
  valk_backpressure_list_remove(nullptr, conn);
  free_test_conn(conn);
  VALK_PASS();
}

void test_remove_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_backpressure_list_remove(&list, nullptr);
  VALK_PASS();
}

void test_remove_not_backpressured(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_aio_handle_t *conn = create_test_conn();
  conn->http.backpressure = false;

  valk_backpressure_list_remove(&list, conn);

  ASSERT_EQ(list.size, 0);
  ASSERT_FALSE(conn->http.backpressure);

  free_test_conn(conn);
  VALK_PASS();
}

void test_remove_single_connection(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_aio_handle_t *conn = create_test_conn();

  valk_backpressure_list_add(&list, conn, 1000);
  ASSERT_EQ(list.size, 1);

  valk_backpressure_list_remove(&list, conn);

  ASSERT_EQ(list.size, 0);
  ASSERT_NULL(list.head);
  ASSERT_FALSE(conn->http.backpressure);
  ASSERT_NULL(conn->http.backpressure_next);

  free_test_conn(conn);
  VALK_PASS();
}

void test_remove_head_of_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_handle_t *conn3 = create_test_conn();

  valk_backpressure_list_add(&list, conn1, 1000);
  valk_backpressure_list_add(&list, conn2, 2000);
  valk_backpressure_list_add(&list, conn3, 3000);

  valk_backpressure_list_remove(&list, conn3);

  ASSERT_EQ(list.size, 2);
  ASSERT_EQ(list.head, conn2);
  ASSERT_FALSE(conn3->http.backpressure);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_conn(conn3);
  VALK_PASS();
}

void test_remove_middle_of_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_handle_t *conn3 = create_test_conn();

  valk_backpressure_list_add(&list, conn1, 1000);
  valk_backpressure_list_add(&list, conn2, 2000);
  valk_backpressure_list_add(&list, conn3, 3000);

  valk_backpressure_list_remove(&list, conn2);

  ASSERT_EQ(list.size, 2);
  ASSERT_EQ(list.head, conn3);
  ASSERT_EQ(conn3->http.backpressure_next, conn1);
  ASSERT_FALSE(conn2->http.backpressure);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_conn(conn3);
  VALK_PASS();
}

void test_remove_tail_of_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_handle_t *conn3 = create_test_conn();

  valk_backpressure_list_add(&list, conn1, 1000);
  valk_backpressure_list_add(&list, conn2, 2000);
  valk_backpressure_list_add(&list, conn3, 3000);

  valk_backpressure_list_remove(&list, conn1);

  ASSERT_EQ(list.size, 2);
  ASSERT_EQ(list.head, conn3);
  ASSERT_EQ(conn3->http.backpressure_next, conn2);
  ASSERT_NULL(conn2->http.backpressure_next);
  ASSERT_FALSE(conn1->http.backpressure);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_conn(conn3);
  VALK_PASS();
}

void test_try_resume_null_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_slab_t *slab = valk_slab_new(64, 10);
  valk_aio_handle_t *result = valk_backpressure_list_try_resume(nullptr, slab, 4);
  ASSERT_NULL(result);
  valk_slab_free(slab);
  VALK_PASS();
}

void test_try_resume_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_slab_t *slab = valk_slab_new(64, 10);

  valk_aio_handle_t *result = valk_backpressure_list_try_resume(&list, slab, 4);
  ASSERT_NULL(result);

  valk_slab_free(slab);
  VALK_PASS();
}

void test_try_resume_null_slab(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_aio_handle_t *conn = create_test_conn();
  valk_backpressure_list_add(&list, conn, 1000);

  valk_aio_handle_t *result = valk_backpressure_list_try_resume(&list, nullptr, 4);
  ASSERT_NULL(result);

  free_test_conn(conn);
  VALK_PASS();
}

void test_try_resume_insufficient_buffers(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_slab_t *slab = valk_slab_new(64, 10);

  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  conn->sys = sys;
  valk_backpressure_list_add(&list, conn, 1000);

  for (int i = 0; i < 10; i++) {
    valk_slab_aquire(slab);
  }
  ASSERT_EQ(valk_slab_available(slab), 0);

  valk_aio_handle_t *result = valk_backpressure_list_try_resume(&list, slab, 4);
  ASSERT_NULL(result);

  ASSERT_EQ(list.size, 1);

  free_test_conn(conn);
  free_test_system(sys);
  valk_slab_free(slab);
  VALK_PASS();
}

void test_try_resume_sufficient_buffers(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_slab_t *slab = valk_slab_new(64, 10);

  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  conn->sys = sys;
  valk_backpressure_list_add(&list, conn, 1000);

  valk_aio_handle_t *result = valk_backpressure_list_try_resume(&list, slab, 4);

  ASSERT_EQ(result, conn);
  ASSERT_EQ(list.size, 0);
  ASSERT_NULL(list.head);
  ASSERT_FALSE(conn->http.backpressure);

  free_test_conn(conn);
  free_test_system(sys);
  valk_slab_free(slab);
  VALK_PASS();
}

void test_try_resume_skips_closing_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_slab_t *slab = valk_slab_new(64, 10);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  conn1->sys = sys;
  conn2->sys = sys;

  valk_backpressure_list_add(&list, conn2, 1000);
  valk_backpressure_list_add(&list, conn1, 2000);

  conn1->http.state = VALK_CONN_CLOSING;

  valk_aio_handle_t *result = valk_backpressure_list_try_resume(&list, slab, 4);

  ASSERT_EQ(result, conn2);
  ASSERT_EQ(list.size, 0);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_system(sys);
  valk_slab_free(slab);
  VALK_PASS();
}

void test_try_resume_skips_closed_conn(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_slab_t *slab = valk_slab_new(64, 10);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  conn1->sys = sys;
  conn2->sys = sys;

  valk_backpressure_list_add(&list, conn2, 1000);
  valk_backpressure_list_add(&list, conn1, 2000);

  conn1->http.state = VALK_CONN_CLOSED;

  valk_aio_handle_t *result = valk_backpressure_list_try_resume(&list, slab, 4);

  ASSERT_EQ(result, conn2);
  ASSERT_EQ(list.size, 0);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_system(sys);
  valk_slab_free(slab);
  VALK_PASS();
}

void test_try_resume_all_closing(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_slab_t *slab = valk_slab_new(64, 10);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  conn1->sys = sys;
  conn2->sys = sys;

  valk_backpressure_list_add(&list, conn2, 1000);
  valk_backpressure_list_add(&list, conn1, 2000);

  conn1->http.state = VALK_CONN_CLOSING;
  conn2->http.state = VALK_CONN_CLOSED;

  valk_aio_handle_t *result = valk_backpressure_list_try_resume(&list, slab, 4);

  ASSERT_NULL(result);
  ASSERT_EQ(list.size, 0);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_system(sys);
  valk_slab_free(slab);
  VALK_PASS();
}

void test_try_resume_zero_min_buffers(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_slab_t *slab = valk_slab_new(64, 10);

  valk_aio_handle_t *conn = create_test_conn();
  valk_aio_system_t *sys = create_test_system();
  conn->sys = sys;
  valk_backpressure_list_add(&list, conn, 1000);

  valk_aio_handle_t *result = valk_backpressure_list_try_resume(&list, slab, 0);

  ASSERT_EQ(result, conn);
  ASSERT_EQ(list.size, 0);

  free_test_conn(conn);
  free_test_system(sys);
  valk_slab_free(slab);
  VALK_PASS();
}

void test_timeout_expired_null_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_handle_t *expired[10];
  u64 count = valk_backpressure_list_timeout_expired(nullptr, 10000, expired, 10);
  ASSERT_EQ(count, 0);
  VALK_PASS();
}

void test_timeout_expired_null_out_array(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_aio_handle_t *conn = create_test_conn();
  valk_backpressure_list_add(&list, conn, 1000);

  u64 count = valk_backpressure_list_timeout_expired(&list, 10000, nullptr, 10);
  ASSERT_EQ(count, 0);

  free_test_conn(conn);
  VALK_PASS();
}

void test_timeout_expired_zero_max(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);
  valk_aio_handle_t *conn = create_test_conn();
  valk_backpressure_list_add(&list, conn, 1000);

  valk_aio_handle_t *expired[10];
  u64 count = valk_backpressure_list_timeout_expired(&list, 10000, expired, 0);
  ASSERT_EQ(count, 0);

  free_test_conn(conn);
  VALK_PASS();
}

void test_timeout_expired_zero_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 0);
  valk_aio_handle_t *conn = create_test_conn();
  valk_backpressure_list_add(&list, conn, 1000);

  valk_aio_handle_t *expired[10];
  u64 count = valk_backpressure_list_timeout_expired(&list, 10000, expired, 10);
  ASSERT_EQ(count, 0);

  free_test_conn(conn);
  VALK_PASS();
}

void test_timeout_expired_none_expired(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  valk_backpressure_list_add(&list, conn, 1000);

  valk_aio_handle_t *expired[10];
  u64 count = valk_backpressure_list_timeout_expired(&list, 2000, expired, 10);

  ASSERT_EQ(count, 0);
  ASSERT_EQ(list.size, 1);

  free_test_conn(conn);
  VALK_PASS();
}

void test_timeout_expired_single_expired(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  valk_backpressure_list_add(&list, conn, 1000);

  valk_aio_handle_t *expired[10];
  u64 count = valk_backpressure_list_timeout_expired(&list, 10000, expired, 10);

  ASSERT_EQ(count, 1);
  ASSERT_EQ(expired[0], conn);
  ASSERT_EQ(list.size, 0);
  ASSERT_FALSE(conn->http.backpressure);

  free_test_conn(conn);
  VALK_PASS();
}

void test_timeout_expired_multiple_expired(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_handle_t *conn3 = create_test_conn();

  valk_backpressure_list_add(&list, conn1, 1000);
  valk_backpressure_list_add(&list, conn2, 2000);
  valk_backpressure_list_add(&list, conn3, 3000);

  valk_aio_handle_t *expired[10];
  u64 count = valk_backpressure_list_timeout_expired(&list, 20000, expired, 10);

  ASSERT_EQ(count, 3);
  ASSERT_EQ(list.size, 0);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_conn(conn3);
  VALK_PASS();
}

void test_timeout_expired_partial(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_handle_t *conn3 = create_test_conn();

  valk_backpressure_list_add(&list, conn1, 10000);
  valk_backpressure_list_add(&list, conn2, 2000);
  valk_backpressure_list_add(&list, conn3, 1000);

  valk_aio_handle_t *expired[10];
  u64 count = valk_backpressure_list_timeout_expired(&list, 10000, expired, 10);

  ASSERT_EQ(count, 2);
  ASSERT_EQ(list.size, 1);
  ASSERT_TRUE(conn1->http.backpressure);
  ASSERT_FALSE(conn2->http.backpressure);
  ASSERT_FALSE(conn3->http.backpressure);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_conn(conn3);
  VALK_PASS();
}

void test_timeout_expired_max_limit(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn1 = create_test_conn();
  valk_aio_handle_t *conn2 = create_test_conn();
  valk_aio_handle_t *conn3 = create_test_conn();

  valk_backpressure_list_add(&list, conn1, 1000);
  valk_backpressure_list_add(&list, conn2, 2000);
  valk_backpressure_list_add(&list, conn3, 3000);

  valk_aio_handle_t *expired[2];
  u64 count = valk_backpressure_list_timeout_expired(&list, 20000, expired, 2);

  ASSERT_EQ(count, 2);
  ASSERT_EQ(list.size, 1);

  free_test_conn(conn1);
  free_test_conn(conn2);
  free_test_conn(conn3);
  VALK_PASS();
}

void test_timeout_expired_zero_start_time(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_backpressure_list_t list;
  valk_backpressure_list_init(&list, 100, 5000);

  valk_aio_handle_t *conn = create_test_conn();
  valk_backpressure_list_add(&list, conn, 0);
  conn->http.backpressure_start_time = 0;

  valk_aio_handle_t *expired[10];
  u64 count = valk_backpressure_list_timeout_expired(&list, 10000, expired, 10);

  ASSERT_EQ(count, 0);
  ASSERT_EQ(list.size, 1);

  free_test_conn(conn);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_init_null_list", test_init_null_list);
  valk_testsuite_add_test(suite, "test_init_basic", test_init_basic);
  valk_testsuite_add_test(suite, "test_init_zero_values", test_init_zero_values);

  valk_testsuite_add_test(suite, "test_add_null_list", test_add_null_list);
  valk_testsuite_add_test(suite, "test_add_null_conn", test_add_null_conn);
  valk_testsuite_add_test(suite, "test_add_single_connection", test_add_single_connection);
  valk_testsuite_add_test(suite, "test_add_multiple_connections", test_add_multiple_connections);
  valk_testsuite_add_test(suite, "test_add_already_backpressured", test_add_already_backpressured);
  valk_testsuite_add_test(suite, "test_add_queue_full", test_add_queue_full);

  valk_testsuite_add_test(suite, "test_remove_null_list", test_remove_null_list);
  valk_testsuite_add_test(suite, "test_remove_null_conn", test_remove_null_conn);
  valk_testsuite_add_test(suite, "test_remove_not_backpressured", test_remove_not_backpressured);
  valk_testsuite_add_test(suite, "test_remove_single_connection", test_remove_single_connection);
  valk_testsuite_add_test(suite, "test_remove_head_of_list", test_remove_head_of_list);
  valk_testsuite_add_test(suite, "test_remove_middle_of_list", test_remove_middle_of_list);
  valk_testsuite_add_test(suite, "test_remove_tail_of_list", test_remove_tail_of_list);

  valk_testsuite_add_test(suite, "test_try_resume_null_list", test_try_resume_null_list);
  valk_testsuite_add_test(suite, "test_try_resume_empty_list", test_try_resume_empty_list);
  valk_testsuite_add_test(suite, "test_try_resume_null_slab", test_try_resume_null_slab);
  valk_testsuite_add_test(suite, "test_try_resume_insufficient_buffers", test_try_resume_insufficient_buffers);
  valk_testsuite_add_test(suite, "test_try_resume_sufficient_buffers", test_try_resume_sufficient_buffers);
  valk_testsuite_add_test(suite, "test_try_resume_skips_closing_conn", test_try_resume_skips_closing_conn);
  valk_testsuite_add_test(suite, "test_try_resume_skips_closed_conn", test_try_resume_skips_closed_conn);
  valk_testsuite_add_test(suite, "test_try_resume_all_closing", test_try_resume_all_closing);
  valk_testsuite_add_test(suite, "test_try_resume_zero_min_buffers", test_try_resume_zero_min_buffers);

  valk_testsuite_add_test(suite, "test_timeout_expired_null_list", test_timeout_expired_null_list);
  valk_testsuite_add_test(suite, "test_timeout_expired_null_out_array", test_timeout_expired_null_out_array);
  valk_testsuite_add_test(suite, "test_timeout_expired_zero_max", test_timeout_expired_zero_max);
  valk_testsuite_add_test(suite, "test_timeout_expired_zero_timeout", test_timeout_expired_zero_timeout);
  valk_testsuite_add_test(suite, "test_timeout_expired_none_expired", test_timeout_expired_none_expired);
  valk_testsuite_add_test(suite, "test_timeout_expired_single_expired", test_timeout_expired_single_expired);
  valk_testsuite_add_test(suite, "test_timeout_expired_multiple_expired", test_timeout_expired_multiple_expired);
  valk_testsuite_add_test(suite, "test_timeout_expired_partial", test_timeout_expired_partial);
  valk_testsuite_add_test(suite, "test_timeout_expired_max_limit", test_timeout_expired_max_limit);
  valk_testsuite_add_test(suite, "test_timeout_expired_zero_start_time", test_timeout_expired_zero_start_time);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
