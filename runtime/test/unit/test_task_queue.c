#include "testing.h"
#include "../../src/memory.h"
#include "../../src/aio/aio_internal.h"

#include <uv.h>

static _Atomic int g_task_executed = 0;
static _Atomic int g_task_ctx_value = 0;

static void simple_task(void *ctx) {
  (void)ctx;
  atomic_fetch_add(&g_task_executed, 1);
}

static void task_with_context(void *ctx) {
  int *value = (int *)ctx;
  atomic_store(&g_task_ctx_value, *value);
  atomic_fetch_add(&g_task_executed, 1);
}

static void drain_loop(uv_loop_t *loop, valk_aio_system_t *sys) {
  uv_ref((uv_handle_t*)&sys->loops[0].task_queue.notify);
  uv_run(loop, UV_RUN_NOWAIT);
  uv_unref((uv_handle_t*)&sys->loops[0].task_queue.notify);
}

static void setup_sys_with_loop(valk_aio_system_t *sys, valk_aio_loop_t *loop, uv_loop_t *uv_loop) {
  memset(sys, 0, sizeof(*sys));
  memset(loop, 0, sizeof(*loop));
  sys->loops = loop;
  sys->num_loops = 1;
  sys->eventloop = uv_loop;
  loop->uv_loop = uv_loop;
  loop->sys = sys;
  loop->id = 0;
}

void test_task_queue_empty_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool empty = valk_aio_task_queue_empty(NULL);
  ASSERT_TRUE(empty);

  VALK_PASS();
}

void test_task_queue_size_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  i64 size = valk_aio_task_queue_size(NULL);
  ASSERT_EQ(size, 0);

  VALK_PASS();
}

void test_task_queue_enqueue_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_enqueue_task(NULL, simple_task, NULL);

  VALK_PASS();
}

void test_task_queue_enqueue_null_fn(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys = {0};
  valk_aio_enqueue_task(&sys, NULL, NULL);

  VALK_PASS();
}

void test_task_queue_init_shutdown(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);

  valk_aio_task_queue_init(&sys);
  ASSERT_TRUE(sys.loops[0].task_queue.initialized);
  ASSERT_TRUE(valk_aio_task_queue_empty(&sys));
  ASSERT_EQ(valk_aio_task_queue_size(&sys), 0);

  valk_aio_task_queue_shutdown(&sys);
  ASSERT_FALSE(sys.loops[0].task_queue.initialized);

  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_double_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);

  valk_aio_task_queue_init(&sys);
  ASSERT_TRUE(sys.loops[0].task_queue.initialized);

  valk_aio_task_queue_init(&sys);
  ASSERT_TRUE(sys.loops[0].task_queue.initialized);

  valk_aio_task_queue_shutdown(&sys);

  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_shutdown_not_initialized(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  uv_loop_t loop;
  uv_loop_init(&loop);
  setup_sys_with_loop(&sys, &aio_loop, &loop);
  sys.loops[0].task_queue.initialized = false;

  valk_aio_task_queue_shutdown(&sys);

  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_enqueue_single(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);

  valk_aio_task_queue_init(&sys);

  atomic_store(&g_task_executed, 0);
  valk_aio_enqueue_task(&sys, simple_task, NULL);

  ASSERT_FALSE(valk_aio_task_queue_empty(&sys));
  ASSERT_EQ(valk_aio_task_queue_size(&sys), 1);

  drain_loop(&loop, &sys);

  ASSERT_EQ(atomic_load(&g_task_executed), 1);
  ASSERT_TRUE(valk_aio_task_queue_empty(&sys));

  valk_aio_task_queue_shutdown(&sys);
  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_enqueue_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);

  valk_aio_task_queue_init(&sys);

  atomic_store(&g_task_executed, 0);

  for (int i = 0; i < 10; i++) {
    valk_aio_enqueue_task(&sys, simple_task, NULL);
  }

  ASSERT_EQ(valk_aio_task_queue_size(&sys), 10);

  drain_loop(&loop, &sys);

  ASSERT_EQ(atomic_load(&g_task_executed), 10);
  ASSERT_TRUE(valk_aio_task_queue_empty(&sys));

  valk_aio_task_queue_shutdown(&sys);
  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_with_context(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);

  valk_aio_task_queue_init(&sys);

  atomic_store(&g_task_executed, 0);
  atomic_store(&g_task_ctx_value, 0);

  int ctx_value = 42;
  valk_aio_enqueue_task(&sys, task_with_context, &ctx_value);

  drain_loop(&loop, &sys);

  ASSERT_EQ(atomic_load(&g_task_executed), 1);
  ASSERT_EQ(atomic_load(&g_task_ctx_value), 42);

  valk_aio_task_queue_shutdown(&sys);
  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_shutdown_drains(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);

  valk_aio_task_queue_init(&sys);

  for (int i = 0; i < 5; i++) {
    valk_aio_enqueue_task(&sys, simple_task, NULL);
  }

  ASSERT_EQ(valk_aio_task_queue_size(&sys), 5);

  valk_aio_task_queue_shutdown(&sys);

  ASSERT_FALSE(sys.loops[0].task_queue.initialized);

  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_shuttingdown_flag(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);
  sys.shuttingDown = false;

  valk_aio_task_queue_init(&sys);

  atomic_store(&g_task_executed, 0);
  valk_aio_enqueue_task(&sys, simple_task, NULL);

  sys.shuttingDown = true;

  drain_loop(&loop, &sys);

  ASSERT_EQ(atomic_load(&g_task_executed), 0);

  sys.shuttingDown = false;
  drain_loop(&loop, &sys);

  ASSERT_EQ(atomic_load(&g_task_executed), 1);

  valk_aio_task_queue_shutdown(&sys);
  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_loop_enqueue_null_loop(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool ok = valk_aio_loop_enqueue_task(NULL, simple_task, NULL);
  ASSERT_FALSE(ok);

  VALK_PASS();
}

void test_task_queue_loop_enqueue_null_fn(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);
  valk_aio_task_queue_init(&sys);

  bool ok = valk_aio_loop_enqueue_task(&aio_loop, NULL, NULL);
  ASSERT_FALSE(ok);

  valk_aio_task_queue_shutdown(&sys);
  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_empty_null_loops(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t sys;
  memset(&sys, 0, sizeof(sys));
  sys.loops = NULL;
  ASSERT_TRUE(valk_aio_task_queue_empty(&sys));
  ASSERT_EQ(valk_aio_task_queue_size(&sys), 0);

  VALK_PASS();
}

static _Atomic int g_task_dropped = 0;

static void drop_task(void *ctx) {
  (void)ctx;
  atomic_fetch_add(&g_task_dropped, 1);
}

void test_task_queue_destroy_uninitialized(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_loop_t aio_loop;
  memset(&aio_loop, 0, sizeof(aio_loop));
  valk_aio_loop_task_queue_destroy(&aio_loop);

  VALK_PASS();
}

void test_task_queue_drop_on_shutdown(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);

  valk_aio_task_queue_init(&sys);

  atomic_store(&g_task_executed, 0);
  atomic_store(&g_task_dropped, 0);
  ASSERT_TRUE(valk_aio_loop_enqueue_task_owned(&aio_loop, simple_task, NULL, drop_task));
  ASSERT_TRUE(valk_aio_loop_enqueue_task_owned(&aio_loop, simple_task, NULL, NULL));

  valk_aio_task_queue_shutdown(&sys);

  ASSERT_EQ(atomic_load(&g_task_executed), 0);
  ASSERT_EQ(atomic_load(&g_task_dropped), 1);

  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_enqueue_while_shutting_down(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);

  valk_aio_task_queue_init(&sys);
  sys.shuttingDown = true;

  atomic_store(&g_task_dropped, 0);
  ASSERT_FALSE(valk_aio_loop_enqueue_task_owned(&aio_loop, simple_task, NULL, drop_task));
  ASSERT_EQ(atomic_load(&g_task_dropped), 1);
  ASSERT_FALSE(valk_aio_loop_enqueue_task_owned(&aio_loop, simple_task, NULL, NULL));
  ASSERT_TRUE(valk_aio_task_queue_empty(&sys));

  sys.shuttingDown = false;
  valk_aio_task_queue_shutdown(&sys);
  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_enqueue_loop_without_sys(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);
  valk_aio_task_queue_init(&sys);

  aio_loop.sys = NULL;
  atomic_store(&g_task_executed, 0);
  ASSERT_TRUE(valk_aio_loop_enqueue_task(&aio_loop, simple_task, NULL));
  aio_loop.sys = &sys;

  drain_loop(&loop, &sys);
  ASSERT_EQ(atomic_load(&g_task_executed), 1);

  valk_aio_task_queue_shutdown(&sys);
  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_task_queue_batch_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_aio_system_t sys;
  valk_aio_loop_t aio_loop;
  setup_sys_with_loop(&sys, &aio_loop, &loop);
  valk_aio_task_queue_init(&sys);

  atomic_store(&g_task_executed, 0);
  const int total = 600;
  for (int i = 0; i < total; i++) {
    ASSERT_TRUE(valk_aio_loop_enqueue_task(&aio_loop, simple_task, NULL));
  }

  int spins = 0;
  while (atomic_load(&g_task_executed) < total && spins < 20) {
    drain_loop(&loop, &sys);
    spins++;
  }
  ASSERT_EQ(atomic_load(&g_task_executed), total);

  valk_aio_task_queue_shutdown(&sys);
  uv_run(&loop, UV_RUN_DEFAULT);
  valk_aio_loop_task_queue_destroy(&sys.loops[0]);
  uv_loop_close(&loop);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_task_queue_empty_null", test_task_queue_empty_null);
  valk_testsuite_add_test(suite, "test_task_queue_size_null", test_task_queue_size_null);
  valk_testsuite_add_test(suite, "test_task_queue_enqueue_null_sys", test_task_queue_enqueue_null_sys);
  valk_testsuite_add_test(suite, "test_task_queue_enqueue_null_fn", test_task_queue_enqueue_null_fn);
  valk_testsuite_add_test(suite, "test_task_queue_init_shutdown", test_task_queue_init_shutdown);
  valk_testsuite_add_test(suite, "test_task_queue_double_init", test_task_queue_double_init);
  valk_testsuite_add_test(suite, "test_task_queue_shutdown_not_initialized", test_task_queue_shutdown_not_initialized);
  valk_testsuite_add_test(suite, "test_task_queue_enqueue_single", test_task_queue_enqueue_single);
  valk_testsuite_add_test(suite, "test_task_queue_enqueue_multiple", test_task_queue_enqueue_multiple);
  valk_testsuite_add_test(suite, "test_task_queue_with_context", test_task_queue_with_context);
  valk_testsuite_add_test(suite, "test_task_queue_shutdown_drains", test_task_queue_shutdown_drains);
  valk_testsuite_add_test(suite, "test_task_queue_shuttingdown_flag", test_task_queue_shuttingdown_flag);
  valk_testsuite_add_test(suite, "test_task_queue_loop_enqueue_null_loop", test_task_queue_loop_enqueue_null_loop);
  valk_testsuite_add_test(suite, "test_task_queue_loop_enqueue_null_fn", test_task_queue_loop_enqueue_null_fn);
  valk_testsuite_add_test(suite, "test_task_queue_empty_null_loops", test_task_queue_empty_null_loops);
  valk_testsuite_add_test(suite, "test_task_queue_destroy_uninitialized", test_task_queue_destroy_uninitialized);
  valk_testsuite_add_test(suite, "test_task_queue_drop_on_shutdown", test_task_queue_drop_on_shutdown);
  valk_testsuite_add_test(suite, "test_task_queue_enqueue_while_shutting_down", test_task_queue_enqueue_while_shutting_down);
  valk_testsuite_add_test(suite, "test_task_queue_enqueue_loop_without_sys", test_task_queue_enqueue_loop_without_sys);
  valk_testsuite_add_test(suite, "test_task_queue_batch_limit", test_task_queue_batch_limit);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
