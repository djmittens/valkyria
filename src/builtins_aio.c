#include "builtins_internal.h"

#include <stdlib.h>
#include <string.h>
#include <uv.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/aio_internal.h"
#include "aio/aio_metrics.h"
#include "gc.h"
#include "metrics_delta.h"
#include "metrics_v2.h"

static valk_lval_t* valk_builtin_aio_start(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  int argc = valk_lval_list_count(a);
  LVAL_ASSERT(a, argc == 0 || argc == 1, "Expected 0 or 1 arguments");

  valk_aio_system_t* sys;
  valk_aio_system_config_t config = valk_aio_system_config_default();

  if (valk_runtime_is_initialized()) { // LCOV_EXCL_BR_LINE - runtime init state
    config.thread_onboard_fn = valk_runtime_get_onboard_fn();
  }

  // LCOV_EXCL_BR_START - config parsing: optional keys may be absent or wrong type
  if (argc >= 1 && LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_QEXPR) {
    valk_lval_t* config_map = valk_lval_list_nth(a, 0);

    valk_lval_t* val;

    if ((val = valk_plist_get(config_map, ":max-connections")) && LVAL_TYPE(val) == LVAL_NUM)
      config.max_connections = (u32)val->num;

    if ((val = valk_plist_get(config_map, ":max-concurrent-streams")) && LVAL_TYPE(val) == LVAL_NUM)
      config.max_concurrent_streams = (u32)val->num;

    if ((val = valk_plist_get(config_map, ":tcp-buffer-pool-size")) && LVAL_TYPE(val) == LVAL_NUM)
      config.tcp_buffer_pool_size = (u32)val->num;

    if ((val = valk_plist_get(config_map, ":arena-pool-size")) && LVAL_TYPE(val) == LVAL_NUM)
      config.arena_pool_size = (u32)val->num;

    if ((val = valk_plist_get(config_map, ":arena-size")) && LVAL_TYPE(val) == LVAL_NUM)
      config.arena_size = (u64)val->num;

    if ((val = valk_plist_get(config_map, ":max-request-body-size")) && LVAL_TYPE(val) == LVAL_NUM)
      config.max_request_body_size = (u64)val->num;

    if ((val = valk_plist_get(config_map, ":backpressure-timeout-ms")) && LVAL_TYPE(val) == LVAL_NUM)
      config.backpressure_timeout_ms = (u32)val->num;

    if ((val = valk_plist_get(config_map, ":backpressure-list-max")) && LVAL_TYPE(val) == LVAL_NUM)
      config.backpressure_list_max = (u32)val->num;
  }
  // LCOV_EXCL_BR_STOP

  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    sys = valk_aio_start_with_config(&config);
  }

  if (!sys) { // LCOV_EXCL_BR_LINE - OOM: aio system allocation failure
    return valk_lval_err("Failed to start AIO system");
  }

  valk_lval_t* ref;
  VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
    ref = valk_lval_ref("aio_system", sys, NULL);
  }

  valk_async_handle_t* startup_handle = valk_async_handle_new(sys, e);
  if (!startup_handle) { // LCOV_EXCL_BR_LINE - OOM: handle allocation failure
    return valk_lval_err("Failed to allocate startup handle");
  }
  valk_async_handle_complete(startup_handle, ref);

  return valk_lval_handle(startup_handle);
}

static valk_lval_t* valk_builtin_aio_run(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, aio_ref);

  valk_aio_system_t* sys = (valk_aio_system_t*)aio_ref->ref.ptr;

  while (!valk_aio_is_shutting_down(sys)) { // LCOV_EXCL_BR_LINE - run loop exit condition
    VALK_GC_SAFE_POINT();
    uv_sleep(100);
  }

  if (!sys->threadJoined &&
      !valk_thread_equal(valk_thread_self(), (valk_thread_t)sys->loopThread)) {
    uv_thread_join(&sys->loopThread);
    sys->threadJoined = true;
  }

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_aio_stop(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, aio_ref);

  valk_aio_system_t* sys = (valk_aio_system_t*)aio_ref->ref.ptr;
  valk_aio_stop(sys);
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_aio_on_loop_thread(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, aio_ref);
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t* sys = (valk_aio_system_t*)aio_ref->ref.ptr;
  bool on_loop = uv_thread_self() == sys->loopThread;
  return valk_lval_num(on_loop ? 1 : 0);
}

static valk_lval_t* valk_builtin_aio_metrics_json(valk_lenv_t* e,
                                                   valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, aio_ref);

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  valk_aio_update_queue_stats(sys);
  char* buf = valk_mem_alloc(131072);
  if (!buf) return valk_lval_err("Failed to allocate buffer for metrics JSON"); // LCOV_EXCL_BR_LINE - OOM
  u64 len = valk_metrics_v2_to_json(&g_metrics, buf, 131072);
  if (len == 0) { // LCOV_EXCL_BR_LINE - metrics serialization failure
    return valk_lval_err("Failed to generate metrics JSON");
  }
  return valk_lval_str(buf);
}

static valk_lval_t* valk_builtin_aio_metrics_json_compact(valk_lenv_t* e,
                                                            valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, aio_ref);

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  valk_aio_update_queue_stats(sys);
  char* buf = valk_mem_alloc(65536);
  if (!buf) return valk_lval_err("Failed to allocate buffer for metrics JSON"); // LCOV_EXCL_BR_LINE - OOM
  u64 len = valk_metrics_v2_to_json(&g_metrics, buf, 65536);
  if (len == 0) { // LCOV_EXCL_BR_LINE - metrics serialization failure
    return valk_lval_err("Failed to generate metrics JSON");
  }
  return valk_lval_str(buf);
}

static valk_lval_t* valk_builtin_aio_systems_json(valk_lenv_t* e,
                                                    valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, aio_ref);

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  valk_aio_update_queue_stats(sys);
  char* buf = valk_mem_alloc(131072);
  if (!buf) return valk_lval_err("Failed to allocate buffer for metrics JSON"); // LCOV_EXCL_BR_LINE - OOM
  u64 len = valk_metrics_v2_to_json(&g_metrics, buf, 131072);
  if (len == 0) { // LCOV_EXCL_BR_LINE - metrics serialization failure
    return valk_lval_err("Failed to generate metrics JSON");
  }
  
  char* result = valk_mem_alloc(len + 3);
  snprintf(result, len + 3, "[%s]", buf);
  return valk_lval_str(result);
}

// LCOV_EXCL_BR_START - arg validation and heap selection branches
static valk_lval_t* vm_metrics_extract_sys(valk_lval_t* a, const char* name,
                                            valk_aio_system_t **out_sys,
                                            valk_vm_metrics_t *out_vm) {
  *out_sys = NULL;
  u64 argc = valk_lval_list_count(a);

  if (argc > 1) {
    return valk_lval_err("%s: expected 0-1 arguments", name);
  }

  if (argc == 1) {
    valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
    LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);
    *out_sys = (valk_aio_system_t *)sys_arg->ref.ptr;
  }

  valk_aio_system_t *sys = *out_sys;
  valk_gc_malloc_heap_t* heap = sys && valk_aio_get_gc_heap(sys)
    ? valk_aio_get_gc_heap(sys)
    : (valk_gc_malloc_heap_t*)valk_thread_ctx.heap;
// LCOV_EXCL_BR_STOP

  valk_vm_metrics_collect(out_vm, heap, sys ? valk_aio_get_event_loop(sys) : NULL);
  return NULL;
}

static valk_lval_t* valk_builtin_vm_metrics_json(valk_lenv_t* e,
                                                  valk_lval_t* a) {
  UNUSED(e);
  valk_aio_system_t *sys;
  valk_vm_metrics_t vm;
  valk_lval_t *err = vm_metrics_extract_sys(a, "vm/metrics-json", &sys, &vm);
  if (err) return err;

  char* json = valk_vm_metrics_to_json(&vm, (valk_mem_allocator_t*)valk_thread_ctx.allocator);
  if (!json) { // LCOV_EXCL_BR_LINE - OOM
    return valk_lval_err("Failed to generate VM metrics JSON");
  }
  return valk_lval_str(json);
}

static valk_lval_t* valk_builtin_vm_metrics_prometheus(valk_lenv_t* e,
                                                         valk_lval_t* a) {
  UNUSED(e);
  valk_aio_system_t *sys;
  valk_vm_metrics_t vm;
  valk_lval_t *err = vm_metrics_extract_sys(a, "vm/metrics-prometheus", &sys, &vm);
  if (err) return err;

  char* prom = valk_vm_metrics_to_prometheus(&vm, (valk_mem_allocator_t*)valk_thread_ctx.allocator);
  if (!prom) { // LCOV_EXCL_BR_LINE - OOM
    return valk_lval_err("Failed to generate VM metrics Prometheus");
  }
  return valk_lval_str(prom);
}

static valk_lval_t* valk_builtin_vm_metrics_json_compact(valk_lenv_t* e,
                                                           valk_lval_t* a) {
  UNUSED(e);
  valk_aio_system_t *sys;
  valk_vm_metrics_t vm;
  valk_lval_t *err = vm_metrics_extract_sys(a, "vm/metrics-json-compact", &sys, &vm);
  if (err) return err;

  char* json = valk_vm_metrics_to_json_compact(&vm, (valk_mem_allocator_t*)valk_thread_ctx.allocator);
  if (!json) { // LCOV_EXCL_BR_LINE - OOM
    return valk_lval_err("Failed to generate compact VM metrics JSON");
  }
  return valk_lval_str(json);
}

static valk_lval_t* valk_builtin_aio_schedule(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg/type validation: compile-time checks catch most
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  valk_lval_t* delay_arg = valk_lval_list_nth(a, 1);
  valk_lval_t* callback = valk_lval_list_nth(a, 2);

  LVAL_ASSERT_AIO_SYSTEM(a, aio_ref);
  LVAL_ASSERT_TYPE(a, delay_arg, LVAL_NUM);
  LVAL_ASSERT_TYPE(a, callback, LVAL_FUN);
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  u64 delay_ms = (u64)delay_arg->num;

  return valk_aio_schedule(sys, delay_ms, callback, e);
}

static valk_lval_t* valk_builtin_aio_interval(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg/type validation: compile-time checks catch most
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  valk_lval_t* interval_arg = valk_lval_list_nth(a, 1);
  valk_lval_t* callback = valk_lval_list_nth(a, 2);

  LVAL_ASSERT_AIO_SYSTEM(a, aio_ref);
  LVAL_ASSERT_TYPE(a, interval_arg, LVAL_NUM);
  LVAL_ASSERT_TYPE(a, callback, LVAL_FUN);
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  u64 interval_ms = (u64)interval_arg->num;

  return valk_aio_interval(sys, interval_ms, callback, e);
}

// LCOV_EXCL_START - exit() terminates process, cannot be unit tested
static valk_lval_t* valk_builtin_exit(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  int code = (int)valk_lval_list_nth(a, 0)->num;
  fflush(stdout);
  fflush(stderr);
  exit(code);
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_shutdown(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_LE(a, a, 1);
  int code = 0;
  if (valk_lval_list_count(a) == 1) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
    code = (int)valk_lval_list_nth(a, 0)->num;
  }

  valk_lenv_def(e, valk_lval_sym("VALK_EXIT_CODE"), valk_lval_num(code));

  valk_lval_t* val = valk_lenv_get(e, valk_lval_sym("aio"));
  if (LVAL_TYPE(val) != LVAL_ERR && LVAL_TYPE(val) == LVAL_REF &&
      strcmp(val->ref.type, "aio_system") == 0 && val->ref.ptr) {
    valk_aio_stop((valk_aio_system_t*)val->ref.ptr);
  }

  return valk_lval_num(code);
}

void valk_register_aio_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "aio/start", valk_builtin_aio_start);
  valk_lenv_put_builtin(env, "aio/run", valk_builtin_aio_run);
  valk_lenv_put_builtin(env, "aio/stop", valk_builtin_aio_stop);
  valk_lenv_put_builtin(env, "aio/on-loop-thread?", valk_builtin_aio_on_loop_thread);
  valk_lenv_put_builtin(env, "aio/metrics-json", valk_builtin_aio_metrics_json);
  valk_lenv_put_builtin(env, "aio/metrics-json-compact",
                        valk_builtin_aio_metrics_json_compact);
  valk_lenv_put_builtin(env, "aio/systems-json", valk_builtin_aio_systems_json);
  valk_lenv_put_builtin(env, "aio/schedule", valk_builtin_aio_schedule);
  valk_lenv_put_builtin(env, "aio/interval", valk_builtin_aio_interval);
  valk_lenv_put_builtin(env, "vm/metrics-json", valk_builtin_vm_metrics_json);
  valk_lenv_put_builtin(env, "vm/metrics-json-compact",
                        valk_builtin_vm_metrics_json_compact);
  valk_lenv_put_builtin(env, "vm/metrics-prometheus",
                        valk_builtin_vm_metrics_prometheus);
  valk_lenv_put_builtin(env, "exit", valk_builtin_exit);
  valk_lenv_put_builtin(env, "shutdown", valk_builtin_shutdown);
}
