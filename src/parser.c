#include "parser.h"

#include <stdatomic.h>

#include "aio/aio.h"
#include "aio/aio_diagnostics_builtins.h"
#include "aio/aio_metrics.h"
#include "aio/http2/stream/aio_stream_body.h"
#include "builtins_internal.h"
#include "common.h"
#include "metrics_delta.h"
#include "metrics_v2.h"

void valk_register_metrics_builtins(valk_lenv_t *env);
void valk_register_ctx_builtins(valk_lenv_t *env);
void valk_register_coverage_builtins(valk_lenv_t *env);
void valk_register_test_builtins(valk_lenv_t *env);

u64 __valk_lval_size = sizeof(valk_lval_t);
u64 __valk_lenv_size = sizeof(valk_lenv_t);

valk_eval_metrics_t g_eval_metrics = {0};

void valk_eval_metrics_init(void) {
  atomic_store(&g_eval_metrics.evals_total, 0);
  atomic_store(&g_eval_metrics.function_calls, 0);
  atomic_store(&g_eval_metrics.builtin_calls, 0);
  atomic_store(&g_eval_metrics.stack_depth, 0);
  g_eval_metrics.stack_depth_max = 0;
  atomic_store(&g_eval_metrics.closures_created, 0);
  atomic_store(&g_eval_metrics.env_lookups, 0);
}

void valk_eval_metrics_get(u64* evals, u64* func_calls,
                            u64* builtin_calls, u32* stack_max,
                            u64* closures, u64* lookups) {
  if (evals) *evals = atomic_load(&g_eval_metrics.evals_total);
  if (func_calls) *func_calls = atomic_load(&g_eval_metrics.function_calls);
  if (builtin_calls) *builtin_calls = atomic_load(&g_eval_metrics.builtin_calls);
  if (stack_max) *stack_max = g_eval_metrics.stack_depth_max;
  if (closures) *closures = atomic_load(&g_eval_metrics.closures_created);
  if (lookups) *lookups = atomic_load(&g_eval_metrics.env_lookups);
}

void valk_lenv_builtins(valk_lenv_t* env) {
  valk_register_io_builtins(env);
  valk_register_string_builtins(env);
  valk_register_mem_builtins(env);
  valk_register_list_builtins(env);
  valk_register_math_builtins(env);
  valk_register_env_builtins(env);
  valk_register_http_builtins(env);
  valk_register_aio_builtins(env);
  valk_register_server_builtins(env);

  valk_register_async_handle_builtins(env);
  valk_register_http_request_builtins(env);
  valk_register_stream_builtins(env);
  valk_register_metrics_builtins(env);
  valk_register_aio_diagnostics_builtins(env);
  valk_register_ctx_builtins(env);
  valk_register_coverage_builtins(env);
  valk_register_test_builtins(env);
  valk_register_json_builtins(env);
  valk_register_stdio_builtins(env);
  valk_register_sqlite_builtins(env);
}
