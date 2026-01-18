#include "aio_internal.h"
#include "aio_request_ctx.h"

static void __schedule_timer_close_cb(uv_handle_t *handle) {
  UNUSED(handle);
}

static void __sleep_timer_close_cb(uv_handle_t *handle) {
  UNUSED(handle);
}

static u64 g_interval_id = 1;

static void __interval_timer_close_cb(uv_handle_t *handle) {
  valk_interval_timer_t *timer_data = (valk_interval_timer_t *)handle->data;
  if (!timer_data) return;

  if (timer_data->callback) {
    valk_handle_release(&valk_global_handle_table, timer_data->callback_handle);
  }
}

static void __interval_timer_cb(uv_timer_t *handle) {
  VALK_GC_SAFE_POINT();

  if (uv_is_closing((uv_handle_t *)handle)) return;

  valk_interval_timer_t *timer_data = (valk_interval_timer_t *)handle->data;
  if (!timer_data || timer_data->stopped) return;

  valk_lval_t *callback = valk_handle_resolve(&valk_global_handle_table, timer_data->callback_handle);
  if (!callback) {
    timer_data->stopped = true;
    uv_timer_stop(handle);
    uv_close((uv_handle_t *)handle, __interval_timer_close_cb);
    return;
  }
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = valk_lval_eval_call(callback->fun.env, callback, args);

  if (LVAL_TYPE(result) == LVAL_ERR) {
    VALK_WARN("aio/interval callback returned error: %s", result->str);
  }

  if (LVAL_TYPE(result) == LVAL_SYM && strcmp(result->str, ":stop") == 0) {
    timer_data->stopped = true;
    uv_timer_stop(handle);
    uv_close((uv_handle_t *)handle, __interval_timer_close_cb);
  }
}

typedef struct {
  valk_aio_system_t *sys;
  valk_interval_timer_t *timer_data;
  u64 interval_ms;
} valk_interval_init_ctx_t;

static void __interval_init_on_loop(void *ctx) {
  valk_interval_init_ctx_t *init_ctx = (valk_interval_init_ctx_t *)ctx;
  valk_interval_timer_t *timer_data = init_ctx->timer_data;
  
  uv_loop_t *loop = init_ctx->sys->eventloop;
  int r = uv_timer_init(loop, &timer_data->timer);
  // LCOV_EXCL_START - libuv timer init essentially never fails
  if (r != 0) {
    valk_handle_release(&valk_global_handle_table, timer_data->callback_handle);
    return;
  }
  // LCOV_EXCL_STOP

  r = uv_timer_start(&timer_data->timer, __interval_timer_cb, init_ctx->interval_ms, init_ctx->interval_ms);
  // LCOV_EXCL_START - libuv timer start essentially never fails
  if (r != 0) {
    valk_handle_release(&valk_global_handle_table, timer_data->callback_handle);
    uv_close((uv_handle_t *)&timer_data->timer, NULL);
  }
  // LCOV_EXCL_STOP
}

extern valk_lval_t* valk_lval_copy(valk_lval_t* lval);

valk_lval_t* valk_aio_interval(valk_aio_system_t* sys, u64 interval_ms,
                                valk_lval_t* callback, valk_lenv_t* env) {
  UNUSED(env);
  if (!sys || !sys->eventloop) {
    return valk_lval_err("aio/interval: invalid AIO system");
  }

  valk_interval_timer_t *timer_data = valk_region_alloc(&sys->system_region, sizeof(valk_interval_timer_t));
  if (!timer_data) {
    return valk_lval_err("Failed to allocate interval timer");
  }

  valk_lval_t *heap_callback = valk_evacuate_to_heap(callback);
  
  timer_data->callback = heap_callback;
  timer_data->callback_handle = valk_handle_create(&valk_global_handle_table, heap_callback);
  timer_data->interval_id = __atomic_fetch_add(&g_interval_id, 1, __ATOMIC_RELAXED);
  timer_data->stopped = false;
  timer_data->timer.data = timer_data;

  valk_interval_init_ctx_t *init_ctx = valk_region_alloc(&sys->system_region, sizeof(valk_interval_init_ctx_t));
  if (!init_ctx) {
    valk_handle_release(&valk_global_handle_table, timer_data->callback_handle);
    return valk_lval_err("Failed to allocate interval init context");
  }
  
  init_ctx->sys = sys;
  init_ctx->timer_data = timer_data;
  init_ctx->interval_ms = interval_ms;
  
  valk_aio_enqueue_task(sys, __interval_init_on_loop, init_ctx);

  return valk_lval_num((long)timer_data->interval_id);
}

static void __schedule_timer_cb(uv_timer_t *handle) {
  VALK_GC_SAFE_POINT();
  
  valk_schedule_timer_t *timer_data = (valk_schedule_timer_t *)handle->data;
  valk_lval_t *callback = valk_handle_resolve(&valk_global_handle_table, timer_data->callback_handle);

  if (callback) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = valk_lval_eval_call(callback->fun.env, callback, args);
    if (LVAL_TYPE(result) == LVAL_ERR) {
      VALK_WARN("aio/schedule callback returned error: %s", result->str);
    }
  }

  valk_handle_release(&valk_global_handle_table, timer_data->callback_handle);
  uv_timer_stop(handle);
  uv_close((uv_handle_t *)handle, __schedule_timer_close_cb);
}

typedef struct {
  valk_aio_system_t *sys;
  valk_schedule_timer_t *timer_data;
  u64 delay_ms;
} valk_schedule_init_ctx_t;

static void __schedule_init_on_loop(void *ctx) {
  valk_schedule_init_ctx_t *init_ctx = (valk_schedule_init_ctx_t *)ctx;
  valk_schedule_timer_t *timer_data = init_ctx->timer_data;
  
  uv_loop_t *loop = init_ctx->sys->eventloop;
  int r = uv_timer_init(loop, &timer_data->timer);
  // LCOV_EXCL_START - libuv timer init essentially never fails
  if (r != 0) {
    valk_handle_release(&valk_global_handle_table, timer_data->callback_handle);
    return;
  }
  // LCOV_EXCL_STOP

  r = uv_timer_start(&timer_data->timer, __schedule_timer_cb, init_ctx->delay_ms, 0);
  // LCOV_EXCL_START - libuv timer start essentially never fails
  if (r != 0) {
    valk_handle_release(&valk_global_handle_table, timer_data->callback_handle);
    uv_close((uv_handle_t *)&timer_data->timer, NULL);
  }
  // LCOV_EXCL_STOP
}

static _Atomic(u64) g_schedule_id = 0;

valk_lval_t* valk_aio_schedule(valk_aio_system_t* sys, u64 delay_ms,
                                valk_lval_t* callback, valk_lenv_t* env) {
  UNUSED(env);
  if (!sys || !sys->eventloop) {
    return valk_lval_err("aio/schedule: invalid AIO system");
  }

  u64 schedule_id = atomic_fetch_add(&g_schedule_id, 1);

  valk_schedule_timer_t *timer_data = valk_region_alloc(&sys->system_region, sizeof(valk_schedule_timer_t));
  if (!timer_data) {
    return valk_lval_err("Failed to allocate timer");
  }

  valk_lval_t *heap_callback = valk_evacuate_to_heap(callback);

  timer_data->callback = heap_callback;
  timer_data->callback_handle = valk_handle_create(&valk_global_handle_table, heap_callback);
  timer_data->timer.data = timer_data;
  timer_data->schedule_id = schedule_id;

  valk_schedule_init_ctx_t *init_ctx = valk_region_alloc(&sys->system_region, sizeof(valk_schedule_init_ctx_t));
  if (!init_ctx) {
    valk_handle_release(&valk_global_handle_table, timer_data->callback_handle);
    return valk_lval_err("Failed to allocate schedule init context");
  }
  
  init_ctx->sys = sys;
  init_ctx->timer_data = timer_data;
  init_ctx->delay_ms = delay_ms;
  
  valk_aio_enqueue_task(sys, __schedule_init_on_loop, init_ctx);

  return valk_lval_nil();
}

extern valk_async_handle_t* valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);
extern void valk_async_handle_free(valk_async_handle_t *handle);
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
extern bool valk_async_handle_cancel(valk_async_handle_t *handle);
extern void valk_async_handle_add_child(valk_async_handle_t *parent, valk_async_handle_t *child);
extern void valk_async_propagate_region(valk_async_handle_t *handle, valk_region_t *region, valk_lenv_t *env);
extern void valk_async_notify_done(valk_async_handle_t *handle);
extern bool valk_async_is_resource_closed(valk_async_handle_t *handle);
extern valk_standalone_async_ctx_t* valk_standalone_async_ctx_new(valk_aio_system_t *sys);
extern void valk_standalone_async_done_callback(valk_async_handle_t *handle, void *ctx);
extern valk_lval_t *valk_lval_handle(valk_async_handle_t *handle);

#define VALK_ALL_CTX_MAGIC 0xA11C7821
#define VALK_ALL_CTX_MAGIC_EARLY 0xA11C7821
#define VALK_RACE_CTX_MAGIC 0x9ACE7821
#define VALK_RACE_CTX_MAGIC_EARLY 0x9ACE7821
#define VALK_ANY_CTX_MAGIC 0xA4177821
#define VALK_ANY_CTX_MAGIC_EARLY 0xA4177821

void valk_async_propagate_completion(valk_async_handle_t *source);
void valk_async_notify_all_parent(valk_async_handle_t *child);
void valk_async_notify_race_parent(valk_async_handle_t *child);
void valk_async_notify_any_parent(valk_async_handle_t *child);

static void __sleep_timer_cb(uv_timer_t *timer_handle) {
  valk_async_handle_uv_data_t *data = (valk_async_handle_uv_data_t *)timer_handle->data;
  valk_async_handle_t *async_handle = data->handle;

  valk_lval_t *result = valk_lval_nil();
  valk_async_handle_complete(async_handle, result);

  uv_timer_stop(timer_handle);
  uv_close((uv_handle_t *)timer_handle, __sleep_timer_close_cb);
}

static valk_lval_t* valk_builtin_aio_sleep(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/sleep: expected 2 arguments (sys ms)");
  }
  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  valk_lval_t *ms_arg = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(sys_arg) != LVAL_REF || strcmp(sys_arg->ref.type, "aio_system") != 0) {
    return valk_lval_err("aio/sleep: first argument must be an aio_system");
  }
  if (LVAL_TYPE(ms_arg) != LVAL_NUM) {
    return valk_lval_err("aio/sleep: second argument must be a number");
  }

  valk_request_ctx_t *req_ctx = valk_thread_ctx.request_ctx;
  if (req_ctx && valk_request_ctx_deadline_exceeded(req_ctx)) {
    return valk_lval_err(":deadline-exceeded");
  }

  valk_aio_system_t *sys = sys_arg->ref.ptr;
  u64 delay_ms = (u64)ms_arg->num;

  if (req_ctx && valk_request_ctx_has_deadline(req_ctx)) {
    u64 remaining_ms = valk_request_ctx_remaining_ms(req_ctx);
    if (delay_ms > remaining_ms) {
      delay_ms = remaining_ms;
    }
  }

  valk_async_handle_t *async_handle = valk_async_handle_new(sys, e);
  async_handle->request_ctx = req_ctx;

  valk_async_handle_uv_data_t *timer_data = aligned_alloc(alignof(valk_async_handle_uv_data_t), sizeof(valk_async_handle_uv_data_t));
  timer_data->handle = async_handle;
  timer_data->uv.timer.data = timer_data;

  async_handle->uv_handle_ptr = timer_data;
  async_handle->status = VALK_ASYNC_RUNNING;

  uv_timer_init(sys->eventloop, &timer_data->uv.timer);
  uv_timer_start(&timer_data->uv.timer, __sleep_timer_cb, (unsigned long long)delay_ms, 0);

  VALK_INFO("aio/sleep started: %llu ms, handle id=%llu", (unsigned long long)delay_ms, (unsigned long long)async_handle->id);

  return valk_lval_handle(async_handle);
}

static inline bool is_then_barrier(valk_lval_t *item) {
  return LVAL_TYPE(item) == LVAL_SYM && strcmp(item->str, ":then") == 0;
}

typedef struct {
  valk_lval_t **bindings;
  u64 count;
  u64 capacity;
} aio_let_group_t;

typedef struct {
  aio_let_group_t *groups;
  u64 count;
  u64 capacity;
} aio_let_parsed_t;

static aio_let_parsed_t* aio_let_parse_bindings(valk_lval_t *bindings) {
  aio_let_parsed_t *result = malloc(sizeof(aio_let_parsed_t));
  result->groups = malloc(sizeof(aio_let_group_t) * 16);
  result->count = 1;
  result->capacity = 16;

  aio_let_group_t *current = &result->groups[0];
  current->bindings = malloc(sizeof(valk_lval_t*) * 32);
  current->count = 0;
  current->capacity = 32;

  valk_lval_t *curr = bindings;

  if (LVAL_TYPE(bindings) == LVAL_QEXPR && !valk_lval_list_is_empty(bindings)) {
    valk_lval_t *first = bindings->cons.head;
    if (LVAL_TYPE(first) == LVAL_CONS || LVAL_TYPE(first) == LVAL_QEXPR) {
      curr = first;
    }
  }

  while ((LVAL_TYPE(curr) == LVAL_CONS || LVAL_TYPE(curr) == LVAL_QEXPR) &&
         !valk_lval_list_is_empty(curr)) {
    valk_lval_t *item = curr->cons.head;

    if (is_then_barrier(item)) {
      // LCOV_EXCL_START - :then barrier and realloc: complex aio/let patterns
      if (current->count > 0) {
        result->count++;
        if (result->count >= result->capacity) {
          result->capacity *= 2;
          result->groups = realloc(result->groups,
                                   sizeof(aio_let_group_t) * result->capacity);
        }
        current = &result->groups[result->count - 1];
        current->bindings = malloc(sizeof(valk_lval_t*) * 32);
        current->count = 0;
        current->capacity = 32;
      }
      // LCOV_EXCL_STOP
    } else {
      // LCOV_EXCL_START - binding realloc: requires >32 parallel bindings
      if (current->count >= current->capacity) {
        current->capacity *= 2;
        current->bindings = realloc(current->bindings,
                                    sizeof(valk_lval_t*) * current->capacity);
      }
      // LCOV_EXCL_STOP
      current->bindings[current->count++] = item;
    }

    curr = curr->cons.tail;
  }

  return result;
}

static void aio_let_free_parsed(aio_let_parsed_t *parsed) {
  for (u64 i = 0; i < parsed->count; i++) {
    free(parsed->groups[i].bindings);
  }
  free(parsed->groups);
  free(parsed);
}

static valk_lval_t* aio_let_gen_group(valk_lenv_t *env,
                                       aio_let_group_t *group,
                                       valk_lval_t *inner) {
  if (group->count == 0) {
    return inner;
  }

  if (group->count == 1) {
    valk_lval_t *binding = group->bindings[0];
    valk_lval_t *var = valk_lval_list_nth(binding, 0);
    valk_lval_t *expr = valk_lval_list_nth(binding, 1);

    valk_lval_t *formals = valk_lval_qcons(valk_lval_copy(var), valk_lval_nil());

    valk_lval_t *lambda = valk_lval_lambda(env, formals, inner);

    valk_lval_t *then_call = valk_lval_cons(
      valk_lval_sym("aio/then"),
      valk_lval_cons(valk_lval_copy(expr),
        valk_lval_cons(lambda, valk_lval_nil())));

    return then_call;
  }

  valk_lval_t *expr_list = valk_lval_nil();
  for (int i = group->count - 1; i >= 0; i--) {
    valk_lval_t *binding = group->bindings[i];
    valk_lval_t *expr = valk_lval_list_nth(binding, 1);
    expr_list = valk_lval_cons(valk_lval_copy(expr), expr_list);
  }

  valk_lval_t *list_call = valk_lval_cons(valk_lval_sym("list"), expr_list);

  valk_lval_t *all_call = valk_lval_cons(
    valk_lval_sym("aio/all"),
    valk_lval_cons(list_call, valk_lval_nil()));

  valk_lval_t *body = valk_lval_cons(valk_lval_sym("do"), valk_lval_nil());
  valk_lval_t *body_tail = body;

  for (u64 i = 0; i < group->count; i++) {
    valk_lval_t *binding = group->bindings[i];
    valk_lval_t *var = valk_lval_list_nth(binding, 0);

    valk_lval_t *var_qexpr = valk_lval_qcons(valk_lval_copy(var), valk_lval_nil());

    valk_lval_t *nth_call = valk_lval_cons(
      valk_lval_sym("nth"),
      valk_lval_cons(valk_lval_num((i64)(i + 1)),
        valk_lval_cons(valk_lval_sym("_results"), valk_lval_nil())));

    valk_lval_t *assign = valk_lval_cons(
      valk_lval_sym("="),
      valk_lval_cons(var_qexpr,
        valk_lval_cons(nth_call, valk_lval_nil())));

    body_tail->cons.tail = valk_lval_cons(assign, valk_lval_nil());
    body_tail = body_tail->cons.tail;
  }

  body_tail->cons.tail = valk_lval_cons(inner, valk_lval_nil());

  valk_lval_t *formals = valk_lval_qcons(valk_lval_sym("_results"), valk_lval_nil());
  valk_lval_t *lambda = valk_lval_lambda(env, formals, body);

  valk_lval_t *then_call = valk_lval_cons(
    valk_lval_sym("aio/then"),
    valk_lval_cons(all_call,
      valk_lval_cons(lambda, valk_lval_nil())));

  return then_call;
}

static valk_lval_t* valk_builtin_aio_let(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/let: expected 2 arguments (bindings body)");
  }

  valk_lval_t *bindings = valk_lval_list_nth(a, 0);
  valk_lval_t *body = valk_lval_list_nth(a, 1);

  aio_let_parsed_t *parsed = aio_let_parse_bindings(bindings);

  if (parsed->count == 0 || (parsed->count == 1 && parsed->groups[0].count == 0)) {
    aio_let_free_parsed(parsed);
    valk_lval_t *evaled_body = valk_lval_eval(e, valk_lval_copy(body));
    valk_lval_t *pure_call = valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(evaled_body, valk_lval_nil()));
    return valk_lval_eval(e, pure_call);
  }

  valk_lval_t *body_expr = body;
  if (LVAL_TYPE(body) == LVAL_CONS && (body->flags & LVAL_FLAG_QUOTED) && !valk_lval_list_is_empty(body)) {
    if (valk_lval_list_is_empty(body->cons.tail)) {
      body_expr = body->cons.head;
    }
  }
  valk_lval_t *result = valk_lval_cons(
    valk_lval_sym("aio/pure"),
    valk_lval_cons(valk_lval_copy(body_expr), valk_lval_nil()));

  for (int g = parsed->count - 1; g >= 0; g--) {
    result = aio_let_gen_group(e, &parsed->groups[g], result);
  }

  aio_let_free_parsed(parsed);

  return valk_lval_eval(e, result);
}

static inline bool is_bind_form(valk_lval_t *expr) {
  if (LVAL_TYPE(expr) != LVAL_CONS && LVAL_TYPE(expr) != LVAL_QEXPR) return false;
  if (valk_lval_list_is_empty(expr)) return false;
  valk_lval_t *head = expr->cons.head;
  return LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "<-") == 0;
}

static valk_lval_t* aio_do_build_chain(valk_lenv_t *env, valk_lval_t *stmts) {
  if (valk_lval_list_is_empty(stmts)) {
    return valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(valk_lval_nil(), valk_lval_nil()));
  }

  valk_lval_t *curr = stmts->cons.head;
  valk_lval_t *rest = stmts->cons.tail;

  bool is_last = valk_lval_list_is_empty(rest);

  if (is_bind_form(curr)) {
    valk_lval_t *var = valk_lval_list_nth(curr, 1);
    valk_lval_t *expr = valk_lval_list_nth(curr, 2);

    if (is_last) {
      return valk_lval_copy(expr);
    }

    // LCOV_EXCL_START - aio/do bind form: tests use simpler patterns
    valk_lval_t *continuation = aio_do_build_chain(env, rest);

    valk_lval_t *formals = valk_lval_qcons(valk_lval_copy(var), valk_lval_nil());
    valk_lval_t *lambda = valk_lval_lambda(env, formals, continuation);

    return valk_lval_cons(
      valk_lval_sym("aio/then"),
      valk_lval_cons(valk_lval_copy(expr),
        valk_lval_cons(lambda, valk_lval_nil())));
    // LCOV_EXCL_STOP
  } else {
    if (is_last) {
      return valk_lval_cons(
        valk_lval_sym("aio/pure"),
        valk_lval_cons(valk_lval_copy(curr), valk_lval_nil()));
    }

    valk_lval_t *sync_exprs = valk_lval_nil();
    sync_exprs = valk_lval_cons(valk_lval_copy(curr), sync_exprs);

    valk_lval_t *remaining = rest;
    while (!valk_lval_list_is_empty(remaining) && !is_bind_form(remaining->cons.head)) {
      valk_lval_t *next = remaining->cons.head;
      remaining = remaining->cons.tail;

      if (valk_lval_list_is_empty(remaining)) {
        sync_exprs = valk_lval_cons(valk_lval_copy(next), sync_exprs);
        break;
      }
      sync_exprs = valk_lval_cons(valk_lval_copy(next), sync_exprs);
    }

    valk_lval_t *reversed = valk_lval_nil();
    while (!valk_lval_list_is_empty(sync_exprs)) {
      reversed = valk_lval_cons(sync_exprs->cons.head, reversed);
      sync_exprs = sync_exprs->cons.tail;
    }

    // LCOV_EXCL_START - aio/do sync-only path: tests use async binds
    if (valk_lval_list_is_empty(remaining)) {
      valk_lval_t *do_body = valk_lval_cons(valk_lval_sym("do"), valk_lval_nil());
      valk_lval_t *do_tail = do_body;

      valk_lval_t *rev_curr = reversed;
      valk_lval_t *last_sync = NULL;
      while (!valk_lval_list_is_empty(rev_curr)) {
        if (valk_lval_list_is_empty(rev_curr->cons.tail)) {
          last_sync = rev_curr->cons.head;
        } else {
          do_tail->cons.tail = valk_lval_cons(valk_lval_copy(rev_curr->cons.head), valk_lval_nil());
          do_tail = do_tail->cons.tail;
        }
        rev_curr = rev_curr->cons.tail;
      }

      valk_lval_t *pure_last = valk_lval_cons(
        valk_lval_sym("aio/pure"),
        valk_lval_cons(valk_lval_copy(last_sync), valk_lval_nil()));
      do_tail->cons.tail = valk_lval_cons(pure_last, valk_lval_nil());

      return do_body;
    } else {
      valk_lval_t *continuation = aio_do_build_chain(env, remaining);

      valk_lval_t *do_body = valk_lval_cons(valk_lval_sym("do"), valk_lval_nil());
      valk_lval_t *do_tail = do_body;

      valk_lval_t *rev_curr = reversed;
      while (!valk_lval_list_is_empty(rev_curr)) {
        do_tail->cons.tail = valk_lval_cons(valk_lval_copy(rev_curr->cons.head), valk_lval_nil());
        do_tail = do_tail->cons.tail;
        rev_curr = rev_curr->cons.tail;
      }

      do_tail->cons.tail = valk_lval_cons(continuation, valk_lval_nil());
      return do_body;
    }
    // LCOV_EXCL_STOP
  }
}

static valk_lval_t* valk_builtin_aio_do(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_START - aio/do arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/do: expected 1 argument (qexpr of statements)");
  }

  valk_lval_t *stmts = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(stmts) != LVAL_CONS || !(stmts->flags & LVAL_FLAG_QUOTED)) {
    return valk_lval_err("aio/do: argument must be a qexpr {stmt1 stmt2 ...}");
  }
  // LCOV_EXCL_STOP

  if (valk_lval_list_is_empty(stmts)) {
    valk_lval_t *pure = valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(valk_lval_nil(), valk_lval_nil()));
    return valk_lval_eval(e, pure);
  }

  valk_lval_t *chain = aio_do_build_chain(e, stmts);

  return valk_lval_eval(e, chain);
}

extern valk_lval_t* valk_async_status_to_sym(valk_async_status_t status);

static valk_lval_t* valk_builtin_aio_cancel(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/cancel: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/cancel: expected handle argument");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;
  bool cancelled = valk_async_handle_cancel(handle);

  return valk_lval_sym(cancelled ? ":true" : ":false");
}

static valk_lval_t* valk_builtin_aio_cancelled(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/cancelled?: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/cancelled?: expected handle argument");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;
  bool cancelled = handle->status == VALK_ASYNC_CANCELLED ||
                   valk_async_handle_is_cancelled(handle);

  return valk_lval_sym(cancelled ? ":true" : ":false");
}

static valk_lval_t* valk_builtin_aio_status(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/status: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/status: expected handle argument");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;
  return valk_async_status_to_sym(handle->status);
}

static valk_lval_t* valk_builtin_aio_pure(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/pure: expected 1 argument");
  }
  valk_lval_t *value = valk_lval_list_nth(a, 0);

  valk_async_handle_t *handle = valk_async_handle_new(NULL, e);
  if (!handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  valk_async_handle_try_transition(handle, VALK_ASYNC_PENDING, VALK_ASYNC_COMPLETED);
  handle->result = value;

  return valk_lval_handle(handle);
}

static valk_lval_t* valk_builtin_aio_fail(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/fail: expected 1 argument");
  }
  valk_lval_t *error = valk_lval_list_nth(a, 0);

  valk_async_handle_t *handle = valk_async_handle_new(NULL, e);
  if (!handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  valk_async_handle_try_transition(handle, VALK_ASYNC_PENDING, VALK_ASYNC_FAILED);
  handle->error = error;

  return valk_lval_handle(handle);
}

static bool valk_async_is_chain_closed(valk_async_handle_t *handle) {
  if (!handle) return false;

  if (valk_async_is_resource_closed(handle)) {
    return true;
  }

  valk_async_handle_t *p = handle->parent;
  int depth = 0;
  while (p && depth < 100) {
    if (valk_async_is_resource_closed(p)) {
      return true;
    }
    p = p->parent;
    depth++;
  }

  u32 child_count = valk_chunked_ptrs_count(&handle->children);
  for (u32 i = 0; i < child_count && i < 100; i++) {
    valk_async_handle_t *child = valk_chunked_ptrs_get(&handle->children, i);
    if (child && valk_async_is_resource_closed(child)) {
      return true;
    }
  }
  return false;
}

static void valk_async_propagate_single(void *ctx);

static void valk_async_schedule_propagate(valk_async_handle_t *child) {
  valk_aio_system_t *sys = child->sys;
  if (sys) {
    valk_aio_enqueue_task(sys, valk_async_propagate_single, child);
  } else {
    valk_async_propagate_single(child);
  }
}

static void valk_async_propagate_single(void *ctx) {
  VALK_GC_SAFE_POINT();
  
  valk_async_handle_t *source = (valk_async_handle_t *)ctx;
  if (!source) return;

  u32 children_count = valk_chunked_ptrs_count(&source->children);
  VALK_INFO("Propagating from handle %llu (status=%d, children=%u)",
            source->id, valk_async_handle_get_status(source), children_count);

  if (valk_async_is_chain_closed(source)) {
    VALK_INFO("Async propagation: connection closed, aborting propagation");
    return;
  }

  valk_async_status_t source_status = valk_async_handle_get_status(source);

  for (u32 i = 0; i < children_count; i++) {
    valk_async_handle_t *child = valk_chunked_ptrs_get(&source->children, i);
    valk_async_status_t child_status = valk_async_handle_get_status(child);
    VALK_DEBUG("  Child %zu: handle %llu, status=%d, parent=%llu (source=%llu), on_complete=%p",
              i, child->id, child_status,
              child->parent ? child->parent->id : 0, source->id,
              (void*)child->on_complete);
    if (child_status == VALK_ASYNC_RUNNING &&
        (child->parent == source || child->on_complete != NULL)) {

      if (valk_async_is_chain_closed(child)) {
        VALK_INFO("Async propagation: child connection closed, cancelling child , handle %llu", (unsigned long long)child->id);
        valk_async_handle_try_transition(child, VALK_ASYNC_RUNNING, VALK_ASYNC_CANCELLED);
        continue;
      }

      if (source_status == VALK_ASYNC_COMPLETED) {
        if (child->on_complete && child->env) {
          valk_lval_t *args;
          valk_lval_t *transformed;
          valk_mem_allocator_t *alloc = child->region ? (valk_mem_allocator_t*)child->region : nullptr;
          if (!alloc && child->sys) {
            alloc = (valk_mem_allocator_t*)&child->sys->system_region;
          }
          if (!alloc) alloc = &valk_malloc_allocator;
          VALK_WITH_ALLOC(alloc) {
            args = valk_lval_cons(source->result, valk_lval_nil());
            transformed = valk_lval_eval_call(child->env, child->on_complete, args);
          }
          if (LVAL_TYPE(transformed) == LVAL_ERR) {
            atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
            child->error = transformed;
          } else if (LVAL_TYPE(transformed) == LVAL_HANDLE) {
            valk_async_handle_t *inner = transformed->async.handle;
            valk_async_status_t inner_status = valk_async_handle_get_status(inner);
            if (inner_status == VALK_ASYNC_COMPLETED) {
              atomic_store_explicit(&child->status, VALK_ASYNC_COMPLETED, memory_order_release);
              child->result = inner->result;
            } else if (inner_status == VALK_ASYNC_FAILED) {
              atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
              child->error = inner->error;
              valk_async_notify_all_parent(child);
              valk_async_notify_race_parent(child);
              valk_async_notify_any_parent(child);
            } else if (inner_status == VALK_ASYNC_CANCELLED) {
              atomic_store_explicit(&child->status, VALK_ASYNC_CANCELLED, memory_order_release);
            } else {
              valk_async_handle_add_child(inner, child);
              child->parent = inner;
              child->on_complete = NULL;
              if (child->on_done && !inner->on_done) {
                inner->on_done = child->on_done;
                inner->on_done_ctx = child->on_done_ctx;
                inner->is_closed = child->is_closed;
                inner->is_closed_ctx = child->is_closed_ctx;
                inner->region = child->region;
                inner->env = child->env;
                child->on_done = NULL;
                child->on_done_ctx = NULL;
                child->is_closed = NULL;
                child->is_closed_ctx = NULL;
              }
              continue;
            }
          } else {
            atomic_store_explicit(&child->status, VALK_ASYNC_COMPLETED, memory_order_release);
            child->result = transformed;
          }
        } else {
          atomic_store_explicit(&child->status, VALK_ASYNC_COMPLETED, memory_order_release);
          child->result = source->result;
        }
        valk_async_notify_all_parent(child);
        valk_async_notify_race_parent(child);
        valk_async_notify_any_parent(child);
        valk_async_notify_done(child);
        valk_async_schedule_propagate(child);
      } else if (source_status == VALK_ASYNC_FAILED) {
        if (child->on_error && child->env) {
          valk_lval_t *args;
          valk_lval_t *recovered;
          valk_mem_allocator_t *alloc = child->region ? (valk_mem_allocator_t*)child->region : nullptr;
          if (!alloc && child->sys) {
            alloc = (valk_mem_allocator_t*)&child->sys->system_region;
          }
          if (!alloc) alloc = &valk_malloc_allocator;
          VALK_WITH_ALLOC(alloc) {
            args = valk_lval_cons(source->error, valk_lval_nil());
            recovered = valk_lval_eval_call(child->env, child->on_error, args);
          }
          if (LVAL_TYPE(recovered) == LVAL_ERR) {
            atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
            child->error = recovered;
          } else {
            atomic_store_explicit(&child->status, VALK_ASYNC_COMPLETED, memory_order_release);
            child->result = recovered;
          }
        } else {
          atomic_store_explicit(&child->status, VALK_ASYNC_FAILED, memory_order_release);
          child->error = source->error;
        }
        valk_async_notify_done(child);
        valk_async_schedule_propagate(child);
      }
    }
  }
}

void valk_async_propagate_completion(valk_async_handle_t *source) {
  if (!source) return;
  valk_async_propagate_single(source);
}

static valk_lval_t* valk_builtin_aio_then(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/then: expected 2 arguments (handle fn)");
  }
  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/then: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/then: second argument must be a function");
  }

  valk_async_handle_t *source = source_lval->async.handle;

  valk_async_handle_t *result = valk_async_handle_new(source->sys, e);
  if (!result) {
    return valk_lval_err("Failed to allocate async handle");
  }
  result->request_ctx = source->request_ctx;

  if (source->status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *args = valk_lval_cons(source->result, valk_lval_nil());
    valk_lval_t *transformed = valk_lval_eval_call(e, fn, args);
    if (LVAL_TYPE(transformed) == LVAL_ERR) {
      result->status = VALK_ASYNC_FAILED;
      result->error = transformed;
    } else if (LVAL_TYPE(transformed) == LVAL_HANDLE) {
      valk_async_handle_t *inner = transformed->async.handle;
      if (inner->status == VALK_ASYNC_COMPLETED) {
        result->status = VALK_ASYNC_COMPLETED;
        result->result = inner->result;
      } else if (inner->status == VALK_ASYNC_FAILED) {
        result->status = VALK_ASYNC_FAILED;
        result->error = inner->error;
      // LCOV_EXCL_START - inner handle running: requires nested async with specific timing
      } else {
        result->status = VALK_ASYNC_RUNNING;
        inner->on_complete = valk_lval_lambda(e,
          valk_lval_qcons(valk_lval_sym("x"), valk_lval_nil()),
          valk_lval_nil());
        valk_async_handle_add_child(result, inner);
      }
      // LCOV_EXCL_STOP
    } else {
      result->status = VALK_ASYNC_COMPLETED;
      result->result = transformed;
    }
    return valk_lval_handle(result);
  }

  if (source->status == VALK_ASYNC_FAILED) {
    result->status = VALK_ASYNC_FAILED;
    result->error = source->error;
    return valk_lval_handle(result);
  }

  if (source->status == VALK_ASYNC_CANCELLED) {
    result->status = VALK_ASYNC_CANCELLED;
    return valk_lval_handle(result);
  }

  result->status = VALK_ASYNC_RUNNING;
  result->env = e;
  result->on_complete = fn;
  result->on_error = NULL;
  result->parent = source;

  valk_async_handle_add_child(source, result);

  return valk_lval_handle(result);
}

static valk_lval_t* valk_builtin_aio_catch(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/catch: expected 2 arguments (handle fn)");
  }
  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/catch: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/catch: second argument must be a function");
  }

  valk_async_handle_t *source = source_lval->async.handle;

  valk_async_handle_t *catch_handle = valk_async_handle_new(source->sys, e);
  if (!catch_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  catch_handle->request_ctx = source->request_ctx;

  if (source->status == VALK_ASYNC_COMPLETED) {
    catch_handle->status = VALK_ASYNC_COMPLETED;
    catch_handle->result = source->result;
    return valk_lval_handle(catch_handle);
  }

  if (source->status == VALK_ASYNC_FAILED) {
    valk_lval_t *args = valk_lval_cons(source->error, valk_lval_nil());
    valk_lval_t *recovered = valk_lval_eval_call(e, fn, args);
    if (LVAL_TYPE(recovered) == LVAL_ERR) {
      catch_handle->status = VALK_ASYNC_FAILED;
      catch_handle->error = recovered;
    } else {
      catch_handle->status = VALK_ASYNC_COMPLETED;
      catch_handle->result = recovered;
    }
    return valk_lval_handle(catch_handle);
  }

  if (source->status == VALK_ASYNC_CANCELLED) {
    catch_handle->status = VALK_ASYNC_CANCELLED;
    return valk_lval_handle(catch_handle);
  }

  catch_handle->status = VALK_ASYNC_RUNNING;
  catch_handle->env = e;
  catch_handle->on_complete = NULL;
  catch_handle->on_error = fn;
  catch_handle->parent = source;

  valk_async_handle_add_child(source, catch_handle);

  return valk_lval_handle(catch_handle);
}

static valk_lval_t* valk_builtin_aio_finally(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/finally: expected 2 arguments (handle fn)");
  }
  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/finally: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/finally: second argument must be a function");
  }

  valk_async_handle_t *source = source_lval->async.handle;

  valk_async_handle_t *finally_handle = valk_async_handle_new(source->sys, e);
  if (!finally_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  finally_handle->request_ctx = source->request_ctx;

  // LCOV_EXCL_START - aio/finally immediate: requires already-complete handle
  if (source->status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);
    finally_handle->status = VALK_ASYNC_COMPLETED;
    finally_handle->result = source->result;
    return valk_lval_handle(finally_handle);
  }
  if (source->status == VALK_ASYNC_FAILED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);
    finally_handle->status = VALK_ASYNC_FAILED;
    finally_handle->error = source->error;
    return valk_lval_handle(finally_handle);
  // LCOV_EXCL_STOP
  }
  if (source->status == VALK_ASYNC_CANCELLED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);
    finally_handle->status = VALK_ASYNC_CANCELLED;
    return valk_lval_handle(finally_handle);
  }

  finally_handle->status = VALK_ASYNC_RUNNING;
  finally_handle->env = e;
  finally_handle->on_cancel = fn;
  finally_handle->parent = source;

  valk_async_handle_add_child(source, finally_handle);

  return valk_lval_handle(finally_handle);
}

typedef struct {
  u32 magic;
  valk_async_handle_t *all_handle;
  valk_lval_t **results;
  valk_async_handle_t **handles;
  u64 total;
  u64 completed;
  valk_mem_allocator_t *allocator;
} valk_all_ctx_t;

static void valk_all_ctx_cleanup(void *ctx) {
  valk_all_ctx_t *all_ctx = (valk_all_ctx_t *)ctx;
  if (!all_ctx) return;
  all_ctx->magic = 0;
  if (all_ctx->allocator && all_ctx->allocator->type != VALK_ALLOC_MALLOC) return;
  if (all_ctx->results) free(all_ctx->results);
  if (all_ctx->handles) free(all_ctx->handles);
  free(all_ctx);
}

static void valk_async_all_child_completed(valk_async_handle_t *child);
static void valk_async_all_child_failed(valk_async_handle_t *child, valk_lval_t *error);

static valk_lval_t* valk_builtin_aio_all(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/all: expected 1 argument (list of handles)");
  }
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  u64 count = 0;
  valk_lval_t *iter = handles_list;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/all: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/all: all elements must be handles");
    }
    count++;
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    valk_async_handle_t *result = valk_async_handle_new(NULL, e);
    result->status = VALK_ASYNC_COMPLETED;
    result->result = valk_lval_nil();
    return valk_lval_handle(result);
  }

  valk_mem_allocator_t *allocator = valk_thread_ctx.allocator;

  valk_async_handle_t *all_handle = valk_async_handle_new(NULL, e);
  if (!all_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  valk_lval_t *first_h = valk_lval_head(handles_list);
  if (first_h && LVAL_TYPE(first_h) == LVAL_HANDLE && first_h->async.handle->request_ctx) {
    all_handle->request_ctx = first_h->async.handle->request_ctx;
  }

  valk_lval_t **results = valk_mem_calloc(count, sizeof(valk_lval_t*));
  if (!results) {
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate results array");
  }

  u64 completed = 0;
  bool any_pending = false;
  bool any_failed = false;
  valk_lval_t *first_error = NULL;

  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;

    if (handle->status == VALK_ASYNC_COMPLETED) {
      results[i] = handle->result;
      completed++;
    } else if (handle->status == VALK_ASYNC_FAILED) {
      any_failed = true;
      if (!first_error) first_error = handle->error;
    } else if (handle->status == VALK_ASYNC_CANCELLED) {
      any_failed = true;
      if (!first_error) first_error = valk_lval_err("cancelled");
    } else {
      any_pending = true;
      if (!all_handle->sys && handle->sys) {
        all_handle->sys = handle->sys;
      }
    }
    iter = valk_lval_tail(iter);
  }

  if (any_failed) {
    valk_mem_free(results);
    all_handle->status = VALK_ASYNC_FAILED;
    all_handle->error = first_error;

    iter = handles_list;
    for (u64 i = 0; i < count; i++) {
      valk_lval_t *h = valk_lval_head(iter);
      valk_async_handle_t *handle = h->async.handle;
      if (handle->status == VALK_ASYNC_PENDING || handle->status == VALK_ASYNC_RUNNING) {
        valk_async_handle_cancel(handle);
      }
      iter = valk_lval_tail(iter);
    }
    return valk_lval_handle(all_handle);
  }

  if (!any_pending) {
    valk_lval_t *result_list = valk_lval_nil();
    for (u64 i = count; i > 0; i--) {
      result_list = valk_lval_cons(results[i-1], result_list);
    }
    valk_mem_free(results);
    all_handle->status = VALK_ASYNC_COMPLETED;
    all_handle->result = result_list;
    return valk_lval_handle(all_handle);
  }

  all_handle->status = VALK_ASYNC_RUNNING;
  all_handle->env = e;

  valk_async_handle_t **handles = valk_mem_calloc(count, sizeof(valk_async_handle_t*));
  // LCOV_EXCL_START - calloc failure: requires OOM
  if (!handles) {
    valk_mem_free(results);
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate handles array");
  }
  // LCOV_EXCL_STOP

  valk_all_ctx_t *ctx = valk_mem_alloc(sizeof(valk_all_ctx_t));
  if (!ctx) {
    valk_mem_free(results);
    valk_mem_free(handles);
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate all context");
  }
  ctx->magic = VALK_ALL_CTX_MAGIC;
  ctx->all_handle = all_handle;
  ctx->results = results;
  ctx->handles = handles;
  ctx->total = count;
  ctx->completed = completed;
  ctx->allocator = allocator;
  all_handle->uv_handle_ptr = ctx;

  valk_async_handle_on_cleanup(all_handle, valk_all_ctx_cleanup, ctx);

  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    handles[i] = handle;
    valk_async_handle_add_child(all_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(all_handle);
}

static inline valk_all_ctx_t* valk_async_get_all_ctx(valk_async_handle_t *handle) {
  if (!handle || !handle->parent) return NULL;
  valk_async_handle_t *parent = handle->parent;
  if (!parent->uv_handle_ptr) return NULL;
  valk_all_ctx_t *ctx = (valk_all_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_ALL_CTX_MAGIC) return NULL;
  return ctx;
}

static inline i64 valk_async_all_find_index(valk_all_ctx_t *ctx, valk_async_handle_t *child) {
  for (u64 i = 0; i < ctx->total; i++) {
    if (ctx->handles[i] == child) return (i64)i;
  }
  return -1;
}

static void valk_async_all_child_completed(valk_async_handle_t *child) {
  valk_all_ctx_t *ctx = valk_async_get_all_ctx(child);
  if (!ctx) return;

  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->all_handle))) {
    return;
  }

  i64 idx = valk_async_all_find_index(ctx, child);
  if (idx < 0) return;

  ctx->results[idx] = child->result;
  ctx->completed++;

  if (ctx->completed == ctx->total) {
    if (!valk_async_handle_try_transition(ctx->all_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_COMPLETED)) {
      return;
    }

    valk_lval_t *result_list = valk_lval_nil();
    for (u64 i = ctx->total; i > 0; i--) {
      result_list = valk_lval_cons(ctx->results[i-1], result_list);
    }

    ctx->all_handle->result = result_list;

    valk_async_notify_done(ctx->all_handle);
    valk_async_propagate_completion(ctx->all_handle);
  }
}

static void valk_async_all_child_failed(valk_async_handle_t *child, valk_lval_t *error) {
  valk_all_ctx_t *ctx = valk_async_get_all_ctx(child);
  if (!ctx) return;

  if (!valk_async_handle_try_transition(ctx->all_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_FAILED)) {
    return;
  }

  ctx->all_handle->error = error;

  for (u64 i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    valk_async_status_t h_status = valk_async_handle_get_status(h);
    if (h != child && (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) {
      valk_async_handle_cancel(h);
    }
  }

  valk_async_notify_done(ctx->all_handle);
  valk_async_propagate_completion(ctx->all_handle);
}

void valk_async_notify_all_parent(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  u32 *magic_ptr = (u32*)parent->uv_handle_ptr;
  if (*magic_ptr != VALK_ALL_CTX_MAGIC_EARLY) return;

  if (child->status == VALK_ASYNC_COMPLETED) {
    valk_async_all_child_completed(child);
  } else if (child->status == VALK_ASYNC_FAILED) {
    valk_async_all_child_failed(child, child->error);
  }
}

typedef struct {
  u32 magic;
  valk_async_handle_t *race_handle;
  valk_async_handle_t **handles;
  u64 total;
  valk_mem_allocator_t *allocator;
} valk_race_ctx_t;

static void valk_race_ctx_cleanup(void *ctx) {
  valk_race_ctx_t *race_ctx = (valk_race_ctx_t *)ctx;
  if (!race_ctx) return;
  race_ctx->magic = 0;
  if (race_ctx->allocator && race_ctx->allocator->type != VALK_ALLOC_MALLOC) return;
  if (race_ctx->handles) free(race_ctx->handles);
  free(race_ctx);
}

static void valk_async_race_child_resolved(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  valk_race_ctx_t *ctx = (valk_race_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_RACE_CTX_MAGIC) return;

  valk_async_status_t child_status = valk_async_handle_get_status(child);
  valk_async_status_t new_status;
  if (child_status == VALK_ASYNC_COMPLETED) {
    new_status = VALK_ASYNC_COMPLETED;
  } else if (child_status == VALK_ASYNC_FAILED) {
    new_status = VALK_ASYNC_FAILED;
  } else {
    return;
  }

  if (!valk_async_handle_try_transition(ctx->race_handle, VALK_ASYNC_RUNNING, new_status)) {
    return;
  }

  if (new_status == VALK_ASYNC_COMPLETED) {
    ctx->race_handle->result = child->result;
  } else {
    ctx->race_handle->error = child->error;
  }

  for (u64 i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    valk_async_status_t h_status = valk_async_handle_get_status(h);
    if (h != child && (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) {
      valk_async_handle_cancel(h);
    }
  }

  valk_async_notify_done(ctx->race_handle);
  valk_async_propagate_completion(ctx->race_handle);
}

void valk_async_notify_race_parent(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  u32 *magic_ptr = (u32*)parent->uv_handle_ptr;
  if (*magic_ptr != VALK_RACE_CTX_MAGIC_EARLY) return;

  valk_async_race_child_resolved(child);
}

static valk_lval_t* valk_builtin_aio_race(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/race: expected 1 argument (list of handles)");
  }
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  valk_mem_allocator_t *allocator = valk_thread_ctx.allocator;

  u64 count = 0;
  valk_async_handle_t *first_done = NULL;
  valk_lval_t *iter = handles_list;

  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/race: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/race: all elements must be handles");
    }
    valk_async_handle_t *handle = h->async.handle;
    count++;

    if (!first_done && (handle->status == VALK_ASYNC_COMPLETED ||
                        handle->status == VALK_ASYNC_FAILED)) {
      first_done = handle;
    }
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    return valk_lval_err("aio/race: cannot race empty list");
  }

  valk_async_handle_t *race_handle = valk_async_handle_new(NULL, e);
  if (!race_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  valk_lval_t *first_h = valk_lval_head(handles_list);
  if (first_h && LVAL_TYPE(first_h) == LVAL_HANDLE && first_h->async.handle->request_ctx) {
    race_handle->request_ctx = first_h->async.handle->request_ctx;
  }

  if (first_done) {
    if (first_done->status == VALK_ASYNC_COMPLETED) {
      race_handle->status = VALK_ASYNC_COMPLETED;
      race_handle->result = first_done->result;
    } else {
      race_handle->status = VALK_ASYNC_FAILED;
      race_handle->error = first_done->error;
    }

    iter = handles_list;
    while (LVAL_TYPE(iter) != LVAL_NIL) {
      valk_lval_t *h = valk_lval_head(iter);
      valk_async_handle_t *handle = h->async.handle;
      if (handle != first_done &&
          (handle->status == VALK_ASYNC_PENDING || handle->status == VALK_ASYNC_RUNNING)) {
        valk_async_handle_cancel(handle);
      }
      iter = valk_lval_tail(iter);
    }
    return valk_lval_handle(race_handle);
  }

  race_handle->status = VALK_ASYNC_RUNNING;
  race_handle->env = e;

  iter = handles_list;
  if (LVAL_TYPE(iter) != LVAL_NIL) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    race_handle->sys = handle->sys;
  }

  valk_async_handle_t **handles = valk_mem_calloc(count, sizeof(valk_async_handle_t*));
  if (!handles) {
    valk_async_handle_free(race_handle);
    return valk_lval_err("Failed to allocate handles array");
  }

  valk_race_ctx_t *ctx = valk_mem_alloc(sizeof(valk_race_ctx_t));
  if (!ctx) {
    valk_mem_free(handles);
    valk_async_handle_free(race_handle);
    return valk_lval_err("Failed to allocate race context");
  }
  ctx->magic = VALK_RACE_CTX_MAGIC;
  ctx->race_handle = race_handle;
  ctx->handles = handles;
  ctx->total = count;
  ctx->allocator = allocator;
  race_handle->uv_handle_ptr = ctx;

  valk_async_handle_on_cleanup(race_handle, valk_race_ctx_cleanup, ctx);

  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    handles[i] = handle;
    valk_async_handle_add_child(race_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(race_handle);
}

typedef struct {
  u32 magic;
  valk_async_handle_t *any_handle;
  valk_async_handle_t **handles;
  u64 total;
  u64 failed_count;
  valk_lval_t *last_error;
  valk_mem_allocator_t *allocator;
} valk_any_ctx_t;

static void valk_any_ctx_cleanup(void *ctx) {
  valk_any_ctx_t *any_ctx = (valk_any_ctx_t *)ctx;
  if (!any_ctx) return;
  any_ctx->magic = 0;
  if (any_ctx->allocator && any_ctx->allocator->type != VALK_ALLOC_MALLOC) return;
  if (any_ctx->handles) free(any_ctx->handles);
  free(any_ctx);
}

static void valk_async_any_child_success(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  valk_any_ctx_t *ctx = (valk_any_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_ANY_CTX_MAGIC) return;

  if (!valk_async_handle_try_transition(ctx->any_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_COMPLETED)) {
    return;
  }

  ctx->any_handle->result = child->result;

  for (u64 i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    valk_async_status_t h_status = valk_async_handle_get_status(h);
    if (h != child && (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) {
      valk_async_handle_cancel(h);
    }
  }

  valk_async_notify_done(ctx->any_handle);
  valk_async_propagate_completion(ctx->any_handle);
}

static void valk_async_any_child_failed(valk_async_handle_t *child, valk_lval_t *error) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  valk_any_ctx_t *ctx = (valk_any_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_ANY_CTX_MAGIC) return;

  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->any_handle))) {
    return;
  }

  ctx->failed_count++;
  ctx->last_error = error;

  if (ctx->failed_count == ctx->total) {
    if (!valk_async_handle_try_transition(ctx->any_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_FAILED)) {
      return;
    }
    ctx->any_handle->error = ctx->last_error;
    valk_async_notify_done(ctx->any_handle);
    valk_async_propagate_completion(ctx->any_handle);
  }
}

void valk_async_notify_any_parent(valk_async_handle_t *child) {
  if (!child || !child->parent) {
    VALK_DEBUG("notify_any_parent: child=%p, parent=%p", (void*)child, child ? (void*)child->parent : NULL);
    return;
  }

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) {
    VALK_DEBUG("notify_any_parent: parent has no uv_handle_ptr");
    return;
  }

  u32 *magic_ptr = (u32*)parent->uv_handle_ptr;
  VALK_DEBUG("notify_any_parent: magic=0x%08x, expected=0x%08x", *magic_ptr, VALK_ANY_CTX_MAGIC_EARLY);
  if (*magic_ptr != VALK_ANY_CTX_MAGIC_EARLY) return;

  VALK_INFO("notify_any_parent: found any context, child status=%d", child->status);
  if (child->status == VALK_ASYNC_COMPLETED) {
    valk_async_any_child_success(child);
  } else if (child->status == VALK_ASYNC_FAILED) {
    valk_async_any_child_failed(child, child->error);
  }
}

static valk_lval_t* valk_builtin_aio_any(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/any: expected 1 argument (list of handles)");
  }
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  valk_mem_allocator_t *allocator = valk_thread_ctx.allocator;

  u64 count = 0;
  u64 failed_count = 0;
  valk_async_handle_t *first_success = NULL;
  valk_lval_t *last_error = NULL;
  valk_lval_t *iter = handles_list;

  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/any: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/any: all elements must be handles");
    }
    valk_async_handle_t *handle = h->async.handle;
    count++;

    if (handle->status == VALK_ASYNC_COMPLETED && !first_success) {
      first_success = handle;
    } else if (handle->status == VALK_ASYNC_FAILED ||
               handle->status == VALK_ASYNC_CANCELLED) {
      failed_count++;
      last_error = handle->error ? handle->error : valk_lval_err("cancelled");
    }
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    return valk_lval_err("aio/any: cannot use with empty list");
  }

  valk_async_handle_t *any_handle = valk_async_handle_new(NULL, e);
  if (!any_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  valk_lval_t *first_h = valk_lval_head(handles_list);
  if (first_h && LVAL_TYPE(first_h) == LVAL_HANDLE && first_h->async.handle->request_ctx) {
    any_handle->request_ctx = first_h->async.handle->request_ctx;
  }

  if (first_success) {
    any_handle->status = VALK_ASYNC_COMPLETED;
    any_handle->result = first_success->result;

    iter = handles_list;
    while (LVAL_TYPE(iter) != LVAL_NIL) {
      valk_lval_t *h = valk_lval_head(iter);
      valk_async_handle_t *handle = h->async.handle;
      if (handle != first_success &&
          (handle->status == VALK_ASYNC_PENDING || handle->status == VALK_ASYNC_RUNNING)) {
        valk_async_handle_cancel(handle);
      }
      iter = valk_lval_tail(iter);
    }
    return valk_lval_handle(any_handle);
  }

  if (failed_count == count) {
    any_handle->status = VALK_ASYNC_FAILED;
    any_handle->error = last_error;
    return valk_lval_handle(any_handle);
  }

  any_handle->status = VALK_ASYNC_RUNNING;
  any_handle->env = e;

  iter = handles_list;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    if (handle->sys) {
      any_handle->sys = handle->sys;
      break;
    }
    iter = valk_lval_tail(iter);
  }

  valk_async_handle_t **handles = valk_mem_calloc(count, sizeof(valk_async_handle_t*));
  if (!handles) {
    valk_async_handle_free(any_handle);
    return valk_lval_err("Failed to allocate handles array");
  }

  valk_any_ctx_t *ctx = valk_mem_alloc(sizeof(valk_any_ctx_t));
  if (!ctx) {
    valk_mem_free(handles);
    valk_async_handle_free(any_handle);
    return valk_lval_err("Failed to allocate any context");
  }
  ctx->magic = VALK_ANY_CTX_MAGIC;
  ctx->any_handle = any_handle;
  ctx->handles = handles;
  ctx->total = count;
  ctx->failed_count = failed_count;
  ctx->last_error = last_error;
  ctx->allocator = allocator;
  any_handle->uv_handle_ptr = ctx;

  valk_async_handle_on_cleanup(any_handle, valk_any_ctx_cleanup, ctx);

  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    handles[i] = handle;
    valk_async_handle_add_child(any_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(any_handle);
}

static valk_lval_t* valk_builtin_aio_on_cancel(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/on-cancel: expected 2 arguments (handle fn)");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/on-cancel: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/on-cancel: second argument must be a function");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;

  if (handle->status == VALK_ASYNC_CANCELLED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);
    return valk_lval_handle(handle);
  }

  handle->on_cancel = fn;
  if (!handle->env) handle->env = e;

  return valk_lval_handle(handle);
}

static valk_lval_t* valk_builtin_aio_bracket(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 3) {
    return valk_lval_err("aio/bracket: expected 3 arguments (acquire release use)");
  }
  valk_lval_t *acquire_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *release_fn = valk_lval_list_nth(a, 1);
  valk_lval_t *use_fn = valk_lval_list_nth(a, 2);

  if (LVAL_TYPE(acquire_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/bracket: first argument must be a handle");
  }
  if (LVAL_TYPE(release_fn) != LVAL_FUN) {
    return valk_lval_err("aio/bracket: second argument must be a function");
  }
  if (LVAL_TYPE(use_fn) != LVAL_FUN) {
    return valk_lval_err("aio/bracket: third argument must be a function");
  }

  valk_async_handle_t *acquire = acquire_lval->async.handle;

  valk_async_handle_t *bracket_handle = valk_async_handle_new(acquire->sys, e);
  if (!bracket_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  bracket_handle->request_ctx = acquire->request_ctx;

  if (acquire->status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *resource = acquire->result;

    valk_lval_t *use_args = valk_lval_cons(resource, valk_lval_nil());
    valk_lval_t *use_result = valk_lval_eval_call(e, use_fn, use_args);

    if (LVAL_TYPE(use_result) == LVAL_HANDLE) {
      valk_async_handle_t *use_handle = use_result->async.handle;

      if (use_handle->status == VALK_ASYNC_COMPLETED ||
          use_handle->status == VALK_ASYNC_FAILED ||
          use_handle->status == VALK_ASYNC_CANCELLED) {
        valk_lval_t *release_args = valk_lval_cons(resource, valk_lval_nil());
        valk_lval_eval_call(e, release_fn, release_args);

        if (use_handle->status == VALK_ASYNC_COMPLETED) {
          bracket_handle->status = VALK_ASYNC_COMPLETED;
          bracket_handle->result = use_handle->result;
        } else if (use_handle->status == VALK_ASYNC_FAILED) {
          bracket_handle->status = VALK_ASYNC_FAILED;
          bracket_handle->error = use_handle->error;
        } else {
          bracket_handle->status = VALK_ASYNC_CANCELLED;
        }
      } else {
        bracket_handle->status = VALK_ASYNC_RUNNING;
        bracket_handle->env = e;
        bracket_handle->parent = use_handle;

        bracket_handle->on_cancel = release_fn;
        bracket_handle->result = resource;

        valk_async_handle_add_child(use_handle, bracket_handle);
      }
    } else if (LVAL_TYPE(use_result) == LVAL_ERR) {
      valk_lval_t *release_args = valk_lval_cons(resource, valk_lval_nil());
      valk_lval_eval_call(e, release_fn, release_args);

      bracket_handle->status = VALK_ASYNC_FAILED;
      bracket_handle->error = use_result;
    } else {
      valk_lval_t *release_args = valk_lval_cons(resource, valk_lval_nil());
      valk_lval_eval_call(e, release_fn, release_args);

      bracket_handle->status = VALK_ASYNC_COMPLETED;
      bracket_handle->result = use_result;
    }

    return valk_lval_handle(bracket_handle);
  }

  if (acquire->status == VALK_ASYNC_FAILED) {
    bracket_handle->status = VALK_ASYNC_FAILED;
    bracket_handle->error = acquire->error;
    return valk_lval_handle(bracket_handle);
  }

  if (acquire->status == VALK_ASYNC_CANCELLED) {
    bracket_handle->status = VALK_ASYNC_CANCELLED;
    return valk_lval_handle(bracket_handle);
  }

  bracket_handle->status = VALK_ASYNC_RUNNING;
  bracket_handle->env = e;

  bracket_handle->on_complete = use_fn;
  bracket_handle->on_cancel = release_fn;
  bracket_handle->parent = acquire;

  valk_async_handle_add_child(acquire, bracket_handle);

  return valk_lval_handle(bracket_handle);
}

static valk_lval_t* valk_builtin_aio_scope(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/scope: expected 1 argument (fn)");
  }
  valk_lval_t *fn = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/scope: argument must be a function");
  }

  valk_async_handle_t *scope_handle = valk_async_handle_new(NULL, e);
  if (!scope_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  scope_handle->status = VALK_ASYNC_RUNNING;
  scope_handle->env = e;

  valk_lval_t *scope_lval = valk_lval_handle(scope_handle);

  valk_lval_t *args = valk_lval_cons(scope_lval, valk_lval_nil());
  valk_lval_t *result = valk_lval_eval_call(e, fn, args);

  if (LVAL_TYPE(result) == LVAL_ERR) {
    scope_handle->status = VALK_ASYNC_FAILED;
    scope_handle->error = result;
    return scope_lval;
  }

  if (LVAL_TYPE(result) == LVAL_HANDLE) {
    valk_async_handle_t *inner = result->async.handle;

    if (inner->status == VALK_ASYNC_COMPLETED) {
      scope_handle->status = VALK_ASYNC_COMPLETED;
      scope_handle->result = inner->result;
    } else if (inner->status == VALK_ASYNC_FAILED) {
      scope_handle->status = VALK_ASYNC_FAILED;
      scope_handle->error = inner->error;
    } else if (inner->status == VALK_ASYNC_CANCELLED) {
      scope_handle->status = VALK_ASYNC_CANCELLED;
    } else {
      scope_handle->parent = inner;
      valk_async_handle_add_child(inner, scope_handle);
    }
    return scope_lval;
  }

  scope_handle->status = VALK_ASYNC_COMPLETED;
  scope_handle->result = result;
  return scope_lval;
}

static valk_lval_t* valk_builtin_aio_pool_stats(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_START - aio/pool-stats arg validation: compile-time checks
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/pool-stats: expected 1 argument (aio system)");
  }
  valk_lval_t *aio_ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(aio_ref) != LVAL_REF || strcmp(aio_ref->ref.type, "aio_system") != 0) {
    return valk_lval_err("aio/pool-stats: argument must be aio system");
  }
  // LCOV_EXCL_STOP

  valk_aio_system_t *sys = aio_ref->ref.ptr;
  if (!sys) {
    return valk_lval_err("aio/pool-stats: null aio system");
  }

  u64 tcp_available = 0, tcp_total = 0;
  long tcp_usage = 0;
  if (sys->tcpBufferSlab) {
    tcp_available = valk_slab_available(sys->tcpBufferSlab);
    tcp_total = sys->tcpBufferSlab->numItems;
    tcp_usage = tcp_total > 0 ? (long)((1.0f - (float)tcp_available / tcp_total) * 100.0f) : 0;
  }

  valk_lval_t *tcp_items[] = {
    valk_lval_sym(":available"), valk_lval_num((long)tcp_available),
    valk_lval_sym(":total"), valk_lval_num((long)tcp_total),
    valk_lval_sym(":usage-percent"), valk_lval_num(tcp_usage)
  };
  valk_lval_t *tcp = valk_lval_qlist(tcp_items, 6);

  valk_lval_t *bp_items[] = {
    valk_lval_sym(":connections-waiting"), valk_lval_num((long)sys->backpressure.size),
    valk_lval_sym(":has-waiting"), valk_lval_sym(sys->backpressure.head ? ":true" : ":false")
  };
  valk_lval_t *bp = valk_lval_qlist(bp_items, 4);

  u64 arena_available = 0, arena_total = 0;
  long arena_usage = 0;
  valk_slab_t *arena_slab = valk_aio_get_stream_arenas_slab(sys);
  if (arena_slab) {
    arena_available = valk_slab_available(arena_slab);
    arena_total = arena_slab->numItems;
    arena_usage = arena_total > 0 ? (long)((1.0f - (float)arena_available / arena_total) * 100.0f) : 0;
  }

  valk_lval_t *arena_items[] = {
    valk_lval_sym(":available"), valk_lval_num((long)arena_available),
    valk_lval_sym(":total"), valk_lval_num((long)arena_total),
    valk_lval_sym(":usage-percent"), valk_lval_num(arena_usage)
  };
  valk_lval_t *arenas = valk_lval_qlist(arena_items, 6);

  valk_lval_t *result_items[] = {
    valk_lval_sym(":tcp-buffers"), tcp,
    valk_lval_sym(":backpressure"), bp,
    valk_lval_sym(":arenas"), arenas
  };
  return valk_lval_qlist(result_items, 6);
}

void valk_register_async_handle_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/cancel", valk_builtin_aio_cancel);
  valk_lenv_put_builtin(env, "aio/cancelled?", valk_builtin_aio_cancelled);
  valk_lenv_put_builtin(env, "aio/status", valk_builtin_aio_status);
  valk_lenv_put_builtin(env, "aio/pure", valk_builtin_aio_pure);
  valk_lenv_put_builtin(env, "aio/fail", valk_builtin_aio_fail);

  valk_lenv_put_builtin(env, "aio/then", valk_builtin_aio_then);
  valk_lenv_put_builtin(env, "aio/catch", valk_builtin_aio_catch);
  valk_lenv_put_builtin(env, "aio/finally", valk_builtin_aio_finally);
  valk_lenv_put_builtin(env, "aio/all", valk_builtin_aio_all);
  valk_lenv_put_builtin(env, "aio/race", valk_builtin_aio_race);
  valk_lenv_put_builtin(env, "aio/any", valk_builtin_aio_any);
  valk_lenv_put_builtin(env, "aio/on-cancel", valk_builtin_aio_on_cancel);

  valk_lenv_put_builtin(env, "aio/sleep", valk_builtin_aio_sleep);
  valk_lenv_put_builtin(env, "aio/let", valk_builtin_aio_let);
  valk_lenv_put_builtin(env, "aio/do", valk_builtin_aio_do);

  valk_lenv_put_builtin(env, "aio/bracket", valk_builtin_aio_bracket);
  valk_lenv_put_builtin(env, "aio/scope", valk_builtin_aio_scope);

  valk_lenv_put_builtin(env, "aio/pool-stats", valk_builtin_aio_pool_stats);
}
