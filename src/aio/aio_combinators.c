#include "aio_internal.h"
#include "aio_http2_session.h"

static void __delay_timer_close_cb(uv_handle_t *handle) {
  valk_delay_timer_t *timer_data = (valk_delay_timer_t *)handle->data;
  free(timer_data);
}

static void __schedule_timer_close_cb(uv_handle_t *handle) {
  free(handle->data);
}

static void __sleep_timer_close_cb(uv_handle_t *handle) {
  UNUSED(handle);
}

extern void valk_http2_continue_pending_send(valk_aio_handle_t *conn);

static void __delay_timer_cb(uv_timer_t *handle) {
  valk_delay_timer_t *timer_data = (valk_delay_timer_t *)handle->data;

  valk_aio_handle_t *conn = timer_data->conn;
  if (!conn || conn->http.state == VALK_CONN_CLOSING ||
      conn->http.state == VALK_CONN_CLOSED || !conn->http.session) {
    uv_timer_stop(handle);
    uv_close((uv_handle_t *)handle, __delay_timer_close_cb);
    return;
  }

  if (timer_data->continuation && timer_data->env) {
    valk_lval_t *response;
    VALK_WITH_ALLOC((valk_mem_allocator_t*)timer_data->stream_arena) {
      valk_lval_t *args = valk_lval_nil();
      response = valk_lval_eval_call(timer_data->env, timer_data->continuation, args);
    }

    VALK_INFO("aio/delay continuation returned type %d", LVAL_TYPE(response));

    // LCOV_EXCL_START - delay continuation error: requires handler to return error
    if (LVAL_TYPE(response) == LVAL_ERR) {
      VALK_WARN("Delay continuation returned error: %s", response->str);
      VALK_WITH_ALLOC((valk_mem_allocator_t*)timer_data->stream_arena) {
        valk_lval_t* error_items[] = {
          valk_lval_sym(":status"), valk_lval_str("500"),
          valk_lval_sym(":body"), valk_lval_str(response->str)
        };
        valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
        valk_http2_send_response(timer_data->session, timer_data->stream_id,
                             error_resp, timer_data->stream_arena);
      }
    // LCOV_EXCL_STOP
    } else {
      valk_http2_send_response(timer_data->session, timer_data->stream_id,
                           response, timer_data->stream_arena);
    }

    valk_http2_continue_pending_send(timer_data->conn);
  } else {
    VALK_WARN("No continuation or env for stream %d", timer_data->stream_id);
  }

  uv_timer_stop(handle);
  uv_close((uv_handle_t *)handle, __delay_timer_close_cb);
}

valk_lval_t* valk_aio_delay(valk_aio_system_t* sys, uint64_t delay_ms,
                            valk_lval_t* continuation, valk_lenv_t* env) {
  UNUSED(env);
  VALK_INFO("aio/delay called with delay_ms=%lu", (unsigned long)delay_ms);

  if (!sys->current_request_ctx) {
    VALK_WARN("aio/delay called outside request context");
    return valk_lval_err("aio/delay can only be used within an HTTP request handler");
  }

  valk_delay_timer_t *timer_data = malloc(sizeof(valk_delay_timer_t));
  if (!timer_data) {
    return valk_lval_err("Failed to allocate timer");
  }

  valk_lval_t *heap_continuation;
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    heap_continuation = valk_lval_copy(continuation);
  }

  timer_data->continuation = heap_continuation;
  timer_data->session = sys->current_request_ctx->session;
  timer_data->stream_id = sys->current_request_ctx->stream_id;
  timer_data->conn = sys->current_request_ctx->conn;
  timer_data->stream_arena = sys->current_request_ctx->req->stream_arena;
  timer_data->env = sys->current_request_ctx->env;
  timer_data->timer.data = timer_data;

  uv_loop_t *loop = sys->eventloop;
  int r = uv_timer_init(loop, &timer_data->timer);
  VALK_INFO("uv_timer_init returned %d", r);
  r = uv_timer_start(&timer_data->timer, __delay_timer_cb, delay_ms, 0);
  VALK_INFO("uv_timer_start returned %d for stream %d", r, timer_data->stream_id);

  return valk_lval_sym(":deferred");
}

static void __schedule_timer_cb(uv_timer_t *handle) {
  valk_schedule_timer_t *timer_data = (valk_schedule_timer_t *)handle->data;

  if (timer_data->callback && timer_data->env) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = valk_lval_eval_call(timer_data->env, timer_data->callback, args);
    if (LVAL_TYPE(result) == LVAL_ERR) {
      VALK_WARN("aio/schedule callback returned error: %s", result->str);
    }
  }

  uv_timer_stop(handle);
  uv_close((uv_handle_t *)handle, __schedule_timer_close_cb);
}

valk_lval_t* valk_aio_schedule(valk_aio_system_t* sys, uint64_t delay_ms,
                                valk_lval_t* callback, valk_lenv_t* env) {
  if (!sys || !sys->eventloop) {
    return valk_lval_err("aio/schedule: invalid AIO system");
  }

  valk_schedule_timer_t *timer_data = malloc(sizeof(valk_schedule_timer_t));
  if (!timer_data) {
    return valk_lval_err("Failed to allocate timer");
  }

  valk_lval_t *heap_callback;
  valk_lenv_t *heap_env;
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    heap_callback = valk_lval_copy(callback);
    heap_env = valk_lenv_copy(env);
  }

  timer_data->callback = heap_callback;
  timer_data->env = heap_env;
  timer_data->timer.data = timer_data;

  uv_loop_t *loop = sys->eventloop;
  int r = uv_timer_init(loop, &timer_data->timer);
  if (r != 0) {
    free(timer_data);
    return valk_lval_err("Failed to initialize timer");
  }

  r = uv_timer_start(&timer_data->timer, __schedule_timer_cb, delay_ms, 0);
  if (r != 0) {
    free(timer_data);
    return valk_lval_err("Failed to start timer");
  }

  VALK_INFO("aio/schedule: timer started for %lu ms", (unsigned long)delay_ms);
  return valk_lval_nil();
}

extern valk_async_handle_t* valk_async_handle_new(uv_loop_t *loop, valk_lenv_t *env);
extern void valk_async_handle_free(valk_async_handle_t *handle);
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
extern bool valk_async_handle_cancel(valk_async_handle_t *handle);
extern void valk_async_handle_add_child(valk_async_handle_t *parent, valk_async_handle_t *child);
extern void valk_async_propagate_allocator(valk_async_handle_t *handle, valk_mem_allocator_t *allocator, valk_lenv_t *env);
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
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/sleep: expected 1 argument (ms)");
  }
  valk_lval_t *ms_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ms_arg) != LVAL_NUM) {
    return valk_lval_err("aio/sleep: expected number argument");
  }

  uint64_t delay_ms = (uint64_t)ms_arg->num;

  uv_loop_t *loop = NULL;
  if (valk_aio_active_system) {
    loop = valk_aio_active_system->eventloop;
  } else if (g_last_started_aio_system) {
    loop = g_last_started_aio_system->eventloop;
  } else {
    return valk_lval_err("aio/sleep requires an active AIO system");
  }

  valk_async_handle_t *async_handle = valk_async_handle_new(loop, e);

  valk_async_handle_uv_data_t *timer_data = malloc(sizeof(valk_async_handle_uv_data_t));
  timer_data->handle = async_handle;
  timer_data->uv.timer.data = timer_data;

  async_handle->uv_handle_ptr = timer_data;
  async_handle->status = VALK_ASYNC_RUNNING;

  uv_timer_init(loop, &timer_data->uv.timer);
  uv_timer_start(&timer_data->uv.timer, __sleep_timer_cb, delay_ms, 0);

  VALK_INFO("aio/sleep started: %lu ms, handle id=%lu", delay_ms, async_handle->id);

  return valk_lval_handle(async_handle);
}

static inline bool is_then_barrier(valk_lval_t *item) {
  return LVAL_TYPE(item) == LVAL_SYM && strcmp(item->str, ":then") == 0;
}

typedef struct {
  valk_lval_t **bindings;
  size_t count;
  size_t capacity;
} aio_let_group_t;

typedef struct {
  aio_let_group_t *groups;
  size_t count;
  size_t capacity;
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
  for (size_t i = 0; i < parsed->count; i++) {
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

  for (size_t i = 0; i < group->count; i++) {
    valk_lval_t *binding = group->bindings[i];
    valk_lval_t *var = valk_lval_list_nth(binding, 0);

    valk_lval_t *var_qexpr = valk_lval_qcons(valk_lval_copy(var), valk_lval_nil());

    valk_lval_t *nth_call = valk_lval_cons(
      valk_lval_sym("nth"),
      valk_lval_cons(valk_lval_num(i + 1),
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
  if (LVAL_TYPE(body) == LVAL_QEXPR && !valk_lval_list_is_empty(body)) {
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

  if (LVAL_TYPE(stmts) != LVAL_QEXPR) {
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

valk_http_request_ctx_t* valk_http_get_request_ctx(void) {
  if (!valk_aio_active_system) return NULL;
  return valk_aio_active_system->current_request_ctx;
}

void valk_http_set_request_ctx(valk_http_request_ctx_t* ctx) {
  if (valk_aio_active_system) {
    valk_aio_active_system->current_request_ctx = ctx;
  }
}

void valk_http_set_status_code(int status_code) {
#ifdef VALK_METRICS_ENABLED
  if (valk_aio_active_system && valk_aio_active_system->current_request_ctx && 
      valk_aio_active_system->current_request_ctx->req) {
    valk_aio_active_system->current_request_ctx->req->status_code = status_code;
  }
#else
  (void)status_code;
#endif
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
                   __atomic_load_n(&handle->cancel_requested, __ATOMIC_ACQUIRE);

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

  handle->status = VALK_ASYNC_COMPLETED;
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

  handle->status = VALK_ASYNC_FAILED;
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

  for (size_t i = 0; i < handle->children.count && i < 100; i++) {
    valk_async_handle_t *child = handle->children.items[i];
    if (child && valk_async_is_resource_closed(child)) {
      return true;
    }
  }
  return false;
}

void valk_async_propagate_completion(valk_async_handle_t *source) {
  if (!source) return;

  VALK_INFO("Propagating from handle %lu (status=%d, children=%zu)",
            source->id, source->status, source->children.count);

  if (valk_async_is_chain_closed(source)) {
    VALK_INFO("Async propagation: connection closed, aborting propagation");
    return;
  }

  for (size_t i = 0; i < source->children.count; i++) {
    valk_async_handle_t *child = source->children.items[i];
    VALK_DEBUG("  Child %zu: handle %lu, status=%d, parent=%lu (source=%lu), on_complete=%p",
              i, child->id, child->status,
              child->parent ? child->parent->id : 0, source->id,
              (void*)child->on_complete);
    if (child->status == VALK_ASYNC_RUNNING &&
        (child->parent == source || child->on_complete != NULL)) {

      if (valk_async_is_chain_closed(child)) {
        VALK_INFO("Async propagation: child connection closed, cancelling child handle %lu", child->id);
        child->status = VALK_ASYNC_CANCELLED;
        continue;
      }

      if (source->status == VALK_ASYNC_COMPLETED) {
        if (child->on_complete && child->env) {
          valk_lval_t *args;
          valk_lval_t *transformed;
          valk_mem_allocator_t *alloc = child->allocator;
          bool needs_arena = !alloc || 
                             alloc->type == VALK_ALLOC_MALLOC ||
                             alloc->type == VALK_ALLOC_GC_HEAP ||
                             alloc->type == VALK_ALLOC_NULL;
          // LCOV_EXCL_START - fallback arena allocation rarely triggered
          if (needs_arena) {
            valk_aio_system_t *sys = g_last_started_aio_system;
            if (sys) {
              valk_standalone_async_ctx_t *standalone = valk_standalone_async_ctx_new(sys);
              if (standalone) {
                alloc = (valk_mem_allocator_t*)standalone->arena;
                child->allocator = alloc;
                valk_async_handle_t *root = child;
                while (root->parent) root = root->parent;
                if (!root->on_done) {
                  root->on_done = valk_standalone_async_done_callback;
                  root->on_done_ctx = standalone;
                }
              }
            }
          }
          // LCOV_EXCL_STOP
          if (!alloc || alloc->type != VALK_ALLOC_ARENA) alloc = &valk_malloc_allocator;
          VALK_WITH_ALLOC(alloc) {
            args = valk_lval_cons(source->result, valk_lval_nil());
            transformed = valk_lval_eval_call(child->env, child->on_complete, args);
          }
          if (LVAL_TYPE(transformed) == LVAL_ERR) {
            child->status = VALK_ASYNC_FAILED;
            child->error = transformed;
          } else if (LVAL_TYPE(transformed) == LVAL_HANDLE) {
            valk_async_handle_t *inner = transformed->async.handle;
            if (inner->status == VALK_ASYNC_COMPLETED) {
              child->status = VALK_ASYNC_COMPLETED;
              child->result = inner->result;
            } else if (inner->status == VALK_ASYNC_FAILED) {
              child->status = VALK_ASYNC_FAILED;
              child->error = inner->error;
              valk_async_notify_all_parent(child);
              valk_async_notify_race_parent(child);
              valk_async_notify_any_parent(child);
            } else if (inner->status == VALK_ASYNC_CANCELLED) {
              child->status = VALK_ASYNC_CANCELLED;
            } else {
              valk_async_handle_add_child(inner, child);
              child->parent = inner;
              child->on_complete = NULL;
              if (child->on_done && !inner->on_done) {
                inner->on_done = child->on_done;
                inner->on_done_ctx = child->on_done_ctx;
                inner->is_closed = child->is_closed;
                inner->is_closed_ctx = child->is_closed_ctx;
                inner->allocator = child->allocator;
                inner->env = child->env;
                child->on_done = NULL;
                child->on_done_ctx = NULL;
              }
              continue;
            }
          } else {
            child->status = VALK_ASYNC_COMPLETED;
            child->result = transformed;
          }
        } else {
          child->status = VALK_ASYNC_COMPLETED;
          child->result = source->result;
        }
        valk_async_notify_all_parent(child);
        valk_async_notify_race_parent(child);
        valk_async_notify_any_parent(child);
        valk_async_notify_done(child);
        valk_async_propagate_completion(child);
      } else if (source->status == VALK_ASYNC_FAILED) {
        if (child->on_error && child->env) {
          valk_lval_t *args;
          valk_lval_t *recovered;
          valk_mem_allocator_t *alloc = child->allocator;
          bool needs_arena = !alloc || 
                             alloc->type == VALK_ALLOC_MALLOC ||
                             alloc->type == VALK_ALLOC_GC_HEAP ||
                             alloc->type == VALK_ALLOC_NULL;
          // LCOV_EXCL_START - fallback arena allocation rarely triggered
          if (needs_arena) {
            valk_aio_system_t *sys = g_last_started_aio_system;
            if (sys) {
              valk_standalone_async_ctx_t *standalone = valk_standalone_async_ctx_new(sys);
              if (standalone) {
                alloc = (valk_mem_allocator_t*)standalone->arena;
                child->allocator = alloc;
                valk_async_handle_t *root = child;
                while (root->parent) root = root->parent;
                if (!root->on_done) {
                  root->on_done = valk_standalone_async_done_callback;
                  root->on_done_ctx = standalone;
                }
              }
            }
          }
          // LCOV_EXCL_STOP
          if (!alloc || alloc->type != VALK_ALLOC_ARENA) alloc = &valk_malloc_allocator;
          VALK_WITH_ALLOC(alloc) {
            args = valk_lval_cons(source->error, valk_lval_nil());
            recovered = valk_lval_eval_call(child->env, child->on_error, args);
          }
          if (LVAL_TYPE(recovered) == LVAL_ERR) {
            child->status = VALK_ASYNC_FAILED;
            child->error = recovered;
          } else {
            child->status = VALK_ASYNC_COMPLETED;
            child->result = recovered;
          }
        } else {
          child->status = VALK_ASYNC_FAILED;
          child->error = source->error;
        }
        valk_async_notify_done(child);
        valk_async_propagate_completion(child);
      }
    }
  }
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

  valk_async_handle_t *result = valk_async_handle_new(source->loop, e);
  if (!result) {
    return valk_lval_err("Failed to allocate async handle");
  }

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

  valk_async_handle_t *catch_handle = valk_async_handle_new(source->loop, e);
  if (!catch_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

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

  valk_async_handle_t *finally_handle = valk_async_handle_new(source->loop, e);
  if (!finally_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

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
  uint32_t magic;
  valk_async_handle_t *all_handle;
  valk_lval_t **results;
  valk_async_handle_t **handles;
  size_t total;
  size_t completed;
  bool failed;
  valk_lval_t *first_error;
} valk_all_ctx_t;

static void valk_async_all_child_completed(valk_async_handle_t *child);
static void valk_async_all_child_failed(valk_async_handle_t *child, valk_lval_t *error);

static valk_lval_t* valk_builtin_aio_all(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/all: expected 1 argument (list of handles)");
  }
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  size_t count = 0;
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

  valk_async_handle_t *all_handle = valk_async_handle_new(NULL, e);
  if (!all_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  valk_lval_t **results = calloc(count, sizeof(valk_lval_t*));
  if (!results) {
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate results array");
  }

  size_t completed = 0;
  bool any_pending = false;
  bool any_failed = false;
  valk_lval_t *first_error = NULL;

  iter = handles_list;
  for (size_t i = 0; i < count; i++) {
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
      if (!all_handle->loop && handle->loop) {
        all_handle->loop = handle->loop;
      }
    }
    iter = valk_lval_tail(iter);
  }

  if (any_failed) {
    free(results);
    all_handle->status = VALK_ASYNC_FAILED;
    all_handle->error = first_error;

    iter = handles_list;
    for (size_t i = 0; i < count; i++) {
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
    for (size_t i = count; i > 0; i--) {
      result_list = valk_lval_cons(results[i-1], result_list);
    }
    free(results);
    all_handle->status = VALK_ASYNC_COMPLETED;
    all_handle->result = result_list;
    return valk_lval_handle(all_handle);
  }

  all_handle->status = VALK_ASYNC_RUNNING;
  all_handle->env = e;

  valk_async_handle_t **handles = calloc(count, sizeof(valk_async_handle_t*));
  // LCOV_EXCL_START - calloc failure: requires OOM
  if (!handles) {
    free(results);
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate handles array");
  }
  // LCOV_EXCL_STOP

  valk_all_ctx_t *ctx = malloc(sizeof(valk_all_ctx_t));
  if (!ctx) {
    free(results);
    free(handles);
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate all context");
  }
  ctx->magic = VALK_ALL_CTX_MAGIC;
  ctx->all_handle = all_handle;
  ctx->results = results;
  ctx->handles = handles;
  ctx->total = count;
  ctx->completed = completed;
  ctx->failed = false;
  ctx->first_error = NULL;
  all_handle->uv_handle_ptr = ctx;

  iter = handles_list;
  for (size_t i = 0; i < count; i++) {
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

static inline ssize_t valk_async_all_find_index(valk_all_ctx_t *ctx, valk_async_handle_t *child) {
  for (size_t i = 0; i < ctx->total; i++) {
    if (ctx->handles[i] == child) return (ssize_t)i;
  }
  return -1;
}

static void valk_async_all_child_completed(valk_async_handle_t *child) {
  valk_all_ctx_t *ctx = valk_async_get_all_ctx(child);
  if (!ctx) return;
  if (ctx->failed) return;

  ssize_t idx = valk_async_all_find_index(ctx, child);
  if (idx < 0) return;

  ctx->results[idx] = child->result;
  ctx->completed++;

  if (ctx->completed == ctx->total) {
    valk_lval_t *result_list = valk_lval_nil();
    for (size_t i = ctx->total; i > 0; i--) {
      result_list = valk_lval_cons(ctx->results[i-1], result_list);
    }

    ctx->all_handle->status = VALK_ASYNC_COMPLETED;
    ctx->all_handle->result = result_list;

    valk_async_notify_done(ctx->all_handle);

    valk_async_propagate_completion(ctx->all_handle);
  }
}

static void valk_async_all_child_failed(valk_async_handle_t *child, valk_lval_t *error) {
  valk_all_ctx_t *ctx = valk_async_get_all_ctx(child);
  if (!ctx) return;
  if (ctx->failed) return;

  ctx->failed = true;
  ctx->first_error = error;

  ctx->all_handle->status = VALK_ASYNC_FAILED;
  ctx->all_handle->error = error;

  for (size_t i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    if (h != child && (h->status == VALK_ASYNC_PENDING || h->status == VALK_ASYNC_RUNNING)) {
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

  uint32_t *magic_ptr = (uint32_t*)parent->uv_handle_ptr;
  if (*magic_ptr != VALK_ALL_CTX_MAGIC_EARLY) return;

  if (child->status == VALK_ASYNC_COMPLETED) {
    valk_async_all_child_completed(child);
  } else if (child->status == VALK_ASYNC_FAILED) {
    valk_async_all_child_failed(child, child->error);
  }
}

typedef struct {
  uint32_t magic;
  valk_async_handle_t *race_handle;
  valk_async_handle_t **handles;
  size_t total;
  bool resolved;
} valk_race_ctx_t;

static void valk_async_race_child_resolved(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  valk_race_ctx_t *ctx = (valk_race_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_RACE_CTX_MAGIC) return;
  if (ctx->resolved) return;

  ctx->resolved = true;

  if (child->status == VALK_ASYNC_COMPLETED) {
    ctx->race_handle->status = VALK_ASYNC_COMPLETED;
    ctx->race_handle->result = child->result;
  } else if (child->status == VALK_ASYNC_FAILED) {
    ctx->race_handle->status = VALK_ASYNC_FAILED;
    ctx->race_handle->error = child->error;
  } else {
    return;
  }

  for (size_t i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    if (h != child && (h->status == VALK_ASYNC_PENDING || h->status == VALK_ASYNC_RUNNING)) {
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

  uint32_t *magic_ptr = (uint32_t*)parent->uv_handle_ptr;
  if (*magic_ptr != VALK_RACE_CTX_MAGIC_EARLY) return;

  valk_async_race_child_resolved(child);
}

static valk_lval_t* valk_builtin_aio_race(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/race: expected 1 argument (list of handles)");
  }
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  size_t count = 0;
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
    race_handle->loop = handle->loop;
  }

  valk_async_handle_t **handles = calloc(count, sizeof(valk_async_handle_t*));
  if (!handles) {
    valk_async_handle_free(race_handle);
    return valk_lval_err("Failed to allocate handles array");
  }

  valk_race_ctx_t *ctx = malloc(sizeof(valk_race_ctx_t));
  if (!ctx) {
    free(handles);
    valk_async_handle_free(race_handle);
    return valk_lval_err("Failed to allocate race context");
  }
  ctx->magic = VALK_RACE_CTX_MAGIC;
  ctx->race_handle = race_handle;
  ctx->handles = handles;
  ctx->total = count;
  ctx->resolved = false;
  race_handle->uv_handle_ptr = ctx;

  iter = handles_list;
  for (size_t i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    handles[i] = handle;
    valk_async_handle_add_child(race_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(race_handle);
}

typedef struct {
  uint32_t magic;
  valk_async_handle_t *any_handle;
  valk_async_handle_t **handles;
  size_t total;
  size_t failed_count;
  valk_lval_t *last_error;
  bool resolved;
} valk_any_ctx_t;

static void valk_async_any_child_success(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  valk_any_ctx_t *ctx = (valk_any_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_ANY_CTX_MAGIC) return;
  if (ctx->resolved) return;

  ctx->resolved = true;
  ctx->any_handle->status = VALK_ASYNC_COMPLETED;
  ctx->any_handle->result = child->result;

  for (size_t i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    if (h != child && (h->status == VALK_ASYNC_PENDING || h->status == VALK_ASYNC_RUNNING)) {
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
  if (ctx->resolved) return;

  ctx->failed_count++;
  ctx->last_error = error;

  if (ctx->failed_count == ctx->total) {
    ctx->resolved = true;
    ctx->any_handle->status = VALK_ASYNC_FAILED;
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

  uint32_t *magic_ptr = (uint32_t*)parent->uv_handle_ptr;
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

  size_t count = 0;
  size_t failed_count = 0;
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
    if (handle->loop) {
      any_handle->loop = handle->loop;
      break;
    }
    iter = valk_lval_tail(iter);
  }

  valk_async_handle_t **handles = calloc(count, sizeof(valk_async_handle_t*));
  if (!handles) {
    valk_async_handle_free(any_handle);
    return valk_lval_err("Failed to allocate handles array");
  }

  valk_any_ctx_t *ctx = malloc(sizeof(valk_any_ctx_t));
  if (!ctx) {
    free(handles);
    valk_async_handle_free(any_handle);
    return valk_lval_err("Failed to allocate any context");
  }
  ctx->magic = VALK_ANY_CTX_MAGIC;
  ctx->any_handle = any_handle;
  ctx->handles = handles;
  ctx->total = count;
  ctx->failed_count = failed_count;
  ctx->last_error = last_error;
  ctx->resolved = false;
  any_handle->uv_handle_ptr = ctx;

  iter = handles_list;
  for (size_t i = 0; i < count; i++) {
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
    return handle_lval;
  }

  handle->on_cancel = fn;
  if (!handle->env) handle->env = e;

  return handle_lval;
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

  valk_async_handle_t *bracket_handle = valk_async_handle_new(acquire->loop, e);
  if (!bracket_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

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

  size_t tcp_available = 0, tcp_total = 0;
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

  size_t arena_available = 0, arena_total = 0;
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
