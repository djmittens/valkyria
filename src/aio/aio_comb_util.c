#include "aio_combinators_internal.h"

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
  // LCOV_EXCL_BR_START - defensive null check
  if (!sys) {
    return valk_lval_err("aio/pool-stats: null aio system");
  }
  // LCOV_EXCL_BR_STOP

  u64 tcp_available = 0, tcp_total = 0;
  long tcp_usage = 0;
  // LCOV_EXCL_BR_START - slab availability: depends on sys configuration
  if (sys->tcpBufferSlab) {
    tcp_available = valk_slab_available(sys->tcpBufferSlab);
    tcp_total = sys->tcpBufferSlab->numItems;
    tcp_usage = tcp_total > 0 ? (long)((1.0f - (float)tcp_available / tcp_total) * 100.0f) : 0;
  }
  // LCOV_EXCL_BR_STOP

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
  // LCOV_EXCL_BR_START - arena slab availability: depends on sys configuration
  valk_slab_t *arena_slab = valk_aio_get_stream_arenas_slab(sys);
  if (arena_slab) {
    arena_available = valk_slab_available(arena_slab);
    arena_total = arena_slab->numItems;
    arena_usage = arena_total > 0 ? (long)((1.0f - (float)arena_available / arena_total) * 100.0f) : 0;
  }
  // LCOV_EXCL_BR_STOP

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

static valk_lval_t* valk_builtin_aio_traverse(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/traverse: expected 2 arguments (list fn)");
  }
  valk_lval_t *list_arg = valk_lval_list_nth(a, 0);
  valk_lval_t *fn_arg = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(fn_arg) != LVAL_FUN) {
    return valk_lval_err("aio/traverse: second argument must be a function");
  }

  valk_lval_t *handles = valk_lval_nil();
  valk_lval_t *current = list_arg;
  
  while (LVAL_TYPE(current) != LVAL_NIL) {
    if (LVAL_TYPE(current) != LVAL_CONS && LVAL_TYPE(current) != LVAL_QEXPR) {
      return valk_lval_err("aio/traverse: first argument must be a list");
    }
    
    valk_lval_t *item = valk_lval_head(current);
    valk_lval_t *args = valk_lval_cons(item, valk_lval_nil());
    valk_lval_t *handle = valk_lval_eval_call(e, fn_arg, args);
    
    if (LVAL_TYPE(handle) == LVAL_ERR) {
      return handle;
    }
    
    if (LVAL_TYPE(handle) != LVAL_HANDLE) {
      return valk_lval_err("aio/traverse: function must return handles (got type %d for item)", LVAL_TYPE(handle));
    }
    
    handles = valk_lval_cons(handle, handles);
    current = valk_lval_tail(current);
  }
  
  valk_lval_t *handles_reversed = valk_lval_nil();
  while (LVAL_TYPE(handles) != LVAL_NIL) {
    handles_reversed = valk_lval_cons(valk_lval_head(handles), handles_reversed);
    handles = valk_lval_tail(handles);
  }

  valk_lval_t *list_call = valk_lval_cons(valk_lval_sym("list"), handles_reversed);
  valk_lval_t *handles_list = valk_lval_eval(e, list_call);
  
  if (LVAL_TYPE(handles_list) == LVAL_ERR) {
    return handles_list;
  }

  valk_lval_t *all_call = valk_lval_cons(
    valk_lval_sym("aio/all"),
    valk_lval_cons(handles_list, valk_lval_nil()));

  return valk_lval_eval(e, all_call);
}

void valk_register_comb_util(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/pool-stats", valk_builtin_aio_pool_stats);
  valk_lenv_put_builtin(env, "aio/traverse", valk_builtin_aio_traverse);
}
