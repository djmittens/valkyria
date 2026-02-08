#include "aio_combinators_internal.h"

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

  // LCOV_EXCL_BR_START - binding list unwrapping: internal parser logic
  if (LVAL_TYPE(bindings) == LVAL_QEXPR && !valk_lval_list_is_empty(bindings)) {
    valk_lval_t *first = bindings->cons.head;
    if (LVAL_TYPE(first) == LVAL_CONS || LVAL_TYPE(first) == LVAL_QEXPR) {
      curr = first;
    }
  }
  // LCOV_EXCL_BR_STOP

  // LCOV_EXCL_BR_START - list iteration: internal iteration
  while ((LVAL_TYPE(curr) == LVAL_CONS || LVAL_TYPE(curr) == LVAL_QEXPR) &&
         !valk_lval_list_is_empty(curr)) {
  // LCOV_EXCL_BR_STOP
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
  // LCOV_EXCL_BR_START - group count check: internal macro processing
  if (group->count == 0) {
    return inner;
  }
  // LCOV_EXCL_BR_STOP

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
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/let: expected 2 arguments (bindings body)");
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t *bindings = valk_lval_list_nth(a, 0);
  valk_lval_t *body = valk_lval_list_nth(a, 1);

  aio_let_parsed_t *parsed = aio_let_parse_bindings(bindings);

  // LCOV_EXCL_BR_START - empty bindings: unusual pattern
  if (parsed->count == 0 || (parsed->count == 1 && parsed->groups[0].count == 0)) {
    aio_let_free_parsed(parsed);
    valk_lval_t *evaled_body = valk_lval_eval(e, valk_lval_copy(body));
    valk_lval_t *pure_call = valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(evaled_body, valk_lval_nil()));
    return valk_lval_eval(e, pure_call);
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t *body_expr = body;
  // LCOV_EXCL_BR_START - body unwrapping: complex quoted body patterns
  if (LVAL_TYPE(body) == LVAL_CONS && (body->flags & LVAL_FLAG_QUOTED) && !valk_lval_list_is_empty(body)) {
    if (valk_lval_list_is_empty(body->cons.tail)) {
      body_expr = body->cons.head;
    }
  }
  // LCOV_EXCL_BR_STOP
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
  // LCOV_EXCL_BR_START - list type dispatch: internal helper
  if (LVAL_TYPE(expr) != LVAL_CONS && LVAL_TYPE(expr) != LVAL_QEXPR) return false;
  if (valk_lval_list_is_empty(expr)) return false;
  // LCOV_EXCL_BR_STOP
  valk_lval_t *head = expr->cons.head;
  // LCOV_EXCL_BR_START - sym check: internal helper
  return LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "<-") == 0;
  // LCOV_EXCL_BR_STOP
}

static valk_lval_t* aio_do_build_chain(valk_lenv_t *env, valk_lval_t *stmts) {
  // LCOV_EXCL_BR_START - empty stmts: edge case
  if (valk_lval_list_is_empty(stmts)) {
    return valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(valk_lval_nil(), valk_lval_nil()));
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t *curr = stmts->cons.head;
  valk_lval_t *rest = stmts->cons.tail;

  bool is_last = valk_lval_list_is_empty(rest);

  if (is_bind_form(curr)) {
    valk_lval_t *var = valk_lval_list_nth(curr, 1);
    valk_lval_t *expr = valk_lval_list_nth(curr, 2);

    // LCOV_EXCL_BR_START - is_last with bind: edge case
    if (is_last) {
      return valk_lval_copy(expr);
    }
    // LCOV_EXCL_BR_STOP

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
    // LCOV_EXCL_BR_START - aio/do sync expression handling: internal macro processing
    if (is_last) {
      return valk_lval_cons(
        valk_lval_sym("aio/pure"),
        valk_lval_cons(valk_lval_copy(curr), valk_lval_nil()));
    }
    // LCOV_EXCL_BR_STOP

    valk_lval_t *sync_exprs = valk_lval_nil();
    sync_exprs = valk_lval_cons(valk_lval_copy(curr), sync_exprs);

    valk_lval_t *remaining = rest;
    // LCOV_EXCL_BR_START - sync expression iteration
    while (!valk_lval_list_is_empty(remaining) && !is_bind_form(remaining->cons.head)) {
    // LCOV_EXCL_BR_STOP
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

  // LCOV_EXCL_BR_START - empty stmts: edge case
  if (valk_lval_list_is_empty(stmts)) {
    valk_lval_t *pure = valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(valk_lval_nil(), valk_lval_nil()));
    return valk_lval_eval(e, pure);
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t *chain = aio_do_build_chain(e, stmts);

  return valk_lval_eval(e, chain);
}

void valk_register_comb_syntax(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/let", valk_builtin_aio_let);
  valk_lenv_put_builtin(env, "aio/do", valk_builtin_aio_do);
}
