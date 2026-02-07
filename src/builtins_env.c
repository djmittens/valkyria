#include "builtins_internal.h"

#include "coverage.h"

static inline valk_lval_t* valk_resolve_symbol(valk_lenv_t* e, valk_lval_t* v) {
  if (LVAL_TYPE(v) == LVAL_SYM) {
    if (v->str[0] == ':') {
      return v;
    }
    return valk_lenv_get(e, v);
  }
  return v;
}

static valk_lval_t* valk_builtin_def(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_thread_ctx.request_ctx != nullptr) {
    return valk_lval_err(
        "def cannot be used in request handler context. "
        "Use = for local bindings instead.");
  }

  LVAL_ASSERT_COUNT_GT(a, a, 1);

  valk_lval_t* first_arg = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(first_arg) == LVAL_SYM) {
    first_arg = valk_lval_cons(first_arg, valk_lval_nil());
  }

  valk_lval_t* syms = first_arg;
  LVAL_ASSERT_TYPE(a, syms, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  for (u64 i = 1; i < valk_lval_list_count(syms); i++) {
    valk_lval_t* sym_elem = valk_lval_list_nth(syms, i);
    LVAL_ASSERT(a, LVAL_TYPE(sym_elem) == LVAL_SYM,
                "Builtin `def` requires that symbols parameter only has "
                "symbols found: %s",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(a, i))));
  }

  LVAL_ASSERT_COUNT_EQ(a, syms, (valk_lval_list_count(a) - 1));

  for (u64 i = 0; i < valk_lval_list_count(syms); i++) {
    valk_lval_t* sym = valk_lval_list_nth(syms, i);
    valk_lval_t* val = valk_resolve_symbol(e, valk_lval_list_nth(a, i + 1));
    if (LVAL_TYPE(val) == LVAL_ERR) {
      return val;
    }
    valk_lenv_def(e, sym, val);
  }

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_put(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_GT(a, a, 1);

  valk_lval_t* syms = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, syms, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  for (u64 i = 1; i < valk_lval_list_count(syms); i++) {
    valk_lval_t* sym_elem = valk_lval_list_nth(syms, i);
    LVAL_ASSERT(a, LVAL_TYPE(sym_elem) == LVAL_SYM,
                "Builtin `def` requires that symbols parameter only has "
                "symbols found: %s",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(a, i))));
  }

  LVAL_ASSERT_COUNT_EQ(a, syms, (valk_lval_list_count(a) - 1));

  for (u64 i = 0; i < valk_lval_list_count(syms); i++) {
    valk_lval_t* val = valk_resolve_symbol(e, valk_lval_list_nth(a, i + 1));

    valk_lval_t* sym = valk_lval_list_nth(syms, i);
    valk_lenv_put(e, sym, val);
  }

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_lambda(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* formals = valk_lval_list_nth(a, 0);
  valk_lval_t* body = valk_lval_list_nth(a, 1);

  LVAL_ASSERT_TYPE(a, formals, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);
  LVAL_ASSERT_TYPE(a, body, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  for (u64 i = 0; i < valk_lval_list_count(formals); i++) {
    LVAL_ASSERT(a, LVAL_TYPE(valk_lval_list_nth(formals, i)) == LVAL_SYM,
                "Cannot use a non symbol[%s] for bind",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(formals, i))));
  }

  formals = valk_lval_pop(a, 0);
  body = valk_lval_pop(a, 0);

  valk_lval_t* func = valk_lval_lambda(e, formals, body);

  return func;
}

static valk_lval_t* valk_builtin_penv(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(a);
  valk_lval_t* res = valk_lval_nil();
  for (u64 i = 0; i < e->symbols.count; i++) {
    res = valk_lval_cons(
        valk_lval_cons(valk_lval_sym(e->symbols.items[i]),
                       valk_lval_cons(e->vals.items[i], valk_lval_nil())),
        res);
  }
  return res;
}

// LCOV_EXCL_BR_START - valk_builtin_if is superseded by special form in evaluator
static valk_lval_t* valk_builtin_if(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  valk_lval_t* cond_val = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, cond_val, LVAL_NUM);
  valk_lval_t* true_branch = valk_lval_list_nth(a, 1);
  valk_lval_t* false_branch = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, true_branch, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);
  LVAL_ASSERT_TYPE(a, false_branch, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  valk_lval_t* branch;
  bool condition = cond_val->num != 0;
#ifdef VALK_COVERAGE
  if (true_branch->cov_file_id != 0 && true_branch->cov_line != 0) {
    valk_coverage_mark_expr(true_branch->cov_file_id, true_branch->cov_line,
                            true_branch->cov_column, 0);
  }
  if (false_branch->cov_file_id != 0 && false_branch->cov_line != 0) {
    valk_coverage_mark_expr(false_branch->cov_file_id, false_branch->cov_line,
                            false_branch->cov_column, 0);
  }
  u16 file_id = true_branch->cov_file_id;
  u16 line = true_branch->cov_line;
  if (file_id == 0 || line == 0) {
    file_id = false_branch->cov_file_id;
    line = false_branch->cov_line;
  }
  VALK_COVERAGE_RECORD_BRANCH(file_id, line, condition);
#endif
  if (condition) {
    branch = true_branch;
  } else {
    branch = false_branch;
  }

  if (LVAL_TYPE(branch) == LVAL_CONS && (branch->flags & LVAL_FLAG_QUOTED)) {
    VALK_COVERAGE_RECORD_LVAL(branch);
    branch = valk_qexpr_to_cons(branch);
  }

  return valk_lval_eval(e, branch);
}
// LCOV_EXCL_BR_STOP

static valk_lval_t* valk_builtin_select(valk_lenv_t* e, valk_lval_t* a) {
  u64 count = valk_lval_list_count(a);
  if (count == 0) {
    return valk_lval_err("No selection found");
  }

  for (u64 i = 0; i < count; i++) {
    valk_lval_t* clause = valk_lval_list_nth(a, i);
    LVAL_ASSERT_TYPE(a, clause, LVAL_CONS, LVAL_QEXPR);

#ifdef VALK_COVERAGE
    u16 file_id = clause->cov_file_id;
    u16 line = clause->cov_line;
#endif

    if (LVAL_TYPE(clause) == LVAL_CONS && (clause->flags & LVAL_FLAG_QUOTED)) {
      clause = valk_qexpr_to_cons(clause);
    }

    u64 clause_len = valk_lval_list_count(clause);
    LVAL_ASSERT(a, clause_len == 2, "Select clause must have condition and result");

    valk_lval_t* cond_expr = valk_lval_list_nth(clause, 0);
    valk_lval_t* result_expr = valk_lval_list_nth(clause, 1);

    valk_lval_t* cond_val = valk_lval_eval(e, cond_expr);
    if (LVAL_TYPE(cond_val) == LVAL_ERR) {
      return cond_val;
    }
    LVAL_ASSERT_TYPE(a, cond_val, LVAL_NUM);

    bool condition = cond_val->num != 0;

#ifdef VALK_COVERAGE
    if (file_id != 0 && line != 0) {
      VALK_COVERAGE_RECORD_BRANCH(file_id, line, condition);
    }
#endif

    if (condition) {
      if (LVAL_TYPE(result_expr) == LVAL_CONS && (result_expr->flags & LVAL_FLAG_QUOTED)) {
        VALK_COVERAGE_RECORD_LVAL(result_expr);
        result_expr = valk_qexpr_to_cons(result_expr);
      }
      return valk_lval_eval(e, result_expr);
    }
  }

  return valk_lval_err("No selection found");
}

static valk_lval_t* valk_builtin_do(valk_lenv_t* e, valk_lval_t* a) {
  u64 count = valk_lval_list_count(a);

  if (count == 0) {
    return valk_lval_nil();
  }

  for (u64 i = 0; i < count - 1; i++) {
    valk_lval_t* expr = valk_lval_list_nth(a, i);
    valk_lval_eval(e, expr);
  }

  valk_lval_t* last = valk_lval_list_nth(a, count - 1);
  return valk_lval_eval(e, last);
}

void valk_register_env_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "def", valk_builtin_def);
  valk_lenv_put_builtin(env, "=", valk_builtin_put);
  valk_lenv_put_builtin(env, "\\", valk_builtin_lambda);
  valk_lenv_put_builtin(env, "penv", valk_builtin_penv);
  valk_lenv_put_builtin(env, "if", valk_builtin_if);
  valk_lenv_put_builtin(env, "select", valk_builtin_select);
  valk_lenv_put_builtin(env, "do", valk_builtin_do);
}
