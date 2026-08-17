#include "builtins_internal.h"

#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

#include "coverage.h"
#include "gc.h"

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
    valk_lval_t* val = valk_lval_list_nth(a, i + 1);
    if (LVAL_TYPE(val) == LVAL_ERR) { // LCOV_EXCL_BR_LINE
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
    valk_lval_t* val = valk_lval_list_nth(a, i + 1);
    valk_lval_t* sym = valk_lval_list_nth(syms, i);
    valk_lenv_put(e, sym, val);
  }

  return valk_lval_nil();
}

static bool is_ann_marker(valk_lval_t *v) {
  return v && LVAL_TYPE(v) == LVAL_SYM &&
    (strcmp(v->str, "::") == 0 || strcmp(v->str, "->") == 0);
}

static valk_lval_t *strip_type_annotations(valk_lval_t *formals) {
  if (!formals || LVAL_TYPE(formals) != LVAL_CONS) return formals;

  bool has_ann = false;
  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    if (is_ann_marker(valk_lval_head(cur))) { has_ann = true; break; }
    cur = valk_lval_tail(cur);
  }
  if (!has_ann) return formals;

  valk_lval_t *params[64];
  int count = 0;
  cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS && count < 64) {
    valk_lval_t *h = valk_lval_head(cur);
    if (is_ann_marker(h)) {
      cur = valk_lval_tail(cur);
      if (cur && LVAL_TYPE(cur) == LVAL_CONS)
        cur = valk_lval_tail(cur);
      continue;
    }
    params[count++] = h;
    cur = valk_lval_tail(cur);
  }
  return valk_lval_qlist(params, (u64)count);
}

static valk_lval_t* valk_builtin_lambda(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* formals = valk_lval_list_nth(a, 0);
  valk_lval_t* body = valk_lval_list_nth(a, 1);

  LVAL_ASSERT_TYPE(a, formals, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);
  LVAL_ASSERT_TYPE(a, body, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  formals = valk_lval_pop(a, 0);
  body = valk_lval_pop(a, 0);

  formals = strip_type_annotations(formals);

  for (u64 i = 0; i < valk_lval_list_count(formals); i++) { // LCOV_EXCL_BR_LINE
    LVAL_ASSERT(a, LVAL_TYPE(valk_lval_list_nth(formals, i)) == LVAL_SYM,
                "Cannot use a non symbol[%s] for bind",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(formals, i))));
  }

  valk_lval_t* func = valk_lval_lambda(e, formals, body);

  return func;
}

static valk_lval_t* valk_builtin_penv(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(a);
  valk_lval_t* res = valk_lval_nil();
  for (valk_lenv_t* env = e; env != nullptr; env = env->parent) {
    for (u64 i = 0; i < env->symbols.count; i++) {
      res = valk_lval_cons(
          valk_lval_cons(valk_lval_sym(env->symbols.items[i]),
                         valk_lval_cons(env->vals.items[i], valk_lval_nil())),
          res);
    }
  }
  return res;
}

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

    // LCOV_EXCL_BR_START - select clause dispatch: quoted/unquoted, coverage instrumentation
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
    // LCOV_EXCL_BR_STOP
  }

  return valk_lval_err("No selection found");
}



#define LVAL_ASSERT_ENV(args, v)                                          \
  LVAL_ASSERT(args,                                                       \
              LVAL_TYPE(v) == LVAL_REF && strcmp((v)->ref.type, "env") == 0, \
              "Expected env ref, got %s", valk_ltype_name(LVAL_TYPE(v)))

valk_lval_t* valk_lval_env_ref(valk_lenv_t* env) {
  valk_lval_t* ref = valk_lval_ref("env", env, NULL);
  ref->ref.mark = valk_gc_mark_env_ref;
  valk_gc_wb_env_insert(env);
  return ref;
}

static valk_lval_t* valk_builtin_env_new(valk_lenv_t* e, valk_lval_t* a) {
  u64 count = valk_lval_list_count(a);
  LVAL_ASSERT(a, count <= 1, "env/new takes 0 or 1 arguments, got %llu",
              (unsigned long long)count);

  valk_lenv_t* parent;
  if (count == 1) {
    valk_lval_t* pref = valk_lval_list_nth(a, 0);
    LVAL_ASSERT_ENV(a, pref);
    parent = pref->ref.ptr;
  } else {
    parent = valk_thread_ctx.root_env ? valk_thread_ctx.root_env : e;
  }

  valk_lenv_t* env = valk_lenv_empty();
  env->parent = parent;
  atomic_fetch_or(&env->flags, LENV_FLAG_DEF_BOUNDARY);
  return valk_lval_env_ref(env);
}

static valk_lval_t* valk_builtin_env_eval(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* env_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_ENV(a, env_ref);
  valk_lval_t* expr = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(expr) == LVAL_CONS && (expr->flags & LVAL_FLAG_QUOTED)) {
    expr = valk_qexpr_to_cons(expr);
  }

  return valk_lval_eval(env_ref->ref.ptr, expr);
}

static valk_lval_t* valk_builtin_env_bindings(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  valk_lval_t* env_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_ENV(a, env_ref);
  valk_lenv_t* env = env_ref->ref.ptr;

  char** names;
  valk_lval_t** vals;
  u64 n = valk_lenv_snapshot(env, &names, &vals);

  valk_lval_t* res = valk_lval_nil();
  for (u64 i = 0; i < n; i++) {
    res = valk_lval_cons(
        valk_lval_cons(valk_lval_sym(names[i]),
                       valk_lval_cons(vals[i], valk_lval_nil())),
        res);
  }
  free(names);
  free(vals);
  return res;
}

static valk_lval_t* valk_builtin_env_parent(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  valk_lval_t* env_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_ENV(a, env_ref);
  valk_lenv_t* env = env_ref->ref.ptr;

  if (env->parent == nullptr) {
    return valk_lval_nil();
  }
  return valk_lval_env_ref(env->parent);
}

static valk_lval_t *valk_builtin_macro(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t *sig = valk_lval_list_nth(a, 0);
  valk_lval_t *body = valk_lval_list_nth(a, 1);

  LVAL_ASSERT_TYPE(a, sig, LVAL_CONS, LVAL_QEXPR);
  LVAL_ASSERT_TYPE(a, body, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);
  LVAL_ASSERT(a, valk_lval_list_count(sig) >= 1,
              "macro: signature must have at least a name");

  valk_lval_t *name_sym = valk_lval_list_nth(sig, 0);
  LVAL_ASSERT_TYPE(a, name_sym, LVAL_SYM);

  valk_lval_t *formals = valk_lval_nil();
  for (i64 i = (i64)valk_lval_list_count(sig) - 1; i >= 1; i--)
    formals = valk_lval_qcons(valk_lval_list_nth(sig, i), formals);

  valk_lval_t *func = valk_lval_lambda(e, formals, body);
  func->flags |= LVAL_FLAG_MACRO;

  valk_lenv_def(e, name_sym, func);
  return valk_lval_nil();
}

void valk_register_env_builtins(valk_lenv_t* env) {
  // def/= accept errors so user code can bind them for inspection
  // (error?, match, etc). Without this, BYOL short-circuit makes
  // errors impossible to catch.
  valk_lenv_put_builtin_err_ok(env, "def", valk_builtin_def);
  valk_lenv_put_builtin_err_ok(env, "=", valk_builtin_put);
  valk_lenv_put_builtin(env, "\\", valk_builtin_lambda);
  valk_lenv_put_builtin(env, "macro", valk_builtin_macro);
  valk_lenv_put_builtin(env, "penv", valk_builtin_penv);
  valk_lenv_put_builtin(env, "select", valk_builtin_select);
  valk_lenv_put_builtin(env, "env/new", valk_builtin_env_new);
  valk_lenv_put_builtin(env, "env/eval", valk_builtin_env_eval);
  valk_lenv_put_builtin(env, "env/bindings", valk_builtin_env_bindings);
  valk_lenv_put_builtin(env, "env/parent", valk_builtin_env_parent);
}
