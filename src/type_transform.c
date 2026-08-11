// Main AST transform dispatcher for the type system.
//
// The type transformer walks a Valkyria AST and rewrites constructs that
// depend on declared types:
//   - (type ...) and (sig ...) forms are registered and erased
//   - Constructor calls get rewritten to tagged list literals
//   - Field access (var:field) resolves to (nth idx var) when the type is known
//   - Record updates (with rec :field v) rewrite to copy-with-override
//   - Match expressions desugar to nested if/cond
//
// Specific form transformers live in type_transform_forms.c. This file
// contains the main dispatcher, scope tracking, HM binding tracking, and
// the public API.

#include "type_transform_internal.h"
#include "type_infer.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "memory.h"

#define GROW_ARRAY(arr, count, cap, type) do {  \
  if ((count) >= (cap)) {                       \
    (cap) = (cap) ? (cap) * 2 : 16;            \
    (arr) = realloc((arr), sizeof(type) * (cap)); \
  }                                             \
} while (0)

// ---------------------------------------------------------------------------
// AST predicates
// ---------------------------------------------------------------------------

bool valk_tt_is_keyword(valk_lval_t *v) {
  return LVAL_TYPE(v) == LVAL_SYM && v->str[0] == ':';
}

bool valk_tt_is_qexpr(valk_lval_t *v) {
  return LVAL_TYPE(v) == LVAL_CONS && (v->flags & LVAL_FLAG_QUOTED);
}

static bool is_type_form(valk_lval_t *expr) {
  if (LVAL_TYPE(expr) != LVAL_CONS || (expr->flags & LVAL_FLAG_QUOTED)) return false;
  valk_lval_t *head = expr->cons.head;
  return LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "type") == 0;
}

static bool is_sig_form(valk_lval_t *expr) {
  if (LVAL_TYPE(expr) != LVAL_CONS || (expr->flags & LVAL_FLAG_QUOTED)) return false;
  valk_lval_t *head = expr->cons.head;
  return LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "sig") == 0;
}

static bool is_match_form(valk_lval_t *expr) {
  if (LVAL_TYPE(expr) != LVAL_CONS || (expr->flags & LVAL_FLAG_QUOTED)) return false; // LCOV_EXCL_BR_LINE
  valk_lval_t *head = expr->cons.head;
  return LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "match") == 0;
}

static bool is_accessor(const char *sym) {
  // LCOV_EXCL_BR_START — sym is always non-NULL from LVAL_SYM; multi-condition short-circuit
  if (!sym || sym[0] < 'A' || sym[0] > 'Z') return false;
  const char *colon = strchr(sym, ':');
  if (!colon || colon == sym || colon[1] == '\0') return false;
  // LCOV_EXCL_BR_STOP
  if (colon[1] == ':') return false;
  return true;
}

static bool is_field_access(const char *sym) {
  if (!sym || !*sym) return false;
  const char *colon = strchr(sym, ':');
  if (!colon || colon == sym || colon[1] == '\0') return false;
  if (colon[1] == ':') return false;
  return true;
}

// ---------------------------------------------------------------------------
// Scope-based type tracking (lexical)
// ---------------------------------------------------------------------------

const char *valk_tt_scope_find_type(valk_type_scope_t *scope, const char *var) {
  while (scope) {
    for (u64 i = scope->count; i > 0; i--) {
      if (strcmp(scope->entries[i - 1].var, var) == 0)
        return scope->entries[i - 1].type;
    }
    scope = scope->parent;
  }
  return NULL;
}

void valk_tt_scope_add(valk_type_scope_t *scope, const char *var, const char *type) {
  GROW_ARRAY(scope->entries, scope->count, scope->capacity,
             typeof(scope->entries[0]));
  scope->entries[scope->count].var = var;
  scope->entries[scope->count].type = type;
  scope->count++;
}

static void scope_cleanup(valk_type_scope_t *scope) {
  free(scope->entries);
  scope->entries = NULL;
  scope->count = 0;
  scope->capacity = 0;
}

// ---------------------------------------------------------------------------
// HM inference integration — uses the persistent inferred-type context to
// feed type info into lexical scope tracking, so later transforms (like
// field access) can resolve types for variables bound to inferred values.
// ---------------------------------------------------------------------------

static valk_ti_ctx_t *g_ti_ctx = NULL;

static const char *infer_rhs_type(valk_type_env_t *env, valk_type_scope_t *scope,
                                  valk_lval_t *rhs) {
  if (!rhs || LVAL_TYPE(rhs) != LVAL_CONS || (rhs->flags & LVAL_FLAG_QUOTED)) return NULL;
  valk_lval_t *rhs_head = rhs->cons.head;
  if (!rhs_head || LVAL_TYPE(rhs_head) != LVAL_SYM) return NULL;
  const char *name = rhs_head->str;
  if (name[0] >= 'A' && name[0] <= 'Z') {
    valk_constructor_t *ctor = valk_type_env_find_constructor(env, name);
    if (!ctor) ctor = valk_tt_find_constructor_by_short_name(env, name);
    if (ctor) return ctor->type_name;
  }
  if (strcmp(name, "with") == 0 && valk_lval_list_count(rhs) >= 4) {
    valk_lval_t *wvar = valk_lval_list_nth(rhs, 1);
    if (LVAL_TYPE(wvar) == LVAL_SYM) return valk_tt_scope_find_type(scope, wvar->str);
  }
  if (g_ti_ctx) {
    const char *ti_name = valk_ti_lookup_type_name(g_ti_ctx, name);
    if (ti_name) return ti_name;
  }
  valk_type_sig_t *fn_sig = valk_type_env_find_sig(env, name);
  if (fn_sig && fn_sig->return_type) {
    valk_constructor_t *rc = valk_type_env_find_constructor(env, fn_sig->return_type);
    if (!rc) rc = valk_tt_find_constructor_by_short_name(env, fn_sig->return_type);
    valk_type_decl_t *rt = rc ? NULL : valk_type_env_find_type(env, fn_sig->return_type);
    if (rc) return rc->type_name;
    if (rt) return rt->name;
  }
  return NULL;
}

static void track_binding(valk_type_env_t *env, valk_type_scope_t *scope, valk_lval_t *child_expr) {
  if (LVAL_TYPE(child_expr) != LVAL_CONS || (child_expr->flags & LVAL_FLAG_QUOTED)) return;
  valk_lval_t *ch = child_expr->cons.head;
  if (LVAL_TYPE(ch) != LVAL_SYM || strcmp(ch->str, "=") != 0) return;
  if (valk_lval_list_count(child_expr) != 3) return;
  valk_lval_t *binding = valk_lval_list_nth(child_expr, 1);
  if (!valk_tt_is_qexpr(binding) || LVAL_TYPE(binding->cons.head) != LVAL_SYM ||
      LVAL_TYPE(binding->cons.tail) != LVAL_NIL) return;
  valk_lval_t *rhs = valk_lval_list_nth(child_expr, 2);
  const char *tname = infer_rhs_type(env, scope, rhs);
  if (!tname && g_ti_ctx)
    tname = valk_ti_lookup_type_name(g_ti_ctx, binding->cons.head->str);
  valk_tt_scope_add(scope, binding->cons.head->str, tname);
}

static void track_fun_params(valk_type_env_t *env, valk_type_scope_t *scope, valk_lval_t *formals) {
  if (!valk_tt_is_qexpr(formals)) return;
  valk_lval_t *fn_name = formals->cons.head;
  if (LVAL_TYPE(fn_name) != LVAL_SYM) return;
  valk_type_sig_t *sig = valk_type_env_find_sig(env, fn_name->str);
  valk_lval_t *p = formals->cons.tail;
  u64 idx = 0;
  while (LVAL_TYPE(p) != LVAL_NIL) {
    valk_lval_t *psym = p->cons.head;
    if (LVAL_TYPE(psym) == LVAL_SYM) {
      const char *tname = g_ti_ctx ? valk_ti_lookup_type_name(g_ti_ctx, psym->str) : NULL;
      if (!tname && sig && idx < sig->param_count && sig->param_types[idx]) {
        valk_constructor_t *pc = valk_type_env_find_constructor(env, sig->param_types[idx]);
        if (!pc) pc = valk_tt_find_constructor_by_short_name(env, sig->param_types[idx]);
        valk_type_decl_t *pt = pc ? NULL : valk_type_env_find_type(env, sig->param_types[idx]);
        tname = pc ? pc->type_name : (pt ? pt->name : NULL);
      }
      valk_tt_scope_add(scope, psym->str, tname);
      idx++;
    }
    p = p->cons.tail;
  }
}

// ---------------------------------------------------------------------------
// Field access on symbols (rec:field or rec:field:nested)
// Chained access uses a __chain__ scope entry to propagate type info through
// intermediate positions so each segment can resolve to nth.
// ---------------------------------------------------------------------------

static valk_lval_t *transform_sym_field_access(valk_type_env_t *env,
                                                valk_type_scope_t *scope,
                                                valk_lval_t *expr) {
  const char *colon = strchr(expr->str, ':');
  u64 var_len = colon - expr->str;

  char var_buf[var_len + 1];
  memcpy(var_buf, expr->str, var_len);
  var_buf[var_len] = '\0';

  if (var_buf[0] < 'a' || var_buf[0] > 'z') return expr;

  const char *rest = colon + 1;
  valk_lval_t *result = valk_lval_sym(var_buf);
  const char *cur_var = var_buf;

  while (*rest) {
    const char *next_colon = strchr(rest, ':');
    if (next_colon && next_colon[1] == ':') next_colon = NULL;
    u64 flen = next_colon ? (u64)(next_colon - rest) : strlen(rest);
    char fbuf[flen + 1];
    memcpy(fbuf, rest, flen);
    fbuf[flen] = '\0';

    const char *next_type = NULL;
    if (cur_var) {
      const char *cur_type = valk_tt_scope_find_type(scope, cur_var);
      if (cur_type) {
        valk_constructor_t *ctor = valk_type_env_find_constructor(env, cur_type);
        if (!ctor) ctor = valk_tt_find_constructor_by_short_name(env, cur_type);
        if (ctor) {
          char fkey[flen + 2];
          fkey[0] = ':';
          memcpy(fkey + 1, fbuf, flen);
          fkey[flen + 1] = 0;
          for (u64 fi = 0; fi < ctor->field_count; fi++) {
            if (strcmp(ctor->fields[fi].name, fkey) == 0) {
              next_type = ctor->fields[fi].type_name;
              break;
            }
          }
        }
      }
    }

    result = valk_tt_resolve_field_access(env, scope, result, cur_var, fbuf);
    if (LVAL_TYPE(result) == LVAL_ERR) return result;

    if (next_type) {
      valk_tt_scope_add(scope, "__chain__", next_type);
      cur_var = "__chain__";
    } else {
      cur_var = NULL;
    }
    rest = next_colon ? next_colon + 1 : rest + flen;
  }
  return result;
}

// ---------------------------------------------------------------------------
// Lambda/fun body transformation — introduces a child scope, tracks
// parameter types from the enclosing sig, then transforms body forms.
// ---------------------------------------------------------------------------

static bool head_is_lambda(valk_lval_t *head) {
  if (LVAL_TYPE(head) == LVAL_SYM &&
      (strcmp(head->str, "fun") == 0 || strcmp(head->str, "\\") == 0))
    return true;
  if (LVAL_TYPE(head) == LVAL_FUN && head->fun.builtin != NULL) {
    extern valk_lenv_t *valk_macro_env(void);
    valk_lval_t *lambda_ref = valk_lenv_get(valk_macro_env(), valk_lval_sym("\\"));
    if (LVAL_TYPE(lambda_ref) == LVAL_FUN &&
        head->fun.builtin == lambda_ref->fun.builtin)
      return true;
  }
  return false;
}

static valk_lval_t *transform_lambda_body(valk_type_env_t *env,
                                           valk_type_scope_t *scope,
                                           valk_lval_t *expr) {
  valk_lval_t *head = expr->cons.head;
  valk_type_scope_t child = { .count = 0, .parent = scope };
  u64 count = valk_lval_list_count(expr);
  valk_lval_t **items = valk_mem_alloc(sizeof(valk_lval_t *) * count);
  items[0] = head;
  if (count > 1) {
    items[1] = valk_lval_list_nth(expr, 1);
    track_fun_params(env, &child, items[1]);
  }
  for (u64 i = 2; i < count; i++) {
    valk_lval_t *child_expr = valk_lval_list_nth(expr, i);
    track_binding(env, &child, child_expr);
    items[i] = valk_tt_transform_expr(env, &child, child_expr);
  }
  valk_lval_t *result = valk_lval_nil();
  for (u64 i = count; i > 0; i--)
    result = valk_lval_cons(items[i - 1], result);
  scope_cleanup(&child);
  return result;
}

// ---------------------------------------------------------------------------
// (def {name} (\ ...)) — track fn-name params alongside lambda formals so
// recursive references get the right type. Only applies when RHS is a lambda.
// ---------------------------------------------------------------------------

static valk_lval_t *transform_def_lambda(valk_type_env_t *env,
                                          valk_type_scope_t *scope,
                                          valk_lval_t *expr) {
  u64 cnt = valk_lval_list_count(expr);
  if (cnt != 3) return NULL;
  valk_lval_t *name_arg = valk_lval_list_nth(expr, 1);
  valk_lval_t *val_arg = valk_lval_list_nth(expr, 2);
  if (!valk_tt_is_qexpr(name_arg) || LVAL_TYPE(val_arg) != LVAL_CONS ||
      (val_arg->flags & LVAL_FLAG_QUOTED)) return NULL;

  valk_lval_t *val_head = val_arg->cons.head;
  bool val_is_lambda = (LVAL_TYPE(val_head) == LVAL_SYM &&
                        strcmp(val_head->str, "\\") == 0);
  if (!val_is_lambda && LVAL_TYPE(val_head) == LVAL_FUN &&
      val_head->fun.builtin != NULL) {
    extern valk_lenv_t *valk_macro_env(void);
    valk_lval_t *lr = valk_lenv_get(valk_macro_env(), valk_lval_sym("\\"));
    if (LVAL_TYPE(lr) == LVAL_FUN && val_head->fun.builtin == lr->fun.builtin)
      val_is_lambda = true;
  }
  if (!val_is_lambda) return NULL;

  valk_lval_t *head = expr->cons.head;
  valk_lval_t *fn_name = name_arg->cons.head;
  valk_lval_t *lambda_formals = valk_lval_list_nth(val_arg, 1);
  valk_lval_t *combined = valk_lval_qcons(fn_name, lambda_formals);
  valk_type_scope_t child = { .count = 0, .parent = scope };
  track_fun_params(env, &child, combined);
  u64 lambda_cnt = valk_lval_list_count(val_arg);
  valk_lval_t **litems = valk_mem_alloc(sizeof(valk_lval_t *) * lambda_cnt);
  litems[0] = val_head;
  if (lambda_cnt > 1) litems[1] = lambda_formals;
  for (u64 i = 2; i < lambda_cnt; i++) {
    valk_lval_t *child_expr = valk_lval_list_nth(val_arg, i);
    track_binding(env, &child, child_expr);
    litems[i] = valk_tt_transform_expr(env, &child, child_expr);
  }
  valk_lval_t *new_lambda = valk_lval_nil();
  for (u64 i = lambda_cnt; i > 0; i--)
    new_lambda = valk_lval_cons(litems[i - 1], new_lambda);
  scope_cleanup(&child);
  return valk_lval_cons(head, valk_lval_cons(name_arg, valk_lval_cons(new_lambda, valk_lval_nil())));
}

// ---------------------------------------------------------------------------
// (do ...) body transformation — introduces a child scope so bindings are
// local to the do block.
// ---------------------------------------------------------------------------

static valk_lval_t *transform_do_body(valk_type_env_t *env,
                                       valk_type_scope_t *scope,
                                       valk_lval_t *expr,
                                       bool quoted) {
  valk_lval_t *head = expr->cons.head;
  valk_type_scope_t child = { .count = 0, .parent = scope };
  u64 count = valk_lval_list_count(expr);
  valk_lval_t **items = valk_mem_alloc(sizeof(valk_lval_t *) * count);
  items[0] = head;
  for (u64 i = 1; i < count; i++) {
    valk_lval_t *child_expr = valk_lval_list_nth(expr, i);
    track_binding(env, &child, child_expr);
    items[i] = valk_tt_transform_expr(env, &child, child_expr);
  }
  valk_lval_t *result = valk_lval_nil();
  for (u64 i = count; i > 0; i--)
    result = quoted ? valk_lval_qcons(items[i - 1], result)
                    : valk_lval_cons(items[i - 1], result);
  scope_cleanup(&child);
  return result;
}

// ---------------------------------------------------------------------------
// Main dispatcher
// ---------------------------------------------------------------------------

valk_lval_t *valk_tt_transform_expr(valk_type_env_t *env, valk_type_scope_t *scope, valk_lval_t *expr) {
  if (expr == NULL) return valk_lval_nil(); // LCOV_EXCL_BR_LINE — AST nodes are never NULL

  valk_ltype_e type = LVAL_TYPE(expr);

  // LCOV_EXCL_BR_START — FUN/REF/HANDLE are runtime-only types
  if (type == LVAL_NUM || type == LVAL_STR || type == LVAL_ERR ||
      type == LVAL_FUN || type == LVAL_REF || type == LVAL_HANDLE ||
      type == LVAL_DICT) {
    return expr;
  }
  // LCOV_EXCL_BR_STOP

  if (type == LVAL_NIL) return expr;

  // Quoted cons — recursively transform contents, preserving quote
  if (type == LVAL_CONS && (expr->flags & LVAL_FLAG_QUOTED)) {
    valk_lval_t *head = expr->cons.head;
    if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "match") == 0) {
      valk_lval_t *as_sexpr = valk_lval_nil();
      u64 count = valk_lval_list_count(expr);
      for (u64 i = count; i > 0; i--) {
        as_sexpr = valk_lval_cons(valk_lval_list_nth(expr, i - 1), as_sexpr);
      }
      valk_lval_t *transformed = valk_tt_transform_match(env, scope, as_sexpr);
      return valk_lval_qcons(transformed, valk_lval_nil());
    }
    if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "do") == 0) {
      return transform_do_body(env, scope, expr, true);
    }
    if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "with") == 0 &&
        valk_lval_list_count(expr) >= 4) {
      valk_lval_t *as_sexpr = valk_lval_nil();
      u64 wcount = valk_lval_list_count(expr);
      for (u64 i = wcount; i > 0; i--)
        as_sexpr = valk_lval_cons(valk_lval_list_nth(expr, i - 1), as_sexpr);
      valk_lval_t *with_var = valk_lval_list_nth(as_sexpr, 1);
      if (LVAL_TYPE(with_var) == LVAL_SYM) {
        const char *with_type = valk_tt_scope_find_type(scope, with_var->str);
        if (with_type) {
          valk_lval_t *transformed = valk_tt_transform_record_update(env, scope, with_var->str, with_type, as_sexpr);
          return valk_lval_qcons(transformed, valk_lval_nil());
        }
      }
    }
    // Rewrite short-name constructor shortcuts inside qexprs ({Some 42} when
    // Some is a known Option constructor), but leave fully-qualified
    // {Type::Ctor ...} alone — that form is the literal internal tagged
    // representation, so rewriting would produce nonsense (wrapping the tag
    // as though it were another short-name call).
    if (LVAL_TYPE(head) == LVAL_SYM && valk_lval_list_count(expr) > 1 &&
        strstr(head->str, "::") == NULL) {
      valk_constructor_t *qctor = valk_type_env_find_constructor(env, head->str);
      if (!qctor) qctor = valk_tt_find_constructor_by_short_name(env, head->str);
      if (qctor && qctor->field_count > 0) {
        valk_lval_t *args = expr->cons.tail;
        valk_lval_t *transformed = valk_tt_transform_constructor_call(env, scope, qctor, args);
        if (LVAL_TYPE(transformed) == LVAL_ERR) return transformed;
        transformed->flags |= LVAL_FLAG_QUOTED;
        return transformed;
      }
    }

    valk_lval_t *result = valk_lval_nil();
    u64 count = valk_lval_list_count(expr);
    for (u64 i = count; i > 0; i--) {
      result = valk_lval_qcons(valk_tt_transform_expr(env, scope, valk_lval_list_nth(expr, i - 1)), result);
    }
    return result;
  }

  // Symbol — handle field access
  if (type == LVAL_SYM) {
    if (scope && is_field_access(expr->str))
      return transform_sym_field_access(env, scope, expr);
    return expr;
  }

  if (type != LVAL_CONS) return expr; // LCOV_EXCL_BR_LINE

  // Unquoted cons forms
  if (is_match_form(expr)) {
    return valk_tt_transform_match(env, scope, expr);
  }

  // (type ...) and (sig ...) are registered elsewhere and erased here
  if (is_type_form(expr) || is_sig_form(expr)) {
#ifdef VALK_COVERAGE
    valk_coverage_unmark_tree(expr);
#endif
    return valk_lval_nil();
  }

  valk_lval_t *head = expr->cons.head;

  if (LVAL_TYPE(head) == LVAL_SYM) {
    if (is_accessor(head->str) && valk_lval_list_count(expr) == 2) {
      return valk_tt_transform_accessor(env, scope, head->str, valk_lval_list_nth(expr, 1));
    }

    valk_constructor_t *ctor = valk_type_env_find_constructor(env, head->str);
    if (!ctor) ctor = valk_tt_find_constructor_by_short_name(env, head->str);
    if (ctor) {
      return valk_tt_transform_constructor_call(env, scope, ctor, expr->cons.tail);
    }

    if (strcmp(head->str, "with") == 0 && valk_lval_list_count(expr) >= 4) {
      valk_lval_t *with_var = valk_lval_list_nth(expr, 1);
      if (LVAL_TYPE(with_var) == LVAL_SYM) {
        const char *with_type = valk_tt_scope_find_type(scope, with_var->str);
        if (with_type)
          return valk_tt_transform_record_update(env, scope, with_var->str, with_type, expr);
      }
    }

    if (strcmp(head->str, "do") == 0) {
      return transform_do_body(env, scope, expr, false);
    }

    if (strcmp(head->str, "def") == 0) {
      valk_lval_t *rewritten = transform_def_lambda(env, scope, expr);
      if (rewritten) return rewritten;
    }
  }

  if (head_is_lambda(head)) {
    return transform_lambda_body(env, scope, expr);
  }

  // Default: recursively transform all children
  valk_lval_t *result = valk_lval_nil();
  u64 count = valk_lval_list_count(expr);
  for (u64 i = count; i > 0; i--) {
    result = valk_lval_cons(valk_tt_transform_expr(env, scope, valk_lval_list_nth(expr, i - 1)), result);
  }
  return result;
}

// ---------------------------------------------------------------------------
// Public API — global type env + entry points
// ---------------------------------------------------------------------------

static valk_type_env_t *g_type_env = NULL;

valk_type_env_t *valk_type_env_global(void) {
  if (!g_type_env) g_type_env = valk_type_env_new();
  return g_type_env;
}

void valk_type_env_reset(void) {
  if (g_type_env) {
    valk_type_env_free(g_type_env);
    g_type_env = NULL;
  }
}

// Per-expression entry point. Uses a persistent HM inference context so
// top-level expressions accumulate types across REPL interactions.
valk_lval_t *valk_type_transform_expr(valk_lval_t *expr) {
  valk_type_env_t *env = valk_type_env_global();

  if (is_type_form(expr)) {
    valk_lval_t *err = valk_type_env_register(env, expr);
    if (err != NULL) return err;
#ifdef VALK_COVERAGE
    valk_coverage_unmark_tree(expr);
#endif
    return valk_lval_nil();
  }

  if (is_sig_form(expr)) {
    valk_type_env_register_sig(env, expr);
#ifdef VALK_COVERAGE
    valk_coverage_unmark_tree(expr);
#endif
    return valk_lval_nil();
  }

  if (env->type_count == 0 && env->sig_count == 0) return expr;

  static valk_type_scope_t persistent_scope = {0};
  static valk_ti_ctx_t *pti = NULL;

  if (!pti) {
    pti = valk_ti_create(env);
    valk_ti_import_new(pti);
  } else if (env->sig_count != pti->imported_sig_count ||
             env->type_count != pti->imported_type_count) {
    pti->scope = pti->base_scope;
    valk_ti_import_new(pti);
  }

  valk_ti_reset(pti);
  valk_ti_infer_expr(pti, pti->scope, expr);

  g_ti_ctx = pti;
  track_binding(env, &persistent_scope, expr);
  valk_lval_t *result = valk_tt_transform_expr(env, &persistent_scope, expr);
  g_ti_ctx = NULL;
  return result;
}

// Whole-file entry point. Registers types/sigs in a first pass, then runs
// HM inference over the full file, then transforms each expression.
valk_lval_t *valk_type_transform(valk_lval_t *exprs) {
  valk_type_env_t *env = valk_type_env_global();

  valk_lval_t *curr = exprs;
  while (LVAL_TYPE(curr) != LVAL_NIL) {
    valk_lval_t *expr = curr->cons.head;
    if (is_type_form(expr)) {
      valk_lval_t *err = valk_type_env_register(env, expr);
      if (err != NULL) {
        return valk_lval_cons(err, valk_lval_nil());
      }
    }
    if (is_sig_form(expr)) {
      valk_type_env_register_sig(env, expr);
    }
    curr = curr->cons.tail;
  }

  if (env->type_count == 0 && env->sig_count == 0) {
    return exprs;
  }

  valk_type_scope_t scope = {0};
  valk_ti_ctx_t *ti = valk_ti_create(env);
  valk_ti_import_new(ti);

  valk_ti_infer_file(ti, exprs);
  valk_ti_populate_type_scope(ti, ti->scope, &scope);
  g_ti_ctx = ti;

  u64 count = valk_lval_list_count(exprs);
  valk_lval_t **items = malloc(sizeof(valk_lval_t *) * count);
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *expr = valk_lval_list_nth(exprs, i);
    track_binding(env, &scope, expr);
    items[i] = valk_tt_transform_expr(env, &scope, expr);
  }
  valk_lval_t *result = valk_lval_nil();
  for (u64 i = count; i > 0; i--) {
    valk_lval_t *expr = valk_lval_list_nth(exprs, i - 1);
    if (LVAL_TYPE(items[i - 1]) != LVAL_NIL || (!is_type_form(expr) && !is_sig_form(expr))) {
      result = valk_lval_cons(items[i - 1], result);
    }
  }
  free(items);

  g_ti_ctx = NULL;
  valk_ti_destroy(ti);
  if (scope.entries) free(scope.entries);
  return result;
}
