// Form-specific transformers for the type system:
// - Constructor calls: (Foo x y) → (list (head {Foo}) x y)
// - Record updates: (with rec :field v) → explicit field copy
// - Accessors: Foo:field → (nth idx arg)
// - Match expressions: (match ...) → nested if/cond
// - Field access: rec:field → (nth idx rec)

#include "type_transform_internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "coverage.h"
#include "memory.h"
#include "parser.h"

// ---------------------------------------------------------------------------
// Constructor lookup helpers
// ---------------------------------------------------------------------------

valk_constructor_t *valk_tt_find_constructor_by_short_name(valk_type_env_t *env,
                                                            const char *short_name) {
  for (u64 i = 0; i < env->constructor_count; i++) {
    const char *full = env->constructors[i]->name;
    const char *sep = strstr(full, "::");
    if (sep && strcmp(sep + 2, short_name) == 0)
      return env->constructors[i];
  }
  return NULL;
}

static valk_constructor_t *find_ctor_for_type(valk_type_env_t *env, const char *type_name) {
  valk_constructor_t *ctor = valk_type_env_find_constructor(env, type_name);
  if (!ctor) ctor = valk_tt_find_constructor_by_short_name(env, type_name);
  if (!ctor) {
    valk_type_decl_t *tdecl = valk_type_env_find_type(env, type_name);
    if (tdecl && tdecl->constructor_count > 0)
      ctor = tdecl->constructors[0];
  }
  return ctor;
}

// ---------------------------------------------------------------------------
// Field access resolution (uses scope-tracked type info)
// ---------------------------------------------------------------------------

valk_lval_t *valk_tt_resolve_field_access(valk_type_env_t *env,
                                           valk_type_scope_t *scope,
                                           valk_lval_t *var_expr,
                                           const char *var_name,
                                           const char *field_name) {
  const char *type_name = var_name ? valk_tt_scope_find_type(scope, var_name) : NULL;
  u64 field_len = strlen(field_name);
  char field_key[field_len + 2];
  field_key[0] = ':';
  memcpy(field_key + 1, field_name, field_len);
  field_key[field_len + 1] = '\0';

  if (type_name) {
    valk_constructor_t *ctor = valk_type_env_find_constructor(env, type_name);
    if (!ctor) ctor = valk_tt_find_constructor_by_short_name(env, type_name);
    if (!ctor) {
      valk_type_decl_t *tdecl = valk_type_env_find_type(env, type_name);
      if (tdecl) {
        for (u64 c = 0; c < tdecl->constructor_count && !ctor; c++) {
          for (u64 f = 0; f < tdecl->constructors[c]->field_count; f++) {
            if (strcmp(tdecl->constructors[c]->fields[f].name, field_key) == 0) {
              ctor = tdecl->constructors[c];
              break;
            }
          }
        }
      }
    }
    if (ctor) {
      for (u64 i = 0; i < ctor->field_count; i++) {
        if (strcmp(ctor->fields[i].name, field_key) == 0) {
          // Emit (record/field VAR 'Tag IDX :field) instead of a bare
          // (nth IDX VAR). This evaluates VAR exactly once and verifies
          // the tag at runtime — if the type system was wrong about the
          // runtime shape (e.g. raw JSON plist annotated as a record),
          // we fall back to plist/get rather than returning whatever
          // bytes happen to live at slot IDX. See valk_builtin_record_field.
          valk_lval_t *index = valk_lval_num((long)(i + 2));
          valk_lval_t *fn_sym = valk_lval_sym("record/field");
          valk_lval_t *tag_sym = valk_lval_sym(ctor->name);
          valk_lval_t *tag_q = valk_lval_qcons(tag_sym, valk_lval_nil());
          valk_lval_t *tag = valk_lval_cons(valk_lval_sym("head"),
                               valk_lval_cons(tag_q, valk_lval_nil()));
          valk_lval_t *key_sym = valk_lval_sym(field_key);
          return valk_lval_cons(fn_sym,
                   valk_lval_cons(var_expr,
                     valk_lval_cons(tag,
                       valk_lval_cons(index,
                         valk_lval_cons(key_sym, valk_lval_nil())))));
        }
      }
      return valk_lval_err("type '%s' has no field ':%s'", type_name, field_name);
    }
    valk_type_decl_t *tdecl2 = valk_type_env_find_type(env, type_name);
    if (tdecl2 && tdecl2->constructor_count > 0)
      return valk_lval_err("type '%s' has no field ':%s'", type_name, field_name);
  }

  valk_lval_t *plist_get_sym = valk_lval_sym("plist/get");
  valk_lval_t *key_sym = valk_lval_sym(field_key);
  return valk_lval_cons(plist_get_sym, valk_lval_cons(var_expr, valk_lval_cons(key_sym, valk_lval_nil())));
}

// ---------------------------------------------------------------------------
// Constructor call: (Foo a b) or (Foo :x a :y b)
// ---------------------------------------------------------------------------

valk_lval_t *valk_tt_transform_constructor_call(valk_type_env_t *env,
                                                 valk_type_scope_t *scope,
                                                 valk_constructor_t *ctor,
                                                 valk_lval_t *args) {
  valk_lval_t *tag_qexpr = valk_lval_qcons(valk_lval_sym(ctor->name), valk_lval_nil());
  valk_lval_t *tag = valk_lval_cons(valk_lval_sym("head"), valk_lval_cons(tag_qexpr, valk_lval_nil()));

  u64 arg_count = valk_lval_list_count(args);
  bool keyword_mode = (arg_count > 0 && valk_tt_is_keyword(args->cons.head));

  u64 result_capacity = ctor->field_count + 2;
  valk_lval_t **result_elems = valk_mem_alloc(sizeof(valk_lval_t *) * result_capacity);
  result_elems[0] = valk_lval_sym("list");
  result_elems[1] = tag;

  if (keyword_mode) {
    for (u64 f = 0; f < ctor->field_count; f++) {
      valk_lval_t *found = NULL;
      valk_lval_t *curr = args;
      while (LVAL_TYPE(curr) != LVAL_NIL) {
        valk_lval_t *key = curr->cons.head;
        curr = curr->cons.tail;
        if (LVAL_TYPE(curr) == LVAL_NIL) break;
        if (LVAL_TYPE(key) == LVAL_SYM && strcmp(key->str, ctor->fields[f].name) == 0) {
          found = curr->cons.head;
          break;
        }
        curr = curr->cons.tail;
      }
      if (found) {
        result_elems[2 + f] = valk_tt_transform_expr(env, scope, found);
      } else {
        return valk_lval_err("constructor '%s': missing field '%s'", ctor->name, ctor->fields[f].name);
      }
    }
  } else {
    if (arg_count != ctor->field_count) {
      return valk_lval_err("constructor '%s': expected %llu args, got %llu",
                           ctor->name, ctor->field_count, arg_count);
    }
    valk_lval_t *curr = args;
    for (u64 f = 0; f < ctor->field_count; f++) {
      result_elems[2 + f] = valk_tt_transform_expr(env, scope, curr->cons.head);
      curr = curr->cons.tail;
    }
  }

  valk_lval_t *result = valk_lval_nil();
  for (u64 j = 2 + ctor->field_count; j > 0; j--) {
    result = valk_lval_cons(result_elems[j - 1], result);
  }
  return result;
}

// ---------------------------------------------------------------------------
// Record update: (with var :field1 v1 :field2 v2 ...)
// Rewrites to a fresh record with overridden fields, others copied via nth
// ---------------------------------------------------------------------------

#define VALK_TT_MAX_RECORD_OVERRIDES 64

valk_lval_t *valk_tt_transform_record_update(valk_type_env_t *env,
                                              valk_type_scope_t *scope,
                                              const char *var_name,
                                              const char *type_name,
                                              valk_lval_t *expr) {
  valk_constructor_t *ctor = find_ctor_for_type(env, type_name);
  if (!ctor) return valk_lval_err("with: no constructor for type '%s'", type_name);

  u64 count = valk_lval_list_count(expr);
  struct { const char *field; valk_lval_t *value; } overrides[VALK_TT_MAX_RECORD_OVERRIDES];
  u64 override_count = 0;

  for (u64 i = 2; i + 1 < count; i += 2) {
    if (override_count >= VALK_TT_MAX_RECORD_OVERRIDES) {
      fprintf(stderr, "[type-transform] warning: record update has more than %d fields, truncating\n",
              VALK_TT_MAX_RECORD_OVERRIDES);
      break;
    }
    valk_lval_t *key = valk_lval_list_nth(expr, i);
    valk_lval_t *val = valk_lval_list_nth(expr, i + 1);
    if (LVAL_TYPE(key) != LVAL_SYM || key->str[0] != ':')
      return valk_lval_err("with: expected keyword field name");
    overrides[override_count].field = key->str;
    overrides[override_count].value = val;
    override_count++;
  }

  u64 result_count = ctor->field_count + 2;
  valk_lval_t **elems = valk_mem_alloc(sizeof(valk_lval_t *) * result_count);
  elems[0] = valk_lval_sym("list");
  elems[1] = valk_lval_cons(valk_lval_sym("nth"),
    valk_lval_cons(valk_lval_num(1),
      valk_lval_cons(valk_lval_sym(var_name), valk_lval_nil())));

  for (u64 f = 0; f < ctor->field_count; f++) {
    bool overridden = false;
    for (u64 o = 0; o < override_count; o++) {
      if (strcmp(ctor->fields[f].name, overrides[o].field) == 0) {
        elems[2 + f] = valk_tt_transform_expr(env, scope, overrides[o].value);
        overridden = true;
        break;
      }
    }
    if (!overridden) {
      elems[2 + f] = valk_lval_cons(valk_lval_sym("nth"),
        valk_lval_cons(valk_lval_num((long)(f + 2)),
          valk_lval_cons(valk_lval_sym(var_name), valk_lval_nil())));
    }
  }

  valk_lval_t *result = valk_lval_nil();
  for (u64 j = result_count; j > 0; j--)
    result = valk_lval_cons(elems[j - 1], result);
  return result;
}

// ---------------------------------------------------------------------------
// Accessor: Foo:field → (nth idx arg)
// ---------------------------------------------------------------------------

valk_lval_t *valk_tt_transform_accessor(valk_type_env_t *env,
                                         valk_type_scope_t *scope,
                                         const char *sym,
                                         valk_lval_t *arg) {
  const char *colon = strchr(sym, ':');
  u64 ctor_len = colon - sym;
  char ctor_name[ctor_len + 1];
  memcpy(ctor_name, sym, ctor_len);
  ctor_name[ctor_len] = '\0';
  const char *field_name_raw = colon;

  valk_constructor_t *ctor = valk_type_env_find_constructor(env, ctor_name);
  if (!ctor) ctor = valk_tt_find_constructor_by_short_name(env, ctor_name);
  if (!ctor) {
    return valk_lval_err("unknown constructor '%s' in accessor '%s'", ctor_name, sym);
  }

  for (u64 i = 0; i < ctor->field_count; i++) {
    if (strcmp(ctor->fields[i].name, field_name_raw) == 0) {
      valk_lval_t *index = valk_lval_num((long)(i + 2));
      valk_lval_t *nth_sym = valk_lval_sym("nth");
      valk_lval_t *target = valk_tt_transform_expr(env, scope, arg);
      return valk_lval_cons(nth_sym, valk_lval_cons(index, valk_lval_cons(target, valk_lval_nil())));
    }
  }

  return valk_lval_err("constructor '%s' has no field '%s'", ctor_name, field_name_raw + 1);
}

// ---------------------------------------------------------------------------
// Match: (match val {pat1 body1} {pat2 body2} ...)
// Rewrites to nested if with the match value bound to __match_val.
// ---------------------------------------------------------------------------

valk_lval_t *valk_tt_transform_match(valk_type_env_t *env,
                                      valk_type_scope_t *scope,
                                      valk_lval_t *match_form) {
  u64 count = valk_lval_list_count(match_form);
  if (count < 3) {
    return valk_lval_err("match requires a value and at least one clause");
  }

  valk_lval_t *match_val = valk_tt_transform_expr(env, scope, valk_lval_list_nth(match_form, 1));

  valk_lval_t *val_sym = valk_lval_sym("__match_val");
  valk_lval_t *bind = valk_lval_cons(valk_lval_sym("="),
    valk_lval_cons(valk_lval_qcons(val_sym, valk_lval_nil()),
      valk_lval_cons(match_val, valk_lval_nil())));

  valk_lval_t *chain = valk_lval_cons(valk_lval_sym("error"),
    valk_lval_cons(valk_lval_str("match: no pattern matched"), valk_lval_nil()));

  for (u64 i = count - 1; i >= 2; i--) {
    valk_lval_t *clause = valk_lval_list_nth(match_form, i);
    if (!valk_tt_is_qexpr(clause)) continue; // LCOV_EXCL_BR_LINE — parser always produces qexpr match clauses

    u64 clause_len = valk_lval_list_count(clause);
    if (clause_len < 2) continue; // LCOV_EXCL_BR_LINE — parser prevents empty match clauses

    valk_lval_t *pattern = valk_lval_list_nth(clause, 0);
#ifdef VALK_COVERAGE
    valk_coverage_unmark_expr_tree(pattern);
#endif
    valk_lval_t *body;
    if (clause_len == 2) {
      body = valk_lval_list_nth(clause, 1);
    } else {
      valk_lval_t *do_exprs = valk_lval_nil();
      for (u64 j = clause_len; j >= 2; j--)
        do_exprs = valk_lval_cons(valk_lval_list_nth(clause, j - 1), do_exprs);
      body = valk_lval_cons(valk_lval_sym("do"), do_exprs);
    }

    // Wildcard pattern
    if (LVAL_TYPE(pattern) == LVAL_SYM && strcmp(pattern->str, "_") == 0) {
      chain = valk_tt_transform_expr(env, scope, body);
      continue;
    }

    // Literal pattern (string or number)
    if (LVAL_TYPE(pattern) == LVAL_STR || LVAL_TYPE(pattern) == LVAL_NUM) {
      valk_lval_t *cond = valk_lval_cons(valk_lval_sym("=="),
        valk_lval_cons(valk_lval_sym("__match_val"),
          valk_lval_cons(pattern, valk_lval_nil())));

      valk_lval_t *transformed_body = valk_tt_transform_expr(env, scope, body);
      valk_lval_t *true_branch = valk_lval_qcons(transformed_body, valk_lval_nil());
      true_branch->flags |= LVAL_FLAG_QUOTED;
      valk_lval_t *false_branch = valk_lval_qcons(chain, valk_lval_nil());
      false_branch->flags |= LVAL_FLAG_QUOTED;

      chain = valk_lval_cons(valk_lval_sym("if"),
        valk_lval_cons(cond,
          valk_lval_cons(true_branch,
            valk_lval_cons(false_branch, valk_lval_nil()))));
      continue;
    }

    // Non-constructor list pattern: treat as body (rare)
    if (LVAL_TYPE(pattern) != LVAL_CONS || (pattern->flags & LVAL_FLAG_QUOTED)) {
      chain = valk_tt_transform_expr(env, scope, body);
      continue;
    }

    // Constructor pattern: (Ctor arg1 arg2 ...) or (Ctor :field1 var1 :field2 var2 ...)
    valk_lval_t *pat_head = pattern->cons.head;
    if (LVAL_TYPE(pat_head) != LVAL_SYM) continue; // LCOV_EXCL_BR_LINE — parser always produces symbol pattern heads

    valk_constructor_t *ctor = valk_type_env_find_constructor(env, pat_head->str);
    if (!ctor) ctor = valk_tt_find_constructor_by_short_name(env, pat_head->str);
    if (!ctor) continue;

    valk_lval_t *cond = valk_lval_cons(valk_lval_sym("=="),
      valk_lval_cons(
        valk_lval_cons(valk_lval_sym("head"), valk_lval_cons(valk_lval_sym("__match_val"), valk_lval_nil())),
        valk_lval_cons(
          valk_lval_cons(valk_lval_sym("head"), valk_lval_cons(valk_lval_qcons(valk_lval_sym(ctor->name), valk_lval_nil()), valk_lval_nil())),
          valk_lval_nil())));

    valk_lval_t *pat_args = pattern->cons.tail;
    u64 pat_arg_count = valk_lval_list_count(pat_args);
    bool pat_keyword = (pat_arg_count > 0 && valk_tt_is_keyword(pat_args->cons.head));

    valk_lval_t *bindings = valk_lval_nil();
    valk_lval_t *bindings_tail = bindings;

    if (pat_keyword) {
      valk_lval_t *curr = pat_args;
      while (LVAL_TYPE(curr) != LVAL_NIL) {
        valk_lval_t *key = curr->cons.head;
        curr = curr->cons.tail;
        if (LVAL_TYPE(curr) == LVAL_NIL) break; // LCOV_EXCL_BR_LINE — parser pairs keyword-value
        valk_lval_t *var = curr->cons.head;
        curr = curr->cons.tail;

        // LCOV_EXCL_BR_START — parser always produces valid keyword pattern bindings
        if (LVAL_TYPE(key) != LVAL_SYM || !valk_tt_is_keyword(key)) continue;
        if (LVAL_TYPE(var) != LVAL_SYM) continue;
        // LCOV_EXCL_BR_STOP

        long index = -1;
        for (u64 f = 0; f < ctor->field_count; f++) {
          if (strcmp(ctor->fields[f].name, key->str) == 0) {
            index = (long)(f + 2);
            break;
          }
        }
        if (index < 0) continue; // LCOV_EXCL_BR_LINE — parser field names match constructor fields

        valk_lval_t *nth_call = valk_lval_cons(valk_lval_sym("nth"),
          valk_lval_cons(valk_lval_num(index),
            valk_lval_cons(valk_lval_sym("__match_val"), valk_lval_nil())));
        valk_lval_t *assign = valk_lval_cons(valk_lval_sym("="),
          valk_lval_cons(valk_lval_qcons(valk_lval_sym(var->str), valk_lval_nil()),
            valk_lval_cons(nth_call, valk_lval_nil())));

        if (LVAL_TYPE(bindings) == LVAL_NIL) {
          bindings = valk_lval_cons(assign, valk_lval_nil());
          bindings_tail = bindings;
        } else {
          bindings_tail->cons.tail = valk_lval_cons(assign, valk_lval_nil());
          bindings_tail = bindings_tail->cons.tail;
        }
      }
    } else {
      valk_lval_t *curr = pat_args;
      for (u64 f = 0; f < ctor->field_count && LVAL_TYPE(curr) != LVAL_NIL; f++) {
        valk_lval_t *var = curr->cons.head;
        curr = curr->cons.tail;
        if (LVAL_TYPE(var) != LVAL_SYM) continue; // LCOV_EXCL_BR_LINE — parser always produces symbol vars in patterns
        if (strcmp(var->str, "_") == 0) continue;

        valk_lval_t *nth_call = valk_lval_cons(valk_lval_sym("nth"),
          valk_lval_cons(valk_lval_num((long)(f + 2)),
            valk_lval_cons(valk_lval_sym("__match_val"), valk_lval_nil())));
        valk_lval_t *assign = valk_lval_cons(valk_lval_sym("="),
          valk_lval_cons(valk_lval_qcons(valk_lval_sym(var->str), valk_lval_nil()),
            valk_lval_cons(nth_call, valk_lval_nil())));

        if (LVAL_TYPE(bindings) == LVAL_NIL) {
          bindings = valk_lval_cons(assign, valk_lval_nil());
          bindings_tail = bindings;
        } else {
          bindings_tail->cons.tail = valk_lval_cons(assign, valk_lval_nil());
          bindings_tail = bindings_tail->cons.tail;
        }
      }
    }

    valk_lval_t *transformed_body = valk_tt_transform_expr(env, scope, body);

    valk_lval_t *do_body;
    if (LVAL_TYPE(bindings) == LVAL_NIL) {
      do_body = transformed_body;
    } else {
      bindings_tail->cons.tail = valk_lval_cons(transformed_body, valk_lval_nil());
      do_body = valk_lval_cons(valk_lval_sym("do"), bindings);
    }

    valk_lval_t *true_branch = valk_lval_qcons(do_body, valk_lval_nil());
    true_branch->flags |= LVAL_FLAG_QUOTED;
    valk_lval_t *false_branch = valk_lval_qcons(chain, valk_lval_nil());
    false_branch->flags |= LVAL_FLAG_QUOTED;

    chain = valk_lval_cons(valk_lval_sym("if"),
      valk_lval_cons(cond,
        valk_lval_cons(true_branch,
          valk_lval_cons(false_branch, valk_lval_nil()))));
  }

  return valk_lval_cons(valk_lval_sym("do"),
    valk_lval_cons(bind,
      valk_lval_cons(chain, valk_lval_nil())));
}
