#include "type_env.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "memory.h"

valk_type_env_t *valk_type_env_new(void) {
  valk_type_env_t *env = calloc(1, sizeof(valk_type_env_t));
  return env;
}

void valk_type_env_free(valk_type_env_t *env) {
  if (!env) return;
  for (u64 i = 0; i < env->type_count; i++) {
    valk_type_decl_t *t = env->types[i];
    free(t->name);
    for (u64 p = 0; p < t->param_count; p++) free(t->params[p]);
    for (u64 c = 0; c < t->constructor_count; c++) {
      valk_constructor_t *ctor = t->constructors[c];
      free(ctor->name);
      free(ctor->type_name);
      for (u64 f = 0; f < ctor->field_count; f++) {
        free(ctor->fields[f].name);
        free(ctor->fields[f].type_name);
      }
      free(ctor);
    }
    free(t);
  }
  free(env);
}

valk_type_decl_t *valk_type_env_find_type(valk_type_env_t *env, const char *name) {
  for (u64 i = 0; i < env->type_count; i++) {
    if (strcmp(env->types[i]->name, name) == 0) return env->types[i];
  }
  return NULL;
}

valk_constructor_t *valk_type_env_find_constructor(valk_type_env_t *env, const char *name) {
  for (u64 i = 0; i < env->constructor_count; i++) {
    if (strcmp(env->constructors[i]->name, name) == 0) return env->constructors[i];
  }
  return NULL;
}

valk_type_decl_t *valk_type_env_type_for_constructor(valk_type_env_t *env, const char *ctor_name) {
  for (u64 i = 0; i < env->type_count; i++) {
    valk_type_decl_t *t = env->types[i];
    for (u64 c = 0; c < t->constructor_count; c++) {
      if (strcmp(t->constructors[c]->name, ctor_name) == 0) return t;
    }
  }
  return NULL;
}

static bool is_keyword(valk_lval_t *v) {
  return LVAL_TYPE(v) == LVAL_SYM && v->str[0] == ':';
}

static valk_constructor_t *parse_constructor(const char *name, const char *type_name,
                                             valk_lval_t *field_list) {
  valk_constructor_t *ctor = calloc(1, sizeof(valk_constructor_t));
  ctor->name = strdup(name);
  ctor->type_name = strdup(type_name);

  valk_lval_t *curr = field_list;
  u64 pos = 0;
  while (LVAL_TYPE(curr) != LVAL_NIL) {
    valk_lval_t *key = curr->cons.head;
    if (!is_keyword(key)) break;
    curr = curr->cons.tail;
    if (LVAL_TYPE(curr) == LVAL_NIL) break;
    valk_lval_t *type_sym = curr->cons.head;

    ctor->fields[pos].name = strdup(key->str);
    ctor->fields[pos].type_name = (LVAL_TYPE(type_sym) == LVAL_SYM) ? strdup(type_sym->str) : strdup("Any");
    ctor->fields[pos].position = pos;
    pos++;
    curr = curr->cons.tail;
  }
  ctor->field_count = pos;
  return ctor;
}

static bool is_qexpr(valk_lval_t *v) {
  return LVAL_TYPE(v) == LVAL_CONS && (v->flags & LVAL_FLAG_QUOTED);
}

valk_lval_t *valk_type_env_register(valk_type_env_t *env, valk_lval_t *type_form) {
  u64 count = valk_lval_list_count(type_form);
  if (count < 3) {
    return valk_lval_err("type requires at least type name and one variant");
  }

  valk_lval_t *name_qexpr = valk_lval_list_nth(type_form, 1);
  if (!is_qexpr(name_qexpr)) {
    return valk_lval_err("type: first argument must be a {name} qexpr");
  }

  valk_lval_t *first_in_name = name_qexpr->cons.head;
  if (LVAL_TYPE(first_in_name) != LVAL_SYM) {
    return valk_lval_err("type: name must be a symbol");
  }
  char *type_name = first_in_name->str;

  if (valk_type_env_find_type(env, type_name)) {
    return NULL;
  }

  valk_type_decl_t *decl = calloc(1, sizeof(valk_type_decl_t));
  decl->name = strdup(type_name);

  valk_lval_t *param_iter = name_qexpr->cons.tail;
  while (LVAL_TYPE(param_iter) != LVAL_NIL) {
    valk_lval_t *p = param_iter->cons.head;
    if (LVAL_TYPE(p) == LVAL_SYM) {
      decl->params[decl->param_count++] = strdup(p->str);
    }
    param_iter = param_iter->cons.tail;
  }

  valk_lval_t *first_variant = valk_lval_list_nth(type_form, 2);
  if (!is_qexpr(first_variant)) {
    free(decl->name);
    free(decl);
    return valk_lval_err("type '%s': variants must be qexprs", type_name);
  }

  valk_lval_t *fv_head = first_variant->cons.head;
  bool is_product = is_keyword(fv_head);

  if (is_product) {
    decl->is_product = true;
    valk_constructor_t *ctor = parse_constructor(type_name, type_name, first_variant);
    decl->constructors[decl->constructor_count++] = ctor;
    env->constructors[env->constructor_count++] = ctor;
  } else {
    decl->is_product = false;
    for (u64 i = 2; i < count; i++) {
      valk_lval_t *variant = valk_lval_list_nth(type_form, i);
      if (!is_qexpr(variant)) {
        continue;
      }
      valk_lval_t *ctor_head = variant->cons.head;
      if (LVAL_TYPE(ctor_head) != LVAL_SYM) {
        continue;
      }
      char *ctor_name_raw = ctor_head->str;

      char qualified[256];
      snprintf(qualified, sizeof(qualified), "%s::%s", type_name, ctor_name_raw);

      if (valk_type_env_find_constructor(env, qualified)) {
        return valk_lval_err("constructor '%s' already declared", qualified);
      }

      valk_constructor_t *ctor = parse_constructor(qualified, type_name, variant->cons.tail);
      decl->constructors[decl->constructor_count++] = ctor;
      env->constructors[env->constructor_count++] = ctor;
    }
  }

  env->types[env->type_count++] = decl;
  return NULL;
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
  if (LVAL_TYPE(expr) != LVAL_CONS || (expr->flags & LVAL_FLAG_QUOTED)) return false;
  valk_lval_t *head = expr->cons.head;
  return LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "match") == 0;
}

static bool is_accessor(const char *sym) {
  if (!sym || sym[0] < 'A' || sym[0] > 'Z') return false;
  const char *colon = strchr(sym, ':');
  if (!colon || colon == sym || colon[1] == '\0') return false;
  if (colon[1] == ':') return false;
  return true;
}

static valk_lval_t *transform_expr(valk_type_env_t *env, valk_lval_t *expr);

static valk_lval_t *transform_constructor_call(valk_type_env_t *env, valk_constructor_t *ctor,
                                               valk_lval_t *args) {
  valk_lval_t *tag_qexpr = valk_lval_qcons(valk_lval_sym(ctor->name), valk_lval_nil());
  valk_lval_t *tag = valk_lval_cons(valk_lval_sym("head"), valk_lval_cons(tag_qexpr, valk_lval_nil()));

  u64 arg_count = valk_lval_list_count(args);
  bool keyword_mode = (arg_count > 0 && is_keyword(args->cons.head));

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
        result_elems[2 + f] = transform_expr(env, found);
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
      result_elems[2 + f] = transform_expr(env, curr->cons.head);
      curr = curr->cons.tail;
    }
  }

  valk_lval_t *result = valk_lval_nil();
  for (u64 j = 2 + ctor->field_count; j > 0; j--) {
    result = valk_lval_cons(result_elems[j - 1], result);
  }
  return result;
}

static valk_constructor_t *find_constructor_by_short_name(valk_type_env_t *env, const char *short_name) {
  for (u64 i = 0; i < env->constructor_count; i++) {
    const char *full = env->constructors[i]->name;
    const char *sep = strstr(full, "::");
    if (sep && strcmp(sep + 2, short_name) == 0)
      return env->constructors[i];
  }
  return NULL;
}

static valk_lval_t *transform_accessor(valk_type_env_t *env, const char *sym, valk_lval_t *arg) {
  const char *colon = strchr(sym, ':');
  u64 ctor_len = colon - sym;
  char ctor_name[ctor_len + 1];
  memcpy(ctor_name, sym, ctor_len);
  ctor_name[ctor_len] = '\0';
  const char *field_name_raw = colon;

  valk_constructor_t *ctor = valk_type_env_find_constructor(env, ctor_name);
  if (!ctor) ctor = find_constructor_by_short_name(env, ctor_name);
  if (!ctor) {
    return valk_lval_err("unknown constructor '%s' in accessor '%s'", ctor_name, sym);
  }

  for (u64 i = 0; i < ctor->field_count; i++) {
    if (strcmp(ctor->fields[i].name, field_name_raw) == 0) {
      valk_lval_t *index = valk_lval_num((long)(i + 2));
      valk_lval_t *nth_sym = valk_lval_sym("nth");
      valk_lval_t *target = transform_expr(env, arg);
      return valk_lval_cons(nth_sym, valk_lval_cons(index, valk_lval_cons(target, valk_lval_nil())));
    }
  }

  return valk_lval_err("constructor '%s' has no field '%s'", ctor_name, field_name_raw + 1);
}

static valk_lval_t *transform_match(valk_type_env_t *env, valk_lval_t *match_form) {
  u64 count = valk_lval_list_count(match_form);
  if (count < 3) {
    return valk_lval_err("match requires a value and at least one clause");
  }

  valk_lval_t *match_val = transform_expr(env, valk_lval_list_nth(match_form, 1));

  valk_lval_t *val_sym = valk_lval_sym("__match_val");
  valk_lval_t *bind = valk_lval_cons(valk_lval_sym("="),
    valk_lval_cons(valk_lval_qcons(val_sym, valk_lval_nil()),
      valk_lval_cons(match_val, valk_lval_nil())));

  valk_lval_t *chain = valk_lval_cons(valk_lval_sym("error"),
    valk_lval_cons(valk_lval_str("match: no pattern matched"), valk_lval_nil()));

  for (u64 i = count - 1; i >= 2; i--) {
    valk_lval_t *clause = valk_lval_list_nth(match_form, i);
    if (!is_qexpr(clause)) continue;

    u64 clause_len = valk_lval_list_count(clause);
    if (clause_len < 2) continue;

    valk_lval_t *pattern = valk_lval_list_nth(clause, 0);
    valk_lval_t *body = valk_lval_list_nth(clause, 1);

    if (LVAL_TYPE(pattern) == LVAL_SYM && strcmp(pattern->str, "_") == 0) {
      chain = transform_expr(env, body);
      continue;
    }

    if (LVAL_TYPE(pattern) != LVAL_CONS || (pattern->flags & LVAL_FLAG_QUOTED)) {
      chain = transform_expr(env, body);
      continue;
    }

    valk_lval_t *pat_head = pattern->cons.head;
    if (LVAL_TYPE(pat_head) != LVAL_SYM) continue;

    valk_constructor_t *ctor = valk_type_env_find_constructor(env, pat_head->str);
    if (!ctor) ctor = find_constructor_by_short_name(env, pat_head->str);
    if (!ctor) continue;

    valk_lval_t *cond = valk_lval_cons(valk_lval_sym("=="),
      valk_lval_cons(
        valk_lval_cons(valk_lval_sym("head"), valk_lval_cons(valk_lval_sym("__match_val"), valk_lval_nil())),
        valk_lval_cons(
          valk_lval_cons(valk_lval_sym("head"), valk_lval_cons(valk_lval_qcons(valk_lval_sym(ctor->name), valk_lval_nil()), valk_lval_nil())),
          valk_lval_nil())));

    valk_lval_t *pat_args = pattern->cons.tail;
    u64 pat_arg_count = valk_lval_list_count(pat_args);
    bool pat_keyword = (pat_arg_count > 0 && is_keyword(pat_args->cons.head));

    valk_lval_t *bindings = valk_lval_nil();
    valk_lval_t *bindings_tail = bindings;

    if (pat_keyword) {
      valk_lval_t *curr = pat_args;
      while (LVAL_TYPE(curr) != LVAL_NIL) {
        valk_lval_t *key = curr->cons.head;
        curr = curr->cons.tail;
        if (LVAL_TYPE(curr) == LVAL_NIL) break;
        valk_lval_t *var = curr->cons.head;
        curr = curr->cons.tail;

        if (LVAL_TYPE(key) != LVAL_SYM || !is_keyword(key)) continue;
        if (LVAL_TYPE(var) != LVAL_SYM) continue;

        long index = -1;
        for (u64 f = 0; f < ctor->field_count; f++) {
          if (strcmp(ctor->fields[f].name, key->str) == 0) {
            index = (long)(f + 2);
            break;
          }
        }
        if (index < 0) continue;

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
        if (LVAL_TYPE(var) != LVAL_SYM) continue;
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

    valk_lval_t *transformed_body = transform_expr(env, body);

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

static valk_lval_t *transform_expr(valk_type_env_t *env, valk_lval_t *expr) {
  if (expr == NULL) return valk_lval_nil();

  valk_ltype_e type = LVAL_TYPE(expr);

  if (type == LVAL_NUM || type == LVAL_STR || type == LVAL_ERR ||
      type == LVAL_FUN || type == LVAL_REF || type == LVAL_HANDLE) {
    return expr;
  }

  if (type == LVAL_NIL) return expr;

  if (type == LVAL_CONS && (expr->flags & LVAL_FLAG_QUOTED)) {
    valk_lval_t *head = expr->cons.head;
    if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "match") == 0) {
      valk_lval_t *as_sexpr = valk_lval_nil();
      u64 count = valk_lval_list_count(expr);
      for (u64 i = count; i > 0; i--) {
        as_sexpr = valk_lval_cons(valk_lval_list_nth(expr, i - 1), as_sexpr);
      }
      valk_lval_t *transformed = transform_match(env, as_sexpr);
      return valk_lval_qcons(transformed, valk_lval_nil());
    }
    valk_lval_t *result = valk_lval_nil();
    u64 count = valk_lval_list_count(expr);
    for (u64 i = count; i > 0; i--) {
      result = valk_lval_qcons(transform_expr(env, valk_lval_list_nth(expr, i - 1)), result);
    }
    return result;
  }

  if (type == LVAL_SYM) return expr;

  if (type != LVAL_CONS) return expr;

  if (is_match_form(expr)) {
    return transform_match(env, expr);
  }

  if (is_type_form(expr)) {
    return valk_lval_nil();
  }

  if (is_sig_form(expr)) {
    return valk_lval_nil();
  }

  valk_lval_t *head = expr->cons.head;

  if (LVAL_TYPE(head) == LVAL_SYM) {
    if (is_accessor(head->str) && valk_lval_list_count(expr) == 2) {
      return transform_accessor(env, head->str, valk_lval_list_nth(expr, 1));
    }

    valk_constructor_t *ctor = valk_type_env_find_constructor(env, head->str);
    if (!ctor) ctor = find_constructor_by_short_name(env, head->str);
    if (ctor) {
      return transform_constructor_call(env, ctor, expr->cons.tail);
    }
  }

  valk_lval_t *result = valk_lval_nil();
  u64 count = valk_lval_list_count(expr);
  for (u64 i = count; i > 0; i--) {
    result = valk_lval_cons(transform_expr(env, valk_lval_list_nth(expr, i - 1)), result);
  }
  return result;
}

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

valk_lval_t *valk_type_transform_expr(valk_lval_t *expr) {
  valk_type_env_t *env = valk_type_env_global();

  if (is_type_form(expr)) {
    valk_lval_t *err = valk_type_env_register(env, expr);
    if (err != NULL) return err;
    return valk_lval_nil();
  }

  if (is_sig_form(expr)) {
    return valk_lval_nil();
  }

  if (env->type_count == 0) return expr;

  return transform_expr(env, expr);
}

valk_lval_t *valk_type_transform(valk_lval_t *exprs) {
  valk_type_env_t *env = valk_type_env_global();

  u64 types_before = env->type_count;

  valk_lval_t *curr = exprs;
  while (LVAL_TYPE(curr) != LVAL_NIL) {
    valk_lval_t *expr = curr->cons.head;
    if (is_type_form(expr)) {
      valk_lval_t *err = valk_type_env_register(env, expr);
      if (err != NULL) {
        return valk_lval_cons(err, valk_lval_nil());
      }
    }
    curr = curr->cons.tail;
  }

  if (env->type_count == 0) {
    return exprs;
  }

  valk_lval_t *result = valk_lval_nil();
  u64 count = valk_lval_list_count(exprs);
  for (u64 i = count; i > 0; i--) {
    valk_lval_t *expr = valk_lval_list_nth(exprs, i - 1);
    valk_lval_t *transformed = transform_expr(env, expr);
    if (LVAL_TYPE(transformed) != LVAL_NIL || (!is_type_form(expr) && !is_sig_form(expr))) {
      result = valk_lval_cons(transformed, result);
    }
  }

  (void)types_before;
  return result;
}
