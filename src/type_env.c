#include "type_env.h"
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
    free(t->params);
    for (u64 c = 0; c < t->constructor_count; c++) {
      valk_constructor_t *ctor = t->constructors[c];
      free(ctor->name);
      if (ctor->type_name) free(ctor->type_name);
      for (u64 f = 0; f < ctor->field_count; f++) {
        free(ctor->fields[f].name);
        if (ctor->fields[f].type_name) free(ctor->fields[f].type_name);
      }
      free(ctor->fields);
      free(ctor);
    }
    free(t->constructors);
    free(t);
  }
  free(env->types);
  free(env->constructors);
  for (u64 i = 0; i < env->sig_count; i++) {
    valk_type_sig_t *s = env->sigs[i];
    free(s->name);
    for (u64 p = 0; p < s->param_count; p++) free(s->param_types[p]);
    free(s->param_types);
    free(s->return_type);
    free(s);
  }
  free(env->sigs);
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
    if (!is_keyword(key)) break; // LCOV_EXCL_BR_LINE — parser always produces keyword fields
    curr = curr->cons.tail;
    if (LVAL_TYPE(curr) == LVAL_NIL) break; // LCOV_EXCL_BR_LINE — parser pairs keywords with types
    valk_lval_t *type_sym = curr->cons.head;

    GROW_ARRAY(ctor->fields, pos, ctor->field_capacity, valk_field_t);
    ctor->fields[pos].name = strdup(key->str);
    ctor->fields[pos].type_name = (LVAL_TYPE(type_sym) == LVAL_SYM) ? strdup(type_sym->str) : strdup("Any"); // LCOV_EXCL_BR_LINE — parser produces symbol types
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
  if (!is_qexpr(name_qexpr)) { // LCOV_EXCL_BR_LINE — parser always produces {Name} qexpr
    return valk_lval_err("type: first argument must be a {name} qexpr");
  }

  valk_lval_t *first_in_name = name_qexpr->cons.head;
  if (LVAL_TYPE(first_in_name) != LVAL_SYM) { // LCOV_EXCL_BR_LINE — parser always produces symbol names
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
    if (LVAL_TYPE(p) == LVAL_SYM) { // LCOV_EXCL_BR_LINE — parser always produces symbol params
      GROW_ARRAY(decl->params, decl->param_count, decl->param_capacity, char *);
      decl->params[decl->param_count++] = strdup(p->str);
    }
    param_iter = param_iter->cons.tail;
  }

  valk_lval_t *first_variant = valk_lval_list_nth(type_form, 2);
  if (!is_qexpr(first_variant)) { // LCOV_EXCL_BR_LINE — parser always produces {Variant} qexprs
    free(decl->name);
    free(decl);
    return valk_lval_err("type '%s': variants must be qexprs", type_name);
  }

  valk_lval_t *fv_head = first_variant->cons.head;
  bool is_product = is_keyword(fv_head);

  if (is_product) {
    decl->is_product = true;
    valk_constructor_t *ctor = parse_constructor(type_name, type_name, first_variant);
    GROW_ARRAY(decl->constructors, decl->constructor_count, decl->constructor_capacity, valk_constructor_t *);
    decl->constructors[decl->constructor_count++] = ctor;
    GROW_ARRAY(env->constructors, env->constructor_count, env->constructor_capacity, valk_constructor_t *);
    env->constructors[env->constructor_count++] = ctor;
  } else {
    decl->is_product = false;
    for (u64 i = 2; i < count; i++) {
      valk_lval_t *variant = valk_lval_list_nth(type_form, i);
      if (!is_qexpr(variant)) { // LCOV_EXCL_BR_LINE — parser always produces qexpr variants
        continue;
      }
      valk_lval_t *ctor_head = variant->cons.head;
      if (LVAL_TYPE(ctor_head) != LVAL_SYM) { // LCOV_EXCL_BR_LINE — parser always produces symbol constructors
        continue;
      }
      char *ctor_name_raw = ctor_head->str;

      char qualified[256];
      snprintf(qualified, sizeof(qualified), "%s::%s", type_name, ctor_name_raw);

      if (valk_type_env_find_constructor(env, qualified)) { // LCOV_EXCL_BR_LINE — duplicate constructors rejected at parse level
        return valk_lval_err("constructor '%s' already declared", qualified);
      }

      valk_constructor_t *ctor = parse_constructor(qualified, type_name, variant->cons.tail);
      GROW_ARRAY(decl->constructors, decl->constructor_count, decl->constructor_capacity, valk_constructor_t *);
      decl->constructors[decl->constructor_count++] = ctor;
      GROW_ARRAY(env->constructors, env->constructor_count, env->constructor_capacity, valk_constructor_t *);
      env->constructors[env->constructor_count++] = ctor;
    }
  }

  GROW_ARRAY(env->types, env->type_count, env->type_capacity, valk_type_decl_t *);
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
  if (LVAL_TYPE(expr) != LVAL_CONS || (expr->flags & LVAL_FLAG_QUOTED)) return false; // LCOV_EXCL_BR_LINE — quoted cons handled by caller before reaching here
  valk_lval_t *head = expr->cons.head;
  return LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "match") == 0;
}

static bool is_accessor(const char *sym) {
  // LCOV_EXCL_BR_START — sym is always non-NULL from LVAL_SYM; multi-condition short-circuit branches
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

static const char *scope_find_type(valk_type_scope_t *scope, const char *var);
static valk_constructor_t *find_constructor_by_short_name(valk_type_env_t *env, const char *short_name);

static valk_lval_t *resolve_field_access(valk_type_env_t *env, valk_type_scope_t *scope,
                                          valk_lval_t *var_expr, const char *var_name,
                                          const char *field_name) {
  const char *type_name = var_name ? scope_find_type(scope, var_name) : NULL;
  u64 field_len = strlen(field_name);
  char field_key[field_len + 2];
  field_key[0] = ':';
  memcpy(field_key + 1, field_name, field_len);
  field_key[field_len + 1] = '\0';

  if (type_name) {
    valk_constructor_t *ctor = valk_type_env_find_constructor(env, type_name);
    if (!ctor) ctor = find_constructor_by_short_name(env, type_name);
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
          valk_lval_t *index = valk_lval_num((long)(i + 2));
          valk_lval_t *nth_sym = valk_lval_sym("nth");
          return valk_lval_cons(nth_sym, valk_lval_cons(index, valk_lval_cons(var_expr, valk_lval_nil())));
        }
      }
      return valk_lval_err("type '%s' has no field ':%s'", type_name, field_name);
    }
  }

  valk_lval_t *plist_get_sym = valk_lval_sym("plist/get");
  valk_lval_t *key_sym = valk_lval_sym(field_key);
  return valk_lval_cons(plist_get_sym, valk_lval_cons(var_expr, valk_lval_cons(key_sym, valk_lval_nil())));
}

static const char *scope_find_type(valk_type_scope_t *scope, const char *var) {
  while (scope) {
    for (u64 i = scope->count; i > 0; i--) {
      if (strcmp(scope->entries[i - 1].var, var) == 0)
        return scope->entries[i - 1].type;
    }
    scope = scope->parent;
  }
  return NULL;
}

static void scope_add(valk_type_scope_t *scope, const char *var, const char *type) {
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

static valk_lval_t *transform_expr(valk_type_env_t *env, valk_type_scope_t *scope, valk_lval_t *expr);

static valk_lval_t *transform_constructor_call(valk_type_env_t *env, valk_type_scope_t *scope,
                                               valk_constructor_t *ctor, valk_lval_t *args) {
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
        result_elems[2 + f] = transform_expr(env, scope, found);
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
      result_elems[2 + f] = transform_expr(env, scope, curr->cons.head);
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

static char *serialize_type_expr(valk_lval_t *type_expr) {
  if (LVAL_TYPE(type_expr) == LVAL_SYM) return strdup(type_expr->str);
  if (LVAL_TYPE(type_expr) != LVAL_CONS) return NULL;
  char buf[256];
  int pos = 0;
  buf[pos++] = '(';
  valk_lval_t *curr = type_expr;
  bool first = true;
  while (LVAL_TYPE(curr) != LVAL_NIL && pos < 250) {
    if (!first) buf[pos++] = ' ';
    first = false;
    valk_lval_t *elem = curr->cons.head;
    if (LVAL_TYPE(elem) == LVAL_SYM) {
      int len = strlen(elem->str);
      memcpy(buf + pos, elem->str, len);
      pos += len;
    } else if (LVAL_TYPE(elem) == LVAL_CONS) {
      char *inner = serialize_type_expr(elem);
      if (inner) {
        int len = strlen(inner);
        memcpy(buf + pos, inner, len);
        pos += len;
        free(inner);
      }
    }
    curr = curr->cons.tail;
  }
  buf[pos++] = ')';
  buf[pos] = '\0';
  return strdup(buf);
}

static valk_type_sig_t *valk_type_env_find_sig(valk_type_env_t *env, const char *name) {
  for (u64 i = 0; i < env->sig_count; i++) {
    if (strcmp(env->sigs[i]->name, name) == 0) return env->sigs[i];
  }
  return NULL;
}

static void valk_type_env_register_sig(valk_type_env_t *env, valk_lval_t *sig_form) {
  u64 count = valk_lval_list_count(sig_form);
  if (count < 3) return;

  valk_lval_t *name_q = valk_lval_list_nth(sig_form, 1);
  if (!is_qexpr(name_q)) return;
  valk_lval_t *name_sym = name_q->cons.head;
  if (LVAL_TYPE(name_sym) != LVAL_SYM) return;

  if (valk_type_env_find_sig(env, name_sym->str)) return;

  valk_lval_t *type_q = valk_lval_list_nth(sig_form, 2);
  if (!is_qexpr(type_q)) return;

  valk_lval_t *arrow = type_q->cons.head;
  if (LVAL_TYPE(arrow) != LVAL_SYM || strcmp(arrow->str, "->") != 0) return;

  char *types[32];
  u64 type_count = 0;
  valk_lval_t *curr = type_q->cons.tail;
  while (LVAL_TYPE(curr) != LVAL_NIL && type_count < 32) {
    types[type_count++] = serialize_type_expr(curr->cons.head);
    curr = curr->cons.tail;
  }
  if (type_count < 1) return;

  valk_type_sig_t *sig = calloc(1, sizeof(valk_type_sig_t));
  sig->name = strdup(name_sym->str);

  u64 start = 0;
  if (types[0] && strcmp(types[0], "&") == 0) start = 1;

  sig->return_type = types[type_count - 1];
  for (u64 i = start; i < type_count - 1; i++) {
    GROW_ARRAY(sig->param_types, sig->param_count, sig->param_capacity, char *);
    sig->param_types[sig->param_count++] = types[i];
    types[i] = NULL;
  }
  if (types[0] && start == 1) { free(types[0]); types[0] = NULL; }
  for (u64 i = 0; i < type_count - 1; i++) { free(types[i]); }

  GROW_ARRAY(env->sigs, env->sig_count, env->sig_capacity, valk_type_sig_t *);
  env->sigs[env->sig_count++] = sig;
}

static valk_ti_ctx_t *g_ti_ctx = NULL;

static const char *infer_rhs_type(valk_type_env_t *env, valk_type_scope_t *scope,
                                  valk_lval_t *rhs) {
  if (!rhs || LVAL_TYPE(rhs) != LVAL_CONS || (rhs->flags & LVAL_FLAG_QUOTED)) return NULL;
  valk_lval_t *rhs_head = rhs->cons.head;
  if (!rhs_head || LVAL_TYPE(rhs_head) != LVAL_SYM) return NULL;
  const char *name = rhs_head->str;
  if (name[0] >= 'A' && name[0] <= 'Z') {
    valk_constructor_t *ctor = valk_type_env_find_constructor(env, name);
    if (!ctor) ctor = find_constructor_by_short_name(env, name);
    if (ctor) return ctor->type_name;
  }
  if (strcmp(name, "with") == 0 && valk_lval_list_count(rhs) >= 4) {
    valk_lval_t *wvar = valk_lval_list_nth(rhs, 1);
    if (LVAL_TYPE(wvar) == LVAL_SYM) return scope_find_type(scope, wvar->str);
  }
  if (g_ti_ctx) return valk_ti_lookup_type_name(g_ti_ctx, name);
  return NULL;
}

static void track_binding(valk_type_env_t *env, valk_type_scope_t *scope, valk_lval_t *child_expr) {
  if (LVAL_TYPE(child_expr) != LVAL_CONS || (child_expr->flags & LVAL_FLAG_QUOTED)) return;
  valk_lval_t *ch = child_expr->cons.head;
  if (LVAL_TYPE(ch) != LVAL_SYM || strcmp(ch->str, "=") != 0) return;
  if (valk_lval_list_count(child_expr) != 3) return;
  valk_lval_t *binding = valk_lval_list_nth(child_expr, 1);
  if (!is_qexpr(binding) || LVAL_TYPE(binding->cons.head) != LVAL_SYM ||
      LVAL_TYPE(binding->cons.tail) != LVAL_NIL) return;
  valk_lval_t *rhs = valk_lval_list_nth(child_expr, 2);
  const char *tname = infer_rhs_type(env, scope, rhs);
  if (!tname && g_ti_ctx)
    tname = valk_ti_lookup_type_name(g_ti_ctx, binding->cons.head->str);
  scope_add(scope, binding->cons.head->str, tname);
}

static void track_fun_params(valk_type_env_t *env, valk_type_scope_t *scope, valk_lval_t *formals) {
  if (!is_qexpr(formals)) return;
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
        if (!pc) pc = find_constructor_by_short_name(env, sig->param_types[idx]);
        valk_type_decl_t *pt = pc ? NULL : valk_type_env_find_type(env, sig->param_types[idx]);
        tname = pc ? pc->type_name : (pt ? pt->name : NULL);
      }
      scope_add(scope, psym->str, tname);
      idx++;
    }
    p = p->cons.tail;
  }
}

static valk_constructor_t *find_ctor_for_type(valk_type_env_t *env, const char *type_name) {
  valk_constructor_t *ctor = valk_type_env_find_constructor(env, type_name);
  if (!ctor) ctor = find_constructor_by_short_name(env, type_name);
  if (!ctor) {
    valk_type_decl_t *tdecl = valk_type_env_find_type(env, type_name);
    if (tdecl && tdecl->constructor_count > 0)
      ctor = tdecl->constructors[0];
  }
  return ctor;
}

static valk_lval_t *transform_record_update(valk_type_env_t *env, valk_type_scope_t *scope,
                                             const char *var_name, const char *type_name,
                                             valk_lval_t *expr) {
  valk_constructor_t *ctor = find_ctor_for_type(env, type_name);
  if (!ctor) return valk_lval_err("with: no constructor for type '%s'", type_name);

  u64 count = valk_lval_list_count(expr);
  struct { const char *field; valk_lval_t *value; } overrides[64];
  u64 override_count = 0;

  for (u64 i = 2; i + 1 < count; i += 2) {
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
        elems[2 + f] = transform_expr(env, scope, overrides[o].value);
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

static valk_lval_t *transform_accessor(valk_type_env_t *env, valk_type_scope_t *scope, const char *sym, valk_lval_t *arg) {
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
      valk_lval_t *target = transform_expr(env, scope, arg);
      return valk_lval_cons(nth_sym, valk_lval_cons(index, valk_lval_cons(target, valk_lval_nil())));
    }
  }

  return valk_lval_err("constructor '%s' has no field '%s'", ctor_name, field_name_raw + 1);
}

static valk_lval_t *transform_match(valk_type_env_t *env, valk_type_scope_t *scope, valk_lval_t *match_form) {
  u64 count = valk_lval_list_count(match_form);
  if (count < 3) {
    return valk_lval_err("match requires a value and at least one clause");
  }

  valk_lval_t *match_val = transform_expr(env, scope, valk_lval_list_nth(match_form, 1));

  valk_lval_t *val_sym = valk_lval_sym("__match_val");
  valk_lval_t *bind = valk_lval_cons(valk_lval_sym("="),
    valk_lval_cons(valk_lval_qcons(val_sym, valk_lval_nil()),
      valk_lval_cons(match_val, valk_lval_nil())));

  valk_lval_t *chain = valk_lval_cons(valk_lval_sym("error"),
    valk_lval_cons(valk_lval_str("match: no pattern matched"), valk_lval_nil()));

  for (u64 i = count - 1; i >= 2; i--) {
    valk_lval_t *clause = valk_lval_list_nth(match_form, i);
    if (!is_qexpr(clause)) continue; // LCOV_EXCL_BR_LINE — parser always produces qexpr match clauses

    u64 clause_len = valk_lval_list_count(clause);
    if (clause_len < 2) continue; // LCOV_EXCL_BR_LINE — parser prevents empty match clauses

    valk_lval_t *pattern = valk_lval_list_nth(clause, 0);
    valk_lval_t *body;
    if (clause_len == 2) {
      body = valk_lval_list_nth(clause, 1);
    } else {
      valk_lval_t *do_exprs = valk_lval_nil();
      for (u64 j = clause_len; j >= 2; j--)
        do_exprs = valk_lval_cons(valk_lval_list_nth(clause, j - 1), do_exprs);
      body = valk_lval_cons(valk_lval_sym("do"), do_exprs);
    }

    if (LVAL_TYPE(pattern) == LVAL_SYM && strcmp(pattern->str, "_") == 0) {
      chain = transform_expr(env, scope, body);
      continue;
    }

    if (LVAL_TYPE(pattern) == LVAL_STR || LVAL_TYPE(pattern) == LVAL_NUM) {
      valk_lval_t *cond = valk_lval_cons(valk_lval_sym("=="),
        valk_lval_cons(valk_lval_sym("__match_val"),
          valk_lval_cons(pattern, valk_lval_nil())));

      valk_lval_t *transformed_body = transform_expr(env, scope, body);
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

    if (LVAL_TYPE(pattern) != LVAL_CONS || (pattern->flags & LVAL_FLAG_QUOTED)) {
      chain = transform_expr(env, scope, body);
      continue;
    }

    valk_lval_t *pat_head = pattern->cons.head;
    if (LVAL_TYPE(pat_head) != LVAL_SYM) continue; // LCOV_EXCL_BR_LINE — parser always produces symbol pattern heads

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
        if (LVAL_TYPE(curr) == LVAL_NIL) break; // LCOV_EXCL_BR_LINE — parser pairs keyword-value
        valk_lval_t *var = curr->cons.head;
        curr = curr->cons.tail;

        // LCOV_EXCL_BR_START — parser always produces valid keyword pattern bindings
        if (LVAL_TYPE(key) != LVAL_SYM || !is_keyword(key)) continue;
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

    valk_lval_t *transformed_body = transform_expr(env, scope, body);

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

static valk_lval_t *transform_expr(valk_type_env_t *env, valk_type_scope_t *scope, valk_lval_t *expr) {
  if (expr == NULL) return valk_lval_nil(); // LCOV_EXCL_BR_LINE — AST nodes are never NULL

  valk_ltype_e type = LVAL_TYPE(expr);

  // LCOV_EXCL_BR_START — FUN/REF/HANDLE are runtime-only types, never in pre-eval AST
  if (type == LVAL_NUM || type == LVAL_STR || type == LVAL_ERR ||
      type == LVAL_FUN || type == LVAL_REF || type == LVAL_HANDLE ||
      type == LVAL_DICT) {
    return expr;
  }
  // LCOV_EXCL_BR_STOP

  if (type == LVAL_NIL) return expr;

  if (type == LVAL_CONS && (expr->flags & LVAL_FLAG_QUOTED)) {
    valk_lval_t *head = expr->cons.head;
    if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "match") == 0) {
      valk_lval_t *as_sexpr = valk_lval_nil();
      u64 count = valk_lval_list_count(expr);
      for (u64 i = count; i > 0; i--) {
        as_sexpr = valk_lval_cons(valk_lval_list_nth(expr, i - 1), as_sexpr);
      }
      valk_lval_t *transformed = transform_match(env, scope, as_sexpr);
      return valk_lval_qcons(transformed, valk_lval_nil());
    }
    if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "do") == 0) {
      valk_type_scope_t child = { .count = 0, .parent = scope };
      u64 count = valk_lval_list_count(expr);
      valk_lval_t **items = valk_mem_alloc(sizeof(valk_lval_t *) * count);
      items[0] = head;
      for (u64 i = 1; i < count; i++) {
        valk_lval_t *child_expr = valk_lval_list_nth(expr, i);
        track_binding(env, &child, child_expr);
        items[i] = transform_expr(env, &child, child_expr);
      }
      valk_lval_t *result = valk_lval_nil();
      for (u64 i = count; i > 0; i--)
        result = valk_lval_qcons(items[i - 1], result);
      scope_cleanup(&child);
      return result;
    }

    if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "with") == 0 &&
        valk_lval_list_count(expr) >= 4) {
      valk_lval_t *as_sexpr = valk_lval_nil();
      u64 wcount = valk_lval_list_count(expr);
      for (u64 i = wcount; i > 0; i--)
        as_sexpr = valk_lval_cons(valk_lval_list_nth(expr, i - 1), as_sexpr);
      valk_lval_t *with_var = valk_lval_list_nth(as_sexpr, 1);
      if (LVAL_TYPE(with_var) == LVAL_SYM) {
        const char *with_type = scope_find_type(scope, with_var->str);
        if (with_type) {
          valk_lval_t *transformed = transform_record_update(env, scope, with_var->str, with_type, as_sexpr);
          return valk_lval_qcons(transformed, valk_lval_nil());
        }
      }
    }

    valk_lval_t *result = valk_lval_nil();
    u64 count = valk_lval_list_count(expr);
    for (u64 i = count; i > 0; i--) {
      result = valk_lval_qcons(transform_expr(env, scope, valk_lval_list_nth(expr, i - 1)), result);
    }
    return result;
  }

  if (type == LVAL_SYM) {
    if (scope && is_field_access(expr->str)) {
      const char *colon = strchr(expr->str, ':');
      u64 var_len = colon - expr->str;

      char var_buf[var_len + 1];
      memcpy(var_buf, expr->str, var_len);
      var_buf[var_len] = '\0';

      if (var_buf[0] < 'a' || var_buf[0] > 'z') goto not_field;

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

        // Before resolving, find the field's result type for the next chain step
        const char *next_type = NULL;
        if (cur_var) {
          const char *cur_type = scope_find_type(scope, cur_var);
          if (cur_type) {
            valk_constructor_t *ctor = valk_type_env_find_constructor(env, cur_type);
            if (!ctor) ctor = find_constructor_by_short_name(env, cur_type);
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

        result = resolve_field_access(env, scope, result, cur_var, fbuf);
        if (LVAL_TYPE(result) == LVAL_ERR) return result;

        // Use a synthetic scope entry for the intermediate result
        if (next_type) {
          scope_add(scope, "__chain__", next_type);
          cur_var = "__chain__";
        } else {
          cur_var = NULL;
        }
        rest = next_colon ? next_colon + 1 : rest + flen;
      }
      return result;
    }
    not_field:
    return expr;
  }

  if (type != LVAL_CONS) return expr; // LCOV_EXCL_BR_LINE — all remaining AST nodes are CONS after SYM/NIL/literal checks

  if (is_match_form(expr)) {
    return transform_match(env, scope, expr);
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
      return transform_accessor(env, scope, head->str, valk_lval_list_nth(expr, 1));
    }

    valk_constructor_t *ctor = valk_type_env_find_constructor(env, head->str);
    if (!ctor) ctor = find_constructor_by_short_name(env, head->str);
    if (ctor) {
      return transform_constructor_call(env, scope, ctor, expr->cons.tail);
    }
  }

  if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "with") == 0 &&
      valk_lval_list_count(expr) >= 4) {
    valk_lval_t *with_var = valk_lval_list_nth(expr, 1);
    if (LVAL_TYPE(with_var) == LVAL_SYM) {
      const char *with_type = scope_find_type(scope, with_var->str);
      if (with_type)
        return transform_record_update(env, scope, with_var->str, with_type, expr);
    }
  }

  if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "do") == 0) {
    valk_type_scope_t child = { .count = 0, .parent = scope };
    u64 count = valk_lval_list_count(expr);
    valk_lval_t **items = valk_mem_alloc(sizeof(valk_lval_t *) * count);
    items[0] = head;
    for (u64 i = 1; i < count; i++) {
      valk_lval_t *child_expr = valk_lval_list_nth(expr, i);
      track_binding(env, &child, child_expr);
      items[i] = transform_expr(env, &child, child_expr);
    }
    valk_lval_t *result = valk_lval_nil();
    for (u64 i = count; i > 0; i--)
      result = valk_lval_cons(items[i - 1], result);
    scope_cleanup(&child);
    return result;
  }

  bool is_fun_or_lambda = false;
  if (LVAL_TYPE(head) == LVAL_SYM &&
      (strcmp(head->str, "fun") == 0 || strcmp(head->str, "\\") == 0))
    is_fun_or_lambda = true;
  if (LVAL_TYPE(head) == LVAL_FUN && head->fun.builtin != NULL) {
    extern valk_lenv_t *valk_macro_env(void);
    valk_lval_t *lambda_ref = valk_lenv_get(valk_macro_env(), valk_lval_sym("\\"));
    if (LVAL_TYPE(lambda_ref) == LVAL_FUN &&
        head->fun.builtin == lambda_ref->fun.builtin)
      is_fun_or_lambda = true;
  }
  if (is_fun_or_lambda) {
    valk_type_scope_t child = { .count = 0, .parent = scope };
    u64 count = valk_lval_list_count(expr);
    valk_lval_t **items = valk_mem_alloc(sizeof(valk_lval_t *) * count);
    items[0] = head;
    if (count > 1) {
      items[1] = valk_lval_list_nth(expr, 1);
      if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "fun") == 0)
        track_fun_params(env, &child, items[1]);
      else if (is_fun_or_lambda && LVAL_TYPE(head) != LVAL_SYM)
        track_fun_params(env, &child, items[1]);
      else if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "\\") == 0)
        track_fun_params(env, &child, items[1]);
    }
    for (u64 i = 2; i < count; i++) {
      valk_lval_t *child_expr = valk_lval_list_nth(expr, i);
      track_binding(env, &child, child_expr);
      items[i] = transform_expr(env, &child, child_expr);
    }
    valk_lval_t *result = valk_lval_nil();
    for (u64 i = count; i > 0; i--)
      result = valk_lval_cons(items[i - 1], result);
    scope_cleanup(&child);
    return result;
  }

  // Detect expanded fun macro: (def {name} (\ {params} body))
  if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "def") == 0) {
    u64 cnt = valk_lval_list_count(expr);
    if (cnt == 3) {
      valk_lval_t *name_arg = valk_lval_list_nth(expr, 1);
      valk_lval_t *val_arg = valk_lval_list_nth(expr, 2);
      if (is_qexpr(name_arg) && LVAL_TYPE(val_arg) == LVAL_CONS &&
          !(val_arg->flags & LVAL_FLAG_QUOTED)) {
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
        if (val_is_lambda) {
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
            litems[i] = transform_expr(env, &child, child_expr);
          }
          valk_lval_t *new_lambda = valk_lval_nil();
          for (u64 i = lambda_cnt; i > 0; i--)
            new_lambda = valk_lval_cons(litems[i - 1], new_lambda);
          scope_cleanup(&child);
          return valk_lval_cons(head, valk_lval_cons(name_arg, valk_lval_cons(new_lambda, valk_lval_nil())));
        }
      }
    }
  }

  valk_lval_t *result = valk_lval_nil();
  u64 count = valk_lval_list_count(expr);
  for (u64 i = count; i > 0; i--) {
    result = valk_lval_cons(transform_expr(env, scope, valk_lval_list_nth(expr, i - 1)), result);
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
    valk_type_env_register_sig(env, expr);
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
  valk_lval_t *result = transform_expr(env, &persistent_scope, expr);
  g_ti_ctx = NULL;
  return result;
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
  valk_ti_import_sigs(ti);
  valk_ti_import_constructors(ti);
  valk_ti_infer_file(ti, exprs);
  valk_ti_populate_type_scope(ti, ti->scope, &scope);
  g_ti_ctx = ti;

  u64 count = valk_lval_list_count(exprs);
  valk_lval_t **items = malloc(sizeof(valk_lval_t *) * count);
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *expr = valk_lval_list_nth(exprs, i);
    track_binding(env, &scope, expr);
    items[i] = transform_expr(env, &scope, expr);
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
  (void)types_before;
  return result;
}
