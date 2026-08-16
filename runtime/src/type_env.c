#include "type_env.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"

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
      free(ctor->type_name);
      for (u64 f = 0; f < ctor->field_count; f++) {
        free(ctor->fields[f].name);
        free(ctor->fields[f].type_name);
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

static const char *strip_module_prefix(const char *name) {
  const char *last = strrchr(name, '/');
  return last ? last + 1 : name;
}

valk_type_decl_t *valk_type_env_find_type(valk_type_env_t *env, const char *name) {
  const char *short_query = strip_module_prefix(name);
  for (u64 i = 0; i < env->type_count; i++) {
    if (strcmp(env->types[i]->name, name) == 0) return env->types[i];
    if (strcmp(strip_module_prefix(env->types[i]->name), short_query) == 0) return env->types[i];
  }
  return NULL;
}

valk_constructor_t *valk_type_env_find_constructor(valk_type_env_t *env, const char *name) {
  const char *short_query = strip_module_prefix(name);
  for (u64 i = 0; i < env->constructor_count; i++) {
    if (strcmp(env->constructors[i]->name, name) == 0) return env->constructors[i];
    if (strcmp(strip_module_prefix(env->constructors[i]->name), short_query) == 0) return env->constructors[i];
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

// ---------------------------------------------------------------------------
// Sig registration
// ---------------------------------------------------------------------------

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
      if (inner) { // LCOV_EXCL_BR_LINE - serialize of a cons never returns NULL
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

valk_type_sig_t *valk_type_env_find_sig(valk_type_env_t *env, const char *name) {
  const char *short_query = strip_module_prefix(name);
  for (u64 i = 0; i < env->sig_count; i++) {
    if (strcmp(env->sigs[i]->name, name) == 0) return env->sigs[i];
    if (strcmp(strip_module_prefix(env->sigs[i]->name), short_query) == 0) return env->sigs[i];
  }
  return NULL;
}

#define VALK_TYPE_SIG_MAX_PARAMS 32

void valk_type_env_register_sig(valk_type_env_t *env, valk_lval_t *sig_form) {
  u64 count = valk_lval_list_count(sig_form);
  if (count < 3) return;

  valk_lval_t *name_q = valk_lval_list_nth(sig_form, 1);
  if (LVAL_TYPE(name_q) != LVAL_CONS || !(name_q->flags & LVAL_FLAG_QUOTED)) return;
  valk_lval_t *name_sym = name_q->cons.head;
  if (LVAL_TYPE(name_sym) != LVAL_SYM) return;

  if (valk_type_env_find_sig(env, name_sym->str)) return;

  valk_lval_t *type_q = valk_lval_list_nth(sig_form, 2);
  if (LVAL_TYPE(type_q) != LVAL_CONS || !(type_q->flags & LVAL_FLAG_QUOTED)) return;

  valk_lval_t *arrow = type_q->cons.head;
  if (LVAL_TYPE(arrow) != LVAL_SYM || strcmp(arrow->str, "->") != 0) return;

  char *types[VALK_TYPE_SIG_MAX_PARAMS];
  u64 type_count = 0;
  valk_lval_t *curr = type_q->cons.tail;
  while (LVAL_TYPE(curr) != LVAL_NIL) {
    if (type_count >= VALK_TYPE_SIG_MAX_PARAMS) {
      fprintf(stderr, "[type-env] warning: sig '%s' has more than %d params, truncating\n",
              name_sym->str, VALK_TYPE_SIG_MAX_PARAMS);
      break;
    }
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
