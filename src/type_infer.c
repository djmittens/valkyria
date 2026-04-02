#include "type_infer.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"

static void *ti_alloc(valk_ti_ctx_t *ctx, sz bytes) {
  bytes = (bytes + 7) & ~(sz)7;
  if (ctx->temp_off + bytes > ctx->temp_cap) return nullptr;
  void *p = ctx->temp + ctx->temp_off;
  ctx->temp_off += bytes;
  return p;
}

static const char *ti_strdup(valk_ti_ctx_t *ctx, const char *s) {
  sz len = strlen(s) + 1;
  char *p = ti_alloc(ctx, len);
  if (!p) return s;
  memcpy(p, s, len);
  return p;
}

static void ti_error(valk_ti_ctx_t *ctx, int line, int col,
                     const char *fmt, ...) {
  if (ctx->error_count >= VALK_TI_MAX_ERRORS) return;
  char buf[512];
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(buf, sizeof(buf), fmt, ap);
  va_end(ap);
  ctx->errors[ctx->error_count++] = (valk_ti_error_t){
    .line = line, .col = col, .message = ti_strdup(ctx, buf),
  };
}

valk_ti_ctx_t *valk_ti_create(valk_type_env_t *type_env) {
  valk_ti_ctx_t *ctx = calloc(1, sizeof(valk_ti_ctx_t));
  VALK_OOM_ASSERT(ctx);
  ctx->perm_cap = VALK_TI_PERM_SIZE;
  ctx->perm = calloc(1, ctx->perm_cap);
  VALK_OOM_ASSERT(ctx->perm);
  ctx->temp_cap = VALK_TI_TEMP_SIZE;
  ctx->temp = calloc(1, ctx->temp_cap);
  VALK_OOM_ASSERT(ctx->temp);
  ctx->type_env = type_env;

  u8 *st = ctx->temp; sz so = ctx->temp_off; sz sc = ctx->temp_cap;
  ctx->temp = ctx->perm; ctx->temp_off = ctx->perm_off; ctx->temp_cap = ctx->perm_cap;

  ctx->scope = valk_ti_scope_new(ctx, nullptr);
  ctx->perm_scope = ctx->scope;
  ctx->t_num = valk_ti_con(ctx, "Num", nullptr, 0);
  ctx->t_str = valk_ti_con(ctx, "Str", nullptr, 0);
  ctx->t_nil = valk_ti_con(ctx, "Nil", nullptr, 0);
  ctx->t_bool = valk_ti_con(ctx, "Num", nullptr, 0);

  ctx->perm_off = ctx->temp_off;
  ctx->temp = st; ctx->temp_off = so; ctx->temp_cap = sc;
  return ctx;
}

void valk_ti_destroy(valk_ti_ctx_t *ctx) {
  if (!ctx) return;
  free(ctx->perm);
  free(ctx->temp);
  free(ctx);
}

void valk_ti_reset(valk_ti_ctx_t *ctx) {
  ctx->temp_off = 0;
  ctx->error_count = 0;
  ctx->all_bindings_count = 0;
  ctx->all_bindings_cap = 0;
  ctx->all_bindings = NULL;
  valk_ti_scope_t *s = valk_ti_scope_new(ctx, ctx->perm_scope);
  ctx->scope = s ? s : ctx->perm_scope;
}

valk_type_t *valk_ti_fresh_var(valk_ti_ctx_t *ctx) {
  valk_type_t *t = ti_alloc(ctx, sizeof(valk_type_t));
  if (!t) return ctx->t_nil;
  *t = (valk_type_t){.kind = VALK_TY_VAR, .var = {.id = ctx->next_var++, .link = nullptr}};
  return t;
}

valk_type_t *valk_ti_con(valk_ti_ctx_t *ctx, const char *name,
                         valk_type_t **args, u32 arity) {
  valk_type_t *t = ti_alloc(ctx, sizeof(valk_type_t));
  if (!t) return ctx->t_nil;
  valk_type_t **stored_args = nullptr;
  if (arity > 0 && args) {
    stored_args = ti_alloc(ctx, sizeof(valk_type_t *) * arity);
    if (!stored_args) return nullptr;
    memcpy(stored_args, args, sizeof(valk_type_t *) * arity);
  }
  *t = (valk_type_t){.kind = VALK_TY_CON, .con = {.name = name, .args = stored_args, .arity = arity}};
  return t;
}

valk_type_t *valk_ti_fun(valk_ti_ctx_t *ctx, valk_type_t **params,
                         u32 param_count, valk_type_t *ret) {
  valk_type_t *t = ti_alloc(ctx, sizeof(valk_type_t));
  if (!t) return ctx->t_nil;
  valk_type_t **stored = nullptr;
  if (param_count > 0 && params) {
    stored = ti_alloc(ctx, sizeof(valk_type_t *) * param_count);
    if (!stored) return nullptr;
    memcpy(stored, params, sizeof(valk_type_t *) * param_count);
  }
  *t = (valk_type_t){.kind = VALK_TY_FUN, .fun = {.params = stored, .param_count = param_count, .ret = ret}};
  return t;
}

valk_type_t *valk_type_find(valk_type_t *t) {
  if (!t) return nullptr;
  if (t->kind != VALK_TY_VAR) return t;
  if (!t->var.link) return t;
  valk_type_t *root = t->var.link;
  while (root->kind == VALK_TY_VAR && root->var.link)
    root = root->var.link;
  valk_type_t *cur = t;
  while (cur != root && cur->kind == VALK_TY_VAR && cur->var.link) {
    valk_type_t *next = cur->var.link;
    cur->var.link = root;
    cur = next;
  }
  return root;
}

bool valk_type_occurs(valk_type_t *var, valk_type_t *type) {
  type = valk_type_find(type);
  if (!type) return false;
  if (type->kind == VALK_TY_VAR) return type->var.id == var->var.id;
  if (type->kind == VALK_TY_CON) {
    for (u32 i = 0; i < type->con.arity; i++)
      if (valk_type_occurs(var, type->con.args[i])) return true;
    return false;
  }
  if (type->kind == VALK_TY_FUN) {
    for (u32 i = 0; i < type->fun.param_count; i++)
      if (valk_type_occurs(var, type->fun.params[i])) return true;
    return valk_type_occurs(var, type->fun.ret);
  }
  return false;
}

static bool is_nil_type(valk_type_t *t) {
  return t->kind == VALK_TY_CON && t->con.arity == 0 && strcmp(t->con.name, "Nil") == 0;
}

valk_type_t *valk_type_unify(valk_ti_ctx_t *ctx, valk_type_t *a,
                             valk_type_t *b, int line, int col) {
  a = valk_type_find(a);
  b = valk_type_find(b);
  if (!a || !b) return nullptr;
  if (a == b) return a;
  if (is_nil_type(a)) return b;
  if (is_nil_type(b)) return a;

  if (a->kind == VALK_TY_VAR) {
    if (valk_type_occurs(a, b)) {
      ti_error(ctx, line, col, "Infinite type: ?%u occurs in its own definition", a->var.id);
      return nullptr;
    }
    a->var.link = b;
    return b;
  }
  if (b->kind == VALK_TY_VAR) {
    if (valk_type_occurs(b, a)) {
      ti_error(ctx, line, col, "Infinite type: ?%u occurs in its own definition", b->var.id);
      return nullptr;
    }
    b->var.link = a;
    return a;
  }

  if (a->kind == VALK_TY_CON && b->kind == VALK_TY_CON) {
    if (strcmp(a->con.name, b->con.name) != 0 || a->con.arity != b->con.arity) {
      char abuf[128], bbuf[128];
      valk_type_to_str(a, abuf, sizeof(abuf));
      valk_type_to_str(b, bbuf, sizeof(bbuf));
      ti_error(ctx, line, col, "Type mismatch: %s vs %s", abuf, bbuf);
      return nullptr;
    }
    for (u32 i = 0; i < a->con.arity; i++) {
      if (!valk_type_unify(ctx, a->con.args[i], b->con.args[i], line, col))
        return nullptr;
    }
    return a;
  }

  if (a->kind == VALK_TY_FUN && b->kind == VALK_TY_FUN) {
    if (a->fun.param_count != b->fun.param_count) {
      ti_error(ctx, line, col,
               "Function arity mismatch: %u params vs %u params",
               a->fun.param_count, b->fun.param_count);
      return nullptr;
    }
    for (u32 i = 0; i < a->fun.param_count; i++) {
      if (!valk_type_unify(ctx, a->fun.params[i], b->fun.params[i], line, col))
        return nullptr;
    }
    if (!valk_type_unify(ctx, a->fun.ret, b->fun.ret, line, col))
      return nullptr;
    return a;
  }

  if ((a->kind == VALK_TY_FUN && b->kind == VALK_TY_CON) ||
      (a->kind == VALK_TY_CON && b->kind == VALK_TY_FUN)) {
    valk_type_t *fn = (a->kind == VALK_TY_FUN) ? a : b;
    valk_type_t *co = (a->kind == VALK_TY_FUN) ? b : a;
    if (strcmp(co->con.name, "->") == 0 && co->con.arity == fn->fun.param_count + 1) {
      for (u32 i = 0; i < fn->fun.param_count; i++) {
        if (!valk_type_unify(ctx, fn->fun.params[i], co->con.args[i], line, col))
          return nullptr;
      }
      if (!valk_type_unify(ctx, fn->fun.ret, co->con.args[fn->fun.param_count], line, col))
        return nullptr;
      return fn;
    }
  }

  char abuf[128], bbuf[128];
  valk_type_to_str(a, abuf, sizeof(abuf));
  valk_type_to_str(b, bbuf, sizeof(bbuf));
  ti_error(ctx, line, col, "Type mismatch: %s vs %s", abuf, bbuf);
  return nullptr;
}

static void collect_free_vars(valk_type_t *t, u32 *vars, u32 *count,
                              u32 cap) {
  t = valk_type_find(t);
  if (!t) return;
  if (t->kind == VALK_TY_VAR) {
    for (u32 i = 0; i < *count; i++)
      if (vars[i] == t->var.id) return;
    if (*count < cap) vars[(*count)++] = t->var.id;
    return;
  }
  if (t->kind == VALK_TY_CON) {
    for (u32 i = 0; i < t->con.arity; i++)
      collect_free_vars(t->con.args[i], vars, count, cap);
    return;
  }
  if (t->kind == VALK_TY_FUN) {
    for (u32 i = 0; i < t->fun.param_count; i++)
      collect_free_vars(t->fun.params[i], vars, count, cap);
    collect_free_vars(t->fun.ret, vars, count, cap);
  }
}

static bool var_in_scope(valk_ti_scope_t *scope, u32 var_id) {
  for (valk_ti_scope_t *s = scope; s; s = s->parent) {
    for (u32 i = 0; i < s->count; i++) {
      u32 svars[64];
      u32 scount = 0;
      collect_free_vars(s->entries[i].scheme.type, svars, &scount, 64);
      for (u32 j = 0; j < scount; j++)
        if (svars[j] == var_id) return true;
    }
  }
  return false;
}

valk_type_scheme_t valk_type_generalize(valk_ti_ctx_t *ctx,
                                        valk_ti_scope_t *scope,
                                        valk_type_t *type) {
  u32 all_vars[128];
  u32 all_count = 0;
  collect_free_vars(type, all_vars, &all_count, 128);

  u32 bound[128];
  u32 bound_count = 0;
  for (u32 i = 0; i < all_count; i++) {
    if (!var_in_scope(scope, all_vars[i])) {
      if (bound_count < 128) bound[bound_count++] = all_vars[i];
    }
  }

  u32 *stored = nullptr;
  if (bound_count > 0) {
    stored = ti_alloc(ctx, sizeof(u32) * bound_count);
    if (stored) memcpy(stored, bound, sizeof(u32) * bound_count);
  }
  return (valk_type_scheme_t){.type = type, .bound_vars = stored, .bound_count = bound_count};
}

static valk_type_t *instantiate_rec(valk_ti_ctx_t *ctx, valk_type_t *t,
                                    u32 *old_ids, valk_type_t **new_vars,
                                    u32 n) {
  t = valk_type_find(t);
  if (!t) return nullptr;
  if (t->kind == VALK_TY_VAR) {
    for (u32 i = 0; i < n; i++)
      if (old_ids[i] == t->var.id) return new_vars[i];
    return t;
  }
  if (t->kind == VALK_TY_CON) {
    if (t->con.arity == 0) return t;
    valk_type_t *args[16];
    u32 arity = t->con.arity < 16 ? t->con.arity : 16;
    bool changed = false;
    for (u32 i = 0; i < arity; i++) {
      args[i] = instantiate_rec(ctx, t->con.args[i], old_ids, new_vars, n);
      if (args[i] != valk_type_find(t->con.args[i])) changed = true;
    }
    if (!changed) return t;
    return valk_ti_con(ctx, t->con.name, args, arity);
  }
  if (t->kind == VALK_TY_FUN) {
    valk_type_t *params[16];
    u32 pc = t->fun.param_count < 16 ? t->fun.param_count : 16;
    bool changed = false;
    for (u32 i = 0; i < pc; i++) {
      params[i] = instantiate_rec(ctx, t->fun.params[i], old_ids, new_vars, n);
      if (params[i] != valk_type_find(t->fun.params[i])) changed = true;
    }
    valk_type_t *ret = instantiate_rec(ctx, t->fun.ret, old_ids, new_vars, n);
    if (ret != valk_type_find(t->fun.ret)) changed = true;
    if (!changed) return t;
    return valk_ti_fun(ctx, params, pc, ret);
  }
  return t;
}

valk_type_t *valk_type_instantiate(valk_ti_ctx_t *ctx,
                                   valk_type_scheme_t *scheme) {
  if (!scheme || scheme->bound_count == 0) return scheme ? scheme->type : nullptr;
  valk_type_t *new_vars[128];
  u32 n = scheme->bound_count < 128 ? scheme->bound_count : 128;
  for (u32 i = 0; i < n; i++)
    new_vars[i] = valk_ti_fresh_var(ctx);
  return instantiate_rec(ctx, scheme->type, scheme->bound_vars, new_vars, n);
}

valk_ti_scope_t *valk_ti_scope_new(valk_ti_ctx_t *ctx,
                                   valk_ti_scope_t *parent) {
  valk_ti_scope_t *s = ti_alloc(ctx, sizeof(valk_ti_scope_t));
  if (!s) return nullptr;
  *s = (valk_ti_scope_t){.parent = parent};
  return s;
}

static void ti_register_binding(valk_ti_ctx_t *ctx, const char *name,
                                valk_type_t *type) {
  if (ctx->all_bindings_count >= ctx->all_bindings_cap) {
    u32 new_cap = ctx->all_bindings_cap ? ctx->all_bindings_cap * 2 : 64;
    typeof(ctx->all_bindings) nb = ti_alloc(ctx, sizeof(ctx->all_bindings[0]) * new_cap);
    if (!nb) return;
    if (ctx->all_bindings_count > 0)
      memcpy(nb, ctx->all_bindings, sizeof(ctx->all_bindings[0]) * ctx->all_bindings_count);
    ctx->all_bindings = nb;
    ctx->all_bindings_cap = new_cap;
  }
  ctx->all_bindings[ctx->all_bindings_count++] = (typeof(ctx->all_bindings[0])){
    .name = name, .type = type,
  };
}

void valk_ti_scope_bind(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                        const char *name, valk_type_scheme_t scheme) {
  if (!scope || !name) return;
  for (u32 i = 0; i < scope->count; i++) {
    if (strcmp(scope->entries[i].name, name) == 0) {
      scope->entries[i].scheme = scheme;
      ti_register_binding(ctx, name, scheme.type);
      return;
    }
  }
  if (scope->count >= scope->capacity) {
    u32 new_cap = scope->capacity ? scope->capacity * 2 : 8;
    typeof(scope->entries) new_ents = ti_alloc(ctx, sizeof(scope->entries[0]) * new_cap);
    if (!new_ents) return;
    if (scope->count > 0)
      memcpy(new_ents, scope->entries, sizeof(scope->entries[0]) * scope->count);
    scope->entries = new_ents;
    scope->capacity = new_cap;
  }
  scope->entries[scope->count++] = (typeof(scope->entries[0])){
    .name = name, .scheme = scheme,
  };
  ti_register_binding(ctx, name, scheme.type);
}

valk_type_scheme_t *valk_ti_scope_lookup(valk_ti_scope_t *scope,
                                         const char *name) {
  int limit = 100;
  for (valk_ti_scope_t *s = scope; s && --limit > 0; s = s->parent) {
    for (u32 i = 0; i < s->count; i++) {
      if (strcmp(s->entries[i].name, name) == 0)
        return &s->entries[i].scheme;
    }
  }
  return nullptr;
}

static void skip_ws(const char *s, int *pos) {
  while (s[*pos] == ' ' || s[*pos] == '\t') (*pos)++;
}

typedef struct {
  char names[16];
  valk_type_t *vars[16];
  u32 count;
} ti_var_map_t;

static valk_type_t *get_or_create_var(valk_ti_ctx_t *ctx, ti_var_map_t *vm, char name) {
  for (u32 i = 0; i < vm->count; i++)
    if (vm->names[i] == name) return vm->vars[i];
  if (vm->count < 16) {
    valk_type_t *v = valk_ti_fresh_var(ctx);
    vm->names[vm->count] = name;
    vm->vars[vm->count] = v;
    vm->count++;
    return v;
  }
  return valk_ti_fresh_var(ctx);
}

static valk_type_t *parse_type_str_vm(valk_ti_ctx_t *ctx, const char *s,
                                      int *pos, ti_var_map_t *vm);

static valk_type_t *parse_type_atom_vm(valk_ti_ctx_t *ctx, const char *s,
                                       int *pos, ti_var_map_t *vm) {
  skip_ws(s, pos);
  if (s[*pos] == '(') {
    (*pos)++;
    skip_ws(s, pos);
    char name[128];
    int ni = 0;
    while (s[*pos] && s[*pos] != ' ' && s[*pos] != ')' && ni < 126)
      name[ni++] = s[(*pos)++];
    name[ni] = 0;
    bool is_arrow = (strcmp(name, "->") == 0);
    valk_type_t *parts[16];
    u32 count = 0;
    while (count < 16) {
      skip_ws(s, pos);
      if (!s[*pos] || s[*pos] == ')') break;
      parts[count] = parse_type_str_vm(ctx, s, pos, vm);
      if (parts[count]) count++;
    }
    if (s[*pos] == ')') (*pos)++;
    if (is_arrow && count >= 1) {
      valk_type_t *ret = parts[count - 1];
      return valk_ti_fun(ctx, parts, count - 1, ret);
    }
    return valk_ti_con(ctx, ti_strdup(ctx, name), parts, count);
  }
  char name[128];
  int ni = 0;
  while (s[*pos] && s[*pos] != ' ' && s[*pos] != ')' && ni < 126)
    name[ni++] = s[(*pos)++];
  name[ni] = 0;
  if (!ni) return valk_ti_fresh_var(ctx);
  if (name[1] == 0 && ((name[0] >= 'a' && name[0] <= 'z') ||
                        (name[0] >= 'A' && name[0] <= 'Z')))
    return get_or_create_var(ctx, vm, name[0]);
  if (strcmp(name, "Num") == 0) return ctx->t_num;
  if (strcmp(name, "Str") == 0) return ctx->t_str;
  if (strcmp(name, "Any") == 0) return valk_ti_fresh_var(ctx);
  return valk_ti_con(ctx, ti_strdup(ctx, name), nullptr, 0);
}

static valk_type_t *parse_type_str_vm(valk_ti_ctx_t *ctx, const char *s,
                                      int *pos, ti_var_map_t *vm) {
  return parse_type_atom_vm(ctx, s, pos, vm);
}

valk_type_t *valk_ti_parse_sig_str(valk_ti_ctx_t *ctx, const char *s) {
  if (!s || !*s) return valk_ti_fresh_var(ctx);
  int pos = 0;
  ti_var_map_t vm = {0};
  return parse_type_str_vm(ctx, s, &pos, &vm);
}

void valk_ti_import_sigs(valk_ti_ctx_t *ctx) {
  valk_ti_import_new(ctx);
}

void valk_ti_import_constructors(valk_ti_ctx_t *ctx) {
  valk_ti_import_new(ctx);
}

static const char *sym_name(valk_lval_t *v);

static valk_type_t *infer_type_qexpr_node(valk_ti_ctx_t *ctx, valk_lval_t *node,
                                          ti_var_map_t *vm) {
  if (!node) return valk_ti_fresh_var(ctx);
  if (LVAL_TYPE(node) == LVAL_SYM) {
    const char *n = node->str;
    if (strlen(n) == 1) return get_or_create_var(ctx, vm, n[0]);
    if (strcmp(n, "Num") == 0) return ctx->t_num;
    if (strcmp(n, "Str") == 0) return ctx->t_str;
    if (strcmp(n, "Any") == 0) return valk_ti_fresh_var(ctx);
    return valk_ti_con(ctx, ti_strdup(ctx, n), nullptr, 0);
  }
  if (LVAL_TYPE(node) == LVAL_CONS) {
    const char *hname = sym_name(node->cons.head);
    if (!hname) return valk_ti_fresh_var(ctx);
    if (strcmp(hname, "->") == 0) {
      valk_type_t *parts[16];
      u32 count = 0;
      valk_lval_t *c = node->cons.tail;
      while (c && LVAL_TYPE(c) == LVAL_CONS && count < 16) {
        parts[count++] = infer_type_qexpr_node(ctx, c->cons.head, vm);
        c = c->cons.tail;
      }
      if (count >= 1) return valk_ti_fun(ctx, parts, count - 1, parts[count - 1]);
      return valk_ti_fresh_var(ctx);
    }
    valk_type_t *args[16];
    u32 ac = 0;
    valk_lval_t *c = node->cons.tail;
    while (c && LVAL_TYPE(c) == LVAL_CONS && ac < 16) {
      args[ac++] = infer_type_qexpr_node(ctx, c->cons.head, vm);
      c = c->cons.tail;
    }
    return valk_ti_con(ctx, ti_strdup(ctx, hname), ac > 0 ? args : nullptr, ac);
  }
  return valk_ti_fresh_var(ctx);
}

static valk_type_t *valk_ti_infer_type_qexpr(valk_ti_ctx_t *ctx, valk_lval_t *qexpr) {
  ti_var_map_t vm = {0};
  const char *hname = sym_name(qexpr->cons.head);
  if (hname && strcmp(hname, "->") == 0) {
    valk_type_t *parts[16];
    u32 count = 0;
    valk_lval_t *c = qexpr->cons.tail;
    while (c && LVAL_TYPE(c) == LVAL_CONS && count < 16) {
      parts[count++] = infer_type_qexpr_node(ctx, c->cons.head, &vm);
      c = c->cons.tail;
    }
    if (count >= 1) return valk_ti_fun(ctx, parts, count - 1, parts[count - 1]);
    return valk_ti_fresh_var(ctx);
  }
  return infer_type_qexpr_node(ctx, qexpr, &vm);
}

static bool is_upper(char c) { return c >= 'A' && c <= 'Z'; }

static const char *sym_name(valk_lval_t *v) {
  if (!v || LVAL_TYPE(v) != LVAL_SYM) return nullptr;
  return v->str;
}

static bool is_sym(valk_lval_t *v, const char *name) {
  const char *s = sym_name(v);
  return s && strcmp(s, name) == 0;
}

static bool is_qexpr_node(valk_lval_t *v) {
  return v && LVAL_TYPE(v) == LVAL_CONS && (v->flags & LVAL_FLAG_QUOTED);
}

static int lval_line(valk_lval_t *v) {
  if (!v) return 0;
  return LVAL_SRC_POS(v) >= 0 ? LVAL_SRC_POS(v) : 0;
}

static valk_type_t *infer_expr(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                               valk_lval_t *expr);

static valk_type_t *infer_do(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                             valk_lval_t *body) {
  valk_ti_scope_t *child = valk_ti_scope_new(ctx, scope);
  if (!child) child = scope;
  valk_type_t *result = ctx->t_nil;
  valk_lval_t *cur = body;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    result = infer_expr(ctx, child, cur->cons.head);
    cur = cur->cons.tail;
  }
  return result;
}

static valk_type_t *infer_lambda(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                                 valk_lval_t *formals, valk_lval_t *body_list,
                                 const char *fname) {
  if (ctx->temp_off > ctx->temp_cap - 256) return ctx->t_nil;
  valk_ti_scope_t *child = valk_ti_scope_new(ctx, scope);
  if (!child) return ctx->t_nil;
  valk_type_t *param_types[32];
  u32 param_count = 0;

  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS && param_count < 32) {
    const char *pname = sym_name(cur->cons.head);
    if (pname && strcmp(pname, "&") == 0) {
      cur = cur->cons.tail;
      if (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        const char *rest_name = sym_name(cur->cons.head);
        if (rest_name) {
          valk_type_t *rest_t = valk_ti_fresh_var(ctx);
          valk_type_t *args[] = {rest_t};
          valk_type_t *list_t = valk_ti_con(ctx, "List", args, 1);
          valk_type_scheme_t s = {.type = list_t};
          valk_ti_scope_bind(ctx, child, rest_name, s);
        }
      }
      break;
    }
    if (pname) {
      param_types[param_count] = valk_ti_fresh_var(ctx);
      valk_type_scheme_t s = {.type = param_types[param_count]};
      valk_ti_scope_bind(ctx, child, pname, s);
      param_count++;
    }
    cur = cur->cons.tail;
  }

  if (fname) {
    valk_type_t *self_ret = valk_ti_fresh_var(ctx);
    valk_type_t *self_t = valk_ti_fun(ctx, param_types, param_count, self_ret);
    valk_type_scheme_t ss = {.type = self_t};
    valk_ti_scope_bind(ctx, child, fname, ss);
  }

  valk_type_t *body_type = ctx->t_nil;
  cur = body_list;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    body_type = infer_expr(ctx, child, cur->cons.head);
    cur = cur->cons.tail;
  }

  if (fname) {
    valk_type_scheme_t *self_s = valk_ti_scope_lookup(child, fname);
    if (self_s) valk_type_unify(ctx, self_s->type->fun.ret, body_type, 0, 0);
  }

  return valk_ti_fun(ctx, param_types, param_count, body_type);
}

static valk_type_t *infer_binding(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                                  valk_lval_t *binding_q, valk_lval_t *rhs) {
  if (!is_qexpr_node(binding_q)) return ctx->t_nil;
  const char *name = sym_name(binding_q->cons.head);
  if (!name) return ctx->t_nil;
  valk_type_t *rhs_t = infer_expr(ctx, scope, rhs);
  valk_type_scheme_t scheme = valk_type_generalize(ctx, scope, rhs_t);
  valk_ti_scope_bind(ctx, scope, name, scheme);
  return rhs_t;
}

static valk_type_t *infer_if(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                             valk_lval_t *args) {
  u64 argc = valk_lval_list_count(args);
  if (argc < 2) return ctx->t_nil;
  infer_expr(ctx, scope, valk_lval_list_nth(args, 0));
  valk_type_t *then_t = infer_expr(ctx, scope, valk_lval_list_nth(args, 1));
  if (argc >= 3) {
    valk_type_t *else_t = infer_expr(ctx, scope, valk_lval_list_nth(args, 2));
    valk_type_unify(ctx, then_t, else_t,
                    lval_line(valk_lval_list_nth(args, 2)), 0);
  }
  return then_t;
}

static valk_type_t *infer_application(valk_ti_ctx_t *ctx,
                                      valk_ti_scope_t *scope,
                                      valk_type_t *fn_type,
                                      valk_lval_t *args, int line) {
  valk_type_t *arg_types[32];
  u32 argc = 0;
  valk_lval_t *cur = args;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS && argc < 32) {
    arg_types[argc++] = infer_expr(ctx, scope, cur->cons.head);
    cur = cur->cons.tail;
  }
  valk_type_t *ret = valk_ti_fresh_var(ctx);
  valk_type_t *expected = valk_ti_fun(ctx, arg_types, argc, ret);
  valk_type_unify(ctx, fn_type, expected, line, 0);
  return ret;
}

static valk_type_t *infer_field_access(valk_ti_ctx_t *ctx,
                                       valk_ti_scope_t *scope,
                                       const char *var_name,
                                       const char *field_name) {
  valk_type_scheme_t *vs = valk_ti_scope_lookup(scope, var_name);
  if (!vs) return valk_ti_fresh_var(ctx);
  valk_type_t *vt = valk_type_find(vs->type);
  if (vt->kind != VALK_TY_CON || !ctx->type_env) return valk_ti_fresh_var(ctx);

  const char *type_name = vt->con.name;
  valk_type_decl_t *decl = valk_type_env_find_type(ctx->type_env, type_name);
  if (!decl) return valk_ti_fresh_var(ctx);

  char kw[128];
  snprintf(kw, sizeof(kw), ":%s", field_name);
  for (u64 c = 0; c < decl->constructor_count; c++) {
    valk_constructor_t *ctor = decl->constructors[c];
    for (u64 f = 0; f < ctor->field_count; f++) {
      if (strcmp(ctor->fields[f].name, kw) == 0)
        return valk_ti_parse_sig_str(ctx, ctor->fields[f].type_name);
    }
  }
  return valk_ti_fresh_var(ctx);
}

static valk_type_t *infer_match(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                                valk_lval_t *args) {
  if (!args || LVAL_TYPE(args) == LVAL_NIL) return ctx->t_nil;
  valk_type_t *val_type = infer_expr(ctx, scope, args->cons.head);
  valk_type_t *result = valk_ti_fresh_var(ctx);
  valk_lval_t *cur = args->cons.tail;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *clause = cur->cons.head;
    if (is_qexpr_node(clause)) {
      valk_ti_scope_t *clause_scope = valk_ti_scope_new(ctx, scope);
      if (!clause_scope) { cur = cur->cons.tail; continue; }
      valk_lval_t *pattern = clause->cons.head;
      valk_lval_t *body = clause->cons.tail;

      if (is_qexpr_node(pattern)) {
        const char *ctor_name = sym_name(pattern->cons.head);
        if (ctor_name && ctx->type_env) {
          valk_type_decl_t *decl = valk_type_env_type_for_constructor(ctx->type_env, ctor_name);
          if (decl) {
            valk_type_t *ctor_parent = valk_ti_con(ctx, ti_strdup(ctx, decl->name), nullptr, 0);
            valk_type_unify(ctx, val_type, ctor_parent, lval_line(pattern), 0);
            valk_constructor_t *ctor = valk_type_env_find_constructor(ctx->type_env, ctor_name);
            if (ctor) {
              valk_lval_t *p = pattern->cons.tail;
              u64 fi = 0;
              while (p && LVAL_TYPE(p) == LVAL_CONS && fi < ctor->field_count) {
                const char *pn = sym_name(p->cons.head);
                if (pn && strcmp(pn, "_") != 0) {
                  valk_type_t *ft = valk_ti_parse_sig_str(ctx, ctor->fields[fi].type_name);
                  valk_type_scheme_t s = {.type = ft};
                  valk_ti_scope_bind(ctx, clause_scope, pn, s);
                }
                fi++;
                p = p->cons.tail;
              }
            }
          }
        }
      } else {
        const char *pname = sym_name(pattern);
        if (pname && strcmp(pname, "_") != 0) {
          valk_type_scheme_t s = {.type = val_type};
          valk_ti_scope_bind(ctx, clause_scope, pname, s);
        }
      }

      valk_type_t *body_type = infer_do(ctx, clause_scope, body);
      valk_type_unify(ctx, result, body_type, lval_line(clause), 0);
    }
    cur = cur->cons.tail;
  }
  return result;
}

static valk_type_t *infer_expr(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                               valk_lval_t *expr) {
  if (!expr || ctx->temp_off > ctx->temp_cap - 256) return ctx->t_nil;
  valk_ltype_e t = LVAL_TYPE(expr);

  if (t == LVAL_NUM) return ctx->t_num;
  if (t == LVAL_STR) return ctx->t_str;
  if (t == LVAL_NIL) return ctx->t_nil;

  if (t == LVAL_SYM) {
    const char *name = expr->str;
    const char *colon = strchr(name, ':');
    if (colon && colon != name && (colon[1] >= 'a' && colon[1] <= 'z')) {
      char var_buf[128];
      sz var_len = colon - name;
      if (var_len < sizeof(var_buf)) {
        memcpy(var_buf, name, var_len);
        var_buf[var_len] = 0;
        return infer_field_access(ctx, scope, var_buf, colon + 1);
      }
    }
    valk_type_scheme_t *s = valk_ti_scope_lookup(scope, name);
    if (s) return valk_type_instantiate(ctx, s);
    return valk_ti_fresh_var(ctx);
  }

  if (t == LVAL_CONS && (expr->flags & LVAL_FLAG_QUOTED)) {
    valk_lval_t *head = expr->cons.head;
    if (!head) return ctx->t_nil;
    if (is_sym(head, "match"))
      return infer_match(ctx, scope, expr->cons.tail);
    if (is_sym(head, "do"))
      return infer_do(ctx, scope, expr->cons.tail);
    bool single = !expr->cons.tail || LVAL_TYPE(expr->cons.tail) == LVAL_NIL;
    if (single)
      return infer_expr(ctx, scope, head);
    const char *hname = sym_name(head);
    if (hname) {
      valk_type_scheme_t *fn_s = valk_ti_scope_lookup(scope, hname);
      if (fn_s) {
        valk_type_t *fn_t = valk_type_instantiate(ctx, fn_s);
        return infer_application(ctx, scope, fn_t, expr->cons.tail, lval_line(expr));
      }
      valk_type_t *fn_t = valk_ti_fresh_var(ctx);
      return infer_application(ctx, scope, fn_t, expr->cons.tail, lval_line(expr));
    }
    return infer_do(ctx, scope, expr);
  }

  if (t != LVAL_CONS) return valk_ti_fresh_var(ctx);

  valk_lval_t *head = expr->cons.head;
  valk_lval_t *rest = expr->cons.tail;
  if (!head) return ctx->t_nil;
  const char *head_name = sym_name(head);

  if (head_name) {
    if (strcmp(head_name, "\\") == 0 || strcmp(head_name, "lambda") == 0) {
      valk_lval_t *formals = rest ? rest->cons.head : nullptr;
      valk_lval_t *body = rest ? rest->cons.tail : nullptr;
      if (!is_qexpr_node(formals)) return ctx->t_nil;
      return infer_lambda(ctx, scope, formals->cons.head ? formals : nullptr,
                          body, nullptr);
    }

    if (strcmp(head_name, "fun") == 0) {
      valk_lval_t *name_q = rest ? rest->cons.head : nullptr;
      valk_lval_t *body = rest ? rest->cons.tail : nullptr;
      if (!is_qexpr_node(name_q)) return ctx->t_nil;
      const char *fname = sym_name(name_q->cons.head);
      valk_lval_t *params = name_q->cons.tail;
      valk_type_scheme_t *existing = fname ? valk_ti_scope_lookup(scope, fname) : nullptr;
      valk_type_t *ft = infer_lambda(ctx, scope, params, body, fname);
      if (existing) {
        valk_type_t *sig_t = valk_type_instantiate(ctx, existing);
        valk_type_unify(ctx, ft, sig_t, lval_line(expr), 0);
      }
      if (fname) {
        valk_type_scheme_t scheme = valk_type_generalize(ctx, scope, ft);
        valk_ti_scope_bind(ctx, scope, fname, scheme);
      }
      return ft;
    }

    if (strcmp(head_name, "=") == 0) {
      valk_lval_t *binding = rest ? rest->cons.head : nullptr;
      valk_lval_t *val = (rest && rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS)
                           ? rest->cons.tail->cons.head : nullptr;
      return infer_binding(ctx, scope, binding, val);
    }

    if (strcmp(head_name, "def") == 0) {
      valk_lval_t *binding = rest ? rest->cons.head : nullptr;
      valk_lval_t *val = (rest && rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS)
                           ? rest->cons.tail->cons.head : nullptr;
      return infer_binding(ctx, scope, binding, val);
    }

    if (strcmp(head_name, "if") == 0)
      return infer_if(ctx, scope, rest);

    if (strcmp(head_name, "do") == 0)
      return infer_do(ctx, scope, rest);

    if (strcmp(head_name, "sig") == 0) {
      if (rest && rest->cons.head) {
        valk_lval_t *name_q = rest->cons.head;
        const char *sname = nullptr;
        if (is_qexpr_node(name_q)) sname = sym_name(name_q->cons.head);
        else if (LVAL_TYPE(name_q) == LVAL_STR) sname = name_q->str;
        if (sname && !valk_ti_scope_lookup(scope, sname) &&
            rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS) {
          valk_lval_t *type_q = rest->cons.tail->cons.head;
          if (is_qexpr_node(type_q)) {
            valk_type_t *sig_type = valk_ti_infer_type_qexpr(ctx, type_q);
            if (sig_type) {
              valk_type_scheme_t scheme = valk_type_generalize(ctx, scope, sig_type);
              valk_ti_scope_bind(ctx, scope, ti_strdup(ctx, sname), scheme);
            }
          }
        }
      }
      return ctx->t_nil;
    }

    if (strcmp(head_name, "type") == 0) return ctx->t_nil;
    if (strcmp(head_name, "load") == 0) return ctx->t_nil;

    if (is_upper(head_name[0]) && ctx->type_env) {
      valk_type_scheme_t *cs = valk_ti_scope_lookup(scope, head_name);
      if (cs) {
        valk_type_t *ct = valk_type_instantiate(ctx, cs);
        return infer_application(ctx, scope, ct, rest, lval_line(expr));
      }
    }

    valk_type_scheme_t *fn_s = valk_ti_scope_lookup(scope, head_name);
    if (fn_s) {
      valk_type_t *fn_t = valk_type_instantiate(ctx, fn_s);
      return infer_application(ctx, scope, fn_t, rest, lval_line(expr));
    }
    valk_type_t *fn_t = valk_ti_fresh_var(ctx);
    return infer_application(ctx, scope, fn_t, rest, lval_line(expr));
  }

  valk_type_t *fn_t = infer_expr(ctx, scope, head);
  return infer_application(ctx, scope, fn_t, rest, lval_line(expr));
}

valk_type_t *valk_ti_infer_expr(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                                valk_lval_t *expr) {
  return infer_expr(ctx, scope, expr);
}

void valk_ti_infer_file(valk_ti_ctx_t *ctx, valk_lval_t *exprs) {
  valk_lval_t *cur = exprs;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    infer_expr(ctx, ctx->scope, cur->cons.head);
    cur = cur->cons.tail;
  }
}

valk_type_t *valk_ti_lookup_binding(valk_ti_ctx_t *ctx, const char *name) {
  if (!ctx || !name) return NULL;
  for (u32 i = ctx->all_bindings_count; i > 0; i--) {
    if (strcmp(ctx->all_bindings[i - 1].name, name) == 0)
      return valk_type_find(ctx->all_bindings[i - 1].type);
  }
  return NULL;
}

void valk_ti_populate_type_scope(valk_ti_ctx_t *ctx, valk_ti_scope_t *ti_scope,
                                valk_type_scope_t *out_scope) {
  UNUSED(ctx);
  for (valk_ti_scope_t *s = ti_scope; s; s = s->parent) {
    for (u32 i = 0; i < s->count; i++) {
      const char *name = s->entries[i].name;
      valk_type_t *t = valk_type_find(s->entries[i].scheme.type);
      if (!t) continue;
      bool found = false;
      for (u64 j = 0; j < out_scope->count; j++) {
        if (strcmp(out_scope->entries[j].var, name) == 0) { found = true; break; }
      }
      if (found) continue;
      if (t->kind == VALK_TY_CON && t->con.arity == 0) {
        if (out_scope->count >= out_scope->capacity) {
          u64 new_cap = out_scope->capacity ? out_scope->capacity * 2 : 16;
          typeof(out_scope->entries) new_e = realloc(out_scope->entries,
            sizeof(out_scope->entries[0]) * new_cap);
          if (!new_e) continue;
          out_scope->entries = new_e;
          out_scope->capacity = new_cap;
        }
        out_scope->entries[out_scope->count].var = name;
        out_scope->entries[out_scope->count].type = t->con.name;
        out_scope->count++;
      }
    }
  }
}

static valk_type_scheme_t ti_scheme_from_type(valk_ti_ctx_t *ctx, valk_type_t *ft) {
  u32 vars[128]; u32 vc = 0;
  collect_free_vars(ft, vars, &vc, 128);
  u32 *bv = NULL;
  if (vc > 0) { bv = ti_alloc(ctx, sizeof(u32) * vc); if (bv) memcpy(bv, vars, sizeof(u32) * vc); }
  return (valk_type_scheme_t){.type = ft, .bound_vars = bv, .bound_count = vc};
}

void valk_ti_import_new(valk_ti_ctx_t *ctx) {
  if (!ctx->type_env) return;
  u8 *st = ctx->temp; sz so = ctx->temp_off; sz sc = ctx->temp_cap;
  ctx->temp = ctx->perm; ctx->temp_off = ctx->perm_off; ctx->temp_cap = ctx->perm_cap;

  for (u64 i = ctx->imported_sig_count; i < ctx->type_env->sig_count; i++) {
    valk_type_sig_t *sig = ctx->type_env->sigs[i];
    if (valk_ti_scope_lookup(ctx->scope, sig->name)) continue;
    valk_type_t *params[32];
    for (u64 p = 0; p < sig->param_count && p < 32; p++)
      params[p] = valk_ti_parse_sig_str(ctx, sig->param_types[p]);
    valk_type_t *ret = valk_ti_parse_sig_str(ctx, sig->return_type);
    valk_type_t *ft = valk_ti_fun(ctx, params, (u32)sig->param_count, ret);
    valk_ti_scope_bind(ctx, ctx->scope, ti_strdup(ctx, sig->name), ti_scheme_from_type(ctx, ft));
  }
  ctx->imported_sig_count = ctx->type_env->sig_count;
  for (u64 i = ctx->imported_type_count; i < ctx->type_env->type_count; i++) {
    valk_type_decl_t *decl = ctx->type_env->types[i];
    valk_type_t *parent_type = valk_ti_con(ctx, ti_strdup(ctx, decl->name), nullptr, 0);
    for (u64 c = 0; c < decl->constructor_count; c++) {
      valk_constructor_t *ctor = decl->constructors[c];
      if (valk_ti_scope_lookup(ctx->scope, ctor->name)) continue;
      if (ctor->field_count == 0) {
        valk_ti_scope_bind(ctx, ctx->scope, ti_strdup(ctx, ctor->name),
                           (valk_type_scheme_t){.type = parent_type});
      } else {
        valk_type_t *field_types[32];
        for (u64 f = 0; f < ctor->field_count && f < 32; f++)
          field_types[f] = valk_ti_parse_sig_str(ctx, ctor->fields[f].type_name);
        valk_type_t *ct = valk_ti_fun(ctx, field_types, (u32)ctor->field_count, parent_type);
        valk_ti_scope_bind(ctx, ctx->scope, ti_strdup(ctx, ctor->name), ti_scheme_from_type(ctx, ct));
      }
    }
  }
  ctx->imported_type_count = ctx->type_env->type_count;

  ctx->perm_off = ctx->temp_off;
  ctx->temp = st; ctx->temp_off = so; ctx->temp_cap = sc;
  ctx->perm_scope = ctx->scope;
}

sz valk_type_to_str(valk_type_t *t, char *buf, sz buf_size) {
  t = valk_type_find(t);
  if (!t) return snprintf(buf, buf_size, "?");
  if (t->kind == VALK_TY_VAR)
    return snprintf(buf, buf_size, "?%u", t->var.id);
  if (t->kind == VALK_TY_CON) {
    if (t->con.arity == 0) return snprintf(buf, buf_size, "%s", t->con.name);
    sz off = snprintf(buf, buf_size, "(%s", t->con.name);
    for (u32 i = 0; i < t->con.arity && off < buf_size; i++) {
      off += snprintf(buf + off, buf_size - off, " ");
      off += valk_type_to_str(t->con.args[i], buf + off, buf_size - off);
    }
    if (off < buf_size) off += snprintf(buf + off, buf_size - off, ")");
    return off;
  }
  if (t->kind == VALK_TY_FUN) {
    sz off = snprintf(buf, buf_size, "(-> ");
    for (u32 i = 0; i < t->fun.param_count && off < buf_size; i++) {
      off += valk_type_to_str(t->fun.params[i], buf + off, buf_size - off);
      if (off < buf_size) off += snprintf(buf + off, buf_size - off, " ");
    }
    off += valk_type_to_str(t->fun.ret, buf + off, buf_size - off);
    if (off < buf_size) off += snprintf(buf + off, buf_size - off, ")");
    return off;
  }
  return snprintf(buf, buf_size, "???");
}
