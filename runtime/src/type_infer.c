#include "type_infer.h"
#include "type_infer_internal.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"

static valk_ti_page_t *ti_page_new(sz cap) {
  valk_ti_page_t *p = calloc(1, sizeof(valk_ti_page_t));
  VALK_OOM_ASSERT(p);
  p->data = calloc(1, cap);
  VALK_OOM_ASSERT(p->data);
  p->cap = cap;
  return p;
}

void *ti_alloc(valk_ti_ctx_t *ctx, sz bytes) {
  bytes = (bytes + 7) & ~(sz)7;
  if (ctx->use_expr) {
    if (ctx->expr_off + bytes <= ctx->expr_cap) {
      void *p = ctx->expr_buf + ctx->expr_off;
      ctx->expr_off += bytes;
      return p;
    }
  }
  valk_ti_page_t *pg = ctx->page;
  if (pg->off + bytes > pg->cap) {
    sz cap = pg->cap;
    while (cap < bytes) cap *= 2;
    valk_ti_page_t *np = ti_page_new(cap);
    np->next = pg;
    ctx->page = np;
    pg = np;
  }
  void *p = pg->data + pg->off;
  pg->off += bytes;
  return p;
}

const char *ti_strdup(valk_ti_ctx_t *ctx, const char *s) {
  sz len = strlen(s) + 1;
  char *p = ti_alloc(ctx, len);
  if (!p) return s;
  memcpy(p, s, len);
  return p;
}

static void ti_error(valk_ti_ctx_t *ctx, int line, int col,
                     const char *fmt, ...) {
  if (ctx->error_count >= VALK_TI_MAX_ERRORS) {
    if (ctx->error_count == VALK_TI_MAX_ERRORS)
      fprintf(stderr, "[type-infer] warning: max errors (%d) reached, further errors suppressed\n", VALK_TI_MAX_ERRORS);
    return;
  }
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
  ctx->page = ti_page_new(VALK_TI_PAGE_SIZE);
  ctx->expr_cap = VALK_TI_EXPR_SIZE;
  ctx->expr_buf = calloc(1, ctx->expr_cap);
  VALK_OOM_ASSERT(ctx->expr_buf);
  ctx->type_env = type_env;

  ctx->scope = valk_ti_scope_new(ctx, nullptr);
  ctx->base_scope = ctx->scope;
  ctx->t_num = valk_ti_con(ctx, "Num", nullptr, 0);
  ctx->t_str = valk_ti_con(ctx, "Str", nullptr, 0);
  ctx->t_nil = valk_ti_con(ctx, "Nil", nullptr, 0);
  ctx->t_bool = valk_ti_con(ctx, "Bool", nullptr, 0);
  return ctx;
}

void valk_ti_destroy(valk_ti_ctx_t *ctx) {
  if (!ctx) return;
  valk_ti_page_t *pg = ctx->page;
  while (pg) {
    valk_ti_page_t *next = pg->next;
    free(pg->data);
    free(pg);
    pg = next;
  }
  free(ctx->expr_buf);
  free(ctx);
}

void valk_ti_reset(valk_ti_ctx_t *ctx) {
  valk_ti_promote_to_base(ctx);
  ctx->expr_off = 0;
  ctx->use_expr = true;
  ctx->error_count = 0;
  ctx->all_bindings_count = 0;
  ctx->all_bindings_cap = 0;
  ctx->all_bindings = NULL;
  ctx->scope = valk_ti_scope_new(ctx, ctx->base_scope);
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

void collect_free_vars(valk_type_t *t, u32 *vars, u32 *count,
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
    if (t->con.arity > VALK_TI_MAX_TYPE_ARITY) {
      fprintf(stderr, "[type-infer] warning: type constructor '%s' has arity %u > max %d, truncating during instantiation\n",
              t->con.name, t->con.arity, VALK_TI_MAX_TYPE_ARITY);
    }
    valk_type_t *args[VALK_TI_MAX_TYPE_ARITY];
    u32 arity = t->con.arity < VALK_TI_MAX_TYPE_ARITY ? t->con.arity : VALK_TI_MAX_TYPE_ARITY;
    bool changed = false;
    for (u32 i = 0; i < arity; i++) {
      args[i] = instantiate_rec(ctx, t->con.args[i], old_ids, new_vars, n);
      if (args[i] != valk_type_find(t->con.args[i])) changed = true;
    }
    if (!changed) return t;
    return valk_ti_con(ctx, t->con.name, args, arity);
  }
  if (t->kind == VALK_TY_FUN) {
    if (t->fun.param_count > VALK_TI_MAX_TYPE_ARITY) {
      fprintf(stderr, "[type-infer] warning: function type has %u params > max %d, truncating during instantiation\n",
              t->fun.param_count, VALK_TI_MAX_TYPE_ARITY);
    }
    valk_type_t *params[VALK_TI_MAX_TYPE_ARITY];
    u32 pc = t->fun.param_count < VALK_TI_MAX_TYPE_ARITY ? t->fun.param_count : VALK_TI_MAX_TYPE_ARITY;
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
  if (scheme->bound_count > VALK_TI_MAX_SCHEME_VARS) {
    fprintf(stderr, "[type-infer] warning: scheme has %u bound vars > max %d, truncating\n",
            scheme->bound_count, VALK_TI_MAX_SCHEME_VARS);
  }
  valk_type_t *new_vars[VALK_TI_MAX_SCHEME_VARS];
  u32 n = scheme->bound_count < VALK_TI_MAX_SCHEME_VARS ? scheme->bound_count : VALK_TI_MAX_SCHEME_VARS;
  for (u32 i = 0; i < n; i++)
    new_vars[i] = valk_ti_fresh_var(ctx);
  return instantiate_rec(ctx, scheme->type, scheme->bound_vars, new_vars, n);
}

valk_ti_scope_t *valk_ti_scope_new(valk_ti_ctx_t *ctx,
                                   valk_ti_scope_t *parent) {
  valk_ti_scope_t *s = ti_alloc(ctx, sizeof(valk_ti_scope_t));
  if (!s) return nullptr;
  *s = (valk_ti_scope_t){.parent = parent, .start_pos = -1, .end_pos = -1};
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
      valk_type_t *parts[VALK_TI_MAX_TYPE_ARITY];
      u32 count = 0;
      valk_lval_t *c = node->cons.tail;
      while (c && LVAL_TYPE(c) == LVAL_CONS) {
        if (count >= VALK_TI_MAX_TYPE_ARITY) {
          fprintf(stderr, "[type-infer] warning: function type annotation has more than %d parts, truncating\n",
                  VALK_TI_MAX_TYPE_ARITY);
          break;
        }
        parts[count++] = infer_type_qexpr_node(ctx, c->cons.head, vm);
        c = c->cons.tail;
      }
      if (count >= 1) return valk_ti_fun(ctx, parts, count - 1, parts[count - 1]);
      return valk_ti_fresh_var(ctx);
    }
    valk_type_t *args[VALK_TI_MAX_TYPE_ARITY];
    u32 ac = 0;
    valk_lval_t *c = node->cons.tail;
    while (c && LVAL_TYPE(c) == LVAL_CONS) {
      if (ac >= VALK_TI_MAX_TYPE_ARITY) {
        fprintf(stderr, "[type-infer] warning: type constructor '%s' has more than %d args, truncating\n",
                hname, VALK_TI_MAX_TYPE_ARITY);
        break;
      }
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
    valk_type_t *parts[VALK_TI_MAX_TYPE_ARITY];
    u32 count = 0;
    valk_lval_t *c = qexpr->cons.tail;
    while (c && LVAL_TYPE(c) == LVAL_CONS) {
      if (count >= VALK_TI_MAX_TYPE_ARITY) {
        fprintf(stderr, "[type-infer] warning: sig function type has more than %d parts, truncating\n",
                VALK_TI_MAX_TYPE_ARITY);
        break;
      }
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
  valk_ti_scope_t *child = valk_ti_scope_new(ctx, scope);
  if (!child) return ctx->t_nil;
  valk_type_t *param_types[VALK_TI_MAX_FUN_PARAMS];
  u32 param_count = 0;

  valk_type_scheme_t *sig = fname ? valk_ti_scope_lookup(scope, fname) : nullptr;
  valk_type_t *sig_t = nullptr;
  if (sig) sig_t = valk_type_find(valk_type_instantiate(ctx, sig));

  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    if (param_count >= VALK_TI_MAX_FUN_PARAMS) {
      fprintf(stderr, "[type-infer] warning: lambda '%s' has more than %d params, truncating\n",
              fname ? fname : "<anon>", VALK_TI_MAX_FUN_PARAMS);
      break;
    }
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
      if (sig_t && sig_t->kind == VALK_TY_FUN && param_count < sig_t->fun.param_count)
        valk_type_unify(ctx, param_types[param_count], sig_t->fun.params[param_count], 0, 0);
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

static bool is_lambda_expr(valk_lval_t *expr) {
  if (!expr || LVAL_TYPE(expr) != LVAL_CONS || (expr->flags & LVAL_FLAG_QUOTED))
    return false;
  valk_lval_t *h = expr->cons.head;
  if (h && LVAL_TYPE(h) == LVAL_SYM &&
      (strcmp(h->str, "\\") == 0 || strcmp(h->str, "lambda") == 0))
    return true;
  if (h && LVAL_TYPE(h) == LVAL_FUN && h->fun.builtin) {
    extern valk_lenv_t *valk_macro_env(void);
    valk_lval_t *lr = valk_lenv_get(valk_macro_env(), valk_lval_sym("\\"));
    if (LVAL_TYPE(lr) == LVAL_FUN && h->fun.builtin == lr->fun.builtin)
      return true;
  }
  return false;
}

static valk_type_t *infer_binding(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                                   valk_lval_t *binding_q, valk_lval_t *rhs) {
  if (!is_qexpr_node(binding_q)) return ctx->t_nil;
  const char *name = sym_name(binding_q->cons.head);
  if (!name) return ctx->t_nil;

  valk_type_t *rhs_t;
  if (rhs && is_lambda_expr(rhs)) {
    valk_lval_t *lrest = rhs->cons.tail;
    valk_lval_t *formals = lrest ? lrest->cons.head : nullptr;
    valk_lval_t *body = lrest ? lrest->cons.tail : nullptr;
    bool nil_formals = formals && LVAL_TYPE(formals) == LVAL_NIL;
    valk_lval_t *flist = nil_formals ? nullptr
                       : (is_qexpr_node(formals) && formals->cons.head ? formals : nullptr);
    rhs_t = infer_lambda(ctx, scope, flist, body, name);
  } else {
    rhs_t = infer_expr(ctx, scope, rhs);
  }

  valk_ti_scope_bind(ctx, scope, name, (valk_type_scheme_t){.type = rhs_t});
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
  valk_type_t *arg_types[VALK_TI_MAX_FUN_PARAMS];
  u32 argc = 0;
  valk_lval_t *cur = args;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    if (argc >= VALK_TI_MAX_FUN_PARAMS) {
      fprintf(stderr, "[type-infer] warning: function application has more than %d args, truncating\n",
              VALK_TI_MAX_FUN_PARAMS);
      break;
    }
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
  if (!expr) return ctx->t_nil;
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
      if (formals && LVAL_TYPE(formals) == LVAL_NIL)
        return infer_lambda(ctx, scope, nullptr, body, nullptr);
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
      if (fname)
        valk_ti_scope_bind(ctx, scope, fname, (valk_type_scheme_t){.type = ft});
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
              valk_ti_scope_bind(ctx, scope, ti_strdup(ctx, sname),
                                ti_scheme_from_type(ctx, sig_type));
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
        valk_type_t *args[32]; u32 ac = 0;
        valk_lval_t *cur = rest;
        while (cur && LVAL_TYPE(cur) == LVAL_CONS && ac < 32) {
          valk_lval_t *a = cur->cons.head;
          if (LVAL_TYPE(a) == LVAL_SYM && a->str[0] == ':') {
            cur = cur->cons.tail;
            if (!cur || LVAL_TYPE(cur) != LVAL_CONS) break;
            args[ac++] = infer_expr(ctx, scope, cur->cons.head);
          } else {
            args[ac++] = infer_expr(ctx, scope, a);
          }
          cur = cur->cons.tail;
        }
        valk_type_t *ret = valk_ti_fresh_var(ctx);
        valk_type_t *exp = valk_ti_fun(ctx, args, ac, ret);
        valk_type_unify(ctx, ct, exp, lval_line(expr), 0);
        return ret;
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

// Populate the file-level type scope from HM-inferred bindings. ONLY the
// top-level scope is consulted: per-function locals (lambda formals, `=`
// bindings inside fn bodies, etc.) live in HM child scopes and are
// lexically scoped to that function. Flattening them into the file scope
// causes name collisions across functions — e.g. one function binds
// `pos: Num` while another binds `pos: LspPosition`, and a third
// function's lambda `(\ {pos} ...)` then resolves field-access on `pos`
// using whichever LspPosition leaked in. That mis-typed transform turns
// `pos:line` into `(nth 2 pos)` against a raw plist, producing wrong
// values or out-of-bounds errors at runtime.
static void populate_scope_entries(valk_ti_scope_t *s,
                                   valk_type_scope_t *out_scope) {
  for (u32 i = 0; i < s->count; i++) {
    const char *name = s->entries[i].name;
    valk_type_t *t = valk_type_find(s->entries[i].scheme.type);
    if (!t) continue;
    if (t->kind != VALK_TY_CON || t->con.arity != 0) continue;
    bool found = false;
    for (u64 j = 0; j < out_scope->count; j++) {
      if (strcmp(out_scope->entries[j].var, name) == 0) { found = true; break; }
    }
    if (found) continue;
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

void valk_ti_populate_type_scope(valk_ti_ctx_t *ctx, valk_ti_scope_t *ti_scope,
                                 valk_type_scope_t *out_scope) {
  UNUSED(ctx);
  populate_scope_entries(ti_scope, out_scope);
}


