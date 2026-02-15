#include "lsp_types.h"
#include "lsp_doc.h"
#include "../parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// Type arena
// ---------------------------------------------------------------------------

void type_arena_init(type_arena_t *a) {
  a->head = nullptr;
  a->next_var_id = 0;
}

void type_arena_free(type_arena_t *a) {
  type_arena_block_t *b = a->head;
  while (b) {
    type_arena_block_t *next = b->next;
    free(b);
    b = next;
  }
  a->head = nullptr;
}

valk_type_t *type_arena_alloc(type_arena_t *a) {
  size_t sz = sizeof(valk_type_t);
  if (!a->head || a->head->used + sz > TYPE_ARENA_BLOCK_SIZE) {
    type_arena_block_t *b = calloc(1, sizeof(type_arena_block_t));
    b->next = a->head;
    a->head = b;
  }
  valk_type_t *ty = (valk_type_t *)(a->head->data + a->head->used);
  a->head->used += sz;
  memset(ty, 0, sz);
  return ty;
}

char *type_arena_strdup(type_arena_t *a, const char *s) {
  size_t len = strlen(s) + 1;
  if (!a->head || a->head->used + len > TYPE_ARENA_BLOCK_SIZE) {
    type_arena_block_t *b = calloc(1, sizeof(type_arena_block_t));
    b->next = a->head;
    a->head = b;
  }
  char *dst = a->head->data + a->head->used;
  a->head->used += len;
  memcpy(dst, s, len);
  return dst;
}

// ---------------------------------------------------------------------------
// Type constructors
// ---------------------------------------------------------------------------

valk_type_t *ty_ground(type_arena_t *a, valk_type_kind_e kind) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = kind;
  return ty;
}

valk_type_t *ty_num(type_arena_t *a) { return ty_ground(a, TY_NUM); }
valk_type_t *ty_str(type_arena_t *a) { return ty_ground(a, TY_STR); }
valk_type_t *ty_sym(type_arena_t *a) { return ty_ground(a, TY_SYM); }
valk_type_t *ty_nil(type_arena_t *a) { return ty_ground(a, TY_NIL); }
valk_type_t *ty_err(type_arena_t *a) { return ty_ground(a, TY_ERR); }
valk_type_t *ty_any(type_arena_t *a) { return ty_ground(a, TY_ANY); }
valk_type_t *ty_never(type_arena_t *a) { return ty_ground(a, TY_NEVER); }

valk_type_t *ty_list(type_arena_t *a, valk_type_t *elem) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_LIST;
  ty->list.elem = elem;
  return ty;
}

valk_type_t *ty_handle(type_arena_t *a, valk_type_t *inner) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_HANDLE;
  ty->handle.inner = inner;
  return ty;
}

valk_type_t *ty_ref(type_arena_t *a, const char *tag) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_REF;
  ty->ref.tag = tag ? type_arena_strdup(a, tag) : nullptr;
  return ty;
}

valk_type_t *ty_fun(type_arena_t *a, valk_type_t **params, int n, valk_type_t *ret, bool variadic) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_FUN;
  ty->fun.param_count = n < TY_MAX_PARAMS ? n : TY_MAX_PARAMS;
  for (int i = 0; i < ty->fun.param_count; i++)
    ty->fun.params[i] = params[i];
  ty->fun.ret = ret;
  ty->fun.variadic = variadic;
  return ty;
}

valk_type_t *ty_var(type_arena_t *a) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_VAR;
  ty->var.id = a->next_var_id++;
  ty->var.link = nullptr;
  return ty;
}

// ---------------------------------------------------------------------------
// Union types
// ---------------------------------------------------------------------------

static bool union_contains(const valk_type_t *u, const valk_type_t *t) {
  if (u->kind == TY_UNION) {
    for (int i = 0; i < u->onion.count; i++)
      if (ty_equal(u->onion.members[i], t)) return true;
    return false;
  }
  return ty_equal(u, t);
}

valk_type_t *ty_union2(type_arena_t *a, valk_type_t *t1, valk_type_t *t2) {
  t1 = ty_resolve(t1);
  t2 = ty_resolve(t2);
  if (ty_equal(t1, t2)) return t1;
  if (t1->kind == TY_ANY || t2->kind == TY_ANY) return ty_any(a);
  if (t1->kind == TY_NEVER) return t2;
  if (t2->kind == TY_NEVER) return t1;

  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_UNION;
  ty->onion.count = 0;

  if (t1->kind == TY_UNION) {
    for (int i = 0; i < t1->onion.count && ty->onion.count < TY_MAX_UNION; i++)
      ty->onion.members[ty->onion.count++] = t1->onion.members[i];
  } else {
    ty->onion.members[ty->onion.count++] = t1;
  }

  if (t2->kind == TY_UNION) {
    for (int i = 0; i < t2->onion.count; i++) {
      if (!union_contains(ty, t2->onion.members[i]) && ty->onion.count < TY_MAX_UNION)
        ty->onion.members[ty->onion.count++] = t2->onion.members[i];
    }
  } else {
    if (!union_contains(ty, t2) && ty->onion.count < TY_MAX_UNION)
      ty->onion.members[ty->onion.count++] = t2;
  }

  if (ty->onion.count == 1) return ty->onion.members[0];
  return ty;
}

valk_type_t *ty_union3(type_arena_t *a, valk_type_t *t1, valk_type_t *t2, valk_type_t *t3) {
  return ty_union2(a, ty_union2(a, t1, t2), t3);
}

valk_type_t *ty_join(type_arena_t *a, const valk_type_t *t1, const valk_type_t *t2) {
  if (!t1) return (valk_type_t *)t2;
  if (!t2) return (valk_type_t *)t1;
  if (ty_equal(t1, t2)) return (valk_type_t *)t1;
  return ty_union2(a, (valk_type_t *)t1, (valk_type_t *)t2);
}

// ---------------------------------------------------------------------------
// Type variable resolution — chase links to find the representative.
// ---------------------------------------------------------------------------

valk_type_t *ty_resolve(valk_type_t *ty) {
  if (!ty) return ty;
  while (ty->kind == TY_VAR && ty->var.link)
    ty = ty->var.link;
  return ty;
}

// ---------------------------------------------------------------------------
// Type display
// ---------------------------------------------------------------------------

static const char *GROUND_NAMES[] = {
  [TY_NUM]    = "Num",
  [TY_STR]    = "Str",
  [TY_SYM]    = "Sym",
  [TY_NIL]    = "Nil",
  [TY_ERR]    = "Err",
  [TY_ANY]    = "Any",
  [TY_NEVER]  = "Never",
};

const char *valk_type_name(const valk_type_t *ty) {
  if (!ty) return "?";
  valk_type_t *r = ty_resolve((valk_type_t *)ty);
  if (r->kind < TY_LIST && r->kind != TY_VAR) return GROUND_NAMES[r->kind];
  if (r->kind == TY_ANY) return "Any";
  if (r->kind == TY_NEVER) return "Never";
  if (r->kind == TY_LIST) return "List";
  if (r->kind == TY_HANDLE) return "Handle";
  if (r->kind == TY_REF) return "Ref";
  if (r->kind == TY_FUN) return "Fun";
  if (r->kind == TY_VAR) return "?";
  if (r->kind == TY_UNION) return "Union";
  return "?";
}

char *valk_type_display(const valk_type_t *ty) {
  if (!ty) return strdup("?");
  valk_type_t *r = ty_resolve((valk_type_t *)ty);

  char buf[256] = {0};
  int pos = 0;

  switch (r->kind) {
  case TY_NUM: case TY_STR: case TY_SYM: case TY_NIL:
  case TY_ERR: case TY_ANY: case TY_NEVER:
    return strdup(GROUND_NAMES[r->kind]);

  case TY_LIST: {
    char *elem = valk_type_display(r->list.elem);
    snprintf(buf, sizeof(buf), "List(%s)", elem);
    free(elem);
    return strdup(buf);
  }

  case TY_HANDLE: {
    char *inner = valk_type_display(r->handle.inner);
    snprintf(buf, sizeof(buf), "Handle(%s)", inner);
    free(inner);
    return strdup(buf);
  }

  case TY_REF:
    if (r->ref.tag)
      snprintf(buf, sizeof(buf), "Ref(%s)", r->ref.tag);
    else
      snprintf(buf, sizeof(buf), "Ref");
    return strdup(buf);

  case TY_FUN: {
    pos += snprintf(buf + pos, sizeof(buf) - pos, "(");
    for (int i = 0; i < r->fun.param_count && pos < 240; i++) {
      if (i > 0) pos += snprintf(buf + pos, sizeof(buf) - pos, ", ");
      char *p = valk_type_display(r->fun.params[i]);
      pos += snprintf(buf + pos, sizeof(buf) - pos, "%s", p);
      free(p);
    }
    if (r->fun.variadic) pos += snprintf(buf + pos, sizeof(buf) - pos, "...");
    char *ret = valk_type_display(r->fun.ret);
    pos += snprintf(buf + pos, sizeof(buf) - pos, " -> %s)", ret);
    free(ret);
    return strdup(buf);
  }

  case TY_VAR:
    snprintf(buf, sizeof(buf), "'t%d", r->var.id);
    return strdup(buf);

  case TY_UNION:
    for (int i = 0; i < r->onion.count && pos < 240; i++) {
      if (i > 0) pos += snprintf(buf + pos, sizeof(buf) - pos, "|");
      char *m = valk_type_display(r->onion.members[i]);
      pos += snprintf(buf + pos, sizeof(buf) - pos, "%s", m);
      free(m);
    }
    return strdup(buf);

  default:
    return strdup("?");
  }
}

// ---------------------------------------------------------------------------
// Type equality (structural, follows links)
// ---------------------------------------------------------------------------

bool ty_equal(const valk_type_t *a, const valk_type_t *b) {
  if (a == b) return true;
  if (!a || !b) return false;

  valk_type_t *ra = ty_resolve((valk_type_t *)a);
  valk_type_t *rb = ty_resolve((valk_type_t *)b);
  if (ra == rb) return true;
  if (ra->kind != rb->kind) return false;

  switch (ra->kind) {
  case TY_NUM: case TY_STR: case TY_SYM: case TY_NIL:
  case TY_ERR: case TY_ANY: case TY_NEVER:
    return true;

  case TY_LIST:
    return ty_equal(ra->list.elem, rb->list.elem);

  case TY_HANDLE:
    return ty_equal(ra->handle.inner, rb->handle.inner);

  case TY_REF:
    if (!ra->ref.tag && !rb->ref.tag) return true;
    if (!ra->ref.tag || !rb->ref.tag) return false;
    return strcmp(ra->ref.tag, rb->ref.tag) == 0;

  case TY_FUN:
    if (ra->fun.param_count != rb->fun.param_count) return false;
    if (ra->fun.variadic != rb->fun.variadic) return false;
    for (int i = 0; i < ra->fun.param_count; i++)
      if (!ty_equal(ra->fun.params[i], rb->fun.params[i])) return false;
    return ty_equal(ra->fun.ret, rb->fun.ret);

  case TY_VAR:
    return ra->var.id == rb->var.id;

  case TY_UNION:
    if (ra->onion.count != rb->onion.count) return false;
    for (int i = 0; i < ra->onion.count; i++) {
      bool found = false;
      for (int j = 0; j < rb->onion.count; j++)
        if (ty_equal(ra->onion.members[i], rb->onion.members[j])) { found = true; break; }
      if (!found) return false;
    }
    return true;

  default:
    return false;
  }
}

// ---------------------------------------------------------------------------
// Occurs check — does var_id appear in ty?
// ---------------------------------------------------------------------------

bool ty_occurs(int var_id, valk_type_t *ty) {
  ty = ty_resolve(ty);
  if (!ty) return false;
  switch (ty->kind) {
  case TY_VAR: return ty->var.id == var_id;
  case TY_LIST: return ty_occurs(var_id, ty->list.elem);
  case TY_HANDLE: return ty_occurs(var_id, ty->handle.inner);
  case TY_FUN:
    for (int i = 0; i < ty->fun.param_count; i++)
      if (ty_occurs(var_id, ty->fun.params[i])) return true;
    return ty_occurs(var_id, ty->fun.ret);
  case TY_UNION:
    for (int i = 0; i < ty->onion.count; i++)
      if (ty_occurs(var_id, ty->onion.members[i])) return true;
    return false;
  default: return false;
  }
}

// ---------------------------------------------------------------------------
// Unification — make two types equal, binding type variables.
// Returns true on success, false on type error.
// ---------------------------------------------------------------------------

bool ty_unify(type_arena_t *a, valk_type_t *t1, valk_type_t *t2) {
  t1 = ty_resolve(t1);
  t2 = ty_resolve(t2);
  if (t1 == t2) return true;

  if (t1->kind == TY_ANY || t2->kind == TY_ANY) return true;

  if (t1->kind == TY_VAR) {
    if (ty_occurs(t1->var.id, t2)) return false;
    t1->var.link = t2;
    return true;
  }
  if (t2->kind == TY_VAR) {
    if (ty_occurs(t2->var.id, t1)) return false;
    t2->var.link = t1;
    return true;
  }

  if (t1->kind == TY_NIL && t2->kind == TY_LIST) return true;
  if (t1->kind == TY_LIST && t2->kind == TY_NIL) return true;

  if (t1->kind != t2->kind) return false;

  switch (t1->kind) {
  case TY_NUM: case TY_STR: case TY_SYM: case TY_NIL: case TY_ERR:
    return true;

  case TY_LIST:
    return ty_unify(a, t1->list.elem, t2->list.elem);

  case TY_HANDLE:
    return ty_unify(a, t1->handle.inner, t2->handle.inner);

  case TY_REF:
    if (!t1->ref.tag || !t2->ref.tag) return true;
    return strcmp(t1->ref.tag, t2->ref.tag) == 0;

  case TY_FUN: {
    int n = t1->fun.param_count < t2->fun.param_count ?
            t1->fun.param_count : t2->fun.param_count;
    for (int i = 0; i < n; i++)
      if (!ty_unify(a, t1->fun.params[i], t2->fun.params[i])) return false;
    return ty_unify(a, t1->fun.ret, t2->fun.ret);
  }

  default:
    return false;
  }
}

// ---------------------------------------------------------------------------
// Compatibility check (for diagnostics — looser than unification).
// actual is compatible with expected if it could unify without binding.
// ---------------------------------------------------------------------------

bool ty_compatible(const valk_type_t *expected, const valk_type_t *actual) {
  if (!expected || !actual) return true;
  valk_type_t *re = ty_resolve((valk_type_t *)expected);
  valk_type_t *ra = ty_resolve((valk_type_t *)actual);
  if (re == ra) return true;
  if (re->kind == TY_ANY || ra->kind == TY_ANY) return true;
  if (ra->kind == TY_NEVER || re->kind == TY_NEVER) return true;
  if (re->kind == TY_VAR || ra->kind == TY_VAR) return true;
  if (ty_equal(re, ra)) return true;

  if (re->kind == TY_LIST && ra->kind == TY_NIL) return true;
  if (re->kind == TY_NIL && ra->kind == TY_LIST) return true;

  if (re->kind == TY_REF && ra->kind == TY_REF) {
    if (!re->ref.tag || !ra->ref.tag) return true;
    return strcmp(re->ref.tag, ra->ref.tag) == 0;
  }

  if (re->kind == TY_LIST && ra->kind == TY_LIST)
    return ty_compatible(re->list.elem, ra->list.elem);

  if (re->kind == TY_HANDLE && ra->kind == TY_HANDLE)
    return ty_compatible(re->handle.inner, ra->handle.inner);

  if (re->kind == TY_UNION) {
    if (ra->kind == TY_UNION) {
      for (int i = 0; i < ra->onion.count; i++)
        if (!ty_compatible(re, ra->onion.members[i])) return false;
      return true;
    }
    for (int i = 0; i < re->onion.count; i++)
      if (ty_compatible(re->onion.members[i], ra)) return true;
    return false;
  }

  if (ra->kind == TY_UNION) {
    for (int i = 0; i < ra->onion.count; i++)
      if (ty_compatible(re, ra->onion.members[i])) return true;
    return false;
  }

  if (re->kind == TY_FUN && ra->kind == TY_FUN) {
    int n = re->fun.param_count < ra->fun.param_count ?
            re->fun.param_count : ra->fun.param_count;
    for (int i = 0; i < n; i++)
      if (!ty_compatible(re->fun.params[i], ra->fun.params[i])) return false;
    return ty_compatible(re->fun.ret, ra->fun.ret);
  }

  return false;
}

// ---------------------------------------------------------------------------
// Type schemes
// ---------------------------------------------------------------------------

static type_scheme_t *scheme_alloc(type_arena_t *a) {
  size_t sz = sizeof(type_scheme_t);
  if (!a->head || a->head->used + sz > TYPE_ARENA_BLOCK_SIZE) {
    type_arena_block_t *b = calloc(1, sizeof(type_arena_block_t));
    b->next = a->head;
    a->head = b;
  }
  type_scheme_t *s = (type_scheme_t *)(a->head->data + a->head->used);
  a->head->used += sz;
  memset(s, 0, sz);
  return s;
}

type_scheme_t *scheme_mono(type_arena_t *a, valk_type_t *ty) {
  type_scheme_t *s = scheme_alloc(a);
  s->var_count = 0;
  s->body = ty;
  return s;
}

type_scheme_t *scheme_poly(type_arena_t *a, int *var_ids, int var_count, valk_type_t *body) {
  type_scheme_t *s = scheme_alloc(a);
  s->var_count = var_count < SCHEME_MAX_VARS ? var_count : SCHEME_MAX_VARS;
  for (int i = 0; i < s->var_count; i++)
    s->var_ids[i] = var_ids[i];
  s->body = body;
  return s;
}

static valk_type_t *instantiate_rec(type_arena_t *a, valk_type_t *ty,
                                     int *old_ids, valk_type_t **new_vars, int n) {
  ty = ty_resolve(ty);
  if (!ty) return nullptr;

  switch (ty->kind) {
  case TY_VAR:
    for (int i = 0; i < n; i++)
      if (ty->var.id == old_ids[i]) return new_vars[i];
    return ty;

  case TY_LIST: {
    valk_type_t *elem = instantiate_rec(a, ty->list.elem, old_ids, new_vars, n);
    if (elem == ty->list.elem) return ty;
    return ty_list(a, elem);
  }

  case TY_HANDLE: {
    valk_type_t *inner = instantiate_rec(a, ty->handle.inner, old_ids, new_vars, n);
    if (inner == ty->handle.inner) return ty;
    return ty_handle(a, inner);
  }

  case TY_REF:
    return ty;

  case TY_FUN: {
    bool changed = false;
    valk_type_t *params[TY_MAX_PARAMS];
    for (int i = 0; i < ty->fun.param_count; i++) {
      params[i] = instantiate_rec(a, ty->fun.params[i], old_ids, new_vars, n);
      if (params[i] != ty->fun.params[i]) changed = true;
    }
    valk_type_t *ret = instantiate_rec(a, ty->fun.ret, old_ids, new_vars, n);
    if (ret != ty->fun.ret) changed = true;
    if (!changed) return ty;
    return ty_fun(a, params, ty->fun.param_count, ret, ty->fun.variadic);
  }

  case TY_UNION: {
    bool changed = false;
    valk_type_t *members[TY_MAX_UNION];
    for (int i = 0; i < ty->onion.count; i++) {
      members[i] = instantiate_rec(a, ty->onion.members[i], old_ids, new_vars, n);
      if (members[i] != ty->onion.members[i]) changed = true;
    }
    if (!changed) return ty;
    valk_type_t *r = members[0];
    for (int i = 1; i < ty->onion.count; i++)
      r = ty_union2(a, r, members[i]);
    return r;
  }

  default:
    return ty;
  }
}

valk_type_t *scheme_instantiate(type_arena_t *a, const type_scheme_t *scheme) {
  if (scheme->var_count == 0) return scheme->body;
  valk_type_t *new_vars[SCHEME_MAX_VARS];
  for (int i = 0; i < scheme->var_count; i++)
    new_vars[i] = ty_var(a);
  return instantiate_rec(a, scheme->body,
                         (int *)scheme->var_ids, new_vars, scheme->var_count);
}

static void collect_free_vars(valk_type_t *ty, int floor,
                               int *ids, int *count, int max) {
  ty = ty_resolve(ty);
  if (!ty || *count >= max) return;

  switch (ty->kind) {
  case TY_VAR:
    if (ty->var.id >= floor) {
      for (int i = 0; i < *count; i++)
        if (ids[i] == ty->var.id) return;
      ids[(*count)++] = ty->var.id;
    }
    return;
  case TY_LIST: collect_free_vars(ty->list.elem, floor, ids, count, max); return;
  case TY_HANDLE: collect_free_vars(ty->handle.inner, floor, ids, count, max); return;
  case TY_FUN:
    for (int i = 0; i < ty->fun.param_count; i++)
      collect_free_vars(ty->fun.params[i], floor, ids, count, max);
    collect_free_vars(ty->fun.ret, floor, ids, count, max);
    return;
  case TY_UNION:
    for (int i = 0; i < ty->onion.count; i++)
      collect_free_vars(ty->onion.members[i], floor, ids, count, max);
    return;
  default: return;
  }
}

type_scheme_t *scheme_generalize(type_arena_t *a, valk_type_t *ty, int floor_var_id) {
  int ids[SCHEME_MAX_VARS];
  int count = 0;
  collect_free_vars(ty, floor_var_id, ids, &count, SCHEME_MAX_VARS);
  if (count == 0) return scheme_mono(a, ty);
  return scheme_poly(a, ids, count, ty);
}

// ---------------------------------------------------------------------------
// Typed scope
// ---------------------------------------------------------------------------

typed_scope_t *typed_scope_push(type_arena_t *a, typed_scope_t *parent) {
  (void)a;
  typed_scope_t *s = calloc(1, sizeof(typed_scope_t));
  s->parent = parent;
  return s;
}

void typed_scope_pop(typed_scope_t *s) {
  for (size_t i = 0; i < s->count; i++)
    free(s->bindings[i].name);
  free(s->bindings);
  free(s);
}

void typed_scope_add(typed_scope_t *s, const char *name, type_scheme_t *scheme) {
  for (size_t i = 0; i < s->count; i++) {
    if (strcmp(s->bindings[i].name, name) == 0) {
      s->bindings[i].scheme = scheme;
      return;
    }
  }
  if (s->count >= s->cap) {
    s->cap = s->cap == 0 ? 16 : s->cap * 2;
    s->bindings = realloc(s->bindings, sizeof(typed_binding_t) * s->cap);
  }
  s->bindings[s->count++] = (typed_binding_t){strdup(name), scheme};
}

void typed_scope_add_mono(typed_scope_t *s, const char *name, valk_type_t *ty) {
  type_scheme_t tmp = {.var_count = 0, .body = ty};
  type_scheme_t *mono = malloc(sizeof(type_scheme_t));
  *mono = tmp;
  typed_scope_add(s, name, mono);
}

type_scheme_t *typed_scope_lookup(typed_scope_t *s, const char *name) {
  while (s) {
    for (size_t i = 0; i < s->count; i++)
      if (strcmp(s->bindings[i].name, name) == 0) return s->bindings[i].scheme;
    s = s->parent;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// Inference helpers
// ---------------------------------------------------------------------------

static valk_type_t *infer_eval(infer_ctx_t *ctx, valk_lval_t *expr) {
  if (!expr) return ty_nil(ctx->arena);
  if (LVAL_TYPE(expr) == LVAL_CONS && (expr->flags & LVAL_FLAG_QUOTED)) {
    uint32_t saved = expr->flags;
    expr->flags &= ~LVAL_FLAG_QUOTED;
    valk_type_t *r = infer_expr(ctx, expr);
    expr->flags = saved;
    return r;
  }
  return infer_expr(ctx, expr);
}

static valk_type_t *infer_body_last(infer_ctx_t *ctx, valk_lval_t *rest) {
  valk_type_t *result = ty_nil(ctx->arena);
  while (rest && LVAL_TYPE(rest) == LVAL_CONS) {
    result = infer_eval(ctx, valk_lval_head(rest));
    rest = valk_lval_tail(rest);
  }
  return result;
}

static void infer_body(infer_ctx_t *ctx, valk_lval_t *rest) {
  while (rest && LVAL_TYPE(rest) == LVAL_CONS) {
    infer_eval(ctx, valk_lval_head(rest));
    rest = valk_lval_tail(rest);
  }
}

static int count_list(valk_lval_t *rest) {
  int n = 0;
  while (rest && LVAL_TYPE(rest) == LVAL_CONS) { n++; rest = valk_lval_tail(rest); }
  return n;
}

static void emit_type_error(infer_ctx_t *ctx, const char *name,
                             int arg_idx, valk_type_t *expected, valk_type_t *actual) {
  char msg[256];
  char *exp_str = valk_type_display(expected);
  char *act_str = valk_type_display(actual);
  snprintf(msg, sizeof(msg), "'%s' argument %d: expected %s, got %s",
           name, arg_idx + 1, exp_str, act_str);
  free(exp_str);
  free(act_str);
  if (ctx->doc && ctx->text) {
    int off = lsp_find_sym_offset(ctx->text, name, *ctx->cursor);
    if (off >= 0) {
      lsp_pos_t p = offset_to_pos(ctx->text, off);
      doc_add_diag_full(ctx->doc, msg, p.line, p.col, (int)strlen(name), 1);
    }
  }
}

// ---------------------------------------------------------------------------
// Infer type of qexpr literal {e1 e2 ... en}
// If all elements have the same type, return List(t). Otherwise List(Any).
// ---------------------------------------------------------------------------

static valk_type_t *infer_qexpr(infer_ctx_t *ctx, valk_lval_t *expr) {
  valk_type_t *elem_ty = nullptr;
  bool homogeneous = true;
  int count = 0;
  valk_lval_t *cur = expr;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_type_t *et = infer_expr(ctx, valk_lval_head(cur));
    et = ty_resolve(et);
    if (!elem_ty) {
      elem_ty = et;
    } else if (homogeneous && !ty_equal(elem_ty, et)) {
      homogeneous = false;
    }
    count++;
    cur = valk_lval_tail(cur);
  }
  if (count == 0) return ty_nil(ctx->arena);
  if (homogeneous && elem_ty)
    return ty_list(ctx->arena, elem_ty);
  return ty_list(ctx->arena, ty_any(ctx->arena));
}

// ---------------------------------------------------------------------------
// Check if name is a type predicate and return the narrowed type.
// e.g. "num?" → TY_NUM, "str?" → TY_STR, etc.
// ---------------------------------------------------------------------------

static valk_type_t *predicate_narrows_to(type_arena_t *a, const char *name) {
  if (strcmp(name, "num?") == 0) return ty_num(a);
  if (strcmp(name, "str?") == 0) return ty_str(a);
  if (strcmp(name, "error?") == 0) return ty_err(a);
  if (strcmp(name, "list?") == 0) return ty_list(a, ty_var(a));
  if (strcmp(name, "ref?") == 0) return ty_ref(a, nullptr);
  if (strcmp(name, "nil?") == 0) return ty_nil(a);
  return nullptr;
}

// ---------------------------------------------------------------------------
// Type inference — Algorithm W style
// ---------------------------------------------------------------------------

valk_type_t *infer_expr(infer_ctx_t *ctx, valk_lval_t *expr) {
  if (!expr) return ty_nil(ctx->arena);

  switch (LVAL_TYPE(expr)) {
  case LVAL_NUM: return ty_num(ctx->arena);
  case LVAL_STR: return ty_str(ctx->arena);
  case LVAL_NIL: return ty_nil(ctx->arena);
  case LVAL_ERR: return ty_err(ctx->arena);
  case LVAL_HANDLE: return ty_handle(ctx->arena, ty_var(ctx->arena));
  case LVAL_REF: return ty_ref(ctx->arena, nullptr);

  case LVAL_SYM: {
    if (expr->str[0] == ':') return ty_sym(ctx->arena);
    if (strcmp(expr->str, "true") == 0 || strcmp(expr->str, "false") == 0)
      return ty_num(ctx->arena);
    if (strcmp(expr->str, "nil") == 0)
      return ty_nil(ctx->arena);
    if (strcmp(expr->str, "otherwise") == 0)
      return ty_num(ctx->arena);

    type_scheme_t *sch = typed_scope_lookup(ctx->scope, expr->str);
    if (sch) return scheme_instantiate(ctx->arena, sch);

    return ty_any(ctx->arena);
  }

  case LVAL_FUN: return ty_fun(ctx->arena, nullptr, 0, ty_var(ctx->arena), false);

  case LVAL_CONS: break;
  default: return ty_any(ctx->arena);
  }

  if (expr->flags & LVAL_FLAG_QUOTED)
    return infer_qexpr(ctx, expr);

  valk_lval_t *head = valk_lval_head(expr);
  valk_lval_t *rest = valk_lval_tail(expr);
  if (!head) return ty_nil(ctx->arena);

  if (LVAL_TYPE(head) != LVAL_SYM) {
    infer_expr(ctx, head);
    infer_body(ctx, rest);
    return ty_any(ctx->arena);
  }

  const char *name = head->str;

  // --- Special forms ---

  if (strcmp(name, "quote") == 0)
    return ty_list(ctx->arena, ty_any(ctx->arena));

  if (strcmp(name, "\\") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_fun(ctx->arena, nullptr, 0, ty_var(ctx->arena), false);
    valk_lval_t *formals = valk_lval_head(rest);
    valk_lval_t *body_rest = valk_lval_tail(rest);

    typed_scope_t *inner = typed_scope_push(ctx->arena, ctx->scope);
    valk_type_t *param_types[TY_MAX_PARAMS];
    int param_count = 0;
    bool variadic = false;

    if (formals && LVAL_TYPE(formals) == LVAL_CONS) {
      valk_lval_t *cur = formals;
      while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        valk_lval_t *h = valk_lval_head(cur);
        if (h && LVAL_TYPE(h) == LVAL_SYM) {
          if (h->str[0] == '&') {
            variadic = true;
          } else {
            valk_type_t *pt = ty_var(ctx->arena);
            if (param_count < TY_MAX_PARAMS)
              param_types[param_count++] = pt;
            typed_scope_add_mono(inner, h->str, pt);
          }
        }
        cur = valk_lval_tail(cur);
      }
    }

    typed_scope_t *saved = ctx->scope;
    ctx->scope = inner;
    valk_type_t *body_ty = infer_body_last(ctx, body_rest);
    ctx->scope = saved;
    typed_scope_pop(inner);

    return ty_fun(ctx->arena, param_types, param_count, body_ty, variadic);
  }

  if (strcmp(name, "fun") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_fun(ctx->arena, nullptr, 0, ty_var(ctx->arena), false);
    valk_lval_t *name_formals = valk_lval_head(rest);
    valk_lval_t *body_rest = valk_lval_tail(rest);

    if (name_formals && LVAL_TYPE(name_formals) == LVAL_CONS) {
      valk_lval_t *fname = valk_lval_head(name_formals);
      typed_scope_t *inner = typed_scope_push(ctx->arena, ctx->scope);

      valk_type_t *param_types[TY_MAX_PARAMS];
      int param_count = 0;
      bool variadic = false;

      valk_lval_t *params = valk_lval_tail(name_formals);
      while (params && LVAL_TYPE(params) == LVAL_CONS) {
        valk_lval_t *h = valk_lval_head(params);
        if (h && LVAL_TYPE(h) == LVAL_SYM) {
          if (h->str[0] == '&') {
            variadic = true;
          } else {
            valk_type_t *pt = ty_var(ctx->arena);
            if (param_count < TY_MAX_PARAMS)
              param_types[param_count++] = pt;
            typed_scope_add_mono(inner, h->str, pt);
          }
        }
        params = valk_lval_tail(params);
      }

      typed_scope_t *saved = ctx->scope;
      ctx->scope = inner;
      valk_type_t *body_ty = infer_body_last(ctx, body_rest);
      ctx->scope = saved;
      typed_scope_pop(inner);

      valk_type_t *fn_ty = ty_fun(ctx->arena, param_types, param_count, body_ty, variadic);
      if (fname && LVAL_TYPE(fname) == LVAL_SYM) {
        int floor = ctx->floor_var_id;
        type_scheme_t *sch = scheme_generalize(ctx->arena, fn_ty, floor);
        typed_scope_add(ctx->scope, fname->str, sch);
      }
      return fn_ty;
    }
    return ty_fun(ctx->arena, nullptr, 0, ty_var(ctx->arena), false);
  }

  if (strcmp(name, "def") == 0 || strcmp(name, "=") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_nil(ctx->arena);
    valk_lval_t *binding = valk_lval_head(rest);
    valk_lval_t *val_rest = valk_lval_tail(rest);

    if (binding && LVAL_TYPE(binding) == LVAL_CONS && val_rest &&
        LVAL_TYPE(val_rest) == LVAL_CONS) {
      valk_lval_t *sym_cur = binding;
      valk_lval_t *val_cur = val_rest;
      while (sym_cur && LVAL_TYPE(sym_cur) == LVAL_CONS &&
             val_cur && LVAL_TYPE(val_cur) == LVAL_CONS) {
        valk_lval_t *s = valk_lval_head(sym_cur);
        valk_lval_t *v = valk_lval_head(val_cur);
        if (s && LVAL_TYPE(s) == LVAL_SYM) {
          int floor = ctx->arena->next_var_id;
          valk_type_t *vt = infer_expr(ctx, v);
          type_scheme_t *sch = scheme_generalize(ctx->arena, vt, floor);
          typed_scope_add(ctx->scope, s->str, sch);
        }
        sym_cur = valk_lval_tail(sym_cur);
        val_cur = valk_lval_tail(val_cur);
      }
    } else if (binding && LVAL_TYPE(binding) == LVAL_SYM &&
               val_rest && LVAL_TYPE(val_rest) == LVAL_CONS) {
      int floor = ctx->arena->next_var_id;
      valk_type_t *vt = infer_expr(ctx, valk_lval_head(val_rest));
      type_scheme_t *sch = scheme_generalize(ctx->arena, vt, floor);
      typed_scope_add(ctx->scope, binding->str, sch);
    }
    return ty_nil(ctx->arena);
  }

  if (strcmp(name, "let") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_any(ctx->arena);
    valk_lval_t *body_rest = valk_lval_tail(rest);
    typed_scope_t *inner = typed_scope_push(ctx->arena, ctx->scope);
    typed_scope_t *saved = ctx->scope;
    ctx->scope = inner;
    valk_type_t *result = infer_body_last(ctx, body_rest);
    ctx->scope = saved;
    typed_scope_pop(inner);
    return result;
  }

  if (strcmp(name, "if") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_any(ctx->arena);
    valk_lval_t *cond_expr = valk_lval_head(rest);
    infer_expr(ctx, cond_expr);

    valk_lval_t *rest2 = valk_lval_tail(rest);
    if (!rest2 || LVAL_TYPE(rest2) != LVAL_CONS) return ty_any(ctx->arena);

    const char *narrowed_var = nullptr;
    valk_type_t *narrowed_type = nullptr;

    if (cond_expr && LVAL_TYPE(cond_expr) == LVAL_CONS) {
      valk_lval_t *ch = valk_lval_head(cond_expr);
      valk_lval_t *ct = valk_lval_tail(cond_expr);
      if (ch && LVAL_TYPE(ch) == LVAL_SYM && ct && LVAL_TYPE(ct) == LVAL_CONS) {
        valk_lval_t *arg = valk_lval_head(ct);
        valk_type_t *nt = predicate_narrows_to(ctx->arena, ch->str);
        if (nt && arg && LVAL_TYPE(arg) == LVAL_SYM)
          narrowed_var = arg->str;
        narrowed_type = nt;
      }
    }

    valk_type_t *then_ty;
    if (narrowed_var && narrowed_type) {
      typed_scope_t *then_scope = typed_scope_push(ctx->arena, ctx->scope);
      typed_scope_add_mono(then_scope, narrowed_var, narrowed_type);
      typed_scope_t *saved = ctx->scope;
      ctx->scope = then_scope;
      then_ty = infer_expr(ctx, valk_lval_head(rest2));
      ctx->scope = saved;
      typed_scope_pop(then_scope);
    } else {
      then_ty = infer_expr(ctx, valk_lval_head(rest2));
    }

    valk_lval_t *rest3 = valk_lval_tail(rest2);
    if (!rest3 || LVAL_TYPE(rest3) != LVAL_CONS) return then_ty;
    valk_type_t *else_ty = infer_expr(ctx, valk_lval_head(rest3));
    return ty_join(ctx->arena, then_ty, else_ty);
  }

  if (strcmp(name, "do") == 0)
    return infer_body_last(ctx, rest);

  if (strcmp(name, "select") == 0 || strcmp(name, "case") == 0) {
    valk_type_t *result = ty_never(ctx->arena);
    if (strcmp(name, "case") == 0 && rest && LVAL_TYPE(rest) == LVAL_CONS) {
      infer_expr(ctx, valk_lval_head(rest));
      rest = valk_lval_tail(rest);
    }
    while (rest && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *clause = valk_lval_head(rest);
      if (clause && LVAL_TYPE(clause) == LVAL_CONS) {
        valk_lval_t *cond = valk_lval_head(clause);
        valk_lval_t *body = valk_lval_tail(clause);
        infer_expr(ctx, cond);
        if (body && LVAL_TYPE(body) == LVAL_CONS)
          result = ty_join(ctx->arena, result, infer_expr(ctx, valk_lval_head(body)));
      }
      rest = valk_lval_tail(rest);
    }
    return result->kind == TY_NEVER ? ty_any(ctx->arena) : result;
  }

  if (strcmp(name, "eval") == 0 || strcmp(name, "read") == 0) {
    infer_body(ctx, rest);
    return ty_any(ctx->arena);
  }

  if (strcmp(name, "load") == 0) {
    infer_body(ctx, rest);
    return ty_nil(ctx->arena);
  }

  if (strcmp(name, "aio/let") == 0 || strcmp(name, "aio/do") == 0) {
    infer_body(ctx, rest);
    return ty_handle(ctx->arena, ty_var(ctx->arena));
  }

  if (strcmp(name, "<-") == 0) {
    infer_body(ctx, rest);
    return ty_any(ctx->arena);
  }

  // --- Function calls (builtins + user-defined) ---

  type_scheme_t *fn_scheme = typed_scope_lookup(ctx->scope, name);
  if (fn_scheme) {
    valk_type_t *fn_ty = ty_resolve(scheme_instantiate(ctx->arena, fn_scheme));

    if (fn_ty->kind == TY_FUN) {
      int nargs = count_list(rest);
      valk_lval_t *arg_cur = rest;
      for (int i = 0; i < nargs && arg_cur && LVAL_TYPE(arg_cur) == LVAL_CONS; i++) {
        valk_type_t *arg_ty = infer_expr(ctx, valk_lval_head(arg_cur));

        int pi = i;
        if (fn_ty->fun.variadic && i >= fn_ty->fun.param_count)
          pi = fn_ty->fun.param_count - 1;
        else if (i >= fn_ty->fun.param_count)
          pi = -1;

        if (pi >= 0 && pi < fn_ty->fun.param_count) {
          valk_type_t *expected = ty_resolve(fn_ty->fun.params[pi]);
          valk_type_t *actual = ty_resolve(arg_ty);

          if (actual->kind != TY_ANY && expected->kind != TY_ANY &&
              expected->kind != TY_VAR && actual->kind != TY_VAR) {
            if (!ty_compatible(expected, actual))
              emit_type_error(ctx, name, i, expected, actual);
          }

          ty_unify(ctx->arena, fn_ty->fun.params[pi], arg_ty);
        }
        arg_cur = valk_lval_tail(arg_cur);
      }
      return ty_resolve(fn_ty->fun.ret);
    }

    infer_body(ctx, rest);
    return ty_any(ctx->arena);
  }

  infer_body(ctx, rest);
  return ty_any(ctx->arena);
}
