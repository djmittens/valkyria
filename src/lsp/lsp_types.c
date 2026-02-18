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
valk_type_t *ty_qexpr(type_arena_t *a) { return ty_ground(a, TY_QEXPR); }

valk_type_t *ty_kw(type_arena_t *a, const char *tag) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_KW;
  ty->kw.tag = tag ? type_arena_strdup(a, tag) : nullptr;
  return ty;
}

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

valk_type_t *ty_fun_named(type_arena_t *a, valk_type_t **params,
                          const char **names, int n,
                          valk_type_t *ret, bool variadic) {
  valk_type_t *ty = ty_fun(a, params, n, ret, variadic);
  for (int i = 0; i < ty->fun.param_count; i++)
    ty->fun.param_names[i] = names ? names[i] : nullptr;
  return ty;
}

valk_type_t *ty_var(type_arena_t *a) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_VAR;
  ty->var.id = a->next_var_id++;
  ty->var.link = nullptr;
  return ty;
}

valk_type_t *ty_named(type_arena_t *a, const char *name, valk_type_t **params, int n) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_NAMED;
  ty->named.name = type_arena_strdup(a, name);
  ty->named.param_count = n < TY_MAX_PARAMS ? n : TY_MAX_PARAMS;
  for (int i = 0; i < ty->named.param_count; i++)
    ty->named.params[i] = params[i];
  return ty;
}

valk_type_t *ty_plist(type_arena_t *a, const char **keys, valk_type_t **vals, int n) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_PLIST;
  ty->plist.count = n < TY_MAX_PARAMS ? n : TY_MAX_PARAMS;
  for (int i = 0; i < ty->plist.count; i++) {
    ty->plist.keys[i] = type_arena_strdup(a, keys[i]);
    ty->plist.vals[i] = vals[i];
  }
  return ty;
}

valk_type_t *ty_tuple(type_arena_t *a, valk_type_t **elems, int n) {
  valk_type_t *ty = type_arena_alloc(a);
  ty->kind = TY_TUPLE;
  ty->tuple.count = n < TY_MAX_PARAMS ? n : TY_MAX_PARAMS;
  for (int i = 0; i < ty->tuple.count; i++)
    ty->tuple.elems[i] = elems[i];
  return ty;
}

valk_type_t *ty_plist_get(const valk_type_t *ty, const char *key) {
  if (!ty || ty->kind != TY_PLIST) return nullptr;
  for (int i = 0; i < ty->plist.count; i++)
    if (strcmp(ty->plist.keys[i], key) == 0) return ty->plist.vals[i];
  return nullptr;
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

static bool union_member_subsumed(const valk_type_t *existing, const valk_type_t *candidate) {
  const valk_type_t *e = ty_resolve((valk_type_t *)existing);
  const valk_type_t *c = ty_resolve((valk_type_t *)candidate);
  if (e->kind == TY_HANDLE && ty_equal(e->handle.inner, c)) return true;
  return false;
}

valk_type_t *ty_union2(type_arena_t *a, valk_type_t *t1, valk_type_t *t2) {
  t1 = ty_resolve(t1);
  t2 = ty_resolve(t2);
  if (ty_equal(t1, t2)) return t1;
  if (t1->kind == TY_ANY) return t2;
  if (t2->kind == TY_ANY) return t1;
  if (t1->kind == TY_NEVER) return t2;
  if (t2->kind == TY_NEVER) return t1;

  if (t1->kind == TY_HANDLE && ty_equal(t1->handle.inner, t2)) return t1;
  if (t2->kind == TY_HANDLE && ty_equal(t2->handle.inner, t1)) return t2;

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
      valk_type_t *m = ty_resolve(t2->onion.members[i]);
      bool skip = union_contains(ty, m);
      if (!skip) {
        for (int j = 0; j < ty->onion.count; j++) {
          if (union_member_subsumed(ty->onion.members[j], m) ||
              union_member_subsumed(m, ty->onion.members[j])) {
            if (m->kind == TY_HANDLE)
              ty->onion.members[j] = m;
            skip = true;
            break;
          }
        }
      }
      if (!skip && ty->onion.count < TY_MAX_UNION)
        ty->onion.members[ty->onion.count++] = m;
    }
  } else {
    bool skip = union_contains(ty, t2);
    if (!skip) {
      for (int j = 0; j < ty->onion.count; j++) {
        if (union_member_subsumed(ty->onion.members[j], t2) ||
            union_member_subsumed(t2, ty->onion.members[j])) {
          if (t2->kind == TY_HANDLE)
            ty->onion.members[j] = t2;
          skip = true;
          break;
        }
      }
    }
    if (!skip && ty->onion.count < TY_MAX_UNION)
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
  [TY_QEXPR]  = "QExpr",
  [TY_ANY]    = "??",
  [TY_NEVER]  = "Never",
};

const char *valk_type_name(const valk_type_t *ty) {
  if (!ty) return "?";
  valk_type_t *r = ty_resolve((valk_type_t *)ty);
  if (r->kind < TY_KW && r->kind != TY_VAR) return GROUND_NAMES[r->kind];
  if (r->kind == TY_KW) return r->kw.tag ? r->kw.tag : "Kw";
  if (r->kind == TY_ANY) return "??";
  if (r->kind == TY_NEVER) return "Never";
  if (r->kind == TY_LIST) return "List";
  if (r->kind == TY_HANDLE) return "Handle";
  if (r->kind == TY_REF) return "Ref";
  if (r->kind == TY_FUN) return "Fun";
  if (r->kind == TY_VAR) return "?";
  if (r->kind == TY_UNION) return "Union";
  if (r->kind == TY_NAMED) return r->named.name;
  if (r->kind == TY_PLIST) return "PList";
  if (r->kind == TY_TUPLE) return "Tuple";
  return "?";
}

// ---------------------------------------------------------------------------
// Type display — unified implementation.
// When var_map is NULL, shows raw var IDs (T0, T1).
// When var_map is provided, shows pretty names (A, B, C).
// ---------------------------------------------------------------------------

typedef struct {
  int ids[64];
  int count;
} var_map_t;

static int var_map_lookup(var_map_t *m, int id) {
  for (int i = 0; i < m->count; i++)
    if (m->ids[i] == id) return i;
  if (m->count < 64) m->ids[m->count++] = id;
  return m->count - 1;
}

static void collect_vars(const valk_type_t *ty, var_map_t *m) {
  if (!ty) return;
  valk_type_t *r = ty_resolve((valk_type_t *)ty);
  switch (r->kind) {
  case TY_VAR: var_map_lookup(m, r->var.id); break;
  case TY_LIST: collect_vars(r->list.elem, m); break;
  case TY_HANDLE: collect_vars(r->handle.inner, m); break;
  case TY_FUN:
    for (int i = 0; i < r->fun.param_count; i++)
      collect_vars(r->fun.params[i], m);
    collect_vars(r->fun.ret, m);
    break;
  case TY_UNION:
    for (int i = 0; i < r->onion.count; i++)
      collect_vars(r->onion.members[i], m);
    break;
  case TY_NAMED:
    for (int i = 0; i < r->named.param_count; i++)
      collect_vars(r->named.params[i], m);
    break;
  case TY_PLIST:
    for (int i = 0; i < r->plist.count; i++)
      collect_vars(r->plist.vals[i], m);
    break;
  case TY_TUPLE:
    for (int i = 0; i < r->tuple.count; i++)
      collect_vars(r->tuple.elems[i], m);
    break;
  default: break;
  }
}

static char *type_display_impl(const valk_type_t *ty, var_map_t *m) {
  if (!ty) return strdup("?");
  valk_type_t *r = ty_resolve((valk_type_t *)ty);

  char buf[256] = {0};
  int pos = 0;

  switch (r->kind) {
  case TY_NUM: case TY_STR: case TY_SYM: case TY_NIL:
  case TY_ERR: case TY_QEXPR: case TY_ANY: case TY_NEVER:
    return strdup(GROUND_NAMES[r->kind]);

  case TY_KW:
    if (r->kw.tag)
      snprintf(buf, sizeof(buf), ":%s", r->kw.tag);
    else
      snprintf(buf, sizeof(buf), "Kw");
    return strdup(buf);

  case TY_LIST: {
    char *elem = type_display_impl(r->list.elem, m);
    snprintf(buf, sizeof(buf), "List(%s)", elem);
    free(elem);
    return strdup(buf);
  }

  case TY_HANDLE: {
    char *inner = type_display_impl(r->handle.inner, m);
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
      char *p = type_display_impl(r->fun.params[i], m);
      pos += snprintf(buf + pos, sizeof(buf) - pos, "%s", p);
      free(p);
    }
    if (r->fun.variadic) pos += snprintf(buf + pos, sizeof(buf) - pos, "...");
    char *ret = type_display_impl(r->fun.ret, m);
    pos += snprintf(buf + pos, sizeof(buf) - pos, " -> %s)", ret);
    free(ret);
    return strdup(buf);
  }

  case TY_VAR:
    if (m) {
      int idx = var_map_lookup(m, r->var.id);
      if (idx < 26)
        snprintf(buf, sizeof(buf), "%c", 'A' + idx);
      else
        snprintf(buf, sizeof(buf), "T%d", idx);
    } else {
      snprintf(buf, sizeof(buf), "T%d", r->var.id);
    }
    return strdup(buf);

  case TY_UNION:
    for (int i = 0; i < r->onion.count && pos < 240; i++) {
      if (i > 0) pos += snprintf(buf + pos, sizeof(buf) - pos, "|");
      char *mem = type_display_impl(r->onion.members[i], m);
      pos += snprintf(buf + pos, sizeof(buf) - pos, "%s", mem);
      free(mem);
    }
    return strdup(buf);

  case TY_NAMED:
    if (r->named.param_count == 0)
      return strdup(r->named.name);
    pos += snprintf(buf + pos, sizeof(buf) - pos, "%s(", r->named.name);
    for (int i = 0; i < r->named.param_count && pos < 240; i++) {
      if (i > 0) pos += snprintf(buf + pos, sizeof(buf) - pos, ", ");
      char *p = type_display_impl(r->named.params[i], m);
      pos += snprintf(buf + pos, sizeof(buf) - pos, "%s", p);
      free(p);
    }
    pos += snprintf(buf + pos, sizeof(buf) - pos, ")");
    return strdup(buf);

  case TY_PLIST:
    pos += snprintf(buf + pos, sizeof(buf) - pos, "PList(");
    for (int i = 0; i < r->plist.count && pos < 240; i++) {
      if (i > 0) pos += snprintf(buf + pos, sizeof(buf) - pos, ", ");
      char *v = type_display_impl(r->plist.vals[i], m);
      pos += snprintf(buf + pos, sizeof(buf) - pos, "%s: %s", r->plist.keys[i], v);
      free(v);
    }
    pos += snprintf(buf + pos, sizeof(buf) - pos, ")");
    return strdup(buf);

  case TY_TUPLE:
    pos += snprintf(buf + pos, sizeof(buf) - pos, "(");
    for (int i = 0; i < r->tuple.count && pos < 240; i++) {
      if (i > 0) pos += snprintf(buf + pos, sizeof(buf) - pos, ", ");
      char *e = type_display_impl(r->tuple.elems[i], m);
      pos += snprintf(buf + pos, sizeof(buf) - pos, "%s", e);
      free(e);
    }
    pos += snprintf(buf + pos, sizeof(buf) - pos, ")");
    return strdup(buf);

  default:
    return strdup("?");
  }
}

char *valk_type_display(const valk_type_t *ty) {
  return type_display_impl(ty, nullptr);
}

char *valk_type_display_pretty(const valk_type_t *ty) {
  var_map_t m = {.count = 0};
  collect_vars(ty, &m);
  return type_display_impl(ty, &m);
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
  case TY_ERR: case TY_QEXPR: case TY_ANY: case TY_NEVER:
    return true;

  case TY_KW:
    if (!ra->kw.tag && !rb->kw.tag) return true;
    if (!ra->kw.tag || !rb->kw.tag) return false;
    return strcmp(ra->kw.tag, rb->kw.tag) == 0;

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

  case TY_NAMED:
    if (strcmp(ra->named.name, rb->named.name) != 0) return false;
    if (ra->named.param_count != rb->named.param_count) return false;
    for (int i = 0; i < ra->named.param_count; i++)
      if (!ty_equal(ra->named.params[i], rb->named.params[i])) return false;
    return true;

  case TY_PLIST:
    if (ra->plist.count != rb->plist.count) return false;
    for (int i = 0; i < ra->plist.count; i++) {
      if (strcmp(ra->plist.keys[i], rb->plist.keys[i]) != 0) return false;
      if (!ty_equal(ra->plist.vals[i], rb->plist.vals[i])) return false;
    }
    return true;

  case TY_TUPLE:
    if (ra->tuple.count != rb->tuple.count) return false;
    for (int i = 0; i < ra->tuple.count; i++)
      if (!ty_equal(ra->tuple.elems[i], rb->tuple.elems[i])) return false;
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
  case TY_NAMED:
    for (int i = 0; i < ty->named.param_count; i++)
      if (ty_occurs(var_id, ty->named.params[i])) return true;
    return false;
  case TY_PLIST:
    for (int i = 0; i < ty->plist.count; i++)
      if (ty_occurs(var_id, ty->plist.vals[i])) return true;
    return false;
  case TY_TUPLE:
    for (int i = 0; i < ty->tuple.count; i++)
      if (ty_occurs(var_id, ty->tuple.elems[i])) return true;
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

  if (t1->kind == TY_ANY || t2->kind == TY_ANY) return false;

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
  if (t1->kind == TY_PLIST && t2->kind == TY_LIST) return true;
  if (t1->kind == TY_LIST && t2->kind == TY_PLIST) return true;
  if (t1->kind == TY_TUPLE && t2->kind == TY_LIST) return true;
  if (t1->kind == TY_LIST && t2->kind == TY_TUPLE) return true;
  if (t1->kind == TY_QEXPR && t2->kind == TY_LIST) return true;
  if (t1->kind == TY_LIST && t2->kind == TY_QEXPR) return true;
  if (t1->kind == TY_KW && t2->kind == TY_SYM) return true;
  if (t1->kind == TY_SYM && t2->kind == TY_KW) return true;

  if (t1->kind != t2->kind) return false;

  switch (t1->kind) {
  case TY_NUM: case TY_STR: case TY_SYM: case TY_NIL: case TY_ERR:
  case TY_QEXPR:
    return true;

  case TY_KW:
    if (!t1->kw.tag || !t2->kw.tag) return true;
    return strcmp(t1->kw.tag, t2->kw.tag) == 0;

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

  case TY_NAMED: {
    if (strcmp(t1->named.name, t2->named.name) != 0) return false;
    int n = t1->named.param_count < t2->named.param_count ?
            t1->named.param_count : t2->named.param_count;
    for (int i = 0; i < n; i++)
      if (!ty_unify(a, t1->named.params[i], t2->named.params[i])) return false;
    return true;
  }

  case TY_PLIST: {
    if (t1->plist.count != t2->plist.count) return false;
    for (int i = 0; i < t1->plist.count; i++) {
      if (strcmp(t1->plist.keys[i], t2->plist.keys[i]) != 0) return false;
      if (!ty_unify(a, t1->plist.vals[i], t2->plist.vals[i])) return false;
    }
    return true;
  }

  case TY_TUPLE: {
    if (t1->tuple.count != t2->tuple.count) return false;
    for (int i = 0; i < t1->tuple.count; i++)
      if (!ty_unify(a, t1->tuple.elems[i], t2->tuple.elems[i])) return false;
    return true;
  }

  default:
    return false;
  }
}

// ---------------------------------------------------------------------------
// Check if a type contains any unresolved type variables (deeply).
// Used to suppress false-positive type errors when types are incomplete.
// ---------------------------------------------------------------------------

bool ty_has_unresolved_var(const valk_type_t *ty) {
  if (!ty) return false;
  valk_type_t *t = ty_resolve((valk_type_t *)ty);
  switch (t->kind) {
  case TY_VAR: return true;
  case TY_LIST: return ty_has_unresolved_var(t->list.elem);
  case TY_HANDLE: return ty_has_unresolved_var(t->handle.inner);
  case TY_FUN:
    for (int i = 0; i < t->fun.param_count; i++)
      if (ty_has_unresolved_var(t->fun.params[i])) return true;
    return ty_has_unresolved_var(t->fun.ret);
  case TY_UNION:
    for (int i = 0; i < t->onion.count; i++)
      if (ty_has_unresolved_var(t->onion.members[i])) return true;
    return false;
  case TY_NAMED:
    for (int i = 0; i < t->named.param_count; i++)
      if (ty_has_unresolved_var(t->named.params[i])) return true;
    return false;
  case TY_PLIST:
    for (int i = 0; i < t->plist.count; i++)
      if (ty_has_unresolved_var(t->plist.vals[i])) return true;
    return false;
  case TY_TUPLE:
    for (int i = 0; i < t->tuple.count; i++)
      if (ty_has_unresolved_var(t->tuple.elems[i])) return true;
    return false;
  default: return false;
  }
}

// ---------------------------------------------------------------------------
// Check if a type contains TY_ANY anywhere (deeply).
// Used to flag bindings like (A -> ??) where ?? is hidden inside.
// ---------------------------------------------------------------------------

bool ty_contains_any(const valk_type_t *ty) {
  if (!ty) return false;
  valk_type_t *t = ty_resolve((valk_type_t *)ty);
  switch (t->kind) {
  case TY_ANY: return true;
  case TY_LIST: return ty_contains_any(t->list.elem);
  case TY_HANDLE: return ty_contains_any(t->handle.inner);
  case TY_FUN:
    for (int i = 0; i < t->fun.param_count; i++)
      if (ty_contains_any(t->fun.params[i])) return true;
    return ty_contains_any(t->fun.ret);
  case TY_UNION:
    for (int i = 0; i < t->onion.count; i++)
      if (ty_contains_any(t->onion.members[i])) return true;
    return false;
  case TY_NAMED:
    for (int i = 0; i < t->named.param_count; i++)
      if (ty_contains_any(t->named.params[i])) return true;
    return false;
  case TY_PLIST:
    for (int i = 0; i < t->plist.count; i++)
      if (ty_contains_any(t->plist.vals[i])) return true;
    return false;
  case TY_TUPLE:
    for (int i = 0; i < t->tuple.count; i++)
      if (ty_contains_any(t->tuple.elems[i])) return true;
    return false;
  default: return false;
  }
}

// ---------------------------------------------------------------------------
// Check if a type contains TY_ANY inside data wrapper types but NOT inside
// functions. Catches Handle(??), List(??), Named(??), PList(key: ??),
// (Num, ??) but not (?? -> ??) which is legitimate polymorphism in lambdas.
// Stops recursion at TY_FUN boundaries entirely.
// ---------------------------------------------------------------------------

bool ty_has_inference_failure(const valk_type_t *ty) {
  if (!ty) return false;
  valk_type_t *t = ty_resolve((valk_type_t *)ty);
  switch (t->kind) {
  case TY_ANY: return true;
  case TY_LIST: return ty_has_inference_failure(t->list.elem);
  case TY_HANDLE: return ty_has_inference_failure(t->handle.inner);
  case TY_FUN:
    return ty_has_inference_failure(t->fun.ret);
  case TY_UNION:
    for (int i = 0; i < t->onion.count; i++)
      if (ty_has_inference_failure(t->onion.members[i])) return true;
    return false;
  case TY_NAMED:
    for (int i = 0; i < t->named.param_count; i++)
      if (ty_has_inference_failure(t->named.params[i])) return true;
    return false;
  case TY_PLIST:
    for (int i = 0; i < t->plist.count; i++)
      if (ty_has_inference_failure(t->plist.vals[i])) return true;
    return false;
  case TY_TUPLE:
    for (int i = 0; i < t->tuple.count; i++)
      if (ty_has_inference_failure(t->tuple.elems[i])) return true;
    return false;
  default: return false;
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
  if (re->kind == TY_ANY || ra->kind == TY_ANY) return false;
  if (ra->kind == TY_NEVER || re->kind == TY_NEVER) return true;
  if (re->kind == TY_VAR || ra->kind == TY_VAR) return true;
  if (ty_equal(re, ra)) return true;

  if (re->kind == TY_SYM && ra->kind == TY_KW) return true;
  if (re->kind == TY_KW && ra->kind == TY_SYM) return true;
  if (re->kind == TY_KW && ra->kind == TY_KW) {
    if (!re->kw.tag || !ra->kw.tag) return true;
    return strcmp(re->kw.tag, ra->kw.tag) == 0;
  }

  if (re->kind == TY_LIST && ra->kind == TY_NIL) return true;
  if (re->kind == TY_NIL && ra->kind == TY_LIST) return true;
  if (re->kind == TY_LIST && ra->kind == TY_PLIST) return true;
  if (re->kind == TY_PLIST && ra->kind == TY_LIST) return true;
  if (re->kind == TY_LIST && ra->kind == TY_TUPLE) return true;
  if (re->kind == TY_TUPLE && ra->kind == TY_LIST) return true;

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

  if (re->kind == TY_NAMED && ra->kind == TY_NAMED) {
    if (strcmp(re->named.name, ra->named.name) != 0) return false;
    int n = re->named.param_count < ra->named.param_count ?
            re->named.param_count : ra->named.param_count;
    for (int i = 0; i < n; i++)
      if (!ty_compatible(re->named.params[i], ra->named.params[i])) return false;
    return true;
  }

  if (re->kind == TY_PLIST && ra->kind == TY_PLIST) {
    if (re->plist.count != ra->plist.count) return false;
    for (int i = 0; i < re->plist.count; i++) {
      if (strcmp(re->plist.keys[i], ra->plist.keys[i]) != 0) return false;
      if (!ty_compatible(re->plist.vals[i], ra->plist.vals[i])) return false;
    }
    return true;
  }

  if (re->kind == TY_TUPLE && ra->kind == TY_TUPLE) {
    if (re->tuple.count != ra->tuple.count) return false;
    for (int i = 0; i < re->tuple.count; i++)
      if (!ty_compatible(re->tuple.elems[i], ra->tuple.elems[i])) return false;
    return true;
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
    valk_type_t *f = ty_fun(a, params, ty->fun.param_count, ret, ty->fun.variadic);
    for (int i = 0; i < f->fun.param_count; i++)
      f->fun.param_names[i] = ty->fun.param_names[i];
    return f;
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

  case TY_NAMED: {
    bool changed = false;
    valk_type_t *params[TY_MAX_PARAMS];
    for (int i = 0; i < ty->named.param_count; i++) {
      params[i] = instantiate_rec(a, ty->named.params[i], old_ids, new_vars, n);
      if (params[i] != ty->named.params[i]) changed = true;
    }
    if (!changed) return ty;
    return ty_named(a, ty->named.name, params, ty->named.param_count);
  }

  case TY_PLIST: {
    bool changed = false;
    valk_type_t *vals[TY_MAX_PARAMS];
    for (int i = 0; i < ty->plist.count; i++) {
      vals[i] = instantiate_rec(a, ty->plist.vals[i], old_ids, new_vars, n);
      if (vals[i] != ty->plist.vals[i]) changed = true;
    }
    if (!changed) return ty;
    return ty_plist(a, (const char **)ty->plist.keys, vals, ty->plist.count);
  }

  case TY_TUPLE: {
    bool changed = false;
    valk_type_t *elems[TY_MAX_PARAMS];
    for (int i = 0; i < ty->tuple.count; i++) {
      elems[i] = instantiate_rec(a, ty->tuple.elems[i], old_ids, new_vars, n);
      if (elems[i] != ty->tuple.elems[i]) changed = true;
    }
    if (!changed) return ty;
    return ty_tuple(a, elems, ty->tuple.count);
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
  case TY_NAMED:
    for (int i = 0; i < ty->named.param_count; i++)
      collect_free_vars(ty->named.params[i], floor, ids, count, max);
    return;
  case TY_PLIST:
    for (int i = 0; i < ty->plist.count; i++)
      collect_free_vars(ty->plist.vals[i], floor, ids, count, max);
    return;
  case TY_TUPLE:
    for (int i = 0; i < ty->tuple.count; i++)
      collect_free_vars(ty->tuple.elems[i], floor, ids, count, max);
    return;
  default: return;
  }
}

type_scheme_t *scheme_generalize(type_arena_t *a, valk_type_t *ty, int floor_var_id) {
  int ids[SCHEME_MAX_VARS];
  int count = 0;
  collect_free_vars(ty, floor_var_id, ids, &count, SCHEME_MAX_VARS);
  if (count == 0) return scheme_mono(a, ty);

  valk_type_t *fresh[SCHEME_MAX_VARS];
  int fresh_ids[SCHEME_MAX_VARS];
  for (int i = 0; i < count; i++) {
    fresh[i] = ty_var(a);
    fresh_ids[i] = fresh[i]->var.id;
  }
  valk_type_t *frozen = instantiate_rec(a, ty, ids, fresh, count);
  return scheme_poly(a, fresh_ids, count, frozen);
}


