#include "lsp_types.h"
#include "lsp_doc.h"
#include "../parser.h"

#include <string.h>

valk_type_t *ann_var(ann_var_map_t *m, const char *name) {
  for (int i = 0; i < m->count; i++)
    if (strcmp(m->names[i], name) == 0) return m->vars[i];
  if (m->count >= ANN_MAX_VARS) return ty_var(m->arena);
  m->names[m->count] = (char *)name;
  m->vars[m->count] = ty_var(m->arena);
  return m->vars[m->count++];
}

valk_type_t *parse_type_ann(ann_var_map_t *m, valk_lval_t *node) {
  if (!node) return ty_any(m->arena);
  type_arena_t *a = m->arena;

  if (LVAL_TYPE(node) == LVAL_SYM) {
    const char *s = node->str;
    if (strcmp(s, "Num") == 0) return ty_num(a);
    if (strcmp(s, "Str") == 0) return ty_str(a);
    if (strcmp(s, "Sym") == 0) return ty_sym(a);
    if (strcmp(s, "Nil") == 0) return ty_nil(a);
    if (strcmp(s, "Err") == 0) return ty_err(a);
    if (strcmp(s, "Any") == 0 || strcmp(s, "??") == 0) return ty_any(a);
    if (strcmp(s, "Never") == 0) return ty_never(a);
    return ann_var(m, s);
  }

  if (LVAL_TYPE(node) == LVAL_CONS) {
    valk_lval_t *h = valk_lval_head(node);
    if (!h || LVAL_TYPE(h) != LVAL_SYM) return ty_any(a);
    const char *name = h->str;
    valk_lval_t *args = valk_lval_tail(node);

    if (strcmp(name, "->") == 0) {
      valk_type_t *pts[TY_MAX_PARAMS];
      int pc = 0;
      bool variadic = false;
      valk_lval_t *cur = args;
      while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        valk_lval_t *elem = valk_lval_head(cur);
        if (is_ann_sym(elem, "&")) {
          variadic = true;
          cur = valk_lval_tail(cur);
          continue;
        }
        if (pc < TY_MAX_PARAMS)
          pts[pc++] = parse_type_ann(m, elem);
        cur = valk_lval_tail(cur);
      }
      if (pc == 0) return ty_any(a);
      valk_type_t *ret = pts[pc - 1];
      return ty_fun(a, pts, pc - 1, ret, variadic);
    }

    if (strcmp(name, "List") == 0) {
      valk_lval_t *elem = args && LVAL_TYPE(args) == LVAL_CONS
        ? valk_lval_head(args) : nullptr;
      return ty_list(a, elem ? parse_type_ann(m, elem) : ty_var(a));
    }

    if (strcmp(name, "PList") == 0) {
      const char *keys[TY_MAX_PARAMS];
      valk_type_t *vals[TY_MAX_PARAMS];
      int n = 0;
      valk_lval_t *cur = args;
      while (cur && LVAL_TYPE(cur) == LVAL_CONS && n < TY_MAX_PARAMS) {
        valk_lval_t *key = valk_lval_head(cur);
        cur = valk_lval_tail(cur);
        if (!cur || LVAL_TYPE(cur) != LVAL_CONS) break;
        valk_lval_t *val = valk_lval_head(cur);
        cur = valk_lval_tail(cur);
        if (key && LVAL_TYPE(key) == LVAL_SYM && key->str[0] == ':')
          keys[n] = key->str + 1;
        else if (key && LVAL_TYPE(key) == LVAL_SYM)
          keys[n] = key->str;
        else
          continue;
        vals[n] = parse_type_ann(m, val);
        n++;
      }
      return ty_plist(a, keys, vals, n);
    }

    if (strcmp(name, "Handle") == 0) {
      valk_lval_t *inner = args && LVAL_TYPE(args) == LVAL_CONS
        ? valk_lval_head(args) : nullptr;
      return ty_handle(a, inner ? parse_type_ann(m, inner) : ty_var(a));
    }

    if (strcmp(name, "Ref") == 0) {
      valk_lval_t *tag = args && LVAL_TYPE(args) == LVAL_CONS
        ? valk_lval_head(args) : nullptr;
      const char *tag_str = (tag && LVAL_TYPE(tag) == LVAL_SYM)
        ? type_arena_strdup(a, tag->str) : nullptr;
      return ty_ref(a, tag_str);
    }

    valk_type_t *tps[TY_MAX_PARAMS];
    int tc = 0;
    valk_lval_t *cur = args;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS && tc < TY_MAX_PARAMS) {
      tps[tc++] = parse_type_ann(m, valk_lval_head(cur));
      cur = valk_lval_tail(cur);
    }
    return ty_named(a, name, tps, tc);
  }

  return ty_any(a);
}

bool is_ann_sym(valk_lval_t *node, const char *s) {
  return node && LVAL_TYPE(node) == LVAL_SYM && strcmp(node->str, s) == 0;
}

void parse_formals(infer_ctx_t *ctx, valk_lval_t *formals,
                   typed_scope_t *inner, parsed_formals_t *out) {
  out->param_count = 0;
  out->variadic = false;
  out->ret_ann = nullptr;

  ann_var_map_t avm = {.count = 0, .arena = ctx->arena};
  valk_lval_t *cur = formals;

  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *h = valk_lval_head(cur);

    if (is_ann_sym(h, "->")) {
      cur = valk_lval_tail(cur);
      if (cur && LVAL_TYPE(cur) == LVAL_CONS)  {
        out->ret_ann = parse_type_ann(&avm, valk_lval_head(cur));
        cur = valk_lval_tail(cur);
      }
      continue;
    }

    if (is_ann_sym(h, "::")) {
      cur = valk_lval_tail(cur);
      if (cur && LVAL_TYPE(cur) == LVAL_CONS && out->param_count > 0) {
        valk_type_t *ann = parse_type_ann(&avm, valk_lval_head(cur));
        ty_unify(ctx->arena, out->param_types[out->param_count - 1], ann);
        cur = valk_lval_tail(cur);
      }
      continue;
    }

    if (h && LVAL_TYPE(h) == LVAL_SYM) {
      if (h->str[0] == '&') {
        out->variadic = true;
      } else {
        valk_type_t *pt = ty_var(ctx->arena);
        if (out->param_count < TY_MAX_PARAMS) {
          out->param_types[out->param_count] = pt;
          out->param_nodes[out->param_count] = h;
          out->param_count++;
        }
        typed_scope_add_mono(inner, h->str, pt);
      }
    }

    cur = valk_lval_tail(cur);
  }
}
