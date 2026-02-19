#include "lsp_types.h"
#include "lsp_doc.h"
#include "../parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
// Inlay hint collection
// ---------------------------------------------------------------------------

static void add_hint(infer_ctx_t *ctx, int offset, inlay_hint_kind_e kind,
                     valk_type_t *ty, bool is_return) {
  if (!ctx->collect_hints || offset < 0 || !ty) return;
  if (ctx->hint_count >= ctx->hint_cap) {
    ctx->hint_cap = ctx->hint_cap == 0 ? 32 : ctx->hint_cap * 2;
    ctx->hints = realloc(ctx->hints, sizeof(lsp_inlay_hint_t) * ctx->hint_cap);
  }
  ctx->hints[ctx->hint_count++] = (lsp_inlay_hint_t){
    .offset = offset,
    .kind = kind,
    .label = nullptr,
    .type = ty,
    .is_return = is_return,
  };
}

static void emit_type_hint(infer_ctx_t *ctx, valk_lval_t *node, valk_type_t *ty) {
  if (!ctx->collect_hints || !node || !ty) return;
  int pos = node->src_pos;
  if (pos < 0) return;
  int end = pos + (int)strlen(node->str);
  add_hint(ctx, end, INLAY_TYPE, ty, false);
}

static void emit_return_hint(infer_ctx_t *ctx, int offset, valk_type_t *ty) {
  add_hint(ctx, offset, INLAY_TYPE, ty, true);
}

static void emit_param_hint(infer_ctx_t *ctx, valk_lval_t *arg_node,
                            const char *param_name) {
  if (!ctx->collect_hints || !arg_node || !param_name) return;
  int pos = arg_node->src_pos;
  if (pos < 0) return;
  if (ctx->hint_count >= ctx->hint_cap) {
    ctx->hint_cap = ctx->hint_cap == 0 ? 32 : ctx->hint_cap * 2;
    ctx->hints = realloc(ctx->hints, sizeof(lsp_inlay_hint_t) * ctx->hint_cap);
  }
  ctx->hints[ctx->hint_count++] = (lsp_inlay_hint_t){
    .offset = pos,
    .kind = INLAY_PARAM,
    .label = strdup(param_name),
    .type = nullptr,
    .is_return = false,
  };
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

int infer_count_list(valk_lval_t *rest) {
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
  int count = 0;
  valk_lval_t *cur = expr;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) { count++; cur = valk_lval_tail(cur); }
  if (count == 0) return ty_nil(ctx->arena);

  bool is_plist = (count >= 2 && count % 2 == 0);
  if (is_plist) {
    cur = expr;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      valk_lval_t *key = valk_lval_head(cur);
      if (!key || LVAL_TYPE(key) != LVAL_SYM || key->str[0] != ':') {
        is_plist = false;
        break;
      }
      cur = valk_lval_tail(cur);
      if (cur) cur = valk_lval_tail(cur);
    }
  }

  if (is_plist) {
    const char *keys[TY_MAX_PARAMS];
    valk_type_t *vals[TY_MAX_PARAMS];
    int n = 0;
    cur = expr;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS && n < TY_MAX_PARAMS) {
      valk_lval_t *key = valk_lval_head(cur);
      cur = valk_lval_tail(cur);
      valk_lval_t *val = valk_lval_head(cur);
      cur = valk_lval_tail(cur);
      keys[n] = key->str + 1;
      vals[n] = infer_expr(ctx, val);
      n++;
    }

    for (int ri = 0; ri < ctx->plist_type_count; ri++) {
      plist_type_reg_t *reg = &ctx->plist_types[ri];
      if (reg->key_count > n) continue;
      bool match = true;
      for (int ki = 0; ki < reg->key_count && match; ki++) {
        bool found = false;
        for (int pi = 0; pi < n; pi++)
          if (strcmp(reg->keys[ki], keys[pi]) == 0) { found = true; break; }
        if (!found) match = false;
      }
      if (match) {
        valk_type_t *fn = ty_resolve(scheme_instantiate(ctx->arena, reg->ctor_scheme));
        if (fn->kind == TY_FUN) {
          for (int ki = 0; ki < reg->key_count; ki++) {
            for (int pi = 0; pi < n; pi++) {
              if (strcmp(reg->keys[ki], keys[pi]) == 0 &&
                  ki < fn->fun.param_count) {
                ty_unify(ctx->arena, fn->fun.params[ki], vals[pi]);
                break;
              }
            }
          }
          return ty_resolve(fn->fun.ret);
        }
        if (fn->kind == TY_NAMED) return fn;
      }
    }

    return ty_plist(ctx->arena, keys, vals, n);
  }

  valk_type_t *elem_types[TY_MAX_PARAMS];
  int elem_count = 0;
  bool homogeneous = true;
  cur = expr;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_type_t *et = infer_expr(ctx, valk_lval_head(cur));
    et = ty_resolve(et);
    if (elem_count < TY_MAX_PARAMS)
      elem_types[elem_count] = et;
    if (elem_count > 0 && homogeneous && !ty_equal(elem_types[0], et))
      homogeneous = false;
    elem_count++;
    cur = valk_lval_tail(cur);
  }
  if (homogeneous && elem_count > 0)
    return ty_list(ctx->arena, elem_types[0]);
  return ty_qexpr(ctx->arena);
}

// ---------------------------------------------------------------------------
// Check if name is a type predicate and return the narrowed type.
// Annotation parsing and formals in lsp_infer_ann.c

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
    if (expr->str[0] == ':' && expr->str[1] != '\0')
      return ty_kw(ctx->arena, expr->str + 1);
    if (expr->str[0] == ':') return ty_sym(ctx->arena);
    if (strcmp(expr->str, "true") == 0 || strcmp(expr->str, "false") == 0)
      return ty_num(ctx->arena);
    if (strcmp(expr->str, "nil") == 0)
      return ty_nil(ctx->arena);
    if (strcmp(expr->str, "otherwise") == 0)
      return ty_num(ctx->arena);

    type_scheme_t *sch = typed_scope_lookup(ctx->scope, expr->str);
    if (sch) {
      valk_type_t *resolved = scheme_instantiate(ctx->arena, sch);
      if (ctx->hover_offset >= 0 && expr->src_pos >= 0 &&
          expr->src_pos <= ctx->hover_offset &&
          ctx->hover_offset < expr->src_pos + (int)strlen(expr->str))
        ctx->hover_result = ty_resolve(resolved);
      return resolved;
    }

    return ty_var(ctx->arena);
  }

  case LVAL_FUN: return ty_fun(ctx->arena, nullptr, 0, ty_var(ctx->arena), false);

  case LVAL_CONS: break;
  default: return ty_var(ctx->arena);
  }

  if (expr->flags & LVAL_FLAG_QUOTED)
    return infer_qexpr(ctx, expr);

  valk_lval_t *head = valk_lval_head(expr);
  valk_lval_t *rest = valk_lval_tail(expr);
  if (!head) return ty_nil(ctx->arena);

  if (LVAL_TYPE(head) != LVAL_SYM) {
    valk_type_t *last = infer_expr(ctx, head);
    valk_lval_t *cur = rest;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      last = infer_eval(ctx, valk_lval_head(cur));
      cur = valk_lval_tail(cur);
    }
    return last;
  }

  const char *name = head->str;

  // --- Special forms ---

  if (strcmp(name, "\\") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_fun(ctx->arena, nullptr, 0, ty_var(ctx->arena), false);
    valk_lval_t *formals = valk_lval_head(rest);
    valk_lval_t *body_rest = valk_lval_tail(rest);

    typed_scope_t *inner = typed_scope_push(ctx->arena, ctx->scope);
    parsed_formals_t pf;

    if (formals && LVAL_TYPE(formals) == LVAL_CONS)
      parse_formals(ctx, formals, inner, &pf);
    else
      pf = (parsed_formals_t){.param_count = 0, .variadic = false, .ret_ann = nullptr};

    typed_scope_t *saved = ctx->scope;
    ctx->scope = inner;
    valk_type_t *body_ty = infer_body_last(ctx, body_rest);
    ctx->scope = saved;

    if (pf.ret_ann)
      ty_unify(ctx->arena, body_ty, pf.ret_ann);

    for (int i = 0; i < pf.param_count; i++) {
      valk_lval_t *h = pf.param_nodes[i];
      if (ctx->hover_offset >= 0 && h->src_pos >= 0 &&
          h->src_pos <= ctx->hover_offset &&
          ctx->hover_offset < h->src_pos + (int)strlen(h->str))
        ctx->hover_result = ty_resolve(pf.param_types[i]);
      emit_type_hint(ctx, h, pf.param_types[i]);
    }

    typed_scope_pop(inner);

    valk_type_t *fn = ty_fun(ctx->arena, pf.param_types, pf.param_count, body_ty, pf.variadic);
    for (int i = 0; i < pf.param_count; i++)
      fn->fun.param_names[i] = pf.param_nodes[i] ? pf.param_nodes[i]->str : nullptr;
    return fn;
  }

  if (strcmp(name, "fun") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_fun(ctx->arena, nullptr, 0, ty_var(ctx->arena), false);
    valk_lval_t *name_formals = valk_lval_head(rest);
    valk_lval_t *body_rest = valk_lval_tail(rest);

    if (name_formals && LVAL_TYPE(name_formals) == LVAL_CONS) {
      valk_lval_t *fname = valk_lval_head(name_formals);
      typed_scope_t *inner = typed_scope_push(ctx->arena, ctx->scope);
      parsed_formals_t pf;

      valk_lval_t *params = valk_lval_tail(name_formals);
      if (params && LVAL_TYPE(params) == LVAL_CONS)
        parse_formals(ctx, params, inner, &pf);
      else
        pf = (parsed_formals_t){.param_count = 0, .variadic = false, .ret_ann = nullptr};

      typed_scope_t *saved = ctx->scope;
      ctx->scope = inner;
      valk_type_t *body_ty = infer_body_last(ctx, body_rest);
      ctx->scope = saved;

      if (pf.ret_ann)
        ty_unify(ctx->arena, body_ty, pf.ret_ann);

      type_scheme_t *builtin_sch = fname && LVAL_TYPE(fname) == LVAL_SYM
        ? typed_scope_lookup(ctx->scope, fname->str) : nullptr;
      valk_type_t *builtin_fn = nullptr;
      if (builtin_sch) {
        builtin_fn = ty_resolve(scheme_instantiate(ctx->arena, builtin_sch));
        if (!builtin_fn || builtin_fn->kind != TY_FUN)
          builtin_fn = nullptr;
      }

      for (int i = 0; i < pf.param_count; i++) {
        valk_lval_t *h = pf.param_nodes[i];
        valk_type_t *local_ty = ty_resolve(pf.param_types[i]);
        valk_type_t *hint_ty = pf.param_types[i];
        if (local_ty->kind == TY_VAR && builtin_fn &&
            i < builtin_fn->fun.param_count)
          hint_ty = builtin_fn->fun.params[i];
        if (ctx->hover_offset >= 0 && h->src_pos >= 0 &&
            h->src_pos <= ctx->hover_offset &&
            ctx->hover_offset < h->src_pos + (int)strlen(h->str))
          ctx->hover_result = ty_resolve(hint_ty);
        emit_type_hint(ctx, h, hint_ty);
      }

      typed_scope_pop(inner);

      valk_type_t *fn_ty = ty_fun(ctx->arena, pf.param_types, pf.param_count, body_ty, pf.variadic);
      for (int i = 0; i < pf.param_count; i++)
        fn_ty->fun.param_names[i] = pf.param_nodes[i] ? pf.param_nodes[i]->str : nullptr;
      if (fname && LVAL_TYPE(fname) == LVAL_SYM) {
        int floor = ctx->floor_var_id;
        type_scheme_t *sch = scheme_generalize(ctx->arena, fn_ty, floor);
        bool has_failure = ty_has_inference_failure(ty_resolve(fn_ty));
        type_scheme_t *existing = has_failure ? typed_scope_lookup(ctx->scope, fname->str) : nullptr;
        if (!existing)
          typed_scope_add(ctx->scope, fname->str, sch);
        if (ctx->hover_offset >= 0 && fname->src_pos >= 0 &&
            fname->src_pos <= ctx->hover_offset &&
            ctx->hover_offset < fname->src_pos + (int)strlen(fname->str))
          ctx->hover_result = ty_resolve(existing ? scheme_instantiate(ctx->arena, existing) : fn_ty);
        emit_return_hint(ctx, fname->src_pos + (int)strlen(fname->str), body_ty);
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
          bool is_lambda = v && LVAL_TYPE(v) == LVAL_CONS && !(v->flags & LVAL_FLAG_QUOTED) &&
            valk_lval_head(v) && LVAL_TYPE(valk_lval_head(v)) == LVAL_SYM &&
            strcmp(valk_lval_head(v)->str, "\\") == 0;
          valk_type_t *self_ret = nullptr;
          if (is_lambda) {
            valk_lval_t *lam_rest = valk_lval_tail(v);
            valk_lval_t *formals_node = lam_rest ? valk_lval_head(lam_rest) : nullptr;
            int arity = 0;
            if (formals_node && LVAL_TYPE(formals_node) == LVAL_CONS) {
              valk_lval_t *fc = formals_node;
              while (fc && LVAL_TYPE(fc) == LVAL_CONS) {
                valk_lval_t *p = valk_lval_head(fc);
                if (p && LVAL_TYPE(p) == LVAL_SYM && strcmp(p->str, "&") == 0) break;
                arity++;
                fc = valk_lval_tail(fc);
              }
            }
            valk_type_t *param_vars[TY_MAX_PARAMS];
            for (int j = 0; j < arity && j < TY_MAX_PARAMS; j++)
              param_vars[j] = ty_var(ctx->arena);
            self_ret = ty_var(ctx->arena);
            valk_type_t *self_fn = ty_fun(ctx->arena, param_vars,
              arity < TY_MAX_PARAMS ? arity : TY_MAX_PARAMS, self_ret, false);
            typed_scope_add_mono(ctx->scope, s->str, self_fn);
          }
          valk_type_t *vt = infer_expr(ctx, v);
          if (self_ret)
            ty_unify(ctx->arena, self_ret, ty_resolve(vt)->kind == TY_FUN ? ty_resolve(vt)->fun.ret : vt);
          type_scheme_t *sch = scheme_generalize(ctx->arena, vt, floor);
          typed_scope_add(ctx->scope, s->str, sch);
          if (ctx->hover_offset >= 0 && s->src_pos >= 0 &&
              s->src_pos <= ctx->hover_offset &&
              ctx->hover_offset < s->src_pos + (int)strlen(s->str))
            ctx->hover_result = ty_resolve(vt);
          emit_type_hint(ctx, s, vt);
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
      if (ctx->hover_offset >= 0 && binding->src_pos >= 0 &&
          binding->src_pos <= ctx->hover_offset &&
          ctx->hover_offset < binding->src_pos + (int)strlen(binding->str))
        ctx->hover_result = ty_resolve(vt);
      emit_type_hint(ctx, binding, vt);
    }
    return ty_nil(ctx->arena);
  }

  if (strcmp(name, "let") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_var(ctx->arena);
    valk_lval_t *body = valk_lval_head(rest);
    typed_scope_t *inner = typed_scope_push(ctx->arena, ctx->scope);
    typed_scope_t *saved = ctx->scope;
    ctx->scope = inner;
    valk_type_t *result = infer_eval(ctx, body);
    ctx->scope = saved;
    typed_scope_pop(inner);
    return result;
  }

  if (strcmp(name, "sig") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_nil(ctx->arena);
    valk_lval_t *name_q = valk_lval_head(rest);
    valk_lval_t *type_rest = valk_lval_tail(rest);
    valk_lval_t *sig_name = (name_q && LVAL_TYPE(name_q) == LVAL_CONS)
      ? valk_lval_head(name_q) : name_q;
    if (!sig_name || LVAL_TYPE(sig_name) != LVAL_SYM) return ty_nil(ctx->arena);
    if (LVAL_TYPE(type_rest) != LVAL_CONS) return ty_nil(ctx->arena);
    valk_lval_t *type_q = valk_lval_head(type_rest);
    valk_lval_t *type_expr = type_q;
    if (type_q && LVAL_TYPE(type_q) == LVAL_CONS) {
      valk_lval_t *inner = valk_lval_head(type_q);
      if (inner && LVAL_TYPE(inner) == LVAL_CONS)
        type_expr = inner;
    }

    ann_var_map_t avm = {.count = 0, .arena = ctx->arena};
    valk_type_t *ty = parse_type_ann(&avm, type_expr);

    int var_ids[SCHEME_MAX_VARS];
    int vc = avm.count < SCHEME_MAX_VARS ? avm.count : SCHEME_MAX_VARS;
    for (int i = 0; i < vc; i++)
      var_ids[i] = avm.vars[i]->var.id;

    type_scheme_t *sch = vc > 0
      ? scheme_poly(ctx->arena, var_ids, vc, ty)
      : scheme_mono(ctx->arena, ty);
    typed_scope_add(ctx->scope, sig_name->str, sch);
    return ty_nil(ctx->arena);
  }

  if (strcmp(name, "aio/let") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS)
      return ty_handle(ctx->arena, ty_var(ctx->arena));
    valk_lval_t *bindings = valk_lval_head(rest);
    valk_lval_t *body_rest = valk_lval_tail(rest);

    typed_scope_t *inner = typed_scope_push(ctx->arena, ctx->scope);
    typed_scope_t *saved = ctx->scope;
    ctx->scope = inner;

    if (bindings && LVAL_TYPE(bindings) == LVAL_CONS) {
      valk_lval_t *bc = bindings;
      if (bc->flags & LVAL_FLAG_QUOTED) {
        uint32_t sf = bc->flags;
        bc->flags &= ~LVAL_FLAG_QUOTED;
        valk_lval_t *inner_bc = bc;
        while (inner_bc && LVAL_TYPE(inner_bc) == LVAL_CONS) {
          valk_lval_t *pair = valk_lval_head(inner_bc);
          if (pair && LVAL_TYPE(pair) == LVAL_CONS) {
            valk_lval_t *bname = valk_lval_head(pair);
            valk_lval_t *bexpr_rest = valk_lval_tail(pair);
            if (bname && LVAL_TYPE(bname) == LVAL_SYM &&
                bexpr_rest && LVAL_TYPE(bexpr_rest) == LVAL_CONS) {
              valk_type_t *ht = infer_expr(ctx, valk_lval_head(bexpr_rest));
              ht = ty_resolve(ht);
              valk_type_t *val_ty = (ht->kind == TY_HANDLE)
                ? ht->handle.inner : ty_var(ctx->arena);
              typed_scope_add_mono(inner, bname->str, val_ty);
              emit_type_hint(ctx, bname, val_ty);
            }
          } else if (pair && LVAL_TYPE(pair) == LVAL_SYM &&
                     strcmp(pair->str, ":then") == 0) {
          }
          inner_bc = valk_lval_tail(inner_bc);
        }
        bc->flags = sf;
      } else {
        while (bc && LVAL_TYPE(bc) == LVAL_CONS) {
          valk_lval_t *pair = valk_lval_head(bc);
          if (pair && LVAL_TYPE(pair) == LVAL_CONS) {
            valk_lval_t *bname = valk_lval_head(pair);
            valk_lval_t *bexpr_rest = valk_lval_tail(pair);
            if (bname && LVAL_TYPE(bname) == LVAL_SYM &&
                bexpr_rest && LVAL_TYPE(bexpr_rest) == LVAL_CONS) {
              valk_type_t *ht = infer_expr(ctx, valk_lval_head(bexpr_rest));
              ht = ty_resolve(ht);
              valk_type_t *val_ty = (ht->kind == TY_HANDLE)
                ? ht->handle.inner : ty_var(ctx->arena);
              typed_scope_add_mono(inner, bname->str, val_ty);
              emit_type_hint(ctx, bname, val_ty);
            }
          } else if (pair && LVAL_TYPE(pair) == LVAL_SYM &&
                     strcmp(pair->str, ":then") == 0) {
          }
          bc = valk_lval_tail(bc);
        }
      }
    }

    valk_type_t *body_ty = ty_nil(ctx->arena);
    while (body_rest && LVAL_TYPE(body_rest) == LVAL_CONS) {
      body_ty = infer_expr(ctx, valk_lval_head(body_rest));
      body_rest = valk_lval_tail(body_rest);
    }
    ctx->scope = saved;
    typed_scope_pop(inner);
    return ty_handle(ctx->arena, body_ty);
  }

  if (strcmp(name, "aio/do") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS)
      return ty_handle(ctx->arena, ty_var(ctx->arena));
    valk_lval_t *body = valk_lval_head(rest);
    if (!body || LVAL_TYPE(body) != LVAL_CONS)
      return ty_handle(ctx->arena, ty_var(ctx->arena));

    typed_scope_t *inner = typed_scope_push(ctx->arena, ctx->scope);
    typed_scope_t *saved = ctx->scope;
    ctx->scope = inner;

    uint32_t sf = body->flags;
    if (body->flags & LVAL_FLAG_QUOTED)
      body->flags &= ~LVAL_FLAG_QUOTED;

    valk_type_t *last_ty = ty_nil(ctx->arena);
    valk_lval_t *cur = body;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      valk_lval_t *stmt = valk_lval_head(cur);
      if (stmt && LVAL_TYPE(stmt) == LVAL_CONS) {
        valk_lval_t *sh = valk_lval_head(stmt);
        valk_lval_t *st = valk_lval_tail(stmt);
        if (sh && LVAL_TYPE(sh) == LVAL_SYM &&
            strcmp(sh->str, "<-") == 0 &&
            st && LVAL_TYPE(st) == LVAL_CONS) {
          valk_lval_t *var = valk_lval_head(st);
          valk_lval_t *expr_rest = valk_lval_tail(st);
          if (var && LVAL_TYPE(var) == LVAL_SYM &&
              expr_rest && LVAL_TYPE(expr_rest) == LVAL_CONS) {
            valk_type_t *ht = infer_expr(ctx, valk_lval_head(expr_rest));
            ht = ty_resolve(ht);
            valk_type_t *val_ty = (ht->kind == TY_HANDLE)
              ? ht->handle.inner : ty_var(ctx->arena);
            if (strcmp(var->str, "_") != 0) {
              typed_scope_add_mono(inner, var->str, val_ty);
              emit_type_hint(ctx, var, val_ty);
            }
            last_ty = ht;
            cur = valk_lval_tail(cur);
            continue;
          }
        }
      }
      last_ty = infer_expr(ctx, stmt);
      cur = valk_lval_tail(cur);
    }

    body->flags = sf;
    ctx->scope = saved;
    typed_scope_pop(inner);

    last_ty = ty_resolve(last_ty);
    valk_type_t *inner_ty = (last_ty->kind == TY_HANDLE)
      ? last_ty->handle.inner : last_ty;
    return ty_handle(ctx->arena, inner_ty);
  }

  // --- type declaration: register constructor functions ---
  // (type {Option a} {None} {Some :value a})
  // (type {Option a} {Some a} {None})  -- positional style
  if (strcmp(name, "type") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_nil(ctx->arena);
    valk_lval_t *name_qexpr = valk_lval_head(rest);
    if (!name_qexpr || LVAL_TYPE(name_qexpr) != LVAL_CONS) return ty_nil(ctx->arena);

    valk_lval_t *type_name_node = valk_lval_head(name_qexpr);
    const char *type_name = (type_name_node && LVAL_TYPE(type_name_node) == LVAL_SYM)
      ? type_name_node->str : "?";

    int type_floor = ctx->arena->next_var_id;
    valk_type_t *param_vars[TY_MAX_PARAMS];
    int param_count = 0;
    char *param_names[TY_MAX_PARAMS];
    valk_lval_t *p = valk_lval_tail(name_qexpr);
    while (p && LVAL_TYPE(p) == LVAL_CONS && param_count < TY_MAX_PARAMS) {
      valk_lval_t *ps = valk_lval_head(p);
      if (ps && LVAL_TYPE(ps) == LVAL_SYM) {
        param_vars[param_count] = ty_var(ctx->arena);
        param_names[param_count] = ps->str;
        param_count++;
      }
      p = valk_lval_tail(p);
    }

    // Auto-discover type params from constructor fields
    // (type {Option} {Some :value a} {None}) — 'a' is implicit param
    // (type {Pair} {:fst a :snd b}) — nameless keyword variant
    valk_lval_t *vt = valk_lval_tail(rest);
    while (vt && LVAL_TYPE(vt) == LVAL_CONS && param_count < TY_MAX_PARAMS) {
      valk_lval_t *variant = valk_lval_head(vt);
      if (variant && LVAL_TYPE(variant) == LVAL_CONS) {
        valk_lval_t *fe = valk_lval_head(variant);
        bool nameless = fe && LVAL_TYPE(fe) == LVAL_SYM && fe->str[0] == ':';
        valk_lval_t *fields = nameless ? variant : valk_lval_tail(variant);
        valk_lval_t *first_fld = (fields && LVAL_TYPE(fields) == LVAL_CONS)
          ? valk_lval_head(fields) : nullptr;
        bool kw = first_fld && LVAL_TYPE(first_fld) == LVAL_SYM
          && first_fld->str[0] == ':';
        valk_lval_t *fc = fields;
        while (fc && LVAL_TYPE(fc) == LVAL_CONS && param_count < TY_MAX_PARAMS) {
          if (kw) { fc = valk_lval_tail(fc); if (!fc || LVAL_TYPE(fc) != LVAL_CONS) break; }
          valk_lval_t *ts = valk_lval_head(fc);
          fc = valk_lval_tail(fc);
          if (ts && LVAL_TYPE(ts) == LVAL_SYM && ts->str[0] != ':' &&
              ts->str[0] >= 'a' && ts->str[0] <= 'z') {
            bool found = false;
            for (int i = 0; i < param_count; i++)
              if (strcmp(param_names[i], ts->str) == 0) { found = true; break; }
            if (!found) {
              param_vars[param_count] = ty_var(ctx->arena);
              param_names[param_count] = ts->str;
              param_count++;
            }
          }
        }
      }
      vt = valk_lval_tail(vt);
    }

    valk_type_t *result_ty = ty_named(ctx->arena, type_name,
                                       param_vars, param_count);

    valk_lval_t *variants = valk_lval_tail(rest);
    while (variants && LVAL_TYPE(variants) == LVAL_CONS) {
      valk_lval_t *variant = valk_lval_head(variants);
      if (variant && LVAL_TYPE(variant) == LVAL_CONS &&
          (variant->flags & LVAL_FLAG_QUOTED)) {
        valk_lval_t *first_elem = valk_lval_head(variant);
        bool nameless_kw = first_elem && LVAL_TYPE(first_elem) == LVAL_SYM
          && first_elem->str[0] == ':';

        const char *ctor_name = nameless_kw ? type_name : nullptr;
        valk_lval_t *fields = nameless_kw ? variant : valk_lval_tail(variant);

        if (!nameless_kw && first_elem && LVAL_TYPE(first_elem) == LVAL_SYM)
          ctor_name = first_elem->str;

        if (ctor_name) {
          int field_count = 0;
          valk_type_t *field_types[TY_MAX_PARAMS];

          valk_lval_t *first_field = (fields && LVAL_TYPE(fields) == LVAL_CONS)
            ? valk_lval_head(fields) : nullptr;
          bool keyword_style = first_field && LVAL_TYPE(first_field) == LVAL_SYM
            && first_field->str[0] == ':';

          const char *field_keys[TY_MAX_PARAMS];
          valk_lval_t *fc = fields;

#define RESOLVE_FIELD_TYPE(sym_str) ({                          \
  valk_type_t *_ft = NULL;                                     \
  for (int _i = 0; _i < param_count; _i++) {                  \
    if (strcmp((sym_str), param_names[_i]) == 0)                \
      { _ft = param_vars[_i]; break; }                         \
  }                                                            \
  if (!_ft) {                                                  \
    if (strcmp((sym_str), "Num") == 0) _ft = ty_num(ctx->arena);\
    else if (strcmp((sym_str), "Str") == 0) _ft = ty_str(ctx->arena);\
    else if (strcmp((sym_str), "Sym") == 0) _ft = ty_sym(ctx->arena);\
    else if (strcmp((sym_str), "Nil") == 0) _ft = ty_nil(ctx->arena);\
    else if (strcmp((sym_str), "Err") == 0) _ft = ty_err(ctx->arena);\
    else _ft = ty_var(ctx->arena);                             \
  }                                                            \
  _ft;                                                         \
})

          if (keyword_style) {
            while (fc && LVAL_TYPE(fc) == LVAL_CONS && field_count < TY_MAX_PARAMS) {
              valk_lval_t *key = valk_lval_head(fc);
              fc = valk_lval_tail(fc);
              if (!fc || LVAL_TYPE(fc) != LVAL_CONS) break;
              valk_lval_t *type_sym = valk_lval_head(fc);
              fc = valk_lval_tail(fc);
              if (key && LVAL_TYPE(key) == LVAL_SYM && key->str[0] == ':' &&
                  type_sym && LVAL_TYPE(type_sym) == LVAL_SYM) {
                field_keys[field_count] = key->str + 1;
                field_types[field_count++] = RESOLVE_FIELD_TYPE(type_sym->str);
              }
            }
          } else {
            while (fc && LVAL_TYPE(fc) == LVAL_CONS && field_count < TY_MAX_PARAMS) {
              valk_lval_t *type_sym = valk_lval_head(fc);
              fc = valk_lval_tail(fc);
              if (type_sym && LVAL_TYPE(type_sym) == LVAL_SYM)
                field_types[field_count++] = RESOLVE_FIELD_TYPE(type_sym->str);
              else
                field_types[field_count++] = ty_var(ctx->arena);
            }
          }
#undef RESOLVE_FIELD_TYPE

          valk_type_t *ctor_ty;
          if (field_count == 0)
            ctor_ty = result_ty;
          else
            ctor_ty = ty_fun(ctx->arena, field_types, field_count,
                             result_ty, false);
          type_scheme_t *sch = scheme_generalize(ctx->arena, ctor_ty, type_floor);
          typed_scope_add(ctx->scope, ctor_name, sch);

          if (!nameless_kw) {
            char qname[256];
            snprintf(qname, sizeof(qname), "%s::%s", type_name, ctor_name);
            typed_scope_add(ctx->scope, qname, sch);
          }

          if (keyword_style && field_count > 0) {
            if (ctx->plist_type_count < MAX_PLIST_TYPES) {
              plist_type_reg_t *reg = &ctx->plist_types[ctx->plist_type_count++];
              reg->name = ctor_name;
              reg->key_count = field_count;
              reg->ctor_scheme = sch;
              for (int i = 0; i < field_count; i++)
                reg->keys[i] = field_keys[i];
            }
            for (int fi = 0; fi < field_count; fi++) {
              valk_type_t *acc_param = result_ty;
              valk_type_t *acc_fn = ty_fun(ctx->arena, &acc_param, 1,
                                           field_types[fi], false);
              type_scheme_t *acc_sch = scheme_generalize(ctx->arena, acc_fn, type_floor);
              char acc_name[256];
              snprintf(acc_name, sizeof(acc_name), "%s:%s", ctor_name, field_keys[fi]);
              typed_scope_add(ctx->scope, acc_name, acc_sch);
              if (!nameless_kw) {
                char qacc[256];
                snprintf(qacc, sizeof(qacc), "%s::%s:%s", type_name, ctor_name, field_keys[fi]);
                typed_scope_add(ctx->scope, qacc, acc_sch);
              }
            }
          }
        }
      }
      variants = valk_lval_tail(variants);
    }
    return ty_nil(ctx->arena);
  }

  // --- match expression: pattern match on constructors ---
  // (match val {(Some :value v) body} {(None) body2} ...)
  if (strcmp(name, "match") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return ty_var(ctx->arena);
    valk_lval_t *scrutinee = valk_lval_head(rest);
    valk_type_t *scrut_ty = infer_expr(ctx, scrutinee);

    valk_type_t *result = ty_var(ctx->arena);
    valk_lval_t *clauses = valk_lval_tail(rest);
    while (clauses && LVAL_TYPE(clauses) == LVAL_CONS) {
      valk_lval_t *clause = valk_lval_head(clauses);
      if (clause && LVAL_TYPE(clause) == LVAL_CONS &&
          (clause->flags & LVAL_FLAG_QUOTED)) {
        valk_lval_t *pattern = valk_lval_head(clause);
        valk_lval_t *body = valk_lval_tail(clause);
        if (!body || LVAL_TYPE(body) != LVAL_CONS) {
          clauses = valk_lval_tail(clauses);
          continue;
        }
        valk_lval_t *body_expr = valk_lval_head(body);

        if (pattern && LVAL_TYPE(pattern) == LVAL_SYM) {
          valk_type_t *bt = infer_expr(ctx, body_expr);
          ty_unify(ctx->arena, result, bt);
          clauses = valk_lval_tail(clauses);
          continue;
        }

        if (pattern && LVAL_TYPE(pattern) == LVAL_CONS &&
            !(pattern->flags & LVAL_FLAG_QUOTED)) {
          valk_lval_t *ctor_sym = valk_lval_head(pattern);
          if (ctor_sym && LVAL_TYPE(ctor_sym) == LVAL_SYM) {
            typed_scope_t *inner = typed_scope_push(ctx->arena, ctx->scope);
            type_scheme_t *ctor_sch = typed_scope_lookup(ctx->scope, ctor_sym->str);
            valk_type_t *ctor_fn = ctor_sch
              ? ty_resolve(scheme_instantiate(ctx->arena, ctor_sch))
              : nullptr;

            if (ctor_fn && ctor_fn->kind == TY_FUN)
              ty_unify(ctx->arena, scrut_ty, ctor_fn->fun.ret);
            else if (ctor_fn && ctor_fn->kind == TY_NAMED)
              ty_unify(ctx->arena, scrut_ty, ctor_fn);

            valk_lval_t *pat_args = valk_lval_tail(pattern);
            valk_lval_t *first_pat_arg = (pat_args && LVAL_TYPE(pat_args) == LVAL_CONS)
              ? valk_lval_head(pat_args) : nullptr;
            bool kw_pat = first_pat_arg && LVAL_TYPE(first_pat_arg) == LVAL_SYM
              && first_pat_arg->str[0] == ':';

            int field_idx = 0;
            if (kw_pat) {
              while (pat_args && LVAL_TYPE(pat_args) == LVAL_CONS) {
                valk_lval_t *key = valk_lval_head(pat_args);
                pat_args = valk_lval_tail(pat_args);
                if (!pat_args || LVAL_TYPE(pat_args) != LVAL_CONS) break;
                valk_lval_t *var = valk_lval_head(pat_args);
                pat_args = valk_lval_tail(pat_args);

                if (key && LVAL_TYPE(key) == LVAL_SYM && key->str[0] == ':' &&
                    var && LVAL_TYPE(var) == LVAL_SYM &&
                    strcmp(var->str, "_") != 0) {
                  valk_type_t *var_ty = ty_var(ctx->arena);
                  if (ctor_fn && ctor_fn->kind == TY_FUN &&
                      field_idx < ctor_fn->fun.param_count)
                    var_ty = ty_resolve(ctor_fn->fun.params[field_idx]);
                  typed_scope_add_mono(inner, var->str, var_ty);

                  if (ctx->hover_offset >= 0 && var->src_pos >= 0 &&
                      var->src_pos <= ctx->hover_offset &&
                      ctx->hover_offset < var->src_pos + (int)strlen(var->str))
                    ctx->hover_result = var_ty;
                  emit_type_hint(ctx, var, var_ty);
                }
                field_idx++;
              }
            } else {
              while (pat_args && LVAL_TYPE(pat_args) == LVAL_CONS) {
                valk_lval_t *var = valk_lval_head(pat_args);
                pat_args = valk_lval_tail(pat_args);

                if (var && LVAL_TYPE(var) == LVAL_SYM &&
                    strcmp(var->str, "_") != 0) {
                  valk_type_t *var_ty = ty_var(ctx->arena);
                  if (ctor_fn && ctor_fn->kind == TY_FUN &&
                      field_idx < ctor_fn->fun.param_count)
                    var_ty = ty_resolve(ctor_fn->fun.params[field_idx]);
                  typed_scope_add_mono(inner, var->str, var_ty);

                  if (ctx->hover_offset >= 0 && var->src_pos >= 0 &&
                      var->src_pos <= ctx->hover_offset &&
                      ctx->hover_offset < var->src_pos + (int)strlen(var->str))
                    ctx->hover_result = var_ty;
                  emit_type_hint(ctx, var, var_ty);
                }
                field_idx++;
              }
            }

            typed_scope_t *saved = ctx->scope;
            ctx->scope = inner;
            valk_type_t *bt = infer_expr(ctx, body_expr);
            ctx->scope = saved;
            typed_scope_pop(inner);
            ty_unify(ctx->arena, result, bt);
          }
        }
      }
      clauses = valk_lval_tail(clauses);
    }
    return ty_resolve(result);
  }

  if (strcmp(name, "do") == 0)
    return infer_body_last(ctx, rest);

  // --- PList special forms (lsp_infer_plist.c) ---
  if (strcmp(name, "list") == 0) {
    valk_type_t *pl = infer_plist_from_list_call(ctx, rest);
    if (pl) return pl;
  }

  if (strcmp(name, "plist/get") == 0) {
    valk_type_t *r = infer_plist_get(ctx, rest);
    if (r) return r;
  }

  if (strcmp(name, "plist/set") == 0) {
    valk_type_t *r = infer_plist_set(ctx, rest);
    if (r) return r;
  }

  if (strcmp(name, "plist/has?") == 0) {
    valk_type_t *r = infer_plist_has(ctx, rest);
    if (r) return r;
  }

  if (strcmp(name, "plist/keys") == 0 || strcmp(name, "plist/vals") == 0) {
    valk_type_t *r = infer_plist_keys_vals(ctx, name, rest);
    if (r) return r;
  }

  // --- Function calls (builtins + user-defined) ---

  type_scheme_t *fn_scheme = typed_scope_lookup(ctx->scope, name);
  if (fn_scheme) {
    valk_type_t *fn_ty = ty_resolve(scheme_instantiate(ctx->arena, fn_scheme));

    if (fn_ty->kind == TY_FUN) {
      valk_lval_t *first_arg = (rest && LVAL_TYPE(rest) == LVAL_CONS)
        ? valk_lval_head(rest) : NULL;
      bool kw_call = first_arg && LVAL_TYPE(first_arg) == LVAL_SYM &&
        first_arg->str[0] == ':' && fn_ty->fun.param_count > 0;
      if (kw_call) {
        valk_lval_t *kc = rest;
        while (kc && LVAL_TYPE(kc) == LVAL_CONS) {
          valk_lval_t *key = valk_lval_head(kc);
          kc = valk_lval_tail(kc);
          if (!kc || LVAL_TYPE(kc) != LVAL_CONS) break;
          valk_lval_t *val = valk_lval_head(kc);
          kc = valk_lval_tail(kc);
          valk_type_t *val_ty = infer_expr(ctx, val);
          if (key && LVAL_TYPE(key) == LVAL_SYM && key->str[0] == ':') {
            for (int pi = 0; pi < fn_ty->fun.param_count; pi++) {
              const char *pn = fn_ty->fun.param_names[pi];
              if (pn && strcmp(key->str + 1, pn) == 0) {
                ty_unify(ctx->arena, fn_ty->fun.params[pi], val_ty);
                break;
              }
            }
          }
        }
        return ty_resolve(fn_ty->fun.ret);
      }
      bool variadic_poly = false;
      if (fn_ty->fun.variadic && fn_ty->fun.param_count > 0) {
        valk_type_t *vparam = ty_resolve(fn_ty->fun.params[fn_ty->fun.param_count - 1]);
        variadic_poly = (vparam->kind == TY_VAR);
      }

      int nargs = infer_count_list(rest);
      valk_lval_t *arg_cur = rest;
      for (int i = 0; i < nargs && arg_cur && LVAL_TYPE(arg_cur) == LVAL_CONS; i++) {
        valk_lval_t *arg_node = valk_lval_head(arg_cur);
        valk_type_t *arg_ty = infer_expr(ctx, arg_node);

        int pi = i;
        if (fn_ty->fun.variadic && i >= fn_ty->fun.param_count)
          pi = fn_ty->fun.param_count - 1;
        else if (i >= fn_ty->fun.param_count)
          pi = -1;

        if (variadic_poly && i >= fn_ty->fun.param_count) {
          arg_cur = valk_lval_tail(arg_cur);
          continue;
        }

        if (pi >= 0 && pi < fn_ty->fun.param_count) {
          const char *pn = fn_ty->fun.param_names[pi];
          if (pn && !(arg_node && LVAL_TYPE(arg_node) == LVAL_SYM &&
                      strcmp(arg_node->str, pn) == 0))
            emit_param_hint(ctx, arg_node, pn);
          valk_type_t *expected = ty_resolve(fn_ty->fun.params[pi]);
          valk_type_t *actual = ty_resolve(arg_ty);

          if (!ty_contains_any(expected) && !ty_contains_any(actual) &&
              expected->kind != TY_VAR && actual->kind != TY_VAR &&
              !ty_has_unresolved_var(expected) && !ty_has_unresolved_var(actual)) {
            if (!ty_compatible(expected, actual))
              emit_type_error(ctx, name, i, expected, actual);
          }

          ty_unify(ctx->arena, fn_ty->fun.params[pi], arg_ty);
        }
        arg_cur = valk_lval_tail(arg_cur);
      }
      return ty_resolve(fn_ty->fun.ret);
    }

    if (fn_ty->kind == TY_VAR) {
      int nargs = infer_count_list(rest);
      int n = nargs < TY_MAX_PARAMS ? nargs : TY_MAX_PARAMS;
      valk_type_t *arg_tys[TY_MAX_PARAMS];
      valk_lval_t *arg_cur = rest;
      for (int i = 0; i < n; i++) {
        arg_tys[i] = infer_expr(ctx, valk_lval_head(arg_cur));
        arg_cur = valk_lval_tail(arg_cur);
      }
      valk_type_t *ret_ty = ty_var(ctx->arena);
      valk_type_t *synth = ty_fun(ctx->arena, arg_tys, n, ret_ty, false);
      ty_unify(ctx->arena, fn_ty, synth);
      return ty_resolve(ret_ty);
    }

    if (!rest || LVAL_TYPE(rest) != LVAL_CONS)
      return fn_ty;
    infer_body(ctx, rest);
    return ty_var(ctx->arena);
  }

  infer_body(ctx, rest);
  return ty_var(ctx->arena);
}
