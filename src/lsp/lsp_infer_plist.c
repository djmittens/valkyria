#include "lsp_types.h"
#include "lsp_doc.h"
#include "../parser.h"

#include <string.h>

valk_type_t *infer_plist_from_list_call(infer_ctx_t *ctx, valk_lval_t *rest) {
  int nargs = infer_count_list(rest);
  if (nargs < 2 || nargs % 2 != 0) return nullptr;

  valk_lval_t *cur = rest;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *key = valk_lval_head(cur);
    if (!key || LVAL_TYPE(key) != LVAL_SYM || key->str[0] != ':')
      return nullptr;
    cur = valk_lval_tail(cur);
    if (cur) cur = valk_lval_tail(cur);
  }

  const char *keys[TY_MAX_PARAMS];
  valk_type_t *vals[TY_MAX_PARAMS];
  int n = 0;
  cur = rest;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS && n < TY_MAX_PARAMS) {
    valk_lval_t *key = valk_lval_head(cur);
    infer_expr(ctx, key);
    cur = valk_lval_tail(cur);
    valk_lval_t *val = valk_lval_head(cur);
    cur = valk_lval_tail(cur);
    keys[n] = key->str + 1;
    vals[n] = infer_expr(ctx, val);
    n++;
  }
  return ty_plist(ctx->arena, keys, vals, n);
}

valk_type_t *infer_plist_get(infer_ctx_t *ctx, valk_lval_t *rest) {
  int nargs = infer_count_list(rest);
  if (nargs != 2) return nullptr;

  valk_lval_t *pl_expr = valk_lval_head(rest);
  valk_lval_t *key_node = valk_lval_head(valk_lval_tail(rest));
  valk_type_t *pl_ty = ty_resolve(infer_expr(ctx, pl_expr));
  infer_expr(ctx, key_node);
  if (pl_ty->kind == TY_PLIST) {
    if (key_node && LVAL_TYPE(key_node) == LVAL_SYM && key_node->str[0] == ':') {
      valk_type_t *field = ty_plist_get(pl_ty, key_node->str + 1);
      return field ? field : ty_nil(ctx->arena);
    }
    valk_type_t *val_union = ty_never(ctx->arena);
    for (int i = 0; i < pl_ty->plist.count; i++)
      val_union = ty_join(ctx->arena, val_union, pl_ty->plist.vals[i]);
    return val_union->kind == TY_NEVER ? ty_any(ctx->arena) : val_union;
  }
  return ty_var(ctx->arena);
}

valk_type_t *infer_plist_set(infer_ctx_t *ctx, valk_lval_t *rest) {
  int nargs = infer_count_list(rest);
  if (nargs != 3) return nullptr;

  valk_lval_t *pl_expr = valk_lval_head(rest);
  valk_lval_t *key_node = valk_lval_head(valk_lval_tail(rest));
  valk_lval_t *val_expr = valk_lval_head(valk_lval_tail(valk_lval_tail(rest)));
  valk_type_t *pl_ty = ty_resolve(infer_expr(ctx, pl_expr));
  infer_expr(ctx, key_node);
  valk_type_t *val_ty = infer_expr(ctx, val_expr);
  if (pl_ty->kind == TY_PLIST && key_node &&
      LVAL_TYPE(key_node) == LVAL_SYM && key_node->str[0] == ':') {
    const char *new_key = key_node->str + 1;
    const char *keys[TY_MAX_PARAMS];
    valk_type_t *vals[TY_MAX_PARAMS];
    int n = 0;
    bool found = false;
    for (int i = 0; i < pl_ty->plist.count && n < TY_MAX_PARAMS; i++) {
      keys[n] = pl_ty->plist.keys[i];
      if (strcmp(keys[n], new_key) == 0) {
        vals[n] = val_ty;
        found = true;
      } else {
        vals[n] = pl_ty->plist.vals[i];
      }
      n++;
    }
    if (!found && n < TY_MAX_PARAMS) {
      keys[n] = new_key;
      vals[n] = val_ty;
      n++;
    }
    return ty_plist(ctx->arena, keys, vals, n);
  }
  return ty_any(ctx->arena);
}

valk_type_t *infer_plist_has(infer_ctx_t *ctx, valk_lval_t *rest) {
  int nargs = infer_count_list(rest);
  if (nargs != 2) return nullptr;
  infer_expr(ctx, valk_lval_head(rest));
  infer_expr(ctx, valk_lval_head(valk_lval_tail(rest)));
  return ty_num(ctx->arena);
}

valk_type_t *infer_plist_keys_vals(infer_ctx_t *ctx, const char *name,
                                   valk_lval_t *rest) {
  if (!rest || LVAL_TYPE(rest) != LVAL_CONS) return nullptr;
  valk_type_t *pl_ty = ty_resolve(infer_expr(ctx, valk_lval_head(rest)));
  if (pl_ty->kind != TY_PLIST) return nullptr;

  if (strcmp(name, "plist/keys") == 0)
    return ty_list(ctx->arena, ty_sym(ctx->arena));

  valk_type_t *val_union = ty_never(ctx->arena);
  for (int i = 0; i < pl_ty->plist.count; i++)
    val_union = ty_join(ctx->arena, val_union, pl_ty->plist.vals[i]);
  return ty_list(ctx->arena, val_union);
}
