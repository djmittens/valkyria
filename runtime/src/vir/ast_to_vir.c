#include "vir.h"
#include "../parser.h"
#include <string.h>
#include <stdlib.h>

typedef struct {
  vir_builder_t *b;
  vir_value_t *env_param;
} lower_ctx_t;

static vir_value_t *lower_expr(lower_ctx_t *ctx, valk_lval_t *expr);
static vir_value_t *lower_literal(lower_ctx_t *ctx, valk_lval_t *expr);

static u64 cons_len(valk_lval_t *list) {
  u64 n = 0;
  while (list && LVAL_TYPE(list) == LVAL_CONS) { n++; list = list->cons.tail; }
  return n;
}

static valk_lval_t *cons_nth(valk_lval_t *list, u64 idx) {
  for (u64 i = 0; i < idx; i++) list = list->cons.tail;
  return list->cons.head;
}

static bool is_sym(valk_lval_t *e, const char *name) {
  return LVAL_TYPE(e) == LVAL_SYM && strcmp(e->str, name) == 0;
}

static vir_value_t *lower_if(lower_ctx_t *ctx, valk_lval_t *args, u64 argc) {
  if (argc < 2) return vir_build_const_nil(ctx->b);

  valk_lval_t *cond_expr = cons_nth(args, 0);
  valk_lval_t *then_expr = cons_nth(args, 1);
  valk_lval_t *else_expr = argc > 2 ? cons_nth(args, 2) : NULL;

  vir_value_t *cond_val = lower_expr(ctx, cond_expr);
  vir_value_t *cond_bool = vir_build_truthy(ctx->b, cond_val);

  vir_block_t *then_bb = vir_builder_add_block(ctx->b, "then");
  vir_block_t *else_bb = vir_builder_add_block(ctx->b, "else");
  vir_block_t *merge_bb = vir_builder_add_block(ctx->b, "merge");

  vir_build_br_if(ctx->b, cond_bool, then_bb, else_bb);

  vir_builder_set_block(ctx->b, then_bb);
  vir_value_t *then_val = lower_expr(ctx, then_expr);
  vir_block_t *then_end = ctx->b->cur_bb;
  vir_build_br(ctx->b, merge_bb);

  vir_builder_set_block(ctx->b, else_bb);
  vir_value_t *else_val;
  if (else_expr) {
    else_val = lower_expr(ctx, else_expr);
  } else {
    else_val = vir_build_const_nil(ctx->b);
  }
  vir_block_t *else_end = ctx->b->cur_bb;
  vir_build_br(ctx->b, merge_bb);

  vir_builder_set_block(ctx->b, merge_bb);
  vir_value_t *phi = vir_build_phi(ctx->b, VIR_TYPE_PTR);
  vir_phi_add_incoming(phi, then_val, then_end);
  vir_phi_add_incoming(phi, else_val, else_end);
  return phi;
}

static vir_value_t *lower_do(lower_ctx_t *ctx, valk_lval_t *args, u64 argc) {
  vir_value_t *result = vir_build_const_nil(ctx->b);
  valk_lval_t *cur = args;
  for (u64 i = 0; i < argc; i++) {
    result = lower_expr(ctx, cur->cons.head);
    cur = cur->cons.tail;
  }
  return result;
}

static vir_value_t *lower_def(lower_ctx_t *ctx, valk_lval_t *args,
                              u64 argc, bool global) {
  if (argc < 2) return vir_build_const_nil(ctx->b);

  valk_lval_t *syms_expr = cons_nth(args, 0);

  if (LVAL_TYPE(syms_expr) == LVAL_SYM) {
    vir_value_t *val = lower_expr(ctx, cons_nth(args, 1));
    if (global)
      vir_build_env_def(ctx->b, ctx->env_param, syms_expr->str, val);
    else
      vir_build_env_put(ctx->b, ctx->env_param, syms_expr->str, val);
    return val;
  }

  if (LVAL_TYPE(syms_expr) == LVAL_CONS) {
    u64 sym_count = cons_len(syms_expr);
    u64 val_count = argc - 1;
    u64 n = sym_count < val_count ? sym_count : val_count;

    vir_value_t *last = vir_build_const_nil(ctx->b);
    valk_lval_t *sym_cur = syms_expr;
    valk_lval_t *val_cur = args->cons.tail;
    for (u64 i = 0; i < n; i++) {
      valk_lval_t *s = sym_cur->cons.head;
      vir_value_t *val = lower_expr(ctx, val_cur->cons.head);
      if (global)
        vir_build_env_def(ctx->b, ctx->env_param, s->str, val);
      else
        vir_build_env_put(ctx->b, ctx->env_param, s->str, val);
      last = val;
      sym_cur = sym_cur->cons.tail;
      val_cur = val_cur->cons.tail;
    }
    return last;
  }
  return vir_build_const_nil(ctx->b);
}

static vir_value_t *lower_lambda(lower_ctx_t *ctx, valk_lval_t *args,
                                 u64 argc) {
  if (argc < 2) return vir_build_const_nil(ctx->b);

  valk_lval_t *formals = cons_nth(args, 0);
  valk_lval_t *body = cons_nth(args, 1);

  vir_value_t *formals_val = lower_literal(ctx, formals);
  vir_value_t *body_val = lower_literal(ctx, body);
  return vir_build_lambda(ctx->b, ctx->env_param, formals_val, body_val);
}

static vir_value_t *build_qcons_list(lower_ctx_t *ctx,
                                     vir_value_t **items, u64 count) {
  vir_value_t *list = vir_build_const_nil(ctx->b);
  for (i64 i = (i64)count - 1; i >= 0; i--)
    list = vir_build_qcons(ctx->b, items[i], list);
  return list;
}

static vir_value_t *lower_funcall(lower_ctx_t *ctx, valk_lval_t *head,
                                  valk_lval_t *args_list, u64 argc) {
  vir_value_t *fn_val = lower_expr(ctx, head);

  vir_value_t **arg_vals = calloc(argc, sizeof(vir_value_t *));
  valk_lval_t *cur = args_list;
  for (u64 i = 0; i < argc; i++) {
    arg_vals[i] = lower_expr(ctx, cur->cons.head);
    cur = cur->cons.tail;
  }

  vir_value_t *qargs = build_qcons_list(ctx, arg_vals, argc);
  free(arg_vals);

  vir_value_t *call_args[] = {qargs};
  return vir_build_call(ctx->b, fn_val, call_args, 1);
}

static vir_value_t *lower_sexpr(lower_ctx_t *ctx, valk_lval_t *expr) {
  valk_lval_t *head = expr->cons.head;
  valk_lval_t *rest = expr->cons.tail;
  u64 argc = 0;
  if (rest && LVAL_TYPE(rest) == LVAL_CONS)
    argc = cons_len(rest);

  if (LVAL_TYPE(head) == LVAL_SYM) {
    if (is_sym(head, "if"))
      return lower_if(ctx, rest, argc);
    if (is_sym(head, "do"))
      return lower_do(ctx, rest, argc);
    if (is_sym(head, "def"))
      return lower_def(ctx, rest, argc, true);
    if (is_sym(head, "="))
      return lower_def(ctx, rest, argc, false);
    if (is_sym(head, "\\"))
      return lower_lambda(ctx, rest, argc);
  }

  return lower_funcall(ctx, head, rest, argc);
}

static vir_value_t *lower_literal_cons(lower_ctx_t *ctx, valk_lval_t *expr,
                                       bool quoted) {
  u64 len = cons_len(expr);
  vir_value_t **items = calloc(len, sizeof(vir_value_t *));
  valk_lval_t *cur = expr;
  for (u64 i = 0; i < len; i++) {
    items[i] = lower_literal(ctx, cur->cons.head);
    cur = cur->cons.tail;
  }

  vir_value_t *list = vir_build_const_nil(ctx->b);
  for (i64 i = (i64)len - 1; i >= 0; i--) {
    if (quoted)
      list = vir_build_qcons(ctx->b, items[i], list);
    else
      list = vir_build_cons(ctx->b, items[i], list);
  }
  free(items);
  return list;
}

static vir_value_t *lower_literal(lower_ctx_t *ctx, valk_lval_t *expr) {
  if (!expr) return vir_build_const_nil(ctx->b);

  switch (LVAL_TYPE(expr)) {
    case LVAL_NUM: return vir_build_const_num(ctx->b, expr->num);
    case LVAL_STR: return vir_build_const_str(ctx->b, expr->str);
    case LVAL_NIL: return vir_build_const_nil(ctx->b);
    case LVAL_SYM: return vir_build_const_sym(ctx->b, expr->str);
    case LVAL_CONS: {
      bool quoted = (expr->flags & LVAL_FLAG_QUOTED) != 0;
      return lower_literal_cons(ctx, expr, quoted);
    }
    default: return vir_build_const_nil(ctx->b);
  }
}

static vir_value_t *lower_expr(lower_ctx_t *ctx, valk_lval_t *expr) {
  if (!expr) return vir_build_const_nil(ctx->b);

  switch (LVAL_TYPE(expr)) {
    case LVAL_NUM: return vir_build_const_num(ctx->b, expr->num);
    case LVAL_STR: return vir_build_const_str(ctx->b, expr->str);
    case LVAL_NIL: return vir_build_const_nil(ctx->b);
    case LVAL_SYM:
      return vir_build_env_get(ctx->b, ctx->env_param, expr->str);
    case LVAL_CONS: {
      bool quoted = (expr->flags & LVAL_FLAG_QUOTED) != 0;
      if (quoted) return lower_literal(ctx, expr);
      return lower_sexpr(ctx, expr);
    }
    default: return vir_build_const_nil(ctx->b);
  }
}

vir_func_t *vir_lower_toplevel(vir_builder_t *b, valk_lval_t *expr,
                               const char *name) {
  vir_func_t *fn = vir_builder_add_func(b, name, 1);
  vir_block_t *entry = vir_builder_add_block(b, "entry");
  vir_builder_set_block(b, entry);

  lower_ctx_t ctx = {.b = b, .env_param = fn->params[0]};
  vir_value_t *result = lower_expr(&ctx, expr);
  vir_build_ret(b, result);

  return fn;
}

vir_func_t *vir_lower_program(vir_builder_t *b, valk_lval_t *exprs) {
  u64 count = 0;
  valk_lval_t *cur = exprs;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    count++;
    cur = cur->cons.tail;
  }

  char **fn_names = calloc(count, sizeof(char *));
  cur = exprs;
  for (u64 i = 0; i < count; i++) {
    char name[64];
    snprintf(name, sizeof(name), "__valk_expr_%llu", (unsigned long long)i);
    fn_names[i] = strdup(name);
    vir_lower_toplevel(b, cur->cons.head, fn_names[i]);
    cur = cur->cons.tail;
  }

  vir_func_t *main_fn = vir_builder_add_func(b, "__valk_main", 1);
  vir_block_t *entry = vir_builder_add_block(b, "entry");
  vir_builder_set_block(b, entry);

  vir_value_t *env = main_fn->params[0];
  vir_value_t *result = vir_build_const_nil(b);

  for (u64 i = 0; i < count; i++) {
    vir_value_t *fn_ref = vir_build_env_get(b, env, fn_names[i]);
    result = vir_build_call(b, fn_ref, &env, 1);
    free(fn_names[i]);
  }
  free(fn_names);

  vir_build_ret(b, result);
  return main_fn;
}
