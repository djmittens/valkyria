#include "vir.h"
#include "../parser.h"
#include "../builtins_internal.h"  // valk_qexpr_to_cons
#include <string.h>
#include <stdlib.h>

typedef struct {
  vir_builder_t *b;
  vir_value_t *env_param;
  // Build-time env for resolving direct AOT-to-AOT calls. When non-NULL,
  // a call whose head resolves to a known compiled lambda gets emitted
  // as VIR_DIRECT_CALL (skipping valk_lval_eval_call). NULL outside
  // --build (JIT, tests).
  valk_lenv_t *build_env;
} lower_ctx_t;

static vir_value_t *lower_expr(lower_ctx_t *ctx, valk_lval_t *expr);
static vir_value_t *lower_literal(lower_ctx_t *ctx, valk_lval_t *expr);
// Lower `expr` in tail position. Always terminates the current basic
// block with a ret (either explicit ret of an evaluated value, or a
// musttail call followed by ret of the call's result). For if/do
// nodes, recurses into branches in tail position so each leaf path
// terminates with its own ret — that's the structure LLVM needs to
// recognize sibcall opportunities and avoid growing the C stack.
//
// Returns nothing because every tail-position emission terminates the
// block; the caller must not emit a follow-on ret.
static void lower_tail(lower_ctx_t *ctx, valk_lval_t *expr);

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

// `if` branches in valk are written as qexprs `{...}` to defer
// evaluation. The qexpr wrapping must be stripped before lowering;
// otherwise the branch is treated as data (a runtime cons literal)
// and `if` returns the unevaluated branch instead of its result.
// Mirrors valk_codegen_unwrap_branch_qexpr in llvm_codegen_emit.c.
static valk_lval_t *unwrap_branch_qexpr(valk_lval_t *branch) {
  if (!branch) return branch;
  if (LVAL_TYPE(branch) != LVAL_CONS) return branch;
  if (!(branch->flags & LVAL_FLAG_QUOTED)) return branch;
  valk_lval_t *cons = valk_qexpr_to_cons(branch);
  if (cons && LVAL_TYPE(cons) == LVAL_CONS && cons->cons.tail &&
      LVAL_TYPE(cons->cons.tail) == LVAL_NIL) {
    return cons->cons.head;
  }
  return cons;
}

static vir_value_t *lower_if(lower_ctx_t *ctx, valk_lval_t *args, u64 argc) {
  if (argc < 2) return vir_build_const_nil(ctx->b);

  valk_lval_t *cond_expr = cons_nth(args, 0);
  valk_lval_t *then_expr = cons_nth(args, 1);
  valk_lval_t *else_expr = argc > 2 ? cons_nth(args, 2) : NULL;

  then_expr = unwrap_branch_qexpr(then_expr);
  else_expr = unwrap_branch_qexpr(else_expr);

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

// Try to resolve `head` as a known AOT lambda eligible for direct call.
// Returns the target if (a) head is a sym, (b) target is non-builtin
// LVAL_FUN with native_name, (c) formal count matches argc, (d) no
// varargs. Mirrors codegen_try_direct_call's eligibility in
// llvm_codegen_call.c.
static valk_lval_t *resolve_direct_target(lower_ctx_t *ctx,
                                          valk_lval_t *head, u64 argc) {
  if (!ctx->build_env) return NULL;
  if (!head || LVAL_TYPE(head) != LVAL_SYM) return NULL;
  valk_lval_t *target = valk_lenv_get(ctx->build_env, head);
  if (!target || LVAL_TYPE(target) != LVAL_FUN) return NULL;
  if (target->fun.builtin) return NULL;
  if (!target->fun.native_name) return NULL;

  u64 nformals = 0;
  for (valk_lval_t *f = target->fun.formals;
       f && LVAL_TYPE(f) == LVAL_CONS; f = f->cons.tail) {
    valk_lval_t *fh = f->cons.head;
    if (LVAL_TYPE(fh) == LVAL_SYM && strcmp(fh->str, "&") == 0) return NULL;
    nformals++;
  }
  if (nformals != argc) return NULL;
  return target;
}

static vir_value_t *lower_funcall(lower_ctx_t *ctx, valk_lval_t *head,
                                  valk_lval_t *args_list, u64 argc) {
  // Direct AOT-to-AOT call when target is a known compiled lambda.
  // Avoids valk_lval_eval_call's tree-walker re-entry on every call,
  // which is the dominant cost in compiled code. test_lsp_profile fails
  // (90s timeout) without this; the LSP-style indirect dispatch chain
  // (each call going eval_call → apply_func_iter → eval_iterative) is
  // too slow under typing load.
  valk_lval_t *direct = resolve_direct_target(ctx, head, argc);
  if (direct) {
    vir_value_t **arg_vals = calloc(argc, sizeof(vir_value_t *));
    const char **formal_names = calloc(argc, sizeof(const char *));
    valk_lval_t *cur_arg = args_list;
    valk_lval_t *cur_fml = direct->fun.formals;
    for (u64 i = 0; i < argc; i++) {
      arg_vals[i] = lower_expr(ctx, cur_arg->cons.head);
      formal_names[i] = cur_fml->cons.head->str;
      cur_arg = cur_arg->cons.tail;
      cur_fml = cur_fml->cons.tail;
    }
    vir_value_t *call = vir_build_direct_call(ctx->b,
      direct->fun.native_name, formal_names, arg_vals, (u32)argc);
    free(arg_vals);
    free(formal_names);
    return call;
  }

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
      // Keywords (symbols starting with ':') are LITERAL values, not
      // env-bound variables. plist/get and friends use them as keys.
      // Without this branch, a `:method` reference compiles to an env
      // lookup that fails, producing nil — silently breaking every
      // plist accessor in the codebase. Mirrors the keyword check in
      // llvm_codegen_emit.c::valk_codegen_sym_lookup.
      if (expr->str && expr->str[0] == ':') {
        return vir_build_const_sym(ctx->b, expr->str);
      }
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

// Lower a lambda body the way valk_lval_eval_apply_func_iter +
// valk_lval_eval_iterative would interpret it. Mirrors the body-shape
// dispatch in src/llvm/llvm_codegen.c::valk_llvm_compile_lambda_body
// (the slow-body codegen we're replacing). Three cases:
//
//   1. body is a quoted cons list whose first element is itself a list
//      → treat as a do-block, evaluate each form in sequence, return last.
//   2. body is a single-element list → evaluate that one element.
//   3. body is a single expression → evaluate it.
//
// Used by build_aot.c for AOT-compiled lambdas that aren't fast-safe
// (have nested closures, varargs, or local mutation). Goes through VIR
// instead of the hand-rolled AST→LLVM path that used to live in
// llvm_codegen.c::valk_llvm_compile_lambda_body.
vir_func_t *vir_lower_lambda_body(vir_builder_t *b, valk_lval_t *body,
                                  const char *name) {
  return vir_lower_lambda_body_with_env(b, body, name, NULL);
}

vir_func_t *vir_lower_lambda_body_with_env(vir_builder_t *b, valk_lval_t *body,
                                           const char *name,
                                           valk_lenv_t *build_env) {
  vir_func_t *fn = vir_builder_add_func(b, name, 1);
  vir_block_t *entry = vir_builder_add_block(b, "entry");
  vir_builder_set_block(b, entry);

  lower_ctx_t ctx = {.b = b, .env_param = fn->params[0], .build_env = build_env};

  // Unwrap qexpr-wrapped bodies (the common case for `(fun {f x} {body})`).
  valk_lval_t *eff = body;
  if (eff && LVAL_TYPE(eff) == LVAL_CONS && (eff->flags & LVAL_FLAG_QUOTED)) {
    eff = valk_qexpr_to_cons(eff);
  }

  if (eff && LVAL_TYPE(eff) == LVAL_CONS) {
    valk_lval_t *first = eff->cons.head;
    bool first_is_list = first && LVAL_TYPE(first) == LVAL_CONS;
    if (first_is_list) {
      // Multi-form do-block. Evaluate each except the last via normal
      // lowering; lower the last in tail position so any call there
      // becomes a musttail (sibcall) and recursive bodies don't grow
      // the C stack.
      valk_lval_t *cur = eff;
      while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        valk_lval_t *next = cur->cons.tail;
        bool is_last = !next || LVAL_TYPE(next) != LVAL_CONS;
        if (is_last) {
          lower_tail(&ctx, cur->cons.head);
          return fn;  // lower_tail terminates the block
        }
        lower_expr(&ctx, cur->cons.head);
        cur = next;
      }
    } else {
      // Single form (count==1) or a sexpr whose head is a symbol.
      u64 count = cons_len(eff);
      if (count == 1) {
        lower_tail(&ctx, first);
      } else {
        lower_tail(&ctx, eff);
      }
      return fn;
    }
  } else if (eff) {
    lower_tail(&ctx, eff);
    return fn;
  }

  // Empty body — return nil.
  vir_build_ret(b, vir_build_const_nil(b));
  return fn;
}

// Lower `expr` knowing the result is the function's return value.
// Always emits a terminator. For calls, sets is_tail=true so vir_to_llvm
// emits musttail + ret (LLVM sibcalls the call, reusing the C frame).
// For if/do, recurses into the tail-position branch.
static void lower_tail(lower_ctx_t *ctx, valk_lval_t *expr) {
  if (!expr) {
    vir_build_ret(ctx->b, vir_build_const_nil(ctx->b));
    return;
  }

  // Sexpr: check for special forms whose tail position propagates into
  // their branches (if, do). Calls in tail position get musttail.
  if (LVAL_TYPE(expr) == LVAL_CONS && !(expr->flags & LVAL_FLAG_QUOTED)) {
    valk_lval_t *head = expr->cons.head;
    valk_lval_t *rest = expr->cons.tail;
    u64 argc = (rest && LVAL_TYPE(rest) == LVAL_CONS) ? cons_len(rest) : 0;

    if (LVAL_TYPE(head) == LVAL_SYM) {
      // (if cond then else) — tail position propagates into both branches.
      if (is_sym(head, "if") && argc >= 2) {
        valk_lval_t *cond_expr = cons_nth(rest, 0);
        valk_lval_t *then_expr = unwrap_branch_qexpr(cons_nth(rest, 1));
        valk_lval_t *else_expr = argc > 2
            ? unwrap_branch_qexpr(cons_nth(rest, 2)) : NULL;

        vir_value_t *cond_val = lower_expr(ctx, cond_expr);
        vir_value_t *cond_bool = vir_build_truthy(ctx->b, cond_val);

        vir_block_t *then_bb = vir_builder_add_block(ctx->b, "then.tail");
        vir_block_t *else_bb = vir_builder_add_block(ctx->b, "else.tail");
        vir_build_br_if(ctx->b, cond_bool, then_bb, else_bb);

        vir_builder_set_block(ctx->b, then_bb);
        lower_tail(ctx, then_expr);

        vir_builder_set_block(ctx->b, else_bb);
        if (else_expr) {
          lower_tail(ctx, else_expr);
        } else {
          vir_build_ret(ctx->b, vir_build_const_nil(ctx->b));
        }
        return;
      }

      // (do ...) — last expr in tail position, others normal.
      if (is_sym(head, "do")) {
        if (argc == 0) {
          vir_build_ret(ctx->b, vir_build_const_nil(ctx->b));
          return;
        }
        valk_lval_t *cur = rest;
        for (u64 i = 0; i < argc - 1; i++) {
          lower_expr(ctx, cur->cons.head);
          cur = cur->cons.tail;
        }
        lower_tail(ctx, cur->cons.head);
        return;
      }

      // Special forms that produce a value but don't recurse into
      // branches — fall through to normal lowering + ret.
      if (is_sym(head, "def") || is_sym(head, "=") || is_sym(head, "\\")) {
        vir_value_t *v = lower_expr(ctx, expr);
        vir_build_ret(ctx->b, v);
        return;
      }
    }

    // Sexpr whose head is a callable. Lower as call with is_tail=true.
    // Try direct AOT-to-AOT first; fall back to general call.
    valk_lval_t *direct = resolve_direct_target(ctx, head, argc);
    if (direct) {
      vir_value_t **arg_vals = calloc(argc, sizeof(vir_value_t *));
      const char **formal_names = calloc(argc, sizeof(const char *));
      valk_lval_t *cur_arg = rest;
      valk_lval_t *cur_fml = direct->fun.formals;
      for (u64 i = 0; i < argc; i++) {
        arg_vals[i] = lower_expr(ctx, cur_arg->cons.head);
        formal_names[i] = cur_fml->cons.head->str;
        cur_arg = cur_arg->cons.tail;
        cur_fml = cur_fml->cons.tail;
      }
      vir_value_t *call = vir_build_direct_call(ctx->b,
        direct->fun.native_name, formal_names, arg_vals, (u32)argc);
      call->direct_call.is_tail = true;
      free(arg_vals);
      free(formal_names);
      vir_build_ret(ctx->b, call);
      return;
    }

    // General (indirect) call.
    vir_value_t *fn_val = lower_expr(ctx, head);
    vir_value_t **arg_vals = calloc(argc, sizeof(vir_value_t *));
    valk_lval_t *cur = rest;
    for (u64 i = 0; i < argc; i++) {
      arg_vals[i] = lower_expr(ctx, cur->cons.head);
      cur = cur->cons.tail;
    }
    vir_value_t *qargs = build_qcons_list(ctx, arg_vals, argc);
    free(arg_vals);
    vir_value_t *call_args[] = {qargs};
    vir_value_t *call = vir_build_call(ctx->b, fn_val, call_args, 1);
    call->call.is_tail = true;
    vir_build_ret(ctx->b, call);
    return;
  }

  // Non-call expression in tail position — lower normally, emit ret.
  vir_value_t *v = lower_expr(ctx, expr);
  vir_build_ret(ctx->b, v);
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
