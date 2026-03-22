#include "vir_to_llvm.h"
#include <stdlib.h>
#include <string.h>

typedef struct {
  valk_llvm_ctx_t *c;
  LLVMValueRef *val_map;
  u32 val_map_size;
  LLVMBasicBlockRef *bb_map;
  u32 bb_map_cap;
  LLVMValueRef fn_gc_root_push;
  LLVMValueRef fn_gc_root_save;
  LLVMValueRef fn_gc_root_restore;
  LLVMValueRef fn_gc_safepoint;
} lower_ctx_t;

static void ensure_val_map(lower_ctx_t *ctx, u32 id) {
  if (id >= ctx->val_map_size) {
    u32 new_size = (id + 1) * 2;
    ctx->val_map = realloc(ctx->val_map, new_size * sizeof(LLVMValueRef));
    memset(ctx->val_map + ctx->val_map_size, 0,
           (new_size - ctx->val_map_size) * sizeof(LLVMValueRef));
    ctx->val_map_size = new_size;
  }
}

static void ensure_bb_map(lower_ctx_t *ctx, u32 id) {
  if (id >= ctx->bb_map_cap) {
    u32 new_size = (id + 1) * 2;
    ctx->bb_map = realloc(ctx->bb_map, new_size * sizeof(LLVMBasicBlockRef));
    memset(ctx->bb_map + ctx->bb_map_cap, 0,
           (new_size - ctx->bb_map_cap) * sizeof(LLVMBasicBlockRef));
    ctx->bb_map_cap = new_size;
  }
}

static void set_val(lower_ctx_t *ctx, u32 id, LLVMValueRef val) {
  ensure_val_map(ctx, id);
  ctx->val_map[id] = val;
}

static LLVMValueRef get_val(lower_ctx_t *ctx, u32 id) {
  if (id < ctx->val_map_size) return ctx->val_map[id];
  return NULL;
}

static LLVMBasicBlockRef get_bb(lower_ctx_t *ctx, u32 id) {
  if (id < ctx->bb_map_cap) return ctx->bb_map[id];
  return NULL;
}

static LLVMValueRef emit_global_str(lower_ctx_t *ctx, const char *str) {
  char name[64];
  snprintf(name, sizeof(name), ".str.%llu",
    (unsigned long long)ctx->c->str_counter++);
  return LLVMBuildGlobalStringPtr(ctx->c->builder, str, name);
}

static LLVMValueRef call1(lower_ctx_t *ctx, LLVMValueRef fn,
                          LLVMTypeRef ret, LLVMValueRef arg,
                          const char *name) {
  LLVMTypeRef ft = LLVMFunctionType(ret, (LLVMTypeRef[]){
    LLVMTypeOf(arg)}, 1, 0);
  return LLVMBuildCall2(ctx->c->builder, ft, fn, &arg, 1, name);
}

static LLVMValueRef call2(lower_ctx_t *ctx, LLVMValueRef fn,
                          LLVMTypeRef ret, LLVMValueRef a, LLVMValueRef b,
                          const char *name) {
  LLVMValueRef args[] = {a, b};
  LLVMTypeRef ft = LLVMFunctionType(ret, (LLVMTypeRef[]){
    LLVMTypeOf(a), LLVMTypeOf(b)}, 2, 0);
  return LLVMBuildCall2(ctx->c->builder, ft, fn, args, 2, name);
}

static LLVMValueRef call3(lower_ctx_t *ctx, LLVMValueRef fn,
                          LLVMTypeRef ret, LLVMValueRef a,
                          LLVMValueRef b, LLVMValueRef d,
                          const char *name) {
  LLVMValueRef args[] = {a, b, d};
  LLVMTypeRef ft = LLVMFunctionType(ret, (LLVMTypeRef[]){
    LLVMTypeOf(a), LLVMTypeOf(b), LLVMTypeOf(d)}, 3, 0);
  return LLVMBuildCall2(ctx->c->builder, ft, fn, args, 3, name);
}

static void declare_gc_fns(lower_ctx_t *ctx, LLVMModuleRef mod) {
  valk_llvm_ctx_t *c = ctx->c;
  LLVMTypeRef ptr = c->ptr_type;
  LLVMTypeRef i64 = c->i64_type;
  LLVMTypeRef vd = c->void_type;

  ctx->fn_gc_root_push = LLVMAddFunction(mod, "valk_gc_root_push_fn",
    LLVMFunctionType(vd, (LLVMTypeRef[]){ptr}, 1, 0));
  ctx->fn_gc_root_save = LLVMAddFunction(mod, "valk_gc_root_save",
    LLVMFunctionType(i64, NULL, 0, 0));
  ctx->fn_gc_root_restore = LLVMAddFunction(mod, "valk_gc_root_restore",
    LLVMFunctionType(vd, (LLVMTypeRef[]){i64}, 1, 0));
  ctx->fn_gc_safepoint = LLVMAddFunction(mod, "valk_gc_safepoint_fn",
    LLVMFunctionType(vd, NULL, 0, 0));
}

static LLVMValueRef lower_value(lower_ctx_t *ctx, vir_value_t *v) {
  valk_llvm_ctx_t *c = ctx->c;
  LLVMValueRef result = NULL;

  switch (v->opcode) {
    case VIR_CONST_NUM: {
      LLVMValueRef num = LLVMConstInt(c->i64_type, (u64)v->num_val, 1);
      result = call1(ctx, c->fn_lval_num, c->ptr_type, num, "num");
      break;
    }
    case VIR_CONST_STR: {
      LLVMValueRef str = emit_global_str(ctx, v->str_val);
      result = call1(ctx, c->fn_lval_str, c->ptr_type, str, "str");
      break;
    }
    case VIR_CONST_NIL: {
      LLVMTypeRef ft = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
      result = LLVMBuildCall2(c->builder, ft, c->fn_lval_nil, NULL, 0, "nil");
      break;
    }
    case VIR_CONST_SYM: {
      LLVMValueRef str = emit_global_str(ctx, v->str_val);
      result = call1(ctx, c->fn_lval_sym, c->ptr_type, str, "sym");
      break;
    }

    case VIR_TRUTHY: {
      LLVMValueRef op = get_val(ctx, v->operands[0]->id);
      result = call1(ctx, c->fn_lval_is_truthy, c->i1_type, op, "truthy");
      break;
    }

    case VIR_ENV_GET: {
      LLVMValueRef env = get_val(ctx, v->operands[0]->id);
      LLVMValueRef sym = emit_global_str(ctx, v->str_val);
      LLVMValueRef sym_val = call1(ctx, c->fn_lval_sym, c->ptr_type,
                                   sym, "sym");
      result = call2(ctx, c->fn_lenv_get, c->ptr_type, env, sym_val, "get");
      break;
    }
    case VIR_ENV_PUT:
    case VIR_ENV_DEF: {
      LLVMValueRef env = get_val(ctx, v->operands[0]->id);
      LLVMValueRef val = get_val(ctx, v->operands[1]->id);
      LLVMValueRef sym = emit_global_str(ctx, v->str_val);
      LLVMValueRef sym_val = call1(ctx, c->fn_lval_sym, c->ptr_type,
                                   sym, "sym");
      LLVMValueRef fn = (v->opcode == VIR_ENV_DEF) ?
                         c->fn_lenv_def : c->fn_lenv_put;
      call3(ctx, fn, c->void_type, env, sym_val, val, "");
      break;
    }

    case VIR_CONS:
    case VIR_QCONS: {
      LLVMValueRef head = get_val(ctx, v->operands[0]->id);
      LLVMValueRef tail = get_val(ctx, v->operands[1]->id);
      LLVMValueRef fn = (v->opcode == VIR_QCONS) ?
                         c->fn_lval_qcons : c->fn_lval_cons;
      result = call2(ctx, fn, c->ptr_type, head, tail,
                     v->opcode == VIR_QCONS ? "qcons" : "cons");
      break;
    }

    case VIR_LAMBDA: {
      LLVMValueRef env = get_val(ctx, v->operands[0]->id);
      LLVMValueRef formals = get_val(ctx, v->operands[1]->id);
      LLVMValueRef body = get_val(ctx, v->operands[2]->id);
      result = call3(ctx, c->fn_lval_lambda, c->ptr_type,
                     env, formals, body, "lambda");
      break;
    }

    case VIR_CALL:
    case VIR_TAIL_CALL: {
      LLVMValueRef fn_val = get_val(ctx, v->operands[0]->id);
      LLVMValueRef args_list = get_val(ctx, v->call.args[0]->id);
      result = call3(ctx, c->fn_lval_eval_call, c->ptr_type,
                     get_val(ctx, v->parent->parent->params[0]->id),
                     fn_val, args_list, "call");
      break;
    }

    case VIR_BR:
      LLVMBuildBr(c->builder, (LLVMBasicBlockRef)get_bb(ctx, v->br.target->id));
      break;

    case VIR_BR_IF: {
      LLVMValueRef cond = get_val(ctx, v->operands[0]->id);
      LLVMBuildCondBr(c->builder, cond,
        (LLVMBasicBlockRef)get_bb(ctx, v->br_if.true_bb->id),
        (LLVMBasicBlockRef)get_bb(ctx, v->br_if.false_bb->id));
      break;
    }

    case VIR_RET: {
      LLVMValueRef val = get_val(ctx, v->operands[0]->id);
      LLVMBuildRet(c->builder, val);
      break;
    }

    case VIR_PHI:
      result = LLVMBuildPhi(c->builder, c->ptr_type, "phi");
      break;

    case VIR_GC_ROOT: {
      LLVMTypeRef save_ft = LLVMFunctionType(c->i64_type, NULL, 0, 0);
      result = LLVMBuildCall2(c->builder, save_ft, ctx->fn_gc_root_save,
                              NULL, 0, "gc.save");
      for (u32 i = 0; i < v->num_operands; i++) {
        LLVMValueRef op = get_val(ctx, v->operands[i]->id);
        if (op) {
          LLVMTypeRef push_ft = LLVMFunctionType(c->void_type,
            (LLVMTypeRef[]){c->ptr_type}, 1, 0);
          LLVMBuildCall2(c->builder, push_ft, ctx->fn_gc_root_push,
                         &op, 1, "");
        }
      }
      break;
    }

    case VIR_GC_UNROOT: {
      LLVMValueRef save = get_val(ctx, v->operands[0]->id);
      LLVMTypeRef ft = LLVMFunctionType(c->void_type,
        (LLVMTypeRef[]){c->i64_type}, 1, 0);
      LLVMBuildCall2(c->builder, ft, ctx->fn_gc_root_restore,
                     &save, 1, "");
      break;
    }

    case VIR_GC_SAFEPOINT: {
      LLVMTypeRef ft = LLVMFunctionType(c->void_type, NULL, 0, 0);
      LLVMBuildCall2(c->builder, ft, ctx->fn_gc_safepoint, NULL, 0, "");
      break;
    }

    default:
      break;
  }

  if (result) set_val(ctx, v->id, result);
  return result;
}

static void fixup_phis(lower_ctx_t *ctx, vir_func_t *fn) {
  vir_block_t *bb = fn->block_list;
  while (bb) {
    vir_value_t *v = bb->first;
    while (v) {
      if (v->opcode == VIR_PHI) {
        LLVMValueRef phi = get_val(ctx, v->id);
        if (phi && v->phi.num_incoming > 0) {
          LLVMValueRef *vals = calloc(v->phi.num_incoming,
                                      sizeof(LLVMValueRef));
          LLVMBasicBlockRef *bbs = calloc(v->phi.num_incoming,
                                          sizeof(LLVMBasicBlockRef));
          for (u32 i = 0; i < v->phi.num_incoming; i++) {
            vals[i] = get_val(ctx, v->phi.incoming_vals[i]->id);
            bbs[i] = (LLVMBasicBlockRef)get_bb(ctx, v->phi.incoming_blocks[i]->id);
          }
          LLVMAddIncoming(phi, vals, bbs, v->phi.num_incoming);
          free(vals);
          free(bbs);
        }
      }
      v = v->next;
    }
    bb = bb->next;
  }
}

LLVMValueRef vir_to_llvm_func(valk_llvm_ctx_t *c, vir_func_t *fn) {
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type}, fn->num_params, 0);
  LLVMValueRef llvm_fn = LLVMAddFunction(c->module, fn->name, fn_type);
  LLVMSetLinkage(llvm_fn, LLVMExternalLinkage);

  lower_ctx_t ctx = {.c = c};
  declare_gc_fns(&ctx, c->module);

  for (u32 i = 0; i < fn->num_params; i++)
    set_val(&ctx, fn->params[i]->id, LLVMGetParam(llvm_fn, i));

  vir_block_t *bb = fn->block_list;
  while (bb) {
    LLVMBasicBlockRef llvm_bb = LLVMAppendBasicBlockInContext(
      c->ctx, llvm_fn, bb->name);
    ensure_bb_map(&ctx, bb->id);
    ctx.bb_map[bb->id] = llvm_bb;
    bb = bb->next;
  }

  bb = fn->block_list;
  while (bb) {
    LLVMPositionBuilderAtEnd(c->builder,
      (LLVMBasicBlockRef)get_bb(&ctx, bb->id));
    vir_value_t *v = bb->first;
    while (v) {
      lower_value(&ctx, v);
      v = v->next;
    }
    bb = bb->next;
  }

  fixup_phis(&ctx, fn);

  free(ctx.val_map);
  free(ctx.bb_map);
  return llvm_fn;
}

void vir_to_llvm_module(valk_llvm_ctx_t *ctx, vir_module_t *vmod) {
  vir_func_t *fn = vmod->func_list;
  while (fn) {
    vir_to_llvm_func(ctx, fn);
    fn = fn->next;
  }
}
