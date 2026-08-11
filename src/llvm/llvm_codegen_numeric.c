#include "llvm_codegen_internal.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Numeric-op specialization. For arity-2 +/-/*//, < > <= >= ==, emit a
// runtime LVAL_NUM type-check; on a hit use a native i64 op, on a miss
// phi over to the general call path so user-shadowed operators still
// work. See try_codegen_numeric_binop comment for the user-shadow caveat
// (arithmetic operators are NOT verified to still resolve to the builtin
// — matches V8/LuaJIT hot-path policy).

typedef enum {
  BINOP_ADD, BINOP_SUB, BINOP_MUL, BINOP_DIV,
  BINOP_LT,  BINOP_GT,  BINOP_LE,  BINOP_GE, BINOP_EQ,
} numeric_binop_e;

static bool match_numeric_binop(const char *s, numeric_binop_e *out) {
  if (strcmp(s, "+") == 0)  { *out = BINOP_ADD; return true; }
  if (strcmp(s, "-") == 0)  { *out = BINOP_SUB; return true; }
  if (strcmp(s, "*") == 0)  { *out = BINOP_MUL; return true; }
  if (strcmp(s, "/") == 0)  { *out = BINOP_DIV; return true; }
  if (strcmp(s, "<") == 0)  { *out = BINOP_LT;  return true; }
  if (strcmp(s, ">") == 0)  { *out = BINOP_GT;  return true; }
  if (strcmp(s, "<=") == 0) { *out = BINOP_LE;  return true; }
  if (strcmp(s, ">=") == 0) { *out = BINOP_GE;  return true; }
  if (strcmp(s, "==") == 0) { *out = BINOP_EQ;  return true; }
  return false;
}

LLVMValueRef valk_codegen_try_numeric_binop(valk_llvm_ctx_t *c,
                                            valk_lval_t *head,
                                            valk_lval_t *args_list,
                                            u64 argc,
                                            LLVMValueRef env_param) {
  if (argc == 0) return NULL;
  if (LVAL_TYPE(head) != LVAL_SYM) return NULL;
  numeric_binop_e op;
  if (!match_numeric_binop(head->str, &op)) return NULL;

  bool is_arith = (op == BINOP_ADD || op == BINOP_SUB ||
                   op == BINOP_MUL || op == BINOP_DIV);
  if (!is_arith && argc != 2) return NULL;

  bool *is_lit  = malloc(sizeof(bool) * argc);
  i64  *lits    = malloc(sizeof(i64)  * argc);
  LLVMValueRef *vals = malloc(sizeof(LLVMValueRef) * argc);
  valk_lval_t *cur = args_list;
  bool saved_tail = c->in_tail;
  c->in_tail = false;
  for (u64 i = 0; i < argc; i++) {
    is_lit[i] = valk_codegen_is_num_literal(cur->cons.head, &lits[i]);
    vals[i] = is_lit[i] ? nullptr
                        : valk_codegen_expr(c, cur->cons.head, env_param);
    cur = cur->cons.tail;
  }
  c->in_tail = saved_tail;

  LLVMValueRef num_const = LLVMConstInt(c->i64_type, LVAL_NUM, 0);
  LLVMValueRef check = LLVMConstInt(c->i1_type, 1, 0);
  for (u64 i = 0; i < argc; i++) {
    if (is_lit[i]) continue;
    LLVMValueRef ty = valk_codegen_emit_load_type_bits(c, vals[i], "arg_type");
    LLVMValueRef is_num = LLVMBuildICmp(c->builder, LLVMIntEQ, ty, num_const,
                                        "arg_is_num");
    check = LLVMBuildAnd(c->builder, check, is_num, "all_num");
  }

  LLVMValueRef fn = LLVMGetBasicBlockParent(LLVMGetInsertBlock(c->builder));
  char fast_name[32], slow_name[32], merge_name[32];
  snprintf(fast_name,  sizeof fast_name,  "num.fast.%llu",
    (unsigned long long)c->block_counter);
  snprintf(slow_name,  sizeof slow_name,  "num.slow.%llu",
    (unsigned long long)c->block_counter);
  snprintf(merge_name, sizeof merge_name, "num.merge.%llu",
    (unsigned long long)c->block_counter++);

  LLVMBasicBlockRef fast_bb  = LLVMAppendBasicBlockInContext(c->ctx, fn, fast_name);
  LLVMBasicBlockRef slow_bb  = LLVMAppendBasicBlockInContext(c->ctx, fn, slow_name);
  LLVMBasicBlockRef merge_bb = LLVMAppendBasicBlockInContext(c->ctx, fn, merge_name);

  LLVMBuildCondBr(c->builder, check, fast_bb, slow_bb);

  LLVMPositionBuilderAtEnd(c->builder, fast_bb);

  LLVMValueRef *nums = malloc(sizeof(LLVMValueRef) * argc);
  for (u64 i = 0; i < argc; i++) {
    nums[i] = is_lit[i]
      ? LLVMConstInt(c->i64_type, (u64)lits[i], 1)
      : valk_codegen_emit_load_num_field(c, vals[i], "arg_num");
  }

  LLVMValueRef fast_i64;
  bool fast_is_i1 = false;

  if (argc == 1 && is_arith) {
    if (op == BINOP_SUB) {
      LLVMValueRef zero = LLVMConstInt(c->i64_type, 0, 1);
      fast_i64 = LLVMBuildSub(c->builder, zero, nums[0], "neg");
    } else {
      fast_i64 = nums[0];
    }
  } else if (argc == 2 && !is_arith) {
    LLVMIntPredicate pred =
      (op == BINOP_LT) ? LLVMIntSLT :
      (op == BINOP_GT) ? LLVMIntSGT :
      (op == BINOP_LE) ? LLVMIntSLE :
      (op == BINOP_GE) ? LLVMIntSGE :
                         LLVMIntEQ;
    const char *nm =
      (op == BINOP_LT) ? "lt" : (op == BINOP_GT) ? "gt" :
      (op == BINOP_LE) ? "le" : (op == BINOP_GE) ? "ge" : "eq";
    fast_i64 = LLVMBuildICmp(c->builder, pred, nums[0], nums[1], nm);
    fast_is_i1 = true;
  } else {
    LLVMValueRef acc = nums[0];
    for (u64 i = 1; i < argc; i++) {
      if (op == BINOP_DIV) {
        // Only a zero divisor needs the builtin's error path. This used to
        // divert every y <= 0 to the slow path to mirror the builtin, which
        // rejected negative divisors as "Division By Zero"; both are fixed.
        LLVMValueRef zero = LLVMConstInt(c->i64_type, 0, 1);
        LLVMValueRef bad = LLVMBuildICmp(c->builder, LLVMIntEQ,
          nums[i], zero, "div_bad");
        char fast2_name[32];
        snprintf(fast2_name, sizeof fast2_name, "num.div.%llu",
          (unsigned long long)c->block_counter++);
        LLVMBasicBlockRef fast2_bb =
          LLVMAppendBasicBlockInContext(c->ctx, fn, fast2_name);
        LLVMBuildCondBr(c->builder, bad, slow_bb, fast2_bb);
        LLVMPositionBuilderAtEnd(c->builder, fast2_bb);
      }
      switch (op) {
        case BINOP_ADD: acc = LLVMBuildAdd(c->builder,  acc, nums[i], "add"); break;
        case BINOP_SUB: acc = LLVMBuildSub(c->builder,  acc, nums[i], "sub"); break;
        case BINOP_MUL: acc = LLVMBuildMul(c->builder,  acc, nums[i], "mul"); break;
        case BINOP_DIV: acc = LLVMBuildSDiv(c->builder, acc, nums[i], "div"); break;
        default: break;
      }
    }
    fast_i64 = acc;
  }

  if (fast_is_i1) {
    fast_i64 = LLVMBuildZExt(c->builder, fast_i64, c->i64_type, "cmp.ext");
  }

  free(nums);

  LLVMTypeRef num_ty = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->i64_type}, 1, 0);
  LLVMValueRef fast_val = LLVMBuildCall2(c->builder, num_ty, c->fn_lval_num,
    &fast_i64, 1, "fast.num");
  LLVMBuildBr(c->builder, merge_bb);
  LLVMBasicBlockRef fast_end = LLVMGetInsertBlock(c->builder);

  LLVMPositionBuilderAtEnd(c->builder, slow_bb);
  LLVMValueRef slow_val =
      valk_codegen_funcall(c, head, args_list, argc, env_param);
  LLVMBuildBr(c->builder, merge_bb);
  LLVMBasicBlockRef slow_end = LLVMGetInsertBlock(c->builder);

  LLVMPositionBuilderAtEnd(c->builder, merge_bb);
  LLVMValueRef phi = LLVMBuildPhi(c->builder, c->ptr_type, "num.result");
  LLVMValueRef incoming_vals[] = {fast_val, slow_val};
  LLVMBasicBlockRef incoming_bbs[] = {fast_end, slow_end};
  LLVMAddIncoming(phi, incoming_vals, incoming_bbs, 2);

  free(is_lit);
  free(lits);
  free(vals);
  return phi;
}
