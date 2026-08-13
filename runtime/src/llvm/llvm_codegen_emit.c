#include "llvm_codegen_internal.h"
#include "../builtins_internal.h"
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

LLVMValueRef valk_codegen_emit_global_string(valk_llvm_ctx_t *c, const char *str) {
  char name[64];
  snprintf(name, sizeof(name), ".str.%llu",
           (unsigned long long)c->str_counter++);
  return LLVMBuildGlobalStringPtr(c->builder, str, name);
}

LLVMValueRef valk_codegen_emit_make_sym_inline(valk_llvm_ctx_t *c,
                                               const char *name) {
  LLVMValueRef str = valk_codegen_emit_global_string(c, name);
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type}, 1, 0);
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_sym, &str, 1, "sym");
}

LLVMValueRef valk_codegen_emit_make_sym(valk_llvm_ctx_t *c, const char *name) {
  if (!c->sym_cache.anchor_bb) {
    return valk_codegen_emit_make_sym_inline(c, name);
  }
  for (size_t i = 0; i < c->sym_cache.count; i++) {
    if (strcmp(c->sym_cache.names[i], name) == 0) {
      return c->sym_cache.vals[i];
    }
  }

  LLVMBasicBlockRef saved_bb = LLVMGetInsertBlock(c->builder);
  LLVMValueRef term = LLVMGetBasicBlockTerminator(c->sym_cache.anchor_bb);
  if (term) {
    LLVMPositionBuilderBefore(c->builder, term);
  } else {
    LLVMPositionBuilderAtEnd(c->builder, c->sym_cache.anchor_bb);
  }
  LLVMValueRef sym = valk_codegen_emit_make_sym_inline(c, name);
  LLVMPositionBuilderAtEnd(c->builder, saved_bb);

  if (c->sym_cache.count == c->sym_cache.cap) {
    c->sym_cache.cap = c->sym_cache.cap ? c->sym_cache.cap * 2 : 8;
    c->sym_cache.names = realloc(c->sym_cache.names,
      c->sym_cache.cap * sizeof(*c->sym_cache.names));
    c->sym_cache.vals = realloc(c->sym_cache.vals,
      c->sym_cache.cap * sizeof(*c->sym_cache.vals));
  }
  c->sym_cache.names[c->sym_cache.count] = strdup(name);
  c->sym_cache.vals[c->sym_cache.count] = sym;
  c->sym_cache.count++;
  return sym;
}

void valk_codegen_sym_cache_enter(valk_llvm_ctx_t *c, LLVMBasicBlockRef anchor) {
  c->sym_cache.anchor_bb = anchor;
}

void valk_codegen_sym_cache_leave(valk_llvm_ctx_t *c) {
  for (size_t i = 0; i < c->sym_cache.count; i++) {
    free(c->sym_cache.names[i]);
  }
  free(c->sym_cache.names);
  free(c->sym_cache.vals);
  c->sym_cache.anchor_bb = nullptr;
  c->sym_cache.names = nullptr;
  c->sym_cache.vals = nullptr;
  c->sym_cache.count = 0;
  c->sym_cache.cap = 0;
}

LLVMValueRef valk_codegen_build_qcons_list(valk_llvm_ctx_t *c,
                                           LLVMValueRef *items, u64 count) {
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
  LLVMValueRef list = LLVMBuildCall2(c->builder, fn_type,
    c->fn_lval_nil, NULL, 0, "nil");

  LLVMTypeRef qcons_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type}, 2, 0);

  for (i64 i = (i64)count - 1; i >= 0; i--) {
    LLVMValueRef args[] = {items[i], list};
    list = LLVMBuildCall2(c->builder, qcons_type, c->fn_lval_qcons,
      args, 2, "qcons");
  }
  return list;
}

LLVMValueRef valk_codegen_build_cons_list(valk_llvm_ctx_t *c,
                                          LLVMValueRef *items, u64 count,
                                          bool quoted) {
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
  LLVMValueRef list = LLVMBuildCall2(c->builder, fn_type,
    c->fn_lval_nil, NULL, 0, "nil");

  LLVMValueRef cons_fn = quoted ? c->fn_lval_qcons : c->fn_lval_cons;
  LLVMTypeRef cons_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type}, 2, 0);

  for (i64 i = (i64)count - 1; i >= 0; i--) {
    LLVMValueRef args[] = {items[i], list};
    list = LLVMBuildCall2(c->builder, cons_type, cons_fn,
      args, 2, quoted ? "qcons" : "cons");
  }
  return list;
}

u64 valk_codegen_cons_list_len(valk_lval_t *list) {
  u64 n = 0;
  while (list && LVAL_TYPE(list) == LVAL_CONS) {
    n++;
    list = list->cons.tail;
  }
  return n;
}

valk_lval_t *valk_codegen_cons_list_nth(valk_lval_t *list, u64 idx) {
  for (u64 i = 0; i < idx; i++) {
    list = list->cons.tail;
  }
  return list->cons.head;
}

bool valk_codegen_is_sym(valk_lval_t *expr, const char *name) {
  return LVAL_TYPE(expr) == LVAL_SYM && strcmp(expr->str, name) == 0;
}

bool valk_codegen_is_num_literal(valk_lval_t *expr, i64 *out) {
  if (!expr || LVAL_TYPE(expr) != LVAL_NUM) return false;
  *out = expr->num;
  return true;
}

valk_lval_t *valk_codegen_unwrap_branch_qexpr(valk_lval_t *branch,
                                              bool *out_single) {
  if (out_single) *out_single = false;
  if (!branch) return branch;
  if (LVAL_TYPE(branch) != LVAL_CONS) return branch;
  if (!(branch->flags & LVAL_FLAG_QUOTED)) return branch;
  valk_lval_t *cons = valk_qexpr_to_cons(branch);
  if (cons && LVAL_TYPE(cons) == LVAL_CONS && cons->cons.tail &&
      LVAL_TYPE(cons->cons.tail) == LVAL_NIL) {
    // A one-element branch keeps one-element S-expression semantics: the
    // caller must emit the zero-arg apply, not just the element's value.
    if (out_single) *out_single = true;
    return cons->cons.head;
  }
  return cons;
}

LLVMValueRef valk_codegen_emit_load_num_field(valk_llvm_ctx_t *c,
                                              LLVMValueRef lval_ptr,
                                              const char *name) {
  LLVMValueRef off = LLVMConstInt(c->i64_type, offsetof(valk_lval_t, num), 0);
  LLVMValueRef fp = LLVMBuildInBoundsGEP2(c->builder, c->i8_type,
    lval_ptr, &off, 1, "num_ptr");
  return LLVMBuildLoad2(c->builder, c->i64_type, fp, name);
}

LLVMValueRef valk_codegen_emit_load_type_bits(valk_llvm_ctx_t *c,
                                              LLVMValueRef lval_ptr,
                                              const char *name) {
  LLVMValueRef off = LLVMConstInt(c->i64_type, offsetof(valk_lval_t, flags), 0);
  LLVMValueRef fp = LLVMBuildInBoundsGEP2(c->builder, c->i8_type,
    lval_ptr, &off, 1, "flags_ptr");
  LLVMValueRef flags = LLVMBuildLoad2(c->builder, c->i64_type, fp, "flags");
  LLVMValueRef mask = LLVMConstInt(c->i64_type, LVAL_TYPE_MASK, 0);
  return LLVMBuildAnd(c->builder, flags, mask, name);
}

LLVMValueRef valk_codegen_num(valk_llvm_ctx_t *c, valk_lval_t *expr) {
  LLVMValueRef val = LLVMConstInt(c->i64_type, (u64)expr->num, 1);
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->i64_type}, 1, 0);
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_num, &val, 1, "num");
}

LLVMValueRef valk_codegen_str(valk_llvm_ctx_t *c, valk_lval_t *expr) {
  LLVMValueRef str = valk_codegen_emit_global_string(c, expr->str);
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type}, 1, 0);
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_str, &str, 1, "str");
}

LLVMValueRef valk_codegen_nil(valk_llvm_ctx_t *c) {
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_nil, NULL, 0, "nil");
}

LLVMValueRef valk_codegen_sym_lookup(valk_llvm_ctx_t *c, valk_lval_t *expr,
                                     LLVMValueRef env_param) {
  if (expr->str && expr->str[0] == ':') {
    return valk_codegen_emit_make_sym(c, expr->str);
  }
  if (c->formals_map.count && expr->str) {
    for (size_t i = 0; i < c->formals_map.count; i++) {
      if (strcmp(c->formals_map.names[i], expr->str) == 0) {
        return c->formals_map.vals[i];
      }
    }
  }
  LLVMValueRef sym = valk_codegen_emit_make_sym(c, expr->str);
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type}, 2, 0);
  LLVMValueRef args[] = {env_param, sym};
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lenv_get, args, 2, "lookup");
}

LLVMValueRef valk_codegen_literal(valk_llvm_ctx_t *c, valk_lval_t *expr) {
  if (!expr) return valk_codegen_nil(c);

  switch (LVAL_TYPE(expr)) {
    case LVAL_NUM:
      return valk_codegen_num(c, expr);
    case LVAL_STR:
      return valk_codegen_str(c, expr);
    case LVAL_NIL:
      return valk_codegen_nil(c);
    case LVAL_SYM:
      return valk_codegen_emit_make_sym(c, expr->str);
    case LVAL_CONS: {
      bool quoted = (expr->flags & LVAL_FLAG_QUOTED) != 0;
      u64 len = valk_codegen_cons_list_len(expr);
      LLVMValueRef *items = malloc(sizeof(LLVMValueRef) * len);
      valk_lval_t *cur = expr;
      for (u64 i = 0; i < len; i++) {
        items[i] = valk_codegen_literal(c, cur->cons.head);
        cur = cur->cons.tail;
      }
      LLVMValueRef result = valk_codegen_build_cons_list(c, items, len, quoted);
      free(items);
      return result;
    }
    default:
      return valk_codegen_nil(c);
  }
}

LLVMValueRef valk_codegen_qexpr(valk_llvm_ctx_t *c, valk_lval_t *expr,
                                __attribute__((unused)) LLVMValueRef env_param) {
  return valk_codegen_literal(c, expr);
}
