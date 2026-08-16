#pragma once
#include "llvm_codegen.h"
#include "../vir/vir.h"

void vir_to_llvm_module(valk_llvm_ctx_t *ctx, vir_module_t *vmod);
LLVMValueRef vir_to_llvm_func(valk_llvm_ctx_t *ctx, vir_func_t *fn);
