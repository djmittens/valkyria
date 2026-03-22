#pragma once
#include "llvm_codegen.h"

int valk_aot_emit_object(valk_llvm_ctx_t *ctx, const char *output_path);
int valk_aot_emit_ir(valk_llvm_ctx_t *ctx, const char *output_path);
int valk_aot_emit_asm(valk_llvm_ctx_t *ctx, const char *output_path);
