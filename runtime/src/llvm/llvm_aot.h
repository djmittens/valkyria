#pragma once
#include "llvm_codegen.h"

int valk_aot_emit_object(valk_llvm_ctx_t *ctx, const char *output_path);
int valk_aot_emit_ir(valk_llvm_ctx_t *ctx, const char *output_path);
int valk_aot_emit_asm(valk_llvm_ctx_t *ctx, const char *output_path);

// Run the LLVM new-PM `default<O2>` pipeline over the AOT module.
// Prunes dead blocks (e.g. tco.dead), inlines runtime-function calls
// that have been marked readonly, folds constants, converts eligible
// direct calls to sibcalls, etc. Returns 0 on success, -1 on failure.
int valk_aot_optimize(valk_llvm_ctx_t *ctx);
