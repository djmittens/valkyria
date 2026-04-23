#include "llvm_aot.h"

#include <llvm-c/Core.h>
#include <llvm-c/Error.h>
#include <llvm-c/Target.h>
#include <llvm-c/TargetMachine.h>
#include <llvm-c/Transforms/PassBuilder.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void init_all_targets(void) {
  LLVMInitializeAllTargetInfos();
  LLVMInitializeAllTargets();
  LLVMInitializeAllTargetMCs();
  LLVMInitializeAllAsmParsers();
  LLVMInitializeAllAsmPrinters();
}

static LLVMTargetMachineRef create_target_machine(char **error) {
  init_all_targets();

  char *triple = LLVMGetDefaultTargetTriple();
  LLVMTargetRef target;
  char *err = NULL;

  if (LLVMGetTargetFromTriple(triple, &target, &err)) {
    if (error) {
      size_t len = strlen(err) + 64;
      *error = malloc(len);
      snprintf(*error, len, "Failed to get target for %s: %s", triple, err);
    }
    LLVMDisposeMessage(err);
    LLVMDisposeMessage(triple);
    return NULL;
  }

  char *cpu = LLVMGetHostCPUName();
  char *features = LLVMGetHostCPUFeatures();

  LLVMTargetMachineRef tm = LLVMCreateTargetMachine(
    target, triple, cpu, features,
    LLVMCodeGenLevelDefault,
    LLVMRelocPIC,
    LLVMCodeModelDefault);


  LLVMDisposeMessage(triple);
  LLVMDisposeMessage(cpu);
  LLVMDisposeMessage(features);

  return tm;
}

int valk_aot_emit_object(valk_llvm_ctx_t *ctx, const char *output_path) {
  char *err = NULL;
  LLVMTargetMachineRef tm = create_target_machine(&err);
  if (!tm) {
    fprintf(stderr, "AOT: %s\n", err ? err : "unknown error");
    free(err);
    return -1;
  }

  char *triple = LLVMGetDefaultTargetTriple();
  LLVMSetTarget(ctx->module, triple);
  LLVMSetModuleDataLayout(ctx->module,
    LLVMCreateTargetDataLayout(tm));
  LLVMDisposeMessage(triple);

  char *error = NULL;
  if (LLVMTargetMachineEmitToFile(tm, ctx->module,
      (char *)output_path, LLVMObjectFile, &error)) {
    fprintf(stderr, "AOT emit object failed: %s\n",
      error ? error : "unknown");
    if (error) LLVMDisposeMessage(error);
    LLVMDisposeTargetMachine(tm);
    return -1;
  }

  LLVMDisposeTargetMachine(tm);
  return 0;
}

int valk_aot_emit_ir(valk_llvm_ctx_t *ctx, const char *output_path) {
  char *error = NULL;
  if (LLVMPrintModuleToFile(ctx->module, output_path, &error)) {
    fprintf(stderr, "AOT emit IR failed: %s\n", error ? error : "unknown");
    if (error) LLVMDisposeMessage(error);
    return -1;
  }
  return 0;
}

int valk_aot_optimize(valk_llvm_ctx_t *ctx) {
  char *err = NULL;
  LLVMTargetMachineRef tm = create_target_machine(&err);
  if (!tm) {
    fprintf(stderr, "AOT optimize: %s\n", err ? err : "unknown error");
    free(err);
    return -1;
  }

  char *triple = LLVMGetDefaultTargetTriple();
  LLVMSetTarget(ctx->module, triple);
  LLVMSetModuleDataLayout(ctx->module, LLVMCreateTargetDataLayout(tm));
  LLVMDisposeMessage(triple);

  LLVMPassBuilderOptionsRef opts = LLVMCreatePassBuilderOptions();
  LLVMErrorRef perr = LLVMRunPasses(ctx->module, "default<O2>", tm, opts);
  LLVMDisposePassBuilderOptions(opts);
  LLVMDisposeTargetMachine(tm);

  if (perr) {
    char *msg = LLVMGetErrorMessage(perr);
    fprintf(stderr, "AOT optimize: %s\n", msg ? msg : "unknown");
    LLVMDisposeErrorMessage(msg);
    return -1;
  }
  return 0;
}

int valk_aot_emit_asm(valk_llvm_ctx_t *ctx, const char *output_path) {
  char *err = NULL;
  LLVMTargetMachineRef tm = create_target_machine(&err);
  if (!tm) {
    fprintf(stderr, "AOT: %s\n", err ? err : "unknown error");
    free(err);
    return -1;
  }

  char *triple = LLVMGetDefaultTargetTriple();
  LLVMSetTarget(ctx->module, triple);
  LLVMSetModuleDataLayout(ctx->module,
    LLVMCreateTargetDataLayout(tm));
  LLVMDisposeMessage(triple);

  char *error = NULL;
  if (LLVMTargetMachineEmitToFile(tm, ctx->module,
      (char *)output_path, LLVMAssemblyFile, &error)) {
    fprintf(stderr, "AOT emit asm failed: %s\n", error ? error : "unknown");
    if (error) LLVMDisposeMessage(error);
    LLVMDisposeTargetMachine(tm);
    return -1;
  }

  LLVMDisposeTargetMachine(tm);
  return 0;
}
