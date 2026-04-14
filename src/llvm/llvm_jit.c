#include "llvm_jit.h"
#include "llvm_codegen.h"

#include <llvm-c/Analysis.h>
#include <llvm-c/Core.h>
#include <llvm-c/LLJIT.h>
#include <llvm-c/Orc.h>
#include <llvm-c/OrcEE.h>
#include <llvm-c/Target.h>
#include <llvm-c/TargetMachine.h>

#include <stdio.h>
#include <stdlib.h>

struct valk_jit_t {
  LLVMOrcLLJITRef lljit;
  u64 module_counter;
};

static bool llvm_initialized = false;

void valk_llvm_init(void) {
  if (llvm_initialized) return;
  LLVMInitializeNativeTarget();
  LLVMInitializeNativeAsmPrinter();
  LLVMInitializeNativeAsmParser();
  llvm_initialized = true;
}

void valk_llvm_init_reset(void) {
  llvm_initialized = false;
  valk_llvm_init();
}

static void check_error(LLVMErrorRef err, const char *context) {
  if (!err) return;
  char *msg = LLVMGetErrorMessage(err);
  fprintf(stderr, "LLVM JIT error (%s): %s\n", context, msg);
  LLVMDisposeErrorMessage(msg);
}

valk_jit_t *valk_jit_new(void) {
  valk_llvm_init();

  valk_jit_t *jit = calloc(1, sizeof(valk_jit_t));

  LLVMOrcLLJITBuilderRef builder = LLVMOrcCreateLLJITBuilder();
  LLVMErrorRef err = LLVMOrcCreateLLJIT(&jit->lljit, builder);
  if (err) {
    check_error(err, "LLVMOrcCreateLLJIT");
    free(jit);
    return NULL;
  }

  LLVMOrcJITDylibRef main_dylib = LLVMOrcLLJITGetMainJITDylib(jit->lljit);

  LLVMOrcDefinitionGeneratorRef gen;
  err = LLVMOrcCreateDynamicLibrarySearchGeneratorForProcess(
    &gen, LLVMOrcLLJITGetGlobalPrefix(jit->lljit), NULL, NULL);
  if (err) {
    check_error(err, "CreateDynamicLibrarySearchGenerator");
    LLVMOrcDisposeLLJIT(jit->lljit);
    free(jit);
    return NULL;
  }
  LLVMOrcJITDylibAddGenerator(main_dylib, gen);

  return jit;
}

void valk_jit_free(valk_jit_t *jit) {
  if (!jit) return;
  if (jit->lljit) {
    LLVMErrorRef err = LLVMOrcDisposeLLJIT(jit->lljit);
    if (err) check_error(err, "LLVMOrcDisposeLLJIT");
  }
  free(jit);
}

typedef valk_lval_t *(*jit_expr_fn_t)(valk_lenv_t *);

static void init_codegen_decls(valk_llvm_ctx_t *c) {
  valk_llvm_declare_runtime_fns(c);
}

valk_lval_t *valk_jit_eval(valk_jit_t *jit, valk_lenv_t *env,
                           valk_lval_t *expr) {
  if (!jit || !expr) return valk_lval_err("JIT: null argument");

  LLVMContextRef llvm_ctx = LLVMContextCreate();

  char mod_name[64];
  snprintf(mod_name, sizeof(mod_name), "jit_mod_%llu",
    (unsigned long long)jit->module_counter);

  valk_llvm_ctx_t codegen = {0};
  codegen.ctx = llvm_ctx;
  codegen.module = LLVMModuleCreateWithNameInContext(mod_name, llvm_ctx);
  codegen.builder = LLVMCreateBuilderInContext(llvm_ctx);
  codegen.ptr_type = LLVMPointerTypeInContext(llvm_ctx, 0);
  codegen.i64_type = LLVMInt64TypeInContext(llvm_ctx);
  codegen.i8_type = LLVMInt8TypeInContext(llvm_ctx);
  codegen.i1_type = LLVMInt1TypeInContext(llvm_ctx);
  codegen.void_type = LLVMVoidTypeInContext(llvm_ctx);

  init_codegen_decls(&codegen);

  char fn_name[64];
  snprintf(fn_name, sizeof(fn_name), "__jit_eval_%llu",
    (unsigned long long)jit->module_counter++);

  LLVMTypeRef fn_type = LLVMFunctionType(codegen.ptr_type,
    (LLVMTypeRef[]){codegen.ptr_type}, 1, 0);
  LLVMValueRef fn = LLVMAddFunction(codegen.module, fn_name, fn_type);
  LLVMSetLinkage(fn, LLVMExternalLinkage);

  LLVMBasicBlockRef entry = LLVMAppendBasicBlockInContext(llvm_ctx, fn, "entry");
  LLVMPositionBuilderAtEnd(codegen.builder, entry);

  LLVMValueRef env_param = LLVMGetParam(fn, 0);
  LLVMValueRef result = valk_llvm_compile_expr(&codegen, expr, env_param);
  LLVMBuildRet(codegen.builder, result);

  char *verify_err = NULL;
  LLVMBool failed = LLVMVerifyModule(codegen.module,
    LLVMReturnStatusAction, &verify_err);
  if (failed) {
    char *ir = LLVMPrintModuleToString(codegen.module);
    fprintf(stderr, "JIT verify failed: %s\nIR:\n%s\n", verify_err, ir);
    LLVMDisposeMessage(ir);
    if (verify_err) LLVMDisposeMessage(verify_err);
    LLVMDisposeBuilder(codegen.builder);
    LLVMDisposeModule(codegen.module);
    LLVMContextDispose(llvm_ctx);
    return valk_lval_err("JIT: module verification failed");
  }
  if (verify_err) LLVMDisposeMessage(verify_err);

  LLVMDisposeBuilder(codegen.builder);

  LLVMOrcThreadSafeContextRef ts_ctx =
    LLVMOrcCreateNewThreadSafeContextFromLLVMContext(llvm_ctx);
  LLVMOrcThreadSafeModuleRef tsm =
    LLVMOrcCreateNewThreadSafeModule(codegen.module, ts_ctx);
  LLVMOrcDisposeThreadSafeContext(ts_ctx);

  LLVMOrcJITDylibRef main_dylib = LLVMOrcLLJITGetMainJITDylib(jit->lljit);
  LLVMOrcResourceTrackerRef rt =
    LLVMOrcJITDylibCreateResourceTracker(main_dylib);

  LLVMErrorRef err = LLVMOrcLLJITAddLLVMIRModuleWithRT(jit->lljit, rt, tsm);
  if (err) {
    check_error(err, "AddLLVMIRModule");
    LLVMOrcReleaseResourceTracker(rt);
    return valk_lval_err("JIT: failed to add module");
  }

  LLVMOrcExecutorAddress addr = 0;
  err = LLVMOrcLLJITLookup(jit->lljit, &addr, fn_name);
  if (err) {
    check_error(err, "LLVMOrcLLJITLookup");
    LLVMOrcResourceTrackerRemove(rt);
    LLVMOrcReleaseResourceTracker(rt);
    return valk_lval_err("JIT: symbol lookup failed");
  }

  jit_expr_fn_t compiled = (jit_expr_fn_t)addr;
  valk_lval_t *result_val = compiled(env);

  LLVMOrcResourceTrackerRemove(rt);
  LLVMOrcReleaseResourceTracker(rt);

  return result_val;
}

valk_lval_t *valk_jit_eval_string(valk_jit_t *jit, valk_lenv_t *env,
                                  const char *code) {
  valk_lval_t *ast = valk_parse_text(code);
  if (!ast || LVAL_TYPE(ast) == LVAL_ERR) return ast;

  if (LVAL_TYPE(ast) == LVAL_CONS) {
    valk_lval_t *result = NULL;
    valk_lval_t *cur = ast;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      result = valk_jit_eval(jit, env, cur->cons.head);
      if (LVAL_TYPE(result) == LVAL_ERR) return result;
      cur = cur->cons.tail;
    }
    return result;
  }

  return valk_jit_eval(jit, env, ast);
}
