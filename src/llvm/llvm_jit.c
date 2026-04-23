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
#include <string.h>

typedef valk_lval_t *(*jit_expr_fn_t)(valk_lenv_t *);

typedef struct {
  char *source;              // strdup'd key
  jit_expr_fn_t fn;          // compiled entry
  LLVMOrcResourceTrackerRef rt;  // owns the module; released at jit_free
} jit_cache_entry_t;

struct valk_jit_t {
  LLVMOrcLLJITRef lljit;
  u64 module_counter;
  jit_cache_entry_t *cache;
  u64 cache_len;
  u64 cache_cap;
  u64 cache_hits;             // diagnostics / test introspection
  u64 cache_misses;
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
  for (u64 i = 0; i < jit->cache_len; i++) {
    if (jit->cache[i].rt) {
      LLVMOrcResourceTrackerRemove(jit->cache[i].rt);
      LLVMOrcReleaseResourceTracker(jit->cache[i].rt);
    }
    free(jit->cache[i].source);
  }
  free(jit->cache);
  if (jit->lljit) {
    LLVMErrorRef err = LLVMOrcDisposeLLJIT(jit->lljit);
    if (err) check_error(err, "LLVMOrcDisposeLLJIT");
  }
  free(jit);
}

static jit_cache_entry_t *jit_cache_lookup(valk_jit_t *jit, const char *src) {
  for (u64 i = 0; i < jit->cache_len; i++) {
    if (strcmp(jit->cache[i].source, src) == 0) return &jit->cache[i];
  }
  return NULL;
}

static void jit_cache_insert(valk_jit_t *jit, const char *src,
                             jit_expr_fn_t fn, LLVMOrcResourceTrackerRef rt) {
  if (jit->cache_len == jit->cache_cap) {
    u64 ncap = jit->cache_cap ? jit->cache_cap * 2 : 8;
    jit->cache = realloc(jit->cache, ncap * sizeof(jit_cache_entry_t));
    jit->cache_cap = ncap;
  }
  jit->cache[jit->cache_len].source = strdup(src);
  jit->cache[jit->cache_len].fn = fn;
  jit->cache[jit->cache_len].rt = rt;
  jit->cache_len++;
}

u64 valk_jit_cache_hits(valk_jit_t *jit) {
  return jit ? jit->cache_hits : 0;
}
u64 valk_jit_cache_misses(valk_jit_t *jit) {
  return jit ? jit->cache_misses : 0;
}

static void init_codegen_decls(valk_llvm_ctx_t *c) {
  valk_llvm_declare_runtime_fns(c);
}

// Codegen core: set up a fresh LLVMContext/Module and an entry function
// (ptr -> ptr). Caller supplies body_emit to fill in the function body.
static bool jit_emit_module(valk_jit_t *jit, bool is_program,
                            valk_lval_t *ast,
                            LLVMContextRef *ctx_out, LLVMModuleRef *mod_out,
                            char *fn_name_out, size_t fn_name_cap) {
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

  snprintf(fn_name_out, fn_name_cap, "__jit_eval_%llu",
    (unsigned long long)jit->module_counter++);

  LLVMTypeRef fn_type = LLVMFunctionType(codegen.ptr_type,
    (LLVMTypeRef[]){codegen.ptr_type}, 1, 0);
  LLVMValueRef fn = LLVMAddFunction(codegen.module, fn_name_out, fn_type);
  LLVMSetLinkage(fn, LLVMExternalLinkage);

  LLVMBasicBlockRef entry = LLVMAppendBasicBlockInContext(llvm_ctx, fn, "entry");
  LLVMPositionBuilderAtEnd(codegen.builder, entry);
  LLVMValueRef env_param = LLVMGetParam(fn, 0);

  LLVMValueRef result = NULL;
  if (is_program) {
    // ast is a parser-returned cons list of top-level forms. Emit each
    // inline; the return value is the last form's value.
    valk_lval_t *cur = ast;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      result = valk_llvm_compile_expr(&codegen, cur->cons.head, env_param);
      cur = cur->cons.tail;
    }
    if (!result) {
      // Empty program: return nil.
      LLVMTypeRef nil_type = LLVMFunctionType(codegen.ptr_type, NULL, 0, 0);
      result = LLVMBuildCall2(codegen.builder, nil_type,
        codegen.fn_lval_nil, NULL, 0, "nil");
    }
  } else {
    result = valk_llvm_compile_expr(&codegen, ast, env_param);
  }
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
    return false;
  }
  if (verify_err) LLVMDisposeMessage(verify_err);

  LLVMDisposeBuilder(codegen.builder);
  *ctx_out = llvm_ctx;
  *mod_out = codegen.module;
  return true;
}

// Install a freshly-emitted module into the JIT under a new ResourceTracker.
// Returns the compiled fn + rt. Ownership of the context/module is transferred
// to the JIT on success; on failure they are disposed here.
static bool jit_install_module(valk_jit_t *jit, LLVMContextRef llvm_ctx,
                               LLVMModuleRef module, const char *fn_name,
                               jit_expr_fn_t *fn_out,
                               LLVMOrcResourceTrackerRef *rt_out) {
  LLVMOrcThreadSafeContextRef ts_ctx =
    LLVMOrcCreateNewThreadSafeContextFromLLVMContext(llvm_ctx);
  LLVMOrcThreadSafeModuleRef tsm =
    LLVMOrcCreateNewThreadSafeModule(module, ts_ctx);
  LLVMOrcDisposeThreadSafeContext(ts_ctx);

  LLVMOrcJITDylibRef main_dylib = LLVMOrcLLJITGetMainJITDylib(jit->lljit);
  LLVMOrcResourceTrackerRef rt =
    LLVMOrcJITDylibCreateResourceTracker(main_dylib);

  LLVMErrorRef err = LLVMOrcLLJITAddLLVMIRModuleWithRT(jit->lljit, rt, tsm);
  if (err) {
    check_error(err, "AddLLVMIRModule");
    LLVMOrcReleaseResourceTracker(rt);
    return false;
  }

  LLVMOrcExecutorAddress addr = 0;
  err = LLVMOrcLLJITLookup(jit->lljit, &addr, fn_name);
  if (err) {
    check_error(err, "LLVMOrcLLJITLookup");
    LLVMOrcResourceTrackerRemove(rt);
    LLVMOrcReleaseResourceTracker(rt);
    return false;
  }

  *fn_out = (jit_expr_fn_t)addr;
  *rt_out = rt;
  return true;
}

valk_lval_t *valk_jit_eval(valk_jit_t *jit, valk_lenv_t *env,
                           valk_lval_t *expr) {
  if (!jit || !expr) return valk_lval_err("JIT: null argument");

  LLVMContextRef llvm_ctx = NULL;
  LLVMModuleRef module = NULL;
  char fn_name[64];
  if (!jit_emit_module(jit, false, expr, &llvm_ctx, &module,
                       fn_name, sizeof(fn_name)))
    return valk_lval_err("JIT: module verification failed");

  jit_expr_fn_t compiled;
  LLVMOrcResourceTrackerRef rt;
  if (!jit_install_module(jit, llvm_ctx, module, fn_name, &compiled, &rt))
    return valk_lval_err("JIT: install failed");

  valk_lval_t *result_val = compiled(env);
  LLVMOrcResourceTrackerRemove(rt);
  LLVMOrcReleaseResourceTracker(rt);
  return result_val;
}

valk_lval_t *valk_jit_eval_string(valk_jit_t *jit, valk_lenv_t *env,
                                  const char *code) {
  if (!jit || !code) return valk_lval_err("JIT: null argument");

  jit_cache_entry_t *hit = jit_cache_lookup(jit, code);
  if (hit) {
    jit->cache_hits++;
    return hit->fn(env);
  }
  jit->cache_misses++;

  valk_lval_t *ast = valk_parse_text(code);
  if (!ast || LVAL_TYPE(ast) == LVAL_ERR) return ast;

  LLVMContextRef llvm_ctx = NULL;
  LLVMModuleRef module = NULL;
  char fn_name[64];
  if (!jit_emit_module(jit, true, ast, &llvm_ctx, &module,
                       fn_name, sizeof(fn_name)))
    return valk_lval_err("JIT: module verification failed");

  jit_expr_fn_t compiled;
  LLVMOrcResourceTrackerRef rt;
  if (!jit_install_module(jit, llvm_ctx, module, fn_name, &compiled, &rt))
    return valk_lval_err("JIT: install failed");

  jit_cache_insert(jit, code, compiled, rt);
  return compiled(env);
}
