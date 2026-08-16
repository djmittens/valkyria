#include "llvm_jit.h"
#include "llvm_codegen.h"

#include <llvm-c/Analysis.h>
#include <llvm-c/Core.h>
#include <llvm-c/LLJIT.h>
#include <llvm-c/Orc.h>
#include <llvm-c/OrcEE.h>
#include <llvm-c/Target.h>
#include <llvm-c/TargetMachine.h>

#include <ctype.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef valk_lval_t *(*jit_expr_fn_t)(valk_lenv_t *);

typedef struct {
  char *source;              // normalized strdup'd key
  jit_expr_fn_t fn;          // compiled entry
  LLVMOrcResourceTrackerRef rt;  // owns the module; released at jit_free
  u64 last_used;             // monotonic stamp for LRU eviction
} jit_cache_entry_t;

// Hard cap on cache entries. Without a cap the LSP/REPL accumulates an
// entry per distinct source string ever JIT'd — pinned modules included
// — for the JIT's lifetime. 1024 fits comfortably for an interactive
// session and bounds resident memory.
#define VALK_JIT_CACHE_MAX 1024

struct valk_jit_t {
  LLVMOrcLLJITRef lljit;
  u64 module_counter;
  jit_cache_entry_t *cache;
  u64 cache_len;
  u64 cache_cap;
  u64 cache_hits;             // diagnostics / test introspection
  u64 cache_misses;
  u64 lru_clock;              // monotonic time-stamp source for LRU
  pthread_mutex_t lock;       // protects cache + lljit (LLJIT add+lookup
                              // are not documented thread-safe)
};

// Whitespace-collapse normalizer: maps any run of horizontal/vertical
// whitespace to a single space, drops line comments. Two source strings
// that differ only in formatting share a cache entry. NOT a full tokeniser
// — it doesn't know strings, so a literal `; foo` inside a "..." would be
// stripped — but Valkyria source uses `;` for line comments only, and the
// JIT cache keys what users actually type into a REPL/LSP, where this
// suffices in practice.
static char *normalize_source(const char *src) {
  size_t n = strlen(src);
  char *out = malloc(n + 1);
  if (!out) return NULL;
  size_t j = 0;
  bool in_ws = true;
  for (size_t i = 0; i < n;) {
    char c = src[i];
    if (c == ';') {
      while (i < n && src[i] != '\n') i++;
      continue;
    }
    if (isspace((unsigned char)c)) {
      if (!in_ws) { out[j++] = ' '; in_ws = true; }
      i++;
      continue;
    }
    out[j++] = c;
    in_ws = false;
    i++;
  }
  while (j > 0 && out[j - 1] == ' ') j--;
  out[j] = 0;
  return out;
}

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
  pthread_mutex_init(&jit->lock, NULL);

  LLVMOrcLLJITBuilderRef builder = LLVMOrcCreateLLJITBuilder();
  LLVMErrorRef err = LLVMOrcCreateLLJIT(&jit->lljit, builder);
  if (err) {
    check_error(err, "LLVMOrcCreateLLJIT");
    pthread_mutex_destroy(&jit->lock);
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
  pthread_mutex_destroy(&jit->lock);
  free(jit);
}

// Caller must hold jit->lock.
static jit_cache_entry_t *jit_cache_lookup(valk_jit_t *jit, const char *src) {
  for (u64 i = 0; i < jit->cache_len; i++) {
    if (strcmp(jit->cache[i].source, src) == 0) return &jit->cache[i];
  }
  return NULL;
}

// Caller must hold jit->lock. Evicts the LRU entry (releasing its module
// from the JIT and its source string) to make room.
static void jit_cache_evict_one(valk_jit_t *jit) {
  if (jit->cache_len == 0) return;
  u64 victim = 0;
  u64 oldest = jit->cache[0].last_used;
  for (u64 i = 1; i < jit->cache_len; i++) {
    if (jit->cache[i].last_used < oldest) {
      oldest = jit->cache[i].last_used;
      victim = i;
    }
  }
  if (jit->cache[victim].rt) {
    LLVMOrcResourceTrackerRemove(jit->cache[victim].rt);
    LLVMOrcReleaseResourceTracker(jit->cache[victim].rt);
  }
  free(jit->cache[victim].source);
  jit->cache[victim] = jit->cache[jit->cache_len - 1];
  jit->cache_len--;
}

// Caller must hold jit->lock. Takes ownership of `src` (already strdup'd
// or normalized; the entry stores it directly without copying).
static bool jit_cache_insert(valk_jit_t *jit, char *src,
                             jit_expr_fn_t fn, LLVMOrcResourceTrackerRef rt) {
  while (jit->cache_len >= VALK_JIT_CACHE_MAX) {
    jit_cache_evict_one(jit);
  }
  if (jit->cache_len == jit->cache_cap) {
    u64 ncap = jit->cache_cap ? jit->cache_cap * 2 : 8;
    if (ncap > VALK_JIT_CACHE_MAX) ncap = VALK_JIT_CACHE_MAX;
    jit_cache_entry_t *nc =
        realloc(jit->cache, ncap * sizeof(jit_cache_entry_t));
    if (!nc) {
      free(src);
      return false;
    }
    jit->cache = nc;
    jit->cache_cap = ncap;
  }
  jit->cache[jit->cache_len].source = src;
  jit->cache[jit->cache_len].fn = fn;
  jit->cache[jit->cache_len].rt = rt;
  jit->cache[jit->cache_len].last_used = ++jit->lru_clock;
  jit->cache_len++;
  return true;
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
// to the JIT on success; on failure they are disposed here. Caller must
// hold jit->lock.
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
    // tsm ownership transfers to the JIT only on success; dispose
    // here on failure to avoid leaking the context+module pair.
    LLVMOrcDisposeThreadSafeModule(tsm);
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

  pthread_mutex_lock(&jit->lock);

  LLVMContextRef llvm_ctx = NULL;
  LLVMModuleRef module = NULL;
  char fn_name[64];
  if (!jit_emit_module(jit, false, expr, &llvm_ctx, &module,
                       fn_name, sizeof(fn_name))) {
    pthread_mutex_unlock(&jit->lock);
    return valk_lval_err("JIT: module verification failed");
  }

  jit_expr_fn_t compiled;
  LLVMOrcResourceTrackerRef rt;
  if (!jit_install_module(jit, llvm_ctx, module, fn_name, &compiled, &rt)) {
    pthread_mutex_unlock(&jit->lock);
    return valk_lval_err("JIT: install failed");
  }

  pthread_mutex_unlock(&jit->lock);

  valk_lval_t *result_val = compiled(env);

  pthread_mutex_lock(&jit->lock);
  LLVMOrcResourceTrackerRemove(rt);
  LLVMOrcReleaseResourceTracker(rt);
  pthread_mutex_unlock(&jit->lock);
  return result_val;
}

valk_lval_t *valk_jit_eval_string(valk_jit_t *jit, valk_lenv_t *env,
                                  const char *code) {
  if (!jit || !code) return valk_lval_err("JIT: null argument");

  // Normalize once: this is what we key the cache by, not the raw input.
  // `(+ 1 2)` and `(+  1 2)` and `(+ 1 2)\n; comment` all share an entry.
  char *norm = normalize_source(code);
  if (!norm) return valk_lval_err("JIT: out of memory");

  pthread_mutex_lock(&jit->lock);
  jit_cache_entry_t *hit = jit_cache_lookup(jit, norm);
  if (hit) {
    jit->cache_hits++;
    hit->last_used = ++jit->lru_clock;
    jit_expr_fn_t fn = hit->fn;
    pthread_mutex_unlock(&jit->lock);
    free(norm);
    return fn(env);
  }
  jit->cache_misses++;
  pthread_mutex_unlock(&jit->lock);

  valk_lval_t *ast = valk_parse_text(code);
  if (!ast || LVAL_TYPE(ast) == LVAL_ERR) { free(norm); return ast; }

  pthread_mutex_lock(&jit->lock);
  LLVMContextRef llvm_ctx = NULL;
  LLVMModuleRef module = NULL;
  char fn_name[64];
  if (!jit_emit_module(jit, true, ast, &llvm_ctx, &module,
                       fn_name, sizeof(fn_name))) {
    pthread_mutex_unlock(&jit->lock);
    free(norm);
    return valk_lval_err("JIT: module verification failed");
  }

  jit_expr_fn_t compiled;
  LLVMOrcResourceTrackerRef rt;
  if (!jit_install_module(jit, llvm_ctx, module, fn_name, &compiled, &rt)) {
    pthread_mutex_unlock(&jit->lock);
    free(norm);
    return valk_lval_err("JIT: install failed");
  }

  // jit_cache_insert takes ownership of `norm` (or frees it on OOM).
  if (!jit_cache_insert(jit, norm, compiled, rt)) {
    pthread_mutex_unlock(&jit->lock);
    return valk_lval_err("JIT: cache insert failed");
  }
  pthread_mutex_unlock(&jit->lock);
  return compiled(env);
}
