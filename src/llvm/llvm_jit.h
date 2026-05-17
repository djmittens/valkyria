#pragma once
#include "../parser.h"

// In-process JIT runner that uses the SAME compilation pipeline as
// `valk --build`. Given a populated env (top-level lambdas defined
// via the interpreter), JIT-compiles every AOT-eligible lambda to
// native code and wires `v->fun.native_fn` for each. Subsequent calls
// to those lambdas (via the tree walker's eval.c:348 dispatch, or via
// direct AOT-to-AOT calls within compiled bodies) execute as native
// code.
//
// Pipeline:
//   parse → eval defs (interp) → valk_jit_compile_env → eval top-level
//
// Uses LLVM ORC LLJIT in-process; symbols against libvalkyria.so
// (valk_lval_*, valk_lenv_*, valk_aot_root_env, etc.) are resolved
// via the dynamic-library search generator. The compiled module is
// owned by ORC's resource tracker until valk_jit_free.
//
// IMPORTANT: the returned `valk_jit_t *` MUST stay alive for as long
// as any compiled lambda may be called. Free it only at process exit
// (or when guaranteeing no live references to JIT'd functions).

typedef struct valk_jit_t valk_jit_t;

// Compile every AOT-eligible lambda in `env` and load into in-process
// JIT. Sets each compiled candidate's v->fun.native_fn to point at
// the JIT'd code. Sets `valk_aot_root_env = env` so AOT'd code can
// resolve global lookups at the LLJIT-resolved root.
//
// Returns NULL on failure (compile or LLJIT error). On failure, env
// is rolled back (any partial native_name assignments cleared) so
// the caller can fall back to interpreted execution.
valk_jit_t *valk_jit_compile_env(valk_lenv_t *env);

// Tear down the LLJIT and free the JIT struct. After this call any
// JIT-compiled native_fn pointers in env become invalid — callers
// must clear them before freeing the JIT, or guarantee no further
// calls into compiled code will happen.
void valk_jit_free(valk_jit_t *jit);

// Number of lambdas this JIT compiled and resolved. Diagnostic only.
size_t valk_jit_compiled_count(valk_jit_t *jit);
