#pragma once
#include <stddef.h>
#include "../parser.h"

// AOT hook used by src/build.c when the valk_llvm library is linked in.
//
// Walks `env` for top-level lambdas (LVAL_FUN with no builtin + a body),
// compiles each body via the LLVM codegen into a uniquely-named function,
// writes all compiled functions into `o_path` (ELF .o), and writes a C
// dispatch source file to `c_path` that defines:
//
//   const valk_aot_entry_t *const valk_aot_table;
//   const size_t              valk_aot_table_count;
//
// For each lambda that compiled + verified successfully, the lambda's
// fun.native_name is set (strdup'd) so the image dumper can serialize
// it; on image load, `valk_image_resolve_aot` maps the name back to the
// compiled fn pointer.
//
// On success returns 0 and writes the count of compiled entries to
// `*out_count`. Returns non-zero on failure; on failure the caller
// should fall back to a pure tree-walker build.
int valk_build_emit_aot(valk_lenv_t *env, const char *o_path,
                        const char *c_path, size_t *out_count);
