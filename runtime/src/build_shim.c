// The entry point of every `valk --build` output binary. Compiled once, at
// runtime build time, with exactly the same flags and ABI as libvalkyria, and
// shipped as valk-shim.o next to the library. `valk --build` links it as-is:
// the deployment machine needs a C toolchain only for assembling the image
// section and linking — never the runtime headers.
#define _POSIX_C_SOURCE 200809L
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

#include "builtins_internal.h"
#include "gc.h"
#include "image.h"
#include "macro.h"
#include "memory.h"
#include "parser.h"

extern const unsigned char valk_build_image_start[];
extern const unsigned char valk_build_image_end[];
extern const valk_aot_entry_t *const valk_aot_table;
extern const size_t valk_aot_table_count;

int main(int argc, char *argv[]) {
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);
  if (!sys) {
    fprintf(stderr, "valk: system init failed\n");
    return 1;
  }
  valk_lval_init_singletons();

  size_t scratch_bytes = 128ULL * 1024 * 1024;
  const char *env_scratch = getenv("VALK_SCRATCH_BYTES");
  if (env_scratch) {
    char *end = NULL;
    unsigned long long v = strtoull(env_scratch, &end, 10);
    if (end && *end == 0 && v >= 1024ULL * 1024) scratch_bytes = (size_t)v;
  }
  valk_mem_arena_t *scratch = malloc(scratch_bytes);
  if (!scratch) {
    fprintf(stderr, "valk: scratch arena malloc failed (%zu bytes)\n",
            scratch_bytes);
    return 1;
  }
  valk_mem_arena_init(scratch, scratch_bytes - sizeof(*scratch));
  valk_thread_ctx.allocator = (void *)sys->heap;
  valk_thread_ctx.scratch = scratch;

  valk_lenv_t *registry = valk_lenv_empty();
  valk_lenv_builtins(registry);

  size_t img_len = (size_t)(valk_build_image_end - valk_build_image_start);
  valk_lenv_t *env =
      valk_image_load_overlay_bytes(valk_build_image_start, img_len, registry);
  if (!env) {
    fprintf(stderr, "valk: failed to load embedded image\n");
    return 1;
  }

  valk_image_resolve_aot(env, valk_aot_table, valk_aot_table_count);
  valk_aot_root_env = env;

  valk_gc_set_root(sys->heap, env);
  valk_thread_ctx.root_env = env;
  // Unify the macro env with the runtime env (matches the interpreter:
  // valk_lenv_builtins left it pointing at the transient registry).
  valk_macro_env_init(env);

  VALK_WITH_ALLOC((void *)sys->heap) {
    valk_lval_t **items = malloc(argc * sizeof(*items));
    for (int i = 0; i < argc; i++) items[i] = valk_lval_str(argv[i]);
    valk_lenv_def(env, valk_lval_sym("argv"), valk_lval_qlist(items, argc));
    free(items);
  }

  valk_lval_t *entry = valk_lenv_get(env, valk_lval_sym("__entry__"));
  if (!entry || LVAL_TYPE(entry) == LVAL_ERR) {
    fprintf(stderr, "valk: image missing __entry__\n");
    return 1;
  }

  valk_lval_t *result = NULL;
  if (LVAL_TYPE(entry) == LVAL_FUN) {
    VALK_WITH_ALLOC((void *)sys->heap) {
      valk_lval_t *call = valk_lval_cons(
          valk_lval_sym("__entry__"),
          valk_lval_cons(valk_lval_sym("argv"), valk_lval_nil()));
      result = valk_lval_eval(env, call);
    }
  } else if (LVAL_TYPE(entry) == LVAL_CONS && (entry->flags & LVAL_FLAG_QUOTED)) {
    VALK_WITH_ALLOC((void *)sys->heap) {
      valk_lval_t *body = valk_qexpr_to_cons(entry);
      result = valk_lval_eval(env, body);
    }
  } else {
    fprintf(stderr, "valk: __entry__ has unsupported type\n");
    return 1;
  }

  int exit_code = 0;
  if (result && LVAL_TYPE(result) == LVAL_ERR) {
    valk_lval_println(result);
    exit_code = 1;
  } else if (result && LVAL_TYPE(result) == LVAL_NUM) {
    exit_code = (int)result->num;
  }

  valk_lval_t *exit_val = valk_lenv_get(env, valk_lval_sym("VALK_EXIT_CODE"));
  if (exit_val && LVAL_TYPE(exit_val) == LVAL_NUM) exit_code = (int)exit_val->num;

  valk_system_unregister_thread(sys);
  free(scratch);
  valk_system_shutdown(sys, 5000);
  valk_system_destroy(sys);
  return exit_code;
}
