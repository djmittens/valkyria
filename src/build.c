#define _POSIX_C_SOURCE 200809L
#include "build.h"

#include <libgen.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "gc.h"
#include "image.h"
#include "macro.h"
#include "memory.h"
#include "parser.h"
#include "type_env.h"

// The shim C source. Compiled along with a generated .S stub that uses
// .incbin to pull the image bytes into the final executable. References to
// `valk_build_image_start` / `valk_build_image_end` come from the .S file.
// The AOT dispatch table (`valk_aot_table` / `valk_aot_table_count`) is
// always-defined externals provided by the generated aot.c.
static const char SHIM_C_TEMPLATE[] =
    "#define _POSIX_C_SOURCE 200809L\n"
    "#include <stddef.h>\n"
    "#include <stdio.h>\n"
    "#include <stdlib.h>\n"
    "#include \"gc.h\"\n"
    "#include \"image.h\"\n"
    "#include \"memory.h\"\n"
    "#include \"parser.h\"\n"
    "#include \"builtins_internal.h\"\n"
    "\n"
    "extern const unsigned char valk_build_image_start[];\n"
    "extern const unsigned char valk_build_image_end[];\n"
    "extern const valk_aot_entry_t *const valk_aot_table;\n"
    "extern const size_t valk_aot_table_count;\n"
    "\n"
    "int main(int argc, char *argv[]) {\n"
    "  valk_system_config_t cfg = valk_system_config_default();\n"
    "  valk_system_t *sys = valk_system_create(&cfg);\n"
    "  if (!sys) { fprintf(stderr, \"valk: system init failed\\n\"); return 1; }\n"
    "  valk_lval_init_singletons();\n"
    "\n"
    "  size_t scratch_bytes = 128ULL * 1024 * 1024;\n"
    "  valk_mem_arena_t *scratch = malloc(scratch_bytes);\n"
    "  valk_mem_arena_init(scratch, scratch_bytes - sizeof(*scratch));\n"
    "  valk_thread_ctx.allocator = (void*)sys->heap;\n"
    "  valk_thread_ctx.scratch = scratch;\n"
    "  valk_thread_ctx.checkpoint_threshold = VALK_CHECKPOINT_THRESHOLD_DEFAULT;\n"
    "  valk_thread_ctx.checkpoint_enabled = true;\n"
    "\n"
    "  valk_lenv_t *registry = valk_lenv_empty();\n"
    "  valk_lenv_builtins(registry);\n"
    "\n"
    "  size_t img_len = (size_t)(valk_build_image_end - valk_build_image_start);\n"
    "  valk_lenv_t *env = valk_image_load_overlay_bytes(\n"
    "      valk_build_image_start, img_len, registry);\n"
    "  if (!env) { fprintf(stderr, \"valk: failed to load embedded image\\n\"); return 1; }\n"
    "\n"
    "  valk_image_resolve_aot(env, valk_aot_table, valk_aot_table_count);\n"
    "  valk_aot_root_env = env;\n"
    "\n"
    "  valk_gc_set_root(sys->heap, env);\n"
    "  valk_thread_ctx.root_env = env;\n"
    "\n"
    "  VALK_WITH_ALLOC((void*)sys->heap) {\n"
    "    valk_lval_t **items = malloc(argc * sizeof(*items));\n"
    "    for (int i = 0; i < argc; i++) items[i] = valk_lval_str(argv[i]);\n"
    "    valk_lenv_def(env, valk_lval_sym(\"argv\"), valk_lval_qlist(items, argc));\n"
    "    free(items);\n"
    "  }\n"
    "\n"
    "  valk_lval_t *entry = valk_lenv_get(env, valk_lval_sym(\"__entry__\"));\n"
    "  if (!entry || LVAL_TYPE(entry) == LVAL_ERR) {\n"
    "    fprintf(stderr, \"valk: image missing __entry__\\n\"); return 1;\n"
    "  }\n"
    "\n"
    "  valk_lval_t *result = NULL;\n"
    "  if (LVAL_TYPE(entry) == LVAL_FUN) {\n"
    "    VALK_WITH_ALLOC((void*)sys->heap) {\n"
    "      valk_lval_t *call = valk_lval_cons(\n"
    "          valk_lval_sym(\"__entry__\"),\n"
    "          valk_lval_cons(valk_lval_sym(\"argv\"), valk_lval_nil()));\n"
    "      result = valk_lval_eval(env, call);\n"
    "    }\n"
    "  } else if (LVAL_TYPE(entry) == LVAL_CONS && (entry->flags & LVAL_FLAG_QUOTED)) {\n"
    "    VALK_WITH_ALLOC((void*)sys->heap) {\n"
    "      valk_lval_t *body = valk_qexpr_to_cons(entry);\n"
    "      result = valk_lval_eval(env, body);\n"
    "    }\n"
    "  } else {\n"
    "    fprintf(stderr, \"valk: __entry__ has unsupported type\\n\"); return 1;\n"
    "  }\n"
    "\n"
    "  int exit_code = 0;\n"
    "  if (result && LVAL_TYPE(result) == LVAL_ERR) {\n"
    "    valk_lval_println(result); exit_code = 1;\n"
    "  } else if (result && LVAL_TYPE(result) == LVAL_NUM) {\n"
    "    exit_code = (int)result->num;\n"
    "  }\n"
    "\n"
    "  valk_lval_t *exit_val = valk_lenv_get(env, valk_lval_sym(\"VALK_EXIT_CODE\"));\n"
    "  if (exit_val && LVAL_TYPE(exit_val) == LVAL_NUM) exit_code = (int)exit_val->num;\n"
    "\n"
    "  valk_system_unregister_thread(sys);\n"
    "  free(scratch);\n"
    "  valk_system_shutdown(sys, 5000);\n"
    "  valk_system_destroy(sys);\n"
    "  return exit_code;\n"
    "}\n";

static int write_file(const char *path, const char *content, size_t len) {
  FILE *f = fopen(path, "w");
  if (!f) { perror(path); return -1; }
  if (fwrite(content, 1, len, f) != len) { perror(path); fclose(f); return -1; }
  fclose(f);
  return 0;
}

// Resolve the absolute directory of the currently-running valk binary.
// Used to find libvalkyria.so (linked at build time) and src/ headers.
static int resolve_exe_dir(char *out, size_t cap) {
  char buf[PATH_MAX];
  ssize_t n = readlink("/proc/self/exe", buf, sizeof(buf) - 1);
  if (n <= 0) return -1;
  buf[n] = 0;
  char *dir = dirname(buf);
  if (strlen(dir) + 1 > cap) return -1;
  strcpy(out, dir);
  return 0;
}

// Parse + eval the script against the given env, returning the last
// non-nil, non-error value (deep-copied onto the GC heap so it survives
// past this function). Returns NULL on eval error (already printed).
static valk_lval_t *eval_script_capture_last(valk_lenv_t *env,
                                             const char *script_path) {
  valk_gc_heap_t *heap = (valk_gc_heap_t *)valk_thread_ctx.allocator;

  valk_lval_t *res;
  VALK_WITH_ALLOC((void *)heap) { res = valk_parse_file(script_path); }
  if (LVAL_TYPE(res) == LVAL_ERR) { valk_lval_println(res); return NULL; }
  valk_gc_root_push(res);

  // Macro-expand pass (mirrors repl.c script mode).
  VALK_WITH_ALLOC((void *)heap) {
    valk_lval_t *cur = res;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      if (valk_macro_is_def(cur->cons.head)) {
        valk_lval_t *r = valk_lval_eval(env, cur->cons.head);
        if (LVAL_TYPE(r) == LVAL_ERR) valk_lval_println(r);
        cur->cons.head = valk_lval_nil();
      } else {
        cur->cons.head = valk_macro_expand_one(env, cur->cons.head);
      }
      cur = cur->cons.tail;
    }
  }

  char *script_prefix = valk_take_pending_module_prefix();
  if (script_prefix) valk_module_apply_prefix(res, script_prefix);

  valk_lval_t *last = valk_lval_nil();
  while (valk_lval_list_count(res) > 0) {
    valk_lval_t *x;
    VALK_WITH_ALLOC((void *)heap) {
      x = valk_lval_pop(res, 0);
      x = valk_type_transform_expr(x);
    }
    if (LVAL_TYPE(x) == LVAL_NIL) continue;
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
      valk_gc_root_pop();
      if (script_prefix) free(script_prefix);
      return NULL;
    }
    valk_gc_root_push(x);
    VALK_WITH_ALLOC((void *)valk_thread_ctx.scratch) {
      x = valk_lval_eval(env, x);
    }
    valk_gc_root_pop();
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
      valk_gc_root_pop();
      if (script_prefix) free(script_prefix);
      return NULL;
    }
    VALK_WITH_ALLOC((void *)heap) { last = valk_lval_copy(x); }
    VALK_GC_SAFE_POINT();
  }
  valk_gc_root_pop();
  if (script_prefix) free(script_prefix);
  return last;
}

// Weak extern: resolved by valk_llvm when VALK_LLVM is ON and the valk
// executable links against valk_llvm; otherwise the symbol address is
// NULL and we skip AOT (fall back to a pure tree-walker image).
__attribute__((weak))
int valk_build_emit_aot(valk_lenv_t *env, const char *o_path,
                        const char *c_path, size_t *out_count);

int valk_build(valk_lenv_t *env, const char *script_path,
               const char *out_path) {
  valk_lval_t *entry = eval_script_capture_last(env, script_path);
  if (!entry) return 1;

  valk_ltype_e t = LVAL_TYPE(entry);
  bool is_qexpr = (t == LVAL_CONS && (entry->flags & LVAL_FLAG_QUOTED));
  if (t != LVAL_FUN && !is_qexpr) {
    fprintf(stderr,
            "valk --build: entry must be a lambda or qexpr; got type=%d\n",
            (int)t);
    return 1;
  }

  valk_gc_heap_t *heap = (valk_gc_heap_t *)valk_thread_ctx.allocator;
  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_def(env, valk_lval_sym("__entry__"), entry);
  }

  // AOT: compile user lambdas into an ELF .o + write a dispatch .c. Must
  // run BEFORE the image dump so native_name fields are populated on
  // lambdas that compiled successfully.
  char aot_o[PATH_MAX] = "";
  char aot_c[PATH_MAX];
  size_t aot_count = 0;
  bool aot_ok = false;
  if (&valk_build_emit_aot != nullptr) {
    snprintf(aot_o, sizeof(aot_o), "%s.aot.o", out_path);
    snprintf(aot_c, sizeof(aot_c), "%s.aot.c", out_path);
    if (valk_build_emit_aot(env, aot_o, aot_c, &aot_count) == 0) {
      aot_ok = true;
    } else {
      fprintf(stderr, "valk --build: AOT emit failed; falling back to "
              "tree-walker only\n");
    }
  }

  char img_path[PATH_MAX];
  snprintf(img_path, sizeof(img_path), "%s.img.tmp", out_path);
  if (valk_image_dump_env(env, img_path) != 0) {
    fprintf(stderr, "valk --build: image dump failed\n");
    if (aot_ok) { unlink(aot_o); unlink(aot_c); }
    return 1;
  }

  char exe_dir[PATH_MAX];
  if (resolve_exe_dir(exe_dir, sizeof(exe_dir)) != 0) {
    fprintf(stderr, "valk --build: could not resolve /proc/self/exe\n");
    unlink(img_path);
    if (aot_ok) { unlink(aot_o); unlink(aot_c); }
    return 1;
  }
  char src_dir[PATH_MAX];
  snprintf(src_dir, sizeof(src_dir), "%s/../src", exe_dir);

  // If the AOT hook wasn't available, we still need to satisfy the shim's
  // extern references to valk_aot_table / valk_aot_table_count by writing
  // a stub dispatch .c with a NULL table.
  if (!aot_ok) {
    snprintf(aot_c, sizeof(aot_c), "%s.aot.c", out_path);
    const char *stub =
        "#include <stddef.h>\n"
        "#include \"image.h\"\n"
        "const valk_aot_entry_t *const valk_aot_table = NULL;\n"
        "const size_t valk_aot_table_count = 0;\n";
    if (write_file(aot_c, stub, strlen(stub)) != 0) {
      unlink(img_path);
      return 1;
    }
  }

  char shim_c[PATH_MAX], shim_s[PATH_MAX];
  snprintf(shim_c, sizeof(shim_c), "%s.shim.c", out_path);
  snprintf(shim_s, sizeof(shim_s), "%s.shim.S", out_path);

  if (write_file(shim_c, SHIM_C_TEMPLATE, sizeof(SHIM_C_TEMPLATE) - 1) != 0) {
    unlink(img_path);
    unlink(aot_c);
    if (aot_ok && aot_count > 0) unlink(aot_o);
    return 1;
  }

  // Resolve image path to absolute (.incbin needs an unambiguous path).
  char img_abs[PATH_MAX];
  if (!realpath(img_path, img_abs)) {
    fprintf(stderr, "valk --build: cannot resolve image path\n");
    unlink(img_path);
    unlink(shim_c);
    unlink(aot_c);
    if (aot_ok && aot_count > 0) unlink(aot_o);
    return 1;
  }

  char shim_s_content[PATH_MAX + 256];
  snprintf(shim_s_content, sizeof(shim_s_content),
           "    .section .rodata\n"
           "    .global valk_build_image_start\n"
           "    .global valk_build_image_end\n"
           "valk_build_image_start:\n"
           "    .incbin \"%s\"\n"
           "valk_build_image_end:\n",
           img_abs);
  if (write_file(shim_s, shim_s_content, strlen(shim_s_content)) != 0) {
    unlink(img_path);
    unlink(shim_c);
    unlink(aot_c);
    if (aot_ok && aot_count > 0) unlink(aot_o);
    return 1;
  }

  char cmd[8192];
  char aot_o_arg[PATH_MAX + 1] = "";
  if (aot_ok && aot_count > 0) snprintf(aot_o_arg, sizeof(aot_o_arg), "%s", aot_o);
  snprintf(cmd, sizeof(cmd),
           "cc -std=gnu2x -O1 "
           "-I%s -I%s/aio -I%s/aio/system -I%s/aio/http2 "
           "-I%s/aio/http2/overload -I%s/aio/http2/stream "
           "%s %s %s %s -L%s -Wl,-rpath,%s -lvalkyria -lpthread -lm -o %s",
           src_dir, src_dir, src_dir, src_dir, src_dir, src_dir,
           shim_c, shim_s, aot_c, aot_o_arg, exe_dir, exe_dir, out_path);
  int rc = system(cmd);

  unlink(img_path);
  unlink(shim_c);
  unlink(shim_s);
  unlink(aot_c);
  if (aot_ok && aot_count > 0) unlink(aot_o);

  if (rc != 0) {
    fprintf(stderr, "valk --build: cc failed (exit %d)\n", rc);
    return 1;
  }
  return 0;
}
