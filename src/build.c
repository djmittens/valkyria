#define _POSIX_C_SOURCE 200809L
#ifdef __APPLE__
#define _DARWIN_C_SOURCE
#endif
#include "build.h"

#include <ctype.h>
#include <dlfcn.h>
#ifdef __APPLE__
#include <mach-o/dyld.h>
#endif
#include <errno.h>
#include <fcntl.h>
#include <libgen.h>
#include <limits.h>
#include <spawn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include "gc.h"
#include "image.h"
#include "macro.h"
#include "memory.h"
#include "parser.h"
#include "type_env.h"

extern char **environ;

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
    "  const char *env_scratch = getenv(\"VALK_SCRATCH_BYTES\");\n"
    "  if (env_scratch) {\n"
    "    char *end = NULL;\n"
    "    unsigned long long v = strtoull(env_scratch, &end, 10);\n"
    "    if (end && *end == 0 && v >= 1024ULL * 1024) scratch_bytes = (size_t)v;\n"
    "  }\n"
    "  valk_mem_arena_t *scratch = malloc(scratch_bytes);\n"
    "  if (!scratch) {\n"
    "    fprintf(stderr, \"valk: scratch arena malloc failed (%zu bytes)\\n\", scratch_bytes);\n"
    "    return 1;\n"
    "  }\n"
    "  valk_mem_arena_init(scratch, scratch_bytes - sizeof(*scratch));\n"
    "  valk_thread_ctx.allocator = (void*)sys->heap;\n"
    "  valk_thread_ctx.scratch = scratch;\n"
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
    "  // Unify the macro env with the runtime env (matches the interpreter:\n"
    "  // valk_lenv_builtins left it pointing at the transient registry).\n"
    "  { extern void valk_macro_env_init(valk_lenv_t *); valk_macro_env_init(env); }\n"
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
  int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC | O_NOFOLLOW, 0600);
  if (fd < 0) { perror(path); return -1; }
  ssize_t off = 0;
  while ((size_t)off < len) {
    ssize_t n = write(fd, content + off, len - (size_t)off);
    if (n < 0) {
      if (errno == EINTR) continue;
      perror(path); close(fd); return -1;
    }
    off += n;
  }
  close(fd);
  return 0;
}

static int resolve_exe_dir(char *out, size_t cap) {
  char buf[PATH_MAX];
#ifdef __APPLE__
  uint32_t bufsize = sizeof(buf);
  if (_NSGetExecutablePath(buf, &bufsize) != 0) return -1;
  char real[PATH_MAX];
  if (realpath(buf, real) != nullptr) {
    if (strlen(real) + 1 > sizeof(buf)) return -1;
    strcpy(buf, real);
  }
#else
  ssize_t n = readlink("/proc/self/exe", buf, sizeof(buf) - 1);
  if (n <= 0) return -1;
  buf[n] = 0;
#endif
  char *dir = dirname(buf);
  if (strlen(dir) + 1 > cap) return -1;
  strcpy(out, dir);
  return 0;
}

static valk_lval_t *eval_script_capture_last(valk_lenv_t *env,
                                             const char *script_path) {
  valk_gc_heap_t *heap = (valk_gc_heap_t *)valk_thread_ctx.allocator;

  valk_lval_t *res;
  VALK_WITH_ALLOC((void *)heap) { res = valk_parse_file(script_path); }
  if (LVAL_TYPE(res) == LVAL_ERR) { valk_lval_println(res); return NULL; }
  valk_gc_root_push(res);

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

typedef int (*valk_build_emit_aot_fn)(valk_lenv_t *env, const char *o_path,
                                      const char *c_path, size_t *out_count);

static valk_build_emit_aot_fn valk_build_resolve_emit_aot(void) {
  return (valk_build_emit_aot_fn)dlsym(RTLD_DEFAULT, "valk_build_emit_aot");
}

#define MAX_TMP_FILES 8
typedef struct {
  char *paths[MAX_TMP_FILES];
  int count;
} tmp_set_t;

static int tmp_set_add(tmp_set_t *s, const char *p) {
  if (s->count >= MAX_TMP_FILES) return -1;
  s->paths[s->count] = strdup(p);
  if (!s->paths[s->count]) return -1;
  s->count++;
  return 0;
}

static void tmp_set_cleanup(tmp_set_t *s) {
  for (int i = 0; i < s->count; i++) {
    if (s->paths[i]) { unlink(s->paths[i]); free(s->paths[i]); }
  }
  s->count = 0;
}

static int mkstemp_named(char *template, const char *suffix, char *out, size_t cap) {
  size_t tlen = strlen(template);
  size_t slen = strlen(suffix);
  if (tlen + slen + 1 > cap) return -1;
  memcpy(out, template, tlen);
  memcpy(out + tlen, suffix, slen + 1);
  int fd = mkstemps(out, (int)slen);
  if (fd < 0) { perror("mkstemps"); return -1; }
  close(fd);
  return 0;
}

static int run_cc(char *const argv[]) {
  pid_t pid = 0;
  posix_spawn_file_actions_t actions;
  if (posix_spawn_file_actions_init(&actions) != 0) return -1;
  int rc = posix_spawnp(&pid, argv[0], &actions, NULL, argv, environ);
  posix_spawn_file_actions_destroy(&actions);
  if (rc != 0) {
    fprintf(stderr, "valk --build: posix_spawnp(%s) failed: %s\n",
            argv[0], strerror(rc));
    return -1;
  }
  int status = 0;
  while (waitpid(pid, &status, 0) < 0) {
    if (errno == EINTR) continue;
    perror("waitpid");
    return -1;
  }
  if (WIFSIGNALED(status)) {
    fprintf(stderr, "valk --build: %s killed by signal %d\n",
            argv[0], WTERMSIG(status));
    return -1;
  }
  if (!WIFEXITED(status)) {
    fprintf(stderr, "valk --build: %s exited abnormally\n", argv[0]);
    return -1;
  }
  int code = WEXITSTATUS(status);
  if (code != 0) {
    fprintf(stderr, "valk --build: %s exited with status %d\n", argv[0], code);
    return -1;
  }
  return 0;
}

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

  tmp_set_t tmps = {0};
  char tmp_template[PATH_MAX];
  const char *tmpdir = getenv("TMPDIR");
  if (!tmpdir || !*tmpdir) tmpdir = "/tmp";
  snprintf(tmp_template, sizeof(tmp_template), "%s/valk-build-XXXXXX", tmpdir);

  char aot_o[PATH_MAX] = "";
  char aot_c[PATH_MAX] = "";
  size_t aot_count = 0;
  bool aot_ok = false;
  valk_build_emit_aot_fn emit_aot = valk_build_resolve_emit_aot();
  if (emit_aot != nullptr) {
    if (mkstemp_named(tmp_template, ".o", aot_o, sizeof(aot_o)) != 0 ||
        mkstemp_named(tmp_template, ".c", aot_c, sizeof(aot_c)) != 0) {
      tmp_set_cleanup(&tmps);
      return 1;
    }
    tmp_set_add(&tmps, aot_o);
    tmp_set_add(&tmps, aot_c);
    if (emit_aot(env, aot_o, aot_c, &aot_count) == 0) {
      aot_ok = true;
    } else {
      fprintf(stderr, "valk --build: AOT emit failed; falling back to "
              "tree-walker only\n");
    }
  }

  char img_path[PATH_MAX];
  if (mkstemp_named(tmp_template, ".img", img_path, sizeof(img_path)) != 0) {
    tmp_set_cleanup(&tmps); return 1;
  }
  tmp_set_add(&tmps, img_path);
  if (valk_image_dump_env(env, img_path) != 0) {
    fprintf(stderr, "valk --build: image dump failed\n");
    tmp_set_cleanup(&tmps); return 1;
  }

  char exe_dir[PATH_MAX];
  if (resolve_exe_dir(exe_dir, sizeof(exe_dir)) != 0) {
    fprintf(stderr, "valk --build: could not resolve executable path\n");
    tmp_set_cleanup(&tmps); return 1;
  }
  char src_dir[PATH_MAX];
  snprintf(src_dir, sizeof(src_dir), "%s/../src", exe_dir);

  if (!aot_ok) {
    if (aot_c[0] == 0 &&
        mkstemp_named(tmp_template, ".c", aot_c, sizeof(aot_c)) != 0) {
      tmp_set_cleanup(&tmps); return 1;
    }
    if (aot_c[0] != 0 && tmps.count > 0 &&
        strcmp(tmps.paths[tmps.count-1], aot_c) != 0) {
      tmp_set_add(&tmps, aot_c);
    }
    const char *stub =
        "#include <stddef.h>\n"
        "#include \"image.h\"\n"
        "const valk_aot_entry_t *const valk_aot_table = NULL;\n"
        "const size_t valk_aot_table_count = 0;\n";
    if (write_file(aot_c, stub, strlen(stub)) != 0) {
      tmp_set_cleanup(&tmps); return 1;
    }
  }

  char shim_c[PATH_MAX], shim_s[PATH_MAX];
  if (mkstemp_named(tmp_template, ".c", shim_c, sizeof(shim_c)) != 0 ||
      mkstemp_named(tmp_template, ".S", shim_s, sizeof(shim_s)) != 0) {
    tmp_set_cleanup(&tmps); return 1;
  }
  tmp_set_add(&tmps, shim_c);
  tmp_set_add(&tmps, shim_s);

  if (write_file(shim_c, SHIM_C_TEMPLATE, sizeof(SHIM_C_TEMPLATE) - 1) != 0) {
    tmp_set_cleanup(&tmps); return 1;
  }

  char img_abs[PATH_MAX];
  if (!realpath(img_path, img_abs)) {
    fprintf(stderr, "valk --build: cannot resolve image path\n");
    tmp_set_cleanup(&tmps); return 1;
  }
  for (const char *p = img_abs; *p; p++) {
    if (*p == '"' || *p == '\\' || *p == '\n') {
      fprintf(stderr, "valk --build: image path contains unsafe character\n");
      tmp_set_cleanup(&tmps); return 1;
    }
  }

  char shim_s_content[PATH_MAX + 256];
#ifdef __APPLE__
  // Mach-O assembler: read-only data lives in __TEXT,__const and C symbols
  // carry a leading underscore in the asm namespace.
  snprintf(shim_s_content, sizeof(shim_s_content),
           "    .section __TEXT,__const\n"
           "    .global _valk_build_image_start\n"
           "    .global _valk_build_image_end\n"
           "_valk_build_image_start:\n"
           "    .incbin \"%s\"\n"
           "_valk_build_image_end:\n",
           img_abs);
#else
  snprintf(shim_s_content, sizeof(shim_s_content),
           "    .section .rodata\n"
           "    .global valk_build_image_start\n"
           "    .global valk_build_image_end\n"
           "valk_build_image_start:\n"
           "    .incbin \"%s\"\n"
           "valk_build_image_end:\n",
           img_abs);
#endif
  if (write_file(shim_s, shim_s_content, strlen(shim_s_content)) != 0) {
    tmp_set_cleanup(&tmps); return 1;
  }

  char inc_src[PATH_MAX], inc_aio[PATH_MAX], inc_sys[PATH_MAX];
  char inc_h2[PATH_MAX], inc_ovl[PATH_MAX], inc_strm[PATH_MAX];
  char lib_arg[PATH_MAX + 8], rpath_arg[PATH_MAX + 16];
  snprintf(inc_src, sizeof(inc_src), "-I%s", src_dir);
  snprintf(inc_aio, sizeof(inc_aio), "-I%s/aio", src_dir);
  snprintf(inc_sys, sizeof(inc_sys), "-I%s/aio/system", src_dir);
  snprintf(inc_h2, sizeof(inc_h2), "-I%s/aio/http2", src_dir);
  snprintf(inc_ovl, sizeof(inc_ovl), "-I%s/aio/http2/overload", src_dir);
  snprintf(inc_strm, sizeof(inc_strm), "-I%s/aio/http2/stream", src_dir);
  snprintf(lib_arg, sizeof(lib_arg), "-L%s", exe_dir);
  snprintf(rpath_arg, sizeof(rpath_arg), "-Wl,-rpath,%s", exe_dir);

  const char *cc = getenv("CC");
  if (!cc || !*cc) cc = "cc";

  char *argv_cc[24];
  int ai = 0;
  argv_cc[ai++] = (char *)cc;
  argv_cc[ai++] = (char *)"-std=gnu2x";
  argv_cc[ai++] = (char *)"-O1";
  argv_cc[ai++] = inc_src;
  argv_cc[ai++] = inc_aio;
  argv_cc[ai++] = inc_sys;
  argv_cc[ai++] = inc_h2;
  argv_cc[ai++] = inc_ovl;
  argv_cc[ai++] = inc_strm;
  argv_cc[ai++] = shim_c;
  argv_cc[ai++] = shim_s;
  argv_cc[ai++] = aot_c;
  if (aot_ok && aot_count > 0) argv_cc[ai++] = aot_o;
  argv_cc[ai++] = lib_arg;
  argv_cc[ai++] = rpath_arg;
  argv_cc[ai++] = (char *)"-lvalkyria";
  argv_cc[ai++] = (char *)"-lpthread";
  argv_cc[ai++] = (char *)"-lm";
  argv_cc[ai++] = (char *)"-o";
  argv_cc[ai++] = (char *)out_path;
  argv_cc[ai] = NULL;

  int rc = run_cc(argv_cc);
  tmp_set_cleanup(&tmps);
  return rc == 0 ? 0 : 1;
}
