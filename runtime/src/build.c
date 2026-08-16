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

// Always provided by the CMake build (the configured CMAKE_C_COMPILER);
// this fallback only keeps non-CMake compilation possible.
#ifndef VALK_CC
#define VALK_CC "cc"
#endif

extern char **environ;

static int write_file(const char *path, const char *content, size_t len) {
  int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC | O_NOFOLLOW, 0600);
  if (fd < 0) { perror(path); return -1; } // LCOV_EXCL_BR_LINE - temp dir validated by earlier mkstemps
  ssize_t off = 0;
  while ((size_t)off < len) {
    ssize_t n = write(fd, content + off, len - (size_t)off);
    // LCOV_EXCL_START - write to a just-created temp file essentially never fails
    if (n < 0) {
      if (errno == EINTR) continue;
      perror(path); close(fd); return -1;
    }
    // LCOV_EXCL_STOP
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
  if (n <= 0) return -1; // LCOV_EXCL_BR_LINE - /proc/self/exe readlink never fails
  buf[n] = 0;
#endif
  char *dir = dirname(buf);
  if (strlen(dir) + 1 > cap) return -1; // LCOV_EXCL_BR_LINE - PATH_MAX-sized caller buffer
  strcpy(out, dir);
  return 0;
}

static valk_lval_t *eval_script_capture_last(valk_lenv_t *env,
                                             const char *script_path) {
  // The loader pipeline treats the file as a (do ...): the last top-level
  // form's value is the file's value (heap-evacuated by the loader).
  valk_lval_t *last = valk_load_file(env, script_path);
  if (LVAL_TYPE(last) == LVAL_ERR) {
    valk_lval_println(last);
    return NULL;
  }
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
  if (s->count >= MAX_TMP_FILES) return -1; // LCOV_EXCL_BR_LINE - callers add a bounded fixed set
  s->paths[s->count] = strdup(p);
  if (!s->paths[s->count]) return -1; // LCOV_EXCL_BR_LINE - strdup OOM
  s->count++;
  return 0;
}

static void tmp_set_cleanup(tmp_set_t *s) {
  for (int i = 0; i < s->count; i++) {
    if (s->paths[i]) { unlink(s->paths[i]); free(s->paths[i]); } // LCOV_EXCL_BR_LINE - entries are never null
  }
  s->count = 0;
}

static int mkstemp_named(char *template, const char *suffix, char *out, size_t cap) {
  size_t tlen = strlen(template);
  size_t slen = strlen(suffix);
  if (tlen + slen + 1 > cap) return -1; // LCOV_EXCL_BR_LINE - PATH_MAX-sized buffers
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
  if (posix_spawn_file_actions_init(&actions) != 0) return -1; // LCOV_EXCL_BR_LINE - platform API
  int rc = posix_spawnp(&pid, argv[0], &actions, NULL, argv, environ);
  posix_spawn_file_actions_destroy(&actions);
  // LCOV_EXCL_START - spawn/waitpid failures are platform-level
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
  // LCOV_EXCL_STOP
  if (WIFSIGNALED(status)) {
    fprintf(stderr, "valk --build: %s killed by signal %d\n",
            argv[0], WTERMSIG(status));
    return -1;
  }
  // LCOV_EXCL_START - impossible: waitpid without WUNTRACED only returns exited/signaled
  if (!WIFEXITED(status)) {
    fprintf(stderr, "valk --build: %s exited abnormally\n", argv[0]);
    return -1;
  }
  // LCOV_EXCL_STOP
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
  if (emit_aot != nullptr) { // LCOV_EXCL_BR_LINE - null only in non-LLVM builds
    if (mkstemp_named(tmp_template, ".o", aot_o, sizeof(aot_o)) != 0 || // LCOV_EXCL_BR_LINE - bad TMPDIR fails the first call
        mkstemp_named(tmp_template, ".c", aot_c, sizeof(aot_c)) != 0) { // LCOV_EXCL_BR_LINE - unreachable after first succeeded
      tmp_set_cleanup(&tmps);
      return 1;
    }
    tmp_set_add(&tmps, aot_o);
    tmp_set_add(&tmps, aot_c);
    if (emit_aot(env, aot_o, aot_c, &aot_count) == 0) { // LCOV_EXCL_BR_LINE - emit failure has no external trigger
      aot_ok = true;
    } else {
      fprintf(stderr, "valk --build: AOT emit failed; falling back to "
              "tree-walker only\n");
    }
  }

  char img_path[PATH_MAX];
  // LCOV_EXCL_START - unreachable: a bad TMPDIR already failed the first mkstemp
  if (mkstemp_named(tmp_template, ".img", img_path, sizeof(img_path)) != 0) {
    tmp_set_cleanup(&tmps); return 1;
  }
  // LCOV_EXCL_STOP
  tmp_set_add(&tmps, img_path);
  if (valk_image_dump_env(env, img_path) != 0) {
    fprintf(stderr, "valk --build: image dump failed\n");
    tmp_set_cleanup(&tmps); return 1;
  }

  char exe_dir[PATH_MAX];
  // LCOV_EXCL_START - resolve_exe_dir only fails on platform API failure
  if (resolve_exe_dir(exe_dir, sizeof(exe_dir)) != 0) {
    fprintf(stderr, "valk --build: could not resolve executable path\n");
    tmp_set_cleanup(&tmps); return 1;
  }
  // LCOV_EXCL_STOP

  // The shim (the output binary's main()) is precompiled at runtime build
  // time with the same flags/ABI as libvalkyria and staged next to it. No
  // headers are needed on this machine — only an assembler and a linker.
  char shim_o[PATH_MAX];
  snprintf(shim_o, sizeof(shim_o), "%s/valk-shim.o", exe_dir);
  if (access(shim_o, R_OK) != 0) {
    fprintf(stderr,
            "valk --build: %s not found\n"
            "valk --build: valk-shim.o must be installed next to the valk "
            "binary (it is produced by the runtime build alongside "
            "libvalkyria)\n",
            shim_o);
    tmp_set_cleanup(&tmps); return 1;
  }

  // LCOV_EXCL_START - only reachable when the runtime lacks the LLVM AOT
  // emitter or the emitter fails internally; every shipped build config
  // links it and emit failure has no external trigger
  if (!aot_ok) {
    if (aot_c[0] == 0 &&
        mkstemp_named(tmp_template, ".c", aot_c, sizeof(aot_c)) != 0) {
      tmp_set_cleanup(&tmps); return 1;
    }
    if (aot_c[0] != 0 && tmps.count > 0 &&
        strcmp(tmps.paths[tmps.count-1], aot_c) != 0) {
      tmp_set_add(&tmps, aot_c);
    }
    // Self-contained: mirrors valk_aot_entry_t (image.h) by layout so the
    // stub compiles without runtime headers.
    const char *stub =
        "#include <stddef.h>\n"
        "typedef struct valk_shim_lval valk_shim_lval_t;\n"
        "typedef struct valk_shim_lenv valk_shim_lenv_t;\n"
        "typedef struct {\n"
        "  const char *name;\n"
        "  valk_shim_lval_t *(*fn)(valk_shim_lenv_t *);\n"
        "} valk_shim_aot_entry_t;\n"
        "const valk_shim_aot_entry_t *const valk_aot_table = NULL;\n"
        "const size_t valk_aot_table_count = 0;\n";
    if (write_file(aot_c, stub, strlen(stub)) != 0) {
      tmp_set_cleanup(&tmps); return 1;
    }
  }
  // LCOV_EXCL_STOP

  char shim_s[PATH_MAX];
  // LCOV_EXCL_START - unreachable: a bad TMPDIR already failed the first mkstemp
  if (mkstemp_named(tmp_template, ".S", shim_s, sizeof(shim_s)) != 0) {
    tmp_set_cleanup(&tmps); return 1;
  }
  // LCOV_EXCL_STOP
  tmp_set_add(&tmps, shim_s);

  char img_abs[PATH_MAX];
  // LCOV_EXCL_START - realpath on a file this process just created never fails
  if (!realpath(img_path, img_abs)) {
    fprintf(stderr, "valk --build: cannot resolve image path\n");
    tmp_set_cleanup(&tmps); return 1;
  }
  // LCOV_EXCL_STOP
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
  if (write_file(shim_s, shim_s_content, strlen(shim_s_content)) != 0) { // LCOV_EXCL_BR_LINE - temp dir already validated
    tmp_set_cleanup(&tmps); return 1;
  }

  char lib_arg[PATH_MAX + 8], rpath_arg[PATH_MAX + 16];
  snprintf(lib_arg, sizeof(lib_arg), "-L%s", exe_dir);
  snprintf(rpath_arg, sizeof(rpath_arg), "-Wl,-rpath,%s", exe_dir);

  // One toolchain, everywhere: the runtime, the shim and the AOT objects are
  // all built by the compiler CMake configured (VALK_CC — homebrew clang on
  // macOS). Mixing in another compiler at link time pairs mismatched
  // sanitizer/coverage runtimes, so a missing VALK_CC is an error, not a
  // fallback. $CC is an explicit, deliberate override.
  const char *cc = getenv("CC");
  if (!cc || !*cc) {
    // LCOV_EXCL_START - requires deleting the compiler this runtime was built with
    if (access(VALK_CC, X_OK) != 0) {
      fprintf(stderr,
              "valk --build: compiler %s not found (the toolchain this "
              "runtime was built with)\n"
              "valk --build: install it, or set CC to a matching compiler\n",
              VALK_CC);
      tmp_set_cleanup(&tmps); return 1;
    }
    // LCOV_EXCL_STOP
    cc = VALK_CC;
  }

  char *argv_cc[32];
  int ai = 0;
  argv_cc[ai++] = (char *)cc;
  argv_cc[ai++] = (char *)"-std=gnu2x";
  argv_cc[ai++] = (char *)"-O1";
  // Propagate the sanitizers this binary was built with: the produced
  // executable links the (instrumented) libvalkyria.so next to us, which
  // fails to link without the matching runtimes. The ASAN build config
  // pairs address with undefined (see SANITIZE_ADDRESS_FLAGS).
#if defined(__SANITIZE_ADDRESS__)
  argv_cc[ai++] = (char *)"-fsanitize=address,undefined";
#elif defined(__has_feature)
#if __has_feature(address_sanitizer)
  argv_cc[ai++] = (char *)"-fsanitize=address,undefined";
#elif __has_feature(thread_sanitizer)
  argv_cc[ai++] = (char *)"-fsanitize=thread";
#endif
#endif
#if defined(__SANITIZE_THREAD__)
  argv_cc[ai++] = (char *)"-fsanitize=thread";
#endif
  // Same propagation for gcov instrumentation: in coverage builds the staged
  // valk-shim.o carries profile-arc references, which need the profile
  // runtime at link time.
#ifdef VALK_COVERAGE_BUILD
  argv_cc[ai++] = (char *)"--coverage";
#endif
  // Note: the shim is precompiled (valk-shim.o) together with libvalkyria,
  // so flag-dependent ABI (e.g. VALK_COVERAGE widening valk_lval_t) can
  // never skew — nothing compiled here touches runtime structs.
  argv_cc[ai++] = shim_o;
  argv_cc[ai++] = shim_s;
  argv_cc[ai++] = aot_c;
  if (aot_ok && aot_count > 0) argv_cc[ai++] = aot_o; // LCOV_EXCL_BR_LINE - prelude always yields AOT entries when emit succeeds
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
