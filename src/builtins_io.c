#include "builtins_internal.h"

#ifdef __APPLE__
#include <mach-o/dyld.h>
#endif

#include <errno.h>
#include <limits.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "coverage.h"
#include "diag.h"
#include "gc.h"
#include "macro.h"
#include "type_env.h"

extern void valk_register_file_builtins(valk_lenv_t *env);

static char load_root[PATH_MAX];
static bool load_root_ok = false;
static pthread_once_t load_root_once = PTHREAD_ONCE_INIT;

static void load_root_init(void) {
  char buf[PATH_MAX];
#ifdef __APPLE__
  uint32_t bufsize = sizeof(buf);
  if (_NSGetExecutablePath(buf, &bufsize) != 0) return;
#else
  ssize_t n = readlink("/proc/self/exe", buf, sizeof(buf) - 1);
  if (n <= 0) return; // LCOV_EXCL_LINE
  buf[n] = 0;
#endif
  char *slash = strrchr(buf, '/');
  if (!slash) return; // LCOV_EXCL_LINE
  *slash = 0;
  char joined[PATH_MAX + 4];
  snprintf(joined, sizeof(joined), "%s/..", buf);
  load_root_ok = realpath(joined, load_root) != NULL;
}

static bool load_path_resolve(const char *path, char *resolved) {
  if (realpath(path, resolved)) return true;
  if (path[0] == '/') return false;
  pthread_once(&load_root_once, load_root_init);
  if (!load_root_ok) return false; // LCOV_EXCL_LINE
  char joined[PATH_MAX * 2];
  snprintf(joined, sizeof(joined), "%s/%s", load_root, path);
  return realpath(joined, resolved) != NULL;
}

#define MODULE_CACHE_MAX 512
#define MODULE_STATE_LOADING 1
#define MODULE_STATE_READY   2

typedef struct {
  char *resolved_path;
  int state;
} module_entry_t;

static pthread_mutex_t module_cache_lock = PTHREAD_MUTEX_INITIALIZER;
static module_entry_t module_cache[MODULE_CACHE_MAX];
static int module_cache_count = 0;

static module_entry_t *module_cache_find(const char *path) {
  for (int i = 0; i < module_cache_count; i++)
    if (strcmp(module_cache[i].resolved_path, path) == 0)
      return &module_cache[i];
  return NULL;
}

// ---------------------------------------------------------------------------
// Parse cache: stores the raw AST of each file keyed by realpath + mtime.
// Hits return a deep-clone so callers can mutate freely. File mtime change
// invalidates. LRU-bounded. Registered as a GC root so cached ASTs survive
// collections.
// ---------------------------------------------------------------------------

#define PARSE_CACHE_MAX 256

typedef struct {
  char *path;          // resolved realpath; NULL slot = empty
  time_t mtime;
  valk_lval_t *ast;    // raw parsed AST (pre-macro, pre-rewrite)
  u64 lru_tick;
} parse_entry_t;

static pthread_mutex_t parse_cache_lock = PTHREAD_MUTEX_INITIALIZER;
static parse_entry_t parse_cache[PARSE_CACHE_MAX];
static int parse_cache_count = 0;
static u64 parse_cache_tick = 0;

// Deep-clone an AST: copy every CONS cell recursively; share leaves.
// Leaves (sym, num, str, err, fun) are effectively immutable — callers mutate
// the list spine (via pop / head / tail assignment), not leaf contents.
static valk_lval_t *deep_clone_ast(valk_lval_t *v) {
  if (!v) return nullptr;
  if (LVAL_TYPE(v) != LVAL_CONS) return valk_lval_copy(v);
  valk_lval_t *h = deep_clone_ast(v->cons.head);
  valk_lval_t *t = deep_clone_ast(v->cons.tail);
  valk_lval_t *res = (v->flags & LVAL_FLAG_QUOTED)
    ? valk_lval_qcons(h, t)
    : valk_lval_cons(h, t);
  // Preserve src-pos for error reporting.
  LVAL_SRC_POS_SET(res, LVAL_SRC_POS(v));
  return res;
}

static parse_entry_t *parse_cache_alloc(void) {
  if (parse_cache_count < PARSE_CACHE_MAX)
    return &parse_cache[parse_cache_count++];
  // Evict LRU.
  parse_entry_t *victim = &parse_cache[0];
  for (int i = 1; i < parse_cache_count; i++)
    if (parse_cache[i].lru_tick < victim->lru_tick) victim = &parse_cache[i];
  free(victim->path);
  victim->path = NULL;
  victim->ast = NULL;
  return victim;
}

// Called from valk_gc_visit_global_roots. Keeps cached ASTs alive across GC.
void valk_parse_cache_visit_roots(void (*visitor)(valk_lval_t *, void *),
                                   void *ctx) {
  pthread_mutex_lock(&parse_cache_lock);
  for (int i = 0; i < parse_cache_count; i++)
    if (parse_cache[i].ast) visitor(parse_cache[i].ast, ctx);
  pthread_mutex_unlock(&parse_cache_lock);
}

// Return a fresh, mutable deep-clone of the parsed AST for `resolved_path`.
// Miss: parse from disk, insert. Stale (mtime changed): reparse.
static valk_lval_t *parse_file_cached(const char *resolved_path) {
  struct stat st;
  time_t mtime = (stat(resolved_path, &st) == 0) ? st.st_mtime : 0;

  pthread_mutex_lock(&parse_cache_lock);
  for (int i = 0; i < parse_cache_count; i++) {
    parse_entry_t *e = &parse_cache[i];
    if (e->path && strcmp(e->path, resolved_path) == 0) {
      if (e->ast && e->mtime == mtime) {
        e->lru_tick = ++parse_cache_tick;
        valk_lval_t *clone = deep_clone_ast(e->ast);
        pthread_mutex_unlock(&parse_cache_lock);
        return clone;
      }
      // Stale — drop and reparse below.
      e->ast = NULL;
      break;
    }
  }
  pthread_mutex_unlock(&parse_cache_lock);

  FILE *f = fopen(resolved_path, "rb");
  if (!f) return valk_lval_err("Could not open file (%s)", resolved_path);
  fseek(f, 0, SEEK_END);
  long flen = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (flen <= 0) { fclose(f); return valk_lval_err("Empty file (%s)", resolved_path); }
  char *text = calloc((size_t)flen + 1, 1);
  fread(text, 1, (size_t)flen, f);
  fclose(f);

  // Allocate the cached AST on the GC heap so it is stable across scratch
  // arena resets. The eval loop rolls back scratch offsets at continuation
  // boundaries; any scratch pointer stored in the cache would dangle after
  // the next rollback, causing valk_parse_cache_visit_roots to crash.
  valk_gc_heap_t *heap = valk_thread_ctx.heap
                           ? (valk_gc_heap_t *)valk_thread_ctx.heap
                           : (valk_sys ? valk_sys->heap : NULL);
  valk_lval_t *ast;
  if (heap) {
    VALK_WITH_ALLOC((void *)heap) { ast = valk_parse_text(text); }
  } else {
    ast = valk_parse_text(text);
  }
  free(text);
  if (LVAL_TYPE(ast) == LVAL_ERR) return ast;

  pthread_mutex_lock(&parse_cache_lock);
  parse_entry_t *slot = NULL;
  for (int i = 0; i < parse_cache_count; i++) {
    if (parse_cache[i].path && strcmp(parse_cache[i].path, resolved_path) == 0) {
      slot = &parse_cache[i];
      break;
    }
  }
  if (!slot) {
    slot = parse_cache_alloc();
    slot->path = strdup(resolved_path);
  }
  slot->mtime = mtime;
  slot->ast = ast;
  slot->lru_tick = ++parse_cache_tick;
  valk_lval_t *clone = deep_clone_ast(ast);
  pthread_mutex_unlock(&parse_cache_lock);
  return clone;
}



// Set by the (module X) macro at expansion time. Files without a (module X)
// declaration load with no prefix — their top-level defs land in the env as
// bare names. Cleared at end of each eval_loaded_ast call.
static _Thread_local char *pending_module_prefix = NULL;

// Take ownership of any pending module prefix set via (module X) during
// macro expansion, clearing the slot. Returns NULL if none was set.
// Caller must free the returned pointer.
char *valk_take_pending_module_prefix(void) {
  char *p = pending_module_prefix;
  pending_module_prefix = NULL;
  return p;
}

static valk_lval_t *valk_builtin_set_module_prefix(valk_lenv_t *e,
                                                    valk_lval_t *a) {
  (void)e;
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *arg = valk_lval_list_nth(a, 0);
  const char *name = NULL;
  if (LVAL_TYPE(arg) == LVAL_SYM || LVAL_TYPE(arg) == LVAL_STR) name = arg->str;
  if (!name || !*name)
    return valk_lval_err("set-module-prefix!: expected non-empty sym or str");
  if (pending_module_prefix) free(pending_module_prefix);
  pending_module_prefix = strdup(name);
  return valk_lval_nil();
}



// Caller owns `ast` (must be a freshly-owned copy — this function mutates it
// via pop/rewrite). Returns the last form's value or the first error.
static valk_lval_t *eval_loaded_ast(valk_lenv_t *target_env,
                                    valk_lval_t *ast) {
  // The remaining AST is referenced only by this C frame while each
  // top-level form is evaluated (and the loop below explicitly collects
  // between forms) — without a root the collector sweeps the not-yet-
  // evaluated tail of the file mid-load.
  VALK_GC_ROOT(ast);
  // Pass 1: expand macros and eval macro defs into target_env. Macros and
  // regular defs live in the same env now, so (macro ...) just evals like
  // any other top-level form. A top-level `(module X)` macro here sets
  // `pending_module_prefix` as a side effect.
  char *prev_pending = pending_module_prefix;
  pending_module_prefix = NULL;
  {
    valk_lval_t *cur = ast;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      if (valk_macro_is_def(cur->cons.head)) {
        valk_lval_t *r = valk_lval_eval(target_env, cur->cons.head);
        if (LVAL_TYPE(r) == LVAL_ERR) valk_lval_println(r);
        cur->cons.head = valk_lval_nil();
      } else {
        cur->cons.head = valk_macro_expand_one(target_env, cur->cons.head);
      }
      cur = cur->cons.tail;
    }
  }

  // Pass 2: if (module X) was declared, qualify this file's def/sig/type
  // names with that prefix. Files without (module X) load with no prefix.
  if (pending_module_prefix)
    valk_module_apply_prefix(ast, pending_module_prefix);
  if (pending_module_prefix) {
    free(pending_module_prefix);
    pending_module_prefix = NULL;
  }
  pending_module_prefix = prev_pending;

  // Pass 3: evaluate. Errors are printed but do not abort subsequent
  // forms — a failed assertion in one top-level expression shouldn't
  // halt loading the rest of the file.
  valk_lval_t *last = nullptr;
  while (valk_lval_list_count(ast)) {
    valk_lval_t *x = valk_lval_pop(ast, 0);
    // Popping unlinked x from the rooted ast; it must survive the
    // allocations inside the type transform below.
    VALK_GC_ROOT(x);

    x = valk_type_transform_expr(x);
    if (LVAL_TYPE(x) == LVAL_NIL) continue;
    if (LVAL_TYPE(x) == LVAL_ERR) { // LCOV_EXCL_BR_LINE
      valk_lval_println(x); // LCOV_EXCL_LINE
      continue;             // LCOV_EXCL_LINE
    }
    x = valk_lval_eval(target_env, x);
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
    } else {
      last = x;
    }
    // LCOV_EXCL_START
    valk_gc_heap_t *gc_heap = (valk_gc_heap_t *)valk_thread_ctx.allocator;
    if (gc_heap->type == VALK_ALLOC_GC_HEAP &&
        valk_gc_should_collect(gc_heap))
      valk_gc_heap_collect(gc_heap);
    // LCOV_EXCL_STOP
  }
  return last ? last : valk_lval_nil();
}

static valk_lval_t *valk_builtin_load(valk_lenv_t *e, valk_lval_t *a) {
  u64 argc = valk_lval_list_count(a);
  // LCOV_EXCL_BR_START
  if (argc < 1 || argc > 2)
    LVAL_RAISE(a, "load: expected 1-2 arguments, got %llu", argc);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  if (argc == 2)
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_SYM);
  // LCOV_EXCL_BR_STOP

  const char *filename = valk_lval_list_nth(a, 0)->str;
  valk_coverage_record_file(filename);

  char resolved[PATH_MAX];
  if (!load_path_resolve(filename, resolved))
    return valk_lval_err("Could not resolve file (%s)", filename);

  pthread_mutex_lock(&module_cache_lock);

  module_entry_t *cached = module_cache_find(resolved);
  if (cached && cached->state == MODULE_STATE_READY) {
    pthread_mutex_unlock(&module_cache_lock);
    return valk_lval_nil();
  }

  if (cached && cached->state == MODULE_STATE_LOADING) {
    pthread_mutex_unlock(&module_cache_lock);
    return valk_lval_err("Circular load detected: %s", filename);
  }

  if (module_cache_count >= MODULE_CACHE_MAX) { // LCOV_EXCL_BR_LINE
    pthread_mutex_unlock(&module_cache_lock); // LCOV_EXCL_LINE
    return valk_lval_err("Module cache full"); // LCOV_EXCL_LINE
  }
  module_entry_t *entry = &module_cache[module_cache_count++];
  entry->resolved_path = strdup(resolved);
  entry->state = MODULE_STATE_LOADING;
  pthread_mutex_unlock(&module_cache_lock);

  valk_lval_t *ast = parse_file_cached(resolved);
  if (LVAL_TYPE(ast) == LVAL_ERR) {
    entry->state = 0;
    return ast;
  }

  valk_lval_t *result = eval_loaded_ast(e, ast);

  if (LVAL_TYPE(result) == LVAL_ERR) {
    entry->state = 0;
    return result;
  }

  pthread_mutex_lock(&module_cache_lock);
  entry->state = MODULE_STATE_READY;
  pthread_mutex_unlock(&module_cache_lock);

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_read(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* input = valk_lval_list_nth(a, 0)->str;
  int pos = 0;
  return valk_lval_read(&pos, input);
}

valk_lval_t *valk_load_file(valk_lenv_t *env, const char *path) {
  char resolved[PATH_MAX];
  if (!load_path_resolve(path, resolved))
    return valk_lval_err("Could not resolve file (%s)", path);
  valk_lval_t *ast = parse_file_cached(resolved);
  if (LVAL_TYPE(ast) == LVAL_ERR) return ast;
  return eval_loaded_ast(env, ast);
}

static valk_lval_t* valk_builtin_parse(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  return valk_parse_text(valk_lval_list_nth(a, 0)->str);
}

// Parse a file via the AST cache (mtime-keyed). Skips reparse on hit.
static valk_lval_t *valk_builtin_parse_file(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  const char *path = valk_lval_list_nth(a, 0)->str;
  char resolved[PATH_MAX];
  if (!load_path_resolve(path, resolved))
    return valk_lval_err("Could not resolve file (%s)", path);
  return parse_file_cached(resolved);
}

// Shared body: macro-expand + module-prefix application for an already-parsed
// AST. Returns the (mutated) ast.
static valk_lval_t *compile_process_ast(valk_lval_t *ast, const char *prefix) {
  valk_lenv_t *menv = valk_macro_env();
  {
    valk_lval_t *cur = ast;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      if (valk_macro_is_def(cur->cons.head)) {
        valk_lval_t *r = valk_lval_eval(menv, cur->cons.head);
        if (LVAL_TYPE(r) == LVAL_ERR) valk_lval_println(r);
        cur->cons.head = valk_lval_nil();
      } else {
        cur->cons.head = valk_macro_expand_one(menv, cur->cons.head);
      }
      cur = cur->cons.tail;
    }
  }

  valk_module_apply_prefix(ast, prefix);
  return ast;
}

static valk_lval_t *valk_builtin_compile_process(valk_lenv_t *e,
                                                  valk_lval_t *a) {
  UNUSED(e);
  u64 argc = valk_lval_list_count(a);
  if (argc < 1 || argc > 2)
    LVAL_RAISE(a, "compile/process: expected 1-2 arguments, got %llu", argc);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char *text = valk_lval_list_nth(a, 0)->str;
  const char *prefix = NULL;
  if (argc >= 2) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
    prefix = valk_lval_list_nth(a, 1)->str;
    if (prefix[0] == '\0') prefix = NULL;
  }

  valk_lval_t *ast = valk_parse_text(text);
  if (LVAL_TYPE(ast) == LVAL_ERR) return ast;
  VALK_GC_ROOT(ast);
  return compile_process_ast(ast, prefix);
}

// Like compile/process but takes a path and uses the parse cache. Avoids
// reparsing files that haven't changed (huge win for valk-check, which
// processes every .valk file in the project).
static valk_lval_t *valk_builtin_compile_process_file(valk_lenv_t *e,
                                                      valk_lval_t *a) {
  UNUSED(e);
  u64 argc = valk_lval_list_count(a);
  if (argc < 1 || argc > 2)
    LVAL_RAISE(a, "compile/process-file: expected 1-2 arguments, got %llu", argc);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char *path = valk_lval_list_nth(a, 0)->str;
  const char *prefix = NULL;
  if (argc >= 2) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
    prefix = valk_lval_list_nth(a, 1)->str;
    if (prefix[0] == '\0') prefix = NULL;
  }

  char resolved[PATH_MAX];
  if (!load_path_resolve(path, resolved))
    return valk_lval_err("Could not resolve file (%s)", path);

  valk_lval_t *ast = parse_file_cached(resolved);
  if (LVAL_TYPE(ast) == LVAL_ERR) return ast;
  VALK_GC_ROOT(ast);
  return compile_process_ast(ast, prefix);
}


static valk_lval_t* valk_builtin_src_pos(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_SRC_POS(v));
}

static valk_lval_t* valk_builtin_quoted_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num((v->flags & LVAL_FLAG_QUOTED) ? 1 : 0);
}

static valk_lval_t* valk_builtin_offset_to_line_col(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);
  // LCOV_EXCL_BR_STOP
  const char *text = valk_lval_list_nth(a, 0)->str;
  int offset = (int)valk_lval_list_nth(a, 1)->num;
  int line = 0, col = 0;
  for (int i = 0; i < offset && text[i]; i++) {
    if (text[i] == '\n') { line++; col = 0; }
    else col++;
  }
  valk_lval_t *items[2] = {valk_lval_num(line), valk_lval_num(col)};
  return valk_lval_qlist(items, 2);
}

static valk_lval_t* valk_builtin_qcons(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* arg1 = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, arg1, LVAL_CONS, LVAL_NIL);
  // LCOV_EXCL_BR_STOP
  return valk_lval_qcons(valk_lval_list_nth(a, 0), arg1);
}

static valk_lval_t* valk_builtin_type_of(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_str(valk_ltype_name(LVAL_TYPE(v)));
}

static valk_lval_t* valk_builtin_str_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_STR ? 1 : 0);
}

static valk_lval_t* valk_builtin_sym_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_SYM ? 1 : 0);
}

static valk_lval_t* valk_builtin_num_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_NUM ? 1 : 0);
}

static valk_lval_t* valk_builtin_fun_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_FUN ? 1 : 0);
}

static valk_lval_t* valk_builtin_read_file(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* filename = valk_lval_list_nth(a, 0)->str;
  FILE* f = fopen(filename, "rb");
  if (f == nullptr) {
    LVAL_RAISE(a, "Could not open file (%s)", filename);
  }

  fseek(f, 0, SEEK_END);
  u64 length = ftell(f);
  fseek(f, 0, SEEK_SET);

  // LCOV_EXCL_START - ftell overflow and partial fread are platform failures
  if (length == UINT64_MAX) {
    fclose(f);
    LVAL_RAISE(a, "File is too large (%s)", filename);
  }
  // LCOV_EXCL_STOP

  char* content = calloc(length + 1, sizeof(char));
  u64 read_len = fread(content, 1, length, f);
  fclose(f);

  // LCOV_EXCL_START - partial fread requires I/O failure mid-read
  if (read_len != length) {
    free(content);
    LVAL_RAISE(a, "Failed to read file (%s)", filename);
  }
  // LCOV_EXCL_STOP

  valk_lval_t* result = valk_lval_str(content);
  free(content);
  return result;
}

static valk_lval_t* valk_builtin_error(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  valk_lval_t* err = valk_lval_err("%s", valk_lval_list_nth(a, 0)->str);
  return err;
}

static valk_lval_t* valk_builtin_error_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_TYPE(v) == LVAL_ERR ? 1 : 0);
}

static valk_lval_t* valk_builtin_list_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  valk_ltype_e t = LVAL_TYPE(v);
  return valk_lval_num(t == LVAL_CONS || t == LVAL_NIL || t == LVAL_QEXPR ? 1 : 0);
}

static valk_lval_t* valk_builtin_ref_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_TYPE(v) == LVAL_REF ? 1 : 0);
}

void valk_register_io_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "error", valk_builtin_error);
  valk_lenv_put_builtin_err_ok(env, "error?", valk_builtin_error_p);
  valk_lenv_put_builtin(env, "list?", valk_builtin_list_p);
  valk_lenv_put_builtin(env, "ref?", valk_builtin_ref_p);
  valk_lenv_put_builtin(env, "load", valk_builtin_load);
  valk_lenv_put_builtin(env, "set-module-prefix!",
                        valk_builtin_set_module_prefix);
  valk_lenv_put_builtin(env, "read", valk_builtin_read);
  valk_lenv_put_builtin(env, "parse", valk_builtin_parse);
  valk_lenv_put_builtin(env, "parse-file", valk_builtin_parse_file);
  valk_lenv_put_builtin(env, "read-file", valk_builtin_read_file);
  valk_lenv_put_builtin(env, "src-pos", valk_builtin_src_pos);
  valk_lenv_put_builtin(env, "qcons", valk_builtin_qcons);
  valk_lenv_put_builtin_err_ok(env, "type-of", valk_builtin_type_of);
  valk_lenv_put_builtin(env, "str?", valk_builtin_str_p);
  valk_lenv_put_builtin(env, "sym?", valk_builtin_sym_p);
  valk_lenv_put_builtin(env, "num?", valk_builtin_num_p);
  valk_lenv_put_builtin(env, "fun?", valk_builtin_fun_p);
  valk_lenv_put_builtin(env, "quoted?", valk_builtin_quoted_p);
  valk_lenv_put_builtin(env, "offset->line-col", valk_builtin_offset_to_line_col);
  valk_lenv_put_builtin(env, "compile/process", valk_builtin_compile_process);
  valk_lenv_put_builtin(env, "compile/process-file",
                        valk_builtin_compile_process_file);
  valk_register_file_builtins(env);
}
