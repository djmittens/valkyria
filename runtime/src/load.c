#include "builtins_internal.h"

#ifdef __APPLE__
#include <mach-o/dyld.h>
#endif

#include <limits.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "coverage.h"
#include "gc.h"
#include "macro.h"
#include "type_env.h"

#define VALK_LOAD_PREFIX_MAX 512
#define VALK_LOAD_MAX_DEPTH 64

// ---------------------------------------------------------------------------
// Search roots: the colon-separated VALK_PATH env var, then <exe_dir> and
// <exe_dir>/.. (workspace root when running build/valk).
// ---------------------------------------------------------------------------

#define VALK_PATH_MAX_ENTRIES 16

static char load_root[PATH_MAX];
static bool load_root_ok = false;
static char exe_dir[PATH_MAX];
static bool exe_dir_ok = false;
static char *valk_path_entries[VALK_PATH_MAX_ENTRIES];
static int valk_path_count = 0;
static pthread_once_t load_root_once = PTHREAD_ONCE_INIT;

static void valk_path_init(void) {
  const char *env = getenv("VALK_PATH");
  if (!env || !*env) return;
  char *copy = strdup(env);
  char *save = NULL;
  for (char *tok = strtok_r(copy, ":", &save);
       tok && valk_path_count < VALK_PATH_MAX_ENTRIES;
       tok = strtok_r(NULL, ":", &save)) {
    if (!*tok) continue;
    valk_path_entries[valk_path_count++] = strdup(tok);
  }
  free(copy);
}

static void load_root_init(void) {
  valk_path_init();
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
  exe_dir_ok = realpath(buf, exe_dir) != NULL;
  char joined[PATH_MAX + 4];
  snprintf(joined, sizeof(joined), "%s/..", buf);
  load_root_ok = realpath(joined, load_root) != NULL;
}

// ---------------------------------------------------------------------------
// Load context stack: one frame per file being loaded on this thread. Tracks
// the file's directory (for file-relative resolution), the module prefix in
// effect (for nesting), and the module aliases introduced by child loads
// (for qualified-reference rewriting).
// ---------------------------------------------------------------------------

typedef struct load_alias {
  char *name; // module name as declared by the child, e.g. "io"
  char *full; // effective (nested) prefix, e.g. "bar/io"
} load_alias_t;

typedef struct load_ctx {
  struct load_ctx *parent;
  const char *dir;    // directory of the current file, NULL if none
  const char *prefix; // module prefix in effect ("" at root)
  load_alias_t *aliases;
  int alias_count;
  int alias_cap;
  int depth;
} load_ctx_t;

static _Thread_local load_ctx_t load_root_ctx;
static _Thread_local load_ctx_t *cur_ctx = NULL;

static load_ctx_t *load_cur_ctx(void) {
  if (!cur_ctx) {
    load_root_ctx.prefix = "";
    cur_ctx = &load_root_ctx;
  }
  return cur_ctx;
}

static void compose_prefix(char *out, size_t cap, const char *parent,
                           const char *child) {
  if (parent && parent[0])
    snprintf(out, cap, "%s/%s", parent, child);
  else
    snprintf(out, cap, "%s", child);
}

// Identity aliases (name == full, i.e. loads at the root prefix) are skipped:
// rewriting through them is a no-op, and a context with an empty prefix can
// never shadow a nested alias in an ancestor.
static void ctx_add_alias(load_ctx_t *ctx, const char *name,
                          const char *full) {
  if (!name || !*name) return;
  if (strcmp(name, full) == 0) return;
  for (int i = 0; i < ctx->alias_count; i++) {
    if (strcmp(ctx->aliases[i].name, name) == 0) {
      free(ctx->aliases[i].full);
      ctx->aliases[i].full = strdup(full);
      return;
    }
  }
  if (ctx->alias_count >= ctx->alias_cap) {
    ctx->alias_cap = ctx->alias_cap ? ctx->alias_cap * 2 : 8;
    ctx->aliases = realloc(ctx->aliases,
                           (size_t)ctx->alias_cap * sizeof(load_alias_t));
  }
  ctx->aliases[ctx->alias_count].name = strdup(name);
  ctx->aliases[ctx->alias_count].full = strdup(full);
  ctx->alias_count++;
}

static void ctx_free_aliases(load_ctx_t *ctx) {
  for (int i = 0; i < ctx->alias_count; i++) {
    free(ctx->aliases[i].name);
    free(ctx->aliases[i].full);
  }
  free(ctx->aliases);
  ctx->aliases = NULL;
  ctx->alias_count = ctx->alias_cap = 0;
}

// Resolve a qualified symbol against the module aliases visible from the
// current load context chain (innermost first). A symbol `io/foo` seen in a
// file whose context (or an ancestor) loaded module `io` under effective
// prefix `bar/io` resolves to `bar/io/foo`.
char *valk_load_resolve_alias(const char *name) {
  for (load_ctx_t *c = load_cur_ctx(); c; c = c->parent) {
    for (int i = 0; i < c->alias_count; i++) {
      const char *alias = c->aliases[i].name;
      size_t n = strlen(alias);
      if (strncmp(name, alias, n) != 0) continue;
      if (name[n] != '/' && name[n] != '\0') continue;
      const char *full = c->aliases[i].full;
      size_t len = strlen(full) + strlen(name + n) + 1;
      char *out = malloc(len);
      snprintf(out, len, "%s%s", full, name + n);
      return out;
    }
  }
  return NULL;
}

// ---------------------------------------------------------------------------
// File resolution. Order:
//   1. absolute paths resolve as-is
//   2. relative to the directory of the loading file
//   3. relative to the process cwd
//   4. relative to each VALK_PATH entry (colon-separated env var, in order)
//   5. relative to <exe_dir>/.. (workspace root for build/valk)
//   6. relative to <exe_dir>
// (The env override `file://{path}` is checked before any of this, in
// valk_load_path.)
// ---------------------------------------------------------------------------

// Resolve `path` as a load from a file living in `dir` (NULL when there is
// no loading file). Public so static tooling (the LSP indexer's load-graph
// emission) resolves dependency edges with exactly the runtime's rules.
bool valk_load_resolve_from(const char *dir, const char *path,
                            char *resolved) {
  if (path[0] == '/') return realpath(path, resolved) != NULL;
  char joined[PATH_MAX * 2];
  if (dir) {
    snprintf(joined, sizeof(joined), "%s/%s", dir, path);
    if (realpath(joined, resolved)) return true;
  }
  if (realpath(path, resolved)) return true;
  pthread_once(&load_root_once, load_root_init);
  for (int i = 0; i < valk_path_count; i++) {
    snprintf(joined, sizeof(joined), "%s/%s", valk_path_entries[i], path);
    if (realpath(joined, resolved)) return true;
  }
  if (load_root_ok) {
    snprintf(joined, sizeof(joined), "%s/%s", load_root, path);
    if (realpath(joined, resolved)) return true;
  }
  if (exe_dir_ok) {
    snprintf(joined, sizeof(joined), "%s/%s", exe_dir, path);
    if (realpath(joined, resolved)) return true;
  }
  return false;
}

static bool load_path_resolve(const char *path, char *resolved) {
  return valk_load_resolve_from(load_cur_ctx()->dir, path, resolved);
}

// ---------------------------------------------------------------------------
// Module cache: load-once per (resolved path, parent prefix). The same file
// loaded under different module prefixes evaluates once per prefix — that is
// the nesting semantics. Stores the file's result value (the last top-level
// form's value) so repeat loads return it, plus the module name the file
// declared so repeat loads still register the alias in the caller's context.
// ---------------------------------------------------------------------------

#define MODULE_CACHE_MAX 512
#define MODULE_STATE_LOADING 1
#define MODULE_STATE_READY   2

typedef struct {
  char *resolved_path;
  char *parent_prefix;
  int state;
  char *declared;      // module name declared by the file, or NULL
  valk_lval_t *result; // heap-evacuated result value
} module_entry_t;

static pthread_mutex_t module_cache_lock = PTHREAD_MUTEX_INITIALIZER;
static module_entry_t module_cache[MODULE_CACHE_MAX];
static int module_cache_count = 0;

static module_entry_t *module_cache_find(const char *path,
                                         const char *prefix) {
  for (int i = 0; i < module_cache_count; i++)
    if (strcmp(module_cache[i].resolved_path, path) == 0 &&
        strcmp(module_cache[i].parent_prefix, prefix) == 0)
      return &module_cache[i];
  return NULL;
}

// Called from valk_gc_visit_global_roots. Keeps cached load results alive.
void valk_load_cache_visit_roots(void (*visitor)(valk_lval_t *, void *),
                                 void *ctx) {
  pthread_mutex_lock(&module_cache_lock);
  for (int i = 0; i < module_cache_count; i++)
    if (module_cache[i].result) visitor(module_cache[i].result, ctx);
  pthread_mutex_unlock(&module_cache_lock);
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
  // Preserve coverage source loc so eval-time expr records match the
  // parse-time marks made on the cached original tree.
  INHERIT_SOURCE_LOC(res, v);
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
    VALK_WITH_ALLOC((void *)heap) {
      ast = valk_parse_text_named(text, resolved_path);
    }
  } else {
    ast = valk_parse_text_named(text, resolved_path);
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

// ---------------------------------------------------------------------------
// Module prefix declaration: (module X) expands via set-module-prefix! into
// this thread-local, consumed by eval_loaded_ast.
// ---------------------------------------------------------------------------

static _Thread_local char *pending_module_prefix = NULL;

static char *take_pending_module_prefix(void) {
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

// ---------------------------------------------------------------------------
// Core loader. A file is semantically a (do ...) expression: forms evaluate
// in order, the first error aborts the load, and the last form's value is
// the value of the load.
//
// A (module X) declaration takes effect from its position: every def after
// that point is qualified with the effective prefix (the parent's prefix
// composed with X — that's the nesting), and loads after that point nest
// under it. Loads placed before the (module X) form run in the parent's
// prefix, which lets a module file pull in shared dependencies without
// nesting them.
// ---------------------------------------------------------------------------

// Caller owns `ast` (must be a freshly-owned copy — this function mutates it
// via pop/rewrite). On success, `*out_declared` receives the module name the
// file declared (malloc'd, caller frees) or NULL.
static valk_lval_t *eval_loaded_ast(valk_lenv_t *target_env, valk_lval_t *ast,
                                    const char *dir, char **out_declared) {
  if (out_declared) *out_declared = NULL;

  load_ctx_t *parent = load_cur_ctx();
  if (parent->depth >= VALK_LOAD_MAX_DEPTH)
    return valk_lval_err("load: nesting too deep (max %d)",
                         VALK_LOAD_MAX_DEPTH);

  VALK_GC_ROOT(ast);
  // Stable root slot for the running last-value (updated in place below).
  valk_gc_root_t last_slot = valk_gc_root_push(valk_lval_nil());

  load_ctx_t ctx = {0};
  ctx.parent = parent;
  ctx.dir = dir ? dir : parent->dir;
  ctx.prefix = parent->prefix;
  ctx.depth = parent->depth + 1;
  cur_ctx = &ctx;

  // Pass 1: expand macros and eval macro defs into target_env. A (module X)
  // macro sets pending_module_prefix as a side effect during expansion;
  // record at which form it fired.
  char *prev_pending = pending_module_prefix;
  pending_module_prefix = NULL;
  valk_lval_t *aborted = NULL;
  char *declared = NULL;
  int module_idx = -1;
  {
    int i = 0;
    valk_lval_t *cur = ast;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      if (valk_macro_is_def(cur->cons.head)) {
        valk_lval_t *r = valk_lval_eval(target_env, cur->cons.head);
        if (LVAL_TYPE(r) == LVAL_ERR) { aborted = r; break; }
        VALK_GC_WB_STORE(&cur->cons.head, valk_lval_nil());
      } else {
        VALK_GC_WB_STORE(&cur->cons.head,
                         valk_macro_expand_one(target_env, cur->cons.head));
      }
      if (pending_module_prefix) {
        if (declared) {
          aborted = valk_lval_err(
              "load: multiple module declarations (%s then %s)", declared,
              pending_module_prefix);
          free(take_pending_module_prefix());
          break;
        }
        declared = take_pending_module_prefix();
        module_idx = i;
      }
      cur = cur->cons.tail;
      i++;
    }
  }
  pending_module_prefix = prev_pending;

  char composed[VALK_LOAD_PREFIX_MAX] = "";
  if (declared)
    compose_prefix(composed, sizeof(composed), parent->prefix, declared);

  // Collect this file's bare def names from the module region, so bare
  // references to them can be rewritten to their qualified form.
  valk_module_locals_t *locals = valk_module_locals_new();
  if (!aborted && declared) {
    int i = 0;
    for (valk_lval_t *cur = ast; cur && LVAL_TYPE(cur) == LVAL_CONS;
         cur = cur->cons.tail, i++)
      if (i >= module_idx) valk_module_locals_collect(locals, cur->cons.head);
  }

  // Pass 2+3 interleaved per form: rewrite (module qualification + alias
  // resolution), type-transform, evaluate. Interleaving matters: a load in
  // an earlier form registers a module alias that later forms' references
  // resolve through.
  valk_lval_t *last = NULL;
  int idx = 0;
  while (!aborted && valk_lval_list_count(ast)) {
    bool in_module = declared && idx >= module_idx;
    ctx.prefix = in_module ? composed : parent->prefix;
    valk_module_rewrite_form(ast, in_module ? composed : "", locals,
                             in_module, true);
    valk_lval_t *x = valk_lval_pop(ast, 0);
    idx++;
    VALK_GC_ROOT(x);

    x = valk_type_transform_expr(x);
    if (LVAL_TYPE(x) == LVAL_NIL) continue;
    if (LVAL_TYPE(x) == LVAL_ERR) { aborted = x; break; }
    x = valk_lval_eval(target_env, x);
    if (LVAL_TYPE(x) == LVAL_ERR) { aborted = x; break; }
    last = x;
    if (valk_thread_ctx.root_stack)
      valk_thread_ctx.root_stack[last_slot.saved_count] = last;
    // LCOV_EXCL_START
    valk_gc_heap_t *gc_heap = (valk_gc_heap_t *)valk_thread_ctx.allocator;
    if (gc_heap->type == VALK_ALLOC_GC_HEAP &&
        valk_gc_should_collect(gc_heap))
      valk_gc_heap_collect(gc_heap);
    if (valk_sys && atomic_load(&valk_sys->shutting_down)) break;
    // LCOV_EXCL_STOP
  }

  valk_module_locals_free(locals);
  ctx_free_aliases(&ctx);
  cur_ctx = parent;
  valk_gc_root_pop();

  if (aborted) {
    free(declared);
    return aborted;
  }
  if (out_declared) *out_declared = declared;
  else free(declared);
  return last ? last : valk_lval_nil();
}

// After a child load completed and declared a module, make that module name
// visible as an alias in the caller's context so qualified references
// resolve through the nesting.
static void register_child_alias(const char *declared) {
  if (!declared) return;
  load_ctx_t *ctx = load_cur_ctx();
  char full[VALK_LOAD_PREFIX_MAX];
  compose_prefix(full, sizeof(full), ctx->prefix, declared);
  ctx_add_alias(ctx, declared, full);
}

static valk_lval_t *load_resolved(valk_lenv_t *env, const char *resolved,
                                  const char *orig) {
  const char *pprefix = load_cur_ctx()->prefix;

  pthread_mutex_lock(&module_cache_lock);
  module_entry_t *entry = module_cache_find(resolved, pprefix);
  if (entry && entry->state == MODULE_STATE_READY) {
    valk_lval_t *res = entry->result;
    const char *declared = entry->declared;
    char declared_buf[VALK_LOAD_PREFIX_MAX] = "";
    if (declared)
      snprintf(declared_buf, sizeof(declared_buf), "%s", declared);
    pthread_mutex_unlock(&module_cache_lock);
    if (declared_buf[0]) register_child_alias(declared_buf);
    return res ? res : valk_lval_nil();
  }
  if (entry && entry->state == MODULE_STATE_LOADING) {
    pthread_mutex_unlock(&module_cache_lock);
    return valk_lval_err("Circular load detected: %s", orig);
  }
  if (!entry) {
    if (module_cache_count >= MODULE_CACHE_MAX) { // LCOV_EXCL_BR_LINE
      pthread_mutex_unlock(&module_cache_lock); // LCOV_EXCL_LINE
      return valk_lval_err("Module cache full"); // LCOV_EXCL_LINE
    }
    entry = &module_cache[module_cache_count++];
    entry->resolved_path = strdup(resolved);
    entry->parent_prefix = strdup(pprefix);
  }
  entry->state = MODULE_STATE_LOADING;
  pthread_mutex_unlock(&module_cache_lock);

  valk_lval_t *ast = parse_file_cached(resolved);
  if (LVAL_TYPE(ast) == LVAL_ERR) {
    entry->state = 0;
    return ast;
  }

  char dir[PATH_MAX];
  snprintf(dir, sizeof(dir), "%s", resolved);
  char *slash = strrchr(dir, '/');
  if (slash) *slash = 0;

  char *declared = NULL;
  valk_lval_t *result = eval_loaded_ast(env, ast, slash ? dir : NULL,
                                        &declared);
  if (LVAL_TYPE(result) == LVAL_ERR) {
    entry->state = 0;
    free(declared);
    return result;
  }

  result = valk_evacuate_to_heap(result);
  pthread_mutex_lock(&module_cache_lock);
  entry->declared = declared;
  entry->result = result;
  entry->state = MODULE_STATE_READY;
  pthread_mutex_unlock(&module_cache_lock);

  register_child_alias(declared);
  return result;
}

// Resolution order: env override `file://{path}` first, then the filesystem.
// The override's value is a list of top-level forms that goes through the
// same pipeline a file would (module nesting included) — it lets the REPL
// (or any code) provide a file inline, overriding what's on disk.
static valk_lval_t *valk_load_path(valk_lenv_t *env, const char *path) {
  valk_coverage_record_file(path);

  char symname[PATH_MAX + 8];
  snprintf(symname, sizeof(symname), "file://%s", path);
  valk_lval_t *override = valk_lenv_get(env, valk_lval_sym(symname));
  if (LVAL_TYPE(override) != LVAL_ERR) {
    if (LVAL_TYPE(override) != LVAL_CONS && LVAL_TYPE(override) != LVAL_NIL)
      return valk_lval_err("load: %s override must be a list of forms",
                           symname);
    valk_lval_t *ast = deep_clone_ast(override);
    char *declared = NULL;
    valk_lval_t *result = eval_loaded_ast(env, ast, NULL, &declared);
    if (LVAL_TYPE(result) != LVAL_ERR) register_child_alias(declared);
    free(declared);
    return result;
  }

  char resolved[PATH_MAX];
  if (!load_path_resolve(path, resolved))
    return valk_lval_err("Could not resolve file (%s)", path);
  return load_resolved(env, resolved, path);
}

valk_lval_t *valk_load_file(valk_lenv_t *env, const char *path) {
  return valk_load_path(env, path);
}

static valk_lval_t *valk_builtin_load(valk_lenv_t *e, valk_lval_t *a) {
  // LCOV_EXCL_BR_START
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  return valk_load_path(e, valk_lval_list_nth(a, 0)->str);
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
        VALK_GC_WB_STORE(&cur->cons.head, valk_lval_nil());
      } else {
        VALK_GC_WB_STORE(&cur->cons.head,
                         valk_macro_expand_one(menv, cur->cons.head));
      }
      cur = cur->cons.tail;
    }
  }

  char *pending = take_pending_module_prefix();
  if (!prefix && pending) prefix = pending;
  valk_module_apply_prefix(ast, prefix);
  free(pending);
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

void valk_register_load_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "load", valk_builtin_load);
  valk_lenv_put_builtin(env, "set-module-prefix!",
                        valk_builtin_set_module_prefix);
  valk_lenv_put_builtin(env, "parse-file", valk_builtin_parse_file);
  valk_lenv_put_builtin(env, "compile/process", valk_builtin_compile_process);
  valk_lenv_put_builtin(env, "compile/process-file",
                        valk_builtin_compile_process_file);
}
