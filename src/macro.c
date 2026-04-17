#include "macro.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static valk_lenv_t *g_macro_env = NULL;

// Thread-local registry of module prefixes loaded so far. Used by the
// sibling rewriter to decide whether `X/Y` in a file with prefix `P`
// should be rewritten to `A/X/Y` for some ancestor `A` of `P`.
typedef struct prefix_node_s {
  char *prefix;
  struct prefix_node_s *next;
} prefix_node_t;
static _Thread_local prefix_node_t *g_loaded_prefixes = NULL;

bool valk_mod_registry_has(const char *prefix) {
  for (prefix_node_t *n = g_loaded_prefixes; n; n = n->next)
    if (strcmp(n->prefix, prefix) == 0) return true;
  return false;
}

void valk_mod_registry_add(const char *prefix) {
  if (!prefix || !*prefix) return;
  if (valk_mod_registry_has(prefix)) return;
  prefix_node_t *n = malloc(sizeof(*n));
  n->prefix = strdup(prefix);
  n->next = g_loaded_prefixes;
  g_loaded_prefixes = n;
}

valk_lenv_t *valk_macro_env(void) {
  if (!g_macro_env) {
    g_macro_env = valk_lenv_empty();
    valk_lenv_builtins(g_macro_env);
  }
  return g_macro_env;
}

void valk_macro_env_set(const char *key, valk_lval_t *val) {
  valk_lenv_t *menv = valk_macro_env();
  valk_lenv_def(menv, valk_lval_sym(key), val);
}

bool valk_macro_is_def(valk_lval_t *expr) {
  if (!expr || LVAL_TYPE(expr) != LVAL_CONS) return false;
  if (expr->flags & LVAL_FLAG_QUOTED) return false;
  valk_lval_t *head = expr->cons.head;
  return LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "macro") == 0;
}

static valk_lval_t *expand_expr(valk_lenv_t *menv, valk_lval_t *expr) {
  if (!expr || LVAL_TYPE(expr) != LVAL_CONS) return expr;
  if (expr->flags & LVAL_FLAG_QUOTED) return expr;
  valk_lval_t *head = expr->cons.head;
  if (LVAL_TYPE(head) != LVAL_SYM) return expr;
  if (strcmp(head->str, "macro") == 0) return expr;

  valk_lval_t *val = valk_lenv_get(menv, head);
  if (LVAL_TYPE(val) == LVAL_ERR) return expr;
  if (LVAL_TYPE(val) != LVAL_FUN || !(val->flags & LVAL_FLAG_MACRO))
    return expr;

  valk_lval_t *args = expr->cons.tail;
  if (args && LVAL_TYPE(args) == LVAL_CONS)
    args->flags |= LVAL_FLAG_QUOTED;

  valk_lval_t *result = valk_lval_eval_call(menv, val, args);
  if (LVAL_TYPE(result) == LVAL_ERR) {
    fprintf(stderr, "macro expansion error in '%s': ", head->str);
    valk_lval_println(result);
    return result;
  }
  return expand_expr(menv, result);
}

valk_lval_t *valk_macro_expand_one(valk_lenv_t *menv, valk_lval_t *expr) {
  return expand_expr(menv, expr);
}

valk_lval_t *valk_eval_form(valk_lenv_t *env, valk_lval_t *form) {
  valk_lenv_t *menv = valk_macro_env();
  if (valk_macro_is_def(form))
    return valk_lval_eval(menv, form);
  form = valk_macro_expand_one(menv, form);
  return valk_lval_eval(env, form);
}

// ---------------------------------------------------------------------------
// Module prefix application (replaces the old module-tree FQN rewriter).
//
// For each top-level form in `ast`:
//   - Qualify unqualified def/sig/type names by prepending `prefix/`.
// Then walk the whole AST with shadow tracking and rewrite bare symbol
// references to locally-defined names into their qualified form — so code
// like `(foo 1)` inside a file that defines `(fun {foo x} ...)` keeps
// working without manual qualification.
//
// No module tree, no sibling resolution, no pre-registration. Cross-file
// references must already be fully qualified (e.g. `nav/handle-hover`);
// simple env lookup handles them.
// ---------------------------------------------------------------------------

#define VALK_MOD_PATH_MAX 512

// --- Local-defs set: flat growable string array with O(n) lookup. ---

typedef struct {
  char **names;
  int count;
  int cap;
} name_set_t;

static void name_set_add(name_set_t *s, const char *name) {
  for (int i = 0; i < s->count; i++)
    if (strcmp(s->names[i], name) == 0) return;
  if (s->count >= s->cap) {
    s->cap = s->cap ? s->cap * 2 : 16;
    s->names = realloc(s->names, (size_t)s->cap * sizeof(char *));
  }
  s->names[s->count++] = strdup(name);
}

static bool name_set_has(name_set_t *s, const char *name) {
  for (int i = 0; i < s->count; i++)
    if (strcmp(s->names[i], name) == 0) return true;
  return false;
}

static void name_set_free(name_set_t *s) {
  for (int i = 0; i < s->count; i++) free(s->names[i]);
  free(s->names);
}

// --- Name qualification helpers. ---

static valk_lval_t *qualify_sym(const char *prefix, const char *name,
                                i32 src_pos) {
  char buf[VALK_MOD_PATH_MAX];
  snprintf(buf, sizeof(buf), "%s/%s", prefix, name);
  valk_lval_t *sym = valk_lval_sym(buf);
  if (src_pos >= 0) LVAL_SRC_POS_SET(sym, src_pos);
  return sym;
}

// Returns the def form's name (with possible `/` inside) or NULL if the
// form isn't a `def` or the name is invalid. Used by Pass 1a to collect
// local bare-name defs that feed intra-file reference rewriting.
static const char *extract_unqualified_def_name(valk_lval_t *form) {
  if (!form || LVAL_TYPE(form) != LVAL_CONS) return NULL;
  if (form->flags & LVAL_FLAG_QUOTED) return NULL;
  valk_lval_t *head = form->cons.head;
  if (!head || LVAL_TYPE(head) != LVAL_SYM) return NULL;
  if (strcmp(head->str, "def") != 0) return NULL;

  valk_lval_t *rest = form->cons.tail;
  if (!rest || LVAL_TYPE(rest) != LVAL_CONS) return NULL;

  valk_lval_t *sym = rest->cons.head;
  const char *name = NULL;
  if (LVAL_TYPE(sym) == LVAL_SYM) {
    name = sym->str;
  } else if (LVAL_TYPE(sym) == LVAL_CONS && sym->cons.head &&
             LVAL_TYPE(sym->cons.head) == LVAL_SYM) {
    name = sym->cons.head->str;
  }
  if (!name || name[0] == ':' || strchr(name, '/')) return NULL;
  return name;
}

// If `name` is `X/...` and some ancestor of `prefix` ends in `/X` or
// equals `X`, return the ancestor that matches (with its last segment
// stripped, i.e. the parent). Returns "" (empty) if X is at the top.
// Returns NULL if no ancestor matches — caller should leave the def
// name alone (self-namespaced).
static bool find_anchor_parent(const char *name, const char *prefix,
                               char *out, size_t out_sz) {
  const char *slash = strchr(name, '/');
  if (!slash) return false;
  size_t first_len = (size_t)(slash - name);
  if (!prefix || !*prefix) return false;

  char ancestor[VALK_MOD_PATH_MAX];
  snprintf(ancestor, sizeof(ancestor), "%s", prefix);
  while (ancestor[0]) {
    const char *last = strrchr(ancestor, '/');
    const char *last_seg = last ? last + 1 : ancestor;
    if (strlen(last_seg) == first_len &&
        memcmp(last_seg, name, first_len) == 0) {
      if (last) {
        size_t plen = (size_t)(last - ancestor);
        if (plen >= out_sz) plen = out_sz - 1;
        memcpy(out, ancestor, plen);
        out[plen] = '\0';
      } else {
        out[0] = '\0';
      }
      return true;
    }
    if (!last) break;
    *(char *)last = '\0';
  }
  return false;
}

// Mutate the name cell in a top-level def form to its qualified form.
// Bare names gain a `prefix/` prefix. `/`-containing names whose first
// segment duplicates an ancestor of `prefix` get the ancestor prepended
// (e.g. `symdb/foo` in module `lsp/symdb` → `lsp/symdb/foo`). Other
// `/`-containing names (e.g. `lsp/find-local-def` in module `lsp/nav`)
// self-namespace and stay unchanged.
static void qualify_def_name(valk_lval_t *form, const char *prefix) {
  valk_lval_t *rest = form->cons.tail;
  if (!rest || LVAL_TYPE(rest) != LVAL_CONS) return;

  valk_lval_t *sym_cell = rest->cons.head;
  valk_lval_t **slot = NULL;
  valk_lval_t *sym = NULL;
  if (LVAL_TYPE(sym_cell) == LVAL_SYM) {
    sym = sym_cell;
    slot = &rest->cons.head;
  } else if (LVAL_TYPE(sym_cell) == LVAL_CONS && sym_cell->cons.head &&
             LVAL_TYPE(sym_cell->cons.head) == LVAL_SYM) {
    sym = sym_cell->cons.head;
    slot = &sym_cell->cons.head;
  }
  if (!sym || !slot) return;
  if (sym->str[0] == ':') return;

  if (!strchr(sym->str, '/')) {
    *slot = qualify_sym(prefix, sym->str, LVAL_SRC_POS(sym));
    return;
  }

  char parent[VALK_MOD_PATH_MAX];
  if (!find_anchor_parent(sym->str, prefix, parent, sizeof(parent))) return;

  char buf[VALK_MOD_PATH_MAX];
  if (*parent)
    snprintf(buf, sizeof(buf), "%s/%s", parent, sym->str);
  else
    snprintf(buf, sizeof(buf), "%s", sym->str);
  if (strcmp(buf, sym->str) == 0) return; // no-op
  valk_lval_t *qs = valk_lval_sym(buf);
  if (LVAL_SRC_POS(sym) >= 0) LVAL_SRC_POS_SET(qs, LVAL_SRC_POS(sym));
  *slot = qs;
}

// --- Sibling-module rewriting: `X/Y` → `A/X/Y` for ancestor `A` of prefix. ---

// Compute the would-be module prefix for `(load "path" [sym])`, given the
// current module's prefix `cur_prefix`. Writes into `out` (up to out_sz).
// Mirrors the composition rule in builtins_io.c's valk_builtin_load.
static void predict_load_prefix(valk_lval_t *load_form, const char *cur_prefix,
                                char *out, size_t out_sz) {
  out[0] = '\0';
  valk_lval_t *args = load_form->cons.tail;
  if (!args || LVAL_TYPE(args) != LVAL_CONS) return;
  valk_lval_t *path = args->cons.head;
  if (!path || LVAL_TYPE(path) != LVAL_STR) return;

  valk_lval_t *rest = args->cons.tail;
  if (rest && LVAL_TYPE(rest) == LVAL_CONS && rest->cons.head &&
      LVAL_TYPE(rest->cons.head) == LVAL_SYM) {
    snprintf(out, out_sz, "%s", rest->cons.head->str);
    return;
  }

  const char *base = strrchr(path->str, '/');
  base = base ? base + 1 : path->str;
  const char *dot = strrchr(base, '.');
  size_t blen = dot ? (size_t)(dot - base) : strlen(base);
  char bname[256];
  if (blen >= sizeof(bname)) blen = sizeof(bname) - 1;
  memcpy(bname, base, blen);
  bname[blen] = '\0';

  if (cur_prefix && *cur_prefix)
    snprintf(out, out_sz, "%s/%s", cur_prefix, bname);
  else
    snprintf(out, out_sz, "%s", bname);
}

// Scan top-level forms for `(load ...)` and collect their predicted prefixes.
static void collect_local_load_prefixes(valk_lval_t *ast, const char *prefix,
                                        name_set_t *out) {
  valk_lval_t *cur = ast;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *form = cur->cons.head;
    if (form && LVAL_TYPE(form) == LVAL_CONS &&
        !(form->flags & LVAL_FLAG_QUOTED)) {
      valk_lval_t *head = form->cons.head;
      if (head && LVAL_TYPE(head) == LVAL_SYM &&
          strcmp(head->str, "load") == 0) {
        char buf[VALK_MOD_PATH_MAX];
        predict_load_prefix(form, prefix, buf, sizeof(buf));
        if (buf[0]) name_set_add(out, buf);
      }
    }
    cur = cur->cons.tail;
  }
}

// For `sym_str` of form `X/Y/...`, try rewriting to `A/X/Y/...` where `A`
// is an ancestor prefix (including `prefix` itself) such that `A/X` is a
// known sibling module (either loaded globally or predicted by pre-scan).
// Returns a newly-allocated replacement symbol, or NULL if no rewrite.
static valk_lval_t *try_sibling_rewrite(const char *sym_str, const char *prefix,
                                        name_set_t *local_loads, i32 src_pos) {
  const char *slash = strchr(sym_str, '/');
  if (!slash) return NULL;
  size_t first_len = (size_t)(slash - sym_str);
  if (first_len == 0 || first_len >= 128) return NULL;
  char first_seg[128];
  memcpy(first_seg, sym_str, first_len);
  first_seg[first_len] = '\0';

  char ancestor[VALK_MOD_PATH_MAX];
  if (!prefix || !*prefix) return NULL;
  snprintf(ancestor, sizeof(ancestor), "%s", prefix);

  while (ancestor[0]) {
    char candidate[VALK_MOD_PATH_MAX];
    snprintf(candidate, sizeof(candidate), "%s/%s", ancestor, first_seg);
    if (name_set_has(local_loads, candidate) ||
        valk_mod_registry_has(candidate)) {
      char out[VALK_MOD_PATH_MAX];
      snprintf(out, sizeof(out), "%s/%s", ancestor, sym_str);
      valk_lval_t *s = valk_lval_sym(out);
      if (src_pos >= 0) LVAL_SRC_POS_SET(s, src_pos);
      return s;
    }
    char *last = strrchr(ancestor, '/');
    if (!last) break;
    *last = '\0';
  }
  return NULL;
}

// --- Shadow-aware rewriter for intra-file call sites. ---

static void push_formals(valk_lval_t *formals, name_set_t *shadows) {
  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    if (LVAL_TYPE(cur->cons.head) == LVAL_SYM)
      name_set_add(shadows, cur->cons.head->str);
    cur = cur->cons.tail;
  }
}

static void rewrite_node(valk_lval_t *cell, const char *prefix,
                         name_set_t *locals, name_set_t *shadows,
                         name_set_t *local_loads);

static void rewrite_list(valk_lval_t *list, const char *prefix,
                         name_set_t *locals, name_set_t *shadows,
                         name_set_t *local_loads) {
  valk_lval_t *cur = list;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    rewrite_node(cur, prefix, locals, shadows, local_loads);
    cur = cur->cons.tail;
  }
}

static void rewrite_node(valk_lval_t *cell, const char *prefix,
                         name_set_t *locals, name_set_t *shadows,
                         name_set_t *local_loads) {
  valk_lval_t *expr = cell->cons.head;
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    if (expr->str[0] == ':') return;
    if (name_set_has(shadows, expr->str)) return;
    if (strchr(expr->str, '/')) {
      valk_lval_t *rewritten = try_sibling_rewrite(expr->str, prefix,
                                                   local_loads,
                                                   LVAL_SRC_POS(expr));
      if (rewritten) cell->cons.head = rewritten;
      return;
    }
    if (name_set_has(locals, expr->str)) {
      cell->cons.head = qualify_sym(prefix, expr->str, LVAL_SRC_POS(expr));
    }
    return;
  }

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = expr->cons.head;

  bool is_lambda = false;
  if (LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "\\") == 0)
    is_lambda = true;
  if (LVAL_TYPE(head) == LVAL_FUN && head->fun.builtin != NULL) {
    valk_lval_t *lambda_sym = valk_lval_sym("\\");
    valk_lval_t *lambda_val = valk_lenv_get(valk_macro_env(), lambda_sym);
    if (LVAL_TYPE(lambda_val) == LVAL_FUN &&
        head->fun.builtin == lambda_val->fun.builtin)
      is_lambda = true;
  }

  if (is_lambda) {
    valk_lval_t *rest = expr->cons.tail;
    if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
      name_set_t inner = {0};
      for (int i = 0; i < shadows->count; i++)
        name_set_add(&inner, shadows->names[i]);
      push_formals(rest->cons.head, &inner);
      if (rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS)
        rewrite_list(rest->cons.tail, prefix, locals, &inner, local_loads);
      name_set_free(&inner);
    }
    return;
  }

  if (LVAL_TYPE(head) == LVAL_SYM) {
    if (strcmp(head->str, "=") == 0) {
      valk_lval_t *rest = expr->cons.tail;
      if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
        valk_lval_t *bind = rest->cons.head;
        if (LVAL_TYPE(bind) == LVAL_SYM) name_set_add(shadows, bind->str);
        else if (LVAL_TYPE(bind) == LVAL_CONS) push_formals(bind, shadows);
        if (rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS)
          rewrite_list(rest->cons.tail, prefix, locals, shadows, local_loads);
      }
      return;
    }

    if (strcmp(head->str, "def") == 0) {
      // Names of top-level defs are qualified in pass 1; here we only need
      // to walk the value expression for call-site rewriting.
      valk_lval_t *rest = expr->cons.tail;
      if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
        if (rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS)
          rewrite_list(rest->cons.tail, prefix, locals, shadows, local_loads);
      }
      return;
    }

    // Type and sig forms register globally under their unqualified names
    // (types go into the type env, sigs into the sig registry). Don't walk
    // into them — their bodies reference type names that must remain
    // unqualified so short-name lookup works across files.
    if (strcmp(head->str, "type") == 0 || strcmp(head->str, "sig") == 0)
      return;
  }

  rewrite_list(expr, prefix, locals, shadows, local_loads);
}

// Qualify a top-level (sig 'name ...) form to match the qualification its
// paired def got. Bare names are qualified if in `locals`. `/`-containing
// names use the same ancestor strip-dup rule as qualify_def_name so the
// sig matches the canonical def name.
static void qualify_sig_if_local(valk_lval_t *form, const char *prefix,
                                 name_set_t *locals) {
  if (!form || LVAL_TYPE(form) != LVAL_CONS) return;
  if (form->flags & LVAL_FLAG_QUOTED) return;
  valk_lval_t *head = form->cons.head;
  if (!head || LVAL_TYPE(head) != LVAL_SYM) return;
  if (strcmp(head->str, "sig") != 0) return;

  valk_lval_t *rest = form->cons.tail;
  if (!rest || LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *name_expr = rest->cons.head;

  valk_lval_t *sym = NULL;
  valk_lval_t **slot = NULL;
  if (LVAL_TYPE(name_expr) == LVAL_CONS && name_expr->cons.head &&
      LVAL_TYPE(name_expr->cons.head) == LVAL_SYM) {
    sym = name_expr->cons.head;
    slot = &name_expr->cons.head;
  } else if (LVAL_TYPE(name_expr) == LVAL_SYM) {
    sym = name_expr;
    slot = &rest->cons.head;
  }
  if (!sym || !slot) return;
  if (sym->str[0] == ':') return;

  if (!strchr(sym->str, '/')) {
    if (!name_set_has(locals, sym->str)) return;
    *slot = qualify_sym(prefix, sym->str, LVAL_SRC_POS(sym));
    return;
  }

  char parent[VALK_MOD_PATH_MAX];
  if (!find_anchor_parent(sym->str, prefix, parent, sizeof(parent))) return;

  char buf[VALK_MOD_PATH_MAX];
  if (*parent)
    snprintf(buf, sizeof(buf), "%s/%s", parent, sym->str);
  else
    snprintf(buf, sizeof(buf), "%s", sym->str);
  if (strcmp(buf, sym->str) == 0) return;
  valk_lval_t *qs = valk_lval_sym(buf);
  if (LVAL_SRC_POS(sym) >= 0) LVAL_SRC_POS_SET(qs, LVAL_SRC_POS(sym));
  *slot = qs;
}

void valk_module_apply_prefix(valk_lval_t *ast, const char *prefix) {
  if (!prefix || !*prefix) return;

  // Pass 1a: collect unqualified def names.
  name_set_t locals = {0};
  {
    valk_lval_t *cur = ast;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      const char *name = extract_unqualified_def_name(cur->cons.head);
      if (name) name_set_add(&locals, name);
      cur = cur->cons.tail;
    }
  }

  // Pass 1b: qualify def names (bare and `/`-containing) and any sig
  // forms paired with them.
  {
    valk_lval_t *cur = ast;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      valk_lval_t *form = cur->cons.head;
      if (form && LVAL_TYPE(form) == LVAL_CONS &&
          !(form->flags & LVAL_FLAG_QUOTED) &&
          form->cons.head && LVAL_TYPE(form->cons.head) == LVAL_SYM &&
          strcmp(form->cons.head->str, "def") == 0)
        qualify_def_name(form, prefix);
      else
        qualify_sig_if_local(form, prefix, &locals);
      cur = cur->cons.tail;
    }
  }

  // Pre-scan top-level (load ...) forms to predict child module prefixes —
  // these are siblings that will be loaded by this file but aren't yet in
  // the global registry during Pass 2.
  name_set_t local_loads = {0};
  collect_local_load_prefixes(ast, prefix, &local_loads);

  // Pass 2: walk the whole AST, qualifying bare references to `locals` that
  // aren't shadowed by a lambda param or `=` binding. Also rewrites
  // qualified cross-sibling references via try_sibling_rewrite.
  name_set_t shadows = {0};
  valk_lval_t *cur = ast;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    rewrite_node(cur, prefix, &locals, &shadows, &local_loads);
    cur = cur->cons.tail;
  }

  name_set_free(&shadows);
  name_set_free(&locals);
  name_set_free(&local_loads);
}
