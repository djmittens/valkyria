#include "macro.h"

#include "coverage.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static valk_lenv_t *g_macro_env = NULL;

valk_lenv_t *valk_macro_env(void) {
  if (!g_macro_env) {
    g_macro_env = valk_lenv_empty();
    valk_lenv_builtins(g_macro_env);
  }
  return g_macro_env;
}

// Unify the macro env with the caller's target env. After this call, macros
// defined via `(macro ...)` live in the same env as regular defs, and macro
// expansion looks up in the unified env. Call once after valk_lenv_builtins.
void valk_macro_env_init(valk_lenv_t *env) {
  g_macro_env = env;
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
  result = expand_expr(menv, result);
#ifdef VALK_COVERAGE
  // Attribute the expansion to the call site: the original form's cell was
  // marked for coverage at parse time; the expansion replaces it and must
  // record at the same (file, line, column) or the mark can never be hit.
  if (result && LVAL_TYPE(result) == LVAL_CONS)
    INHERIT_SOURCE_LOC(result, expr);
  // Side-effect-only macros (e.g. module) erase the form entirely; the
  // parse-time marks can never be hit. Retract them like sig/type lines.
  if (result && LVAL_TYPE(result) == LVAL_NIL)
    valk_coverage_unmark_tree(expr);
#endif
  return result;
}

valk_lval_t *valk_macro_expand_one(valk_lenv_t *menv, valk_lval_t *expr) {
  return expand_expr(menv, expr);
}

// ---------------------------------------------------------------------------
// Module prefix application.
//
// For a file that declared `(module X)`:
//   1. Qualify each top-level unqualified `(def {name} ...)` form's name to
//      `X/name`. Same for `(sig 'name ...)` paired with a local def.
//   2. Walk the whole AST with shadow tracking and rewrite bare references
//      to those local defs into their qualified form — so `(foo 1)` inside
//      a file that defines `(fun {foo x} ...)` keeps working.
//
// Already-qualified names (containing `/`) are left untouched. Cross-file
// references must be written fully qualified (e.g. `nav/handle-hover`) —
// plain env lookup handles them.
// ---------------------------------------------------------------------------

#define VALK_MOD_PATH_MAX 512

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

static valk_lval_t *qualify_sym(const char *prefix, const char *name,
                                i32 src_pos) {
  char buf[VALK_MOD_PATH_MAX];
  snprintf(buf, sizeof(buf), "%s/%s", prefix, name);
  valk_lval_t *sym = valk_lval_sym(buf);
  if (src_pos >= 0) LVAL_SRC_POS_SET(sym, src_pos);
  return sym;
}

// Returns the def form's bare name or NULL if the form isn't a `def` with
// an unqualified name.
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

// Mutate the name cell in a top-level def form: if bare, prepend prefix.
// Already-qualified names (containing `/`) are left alone.
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
  if (strchr(sym->str, '/')) return;

  *slot = qualify_sym(prefix, sym->str, LVAL_SRC_POS(sym));
}

// --- Shadow-aware rewriter for intra-file call sites. ---

struct valk_module_locals {
  name_set_t set;
};

valk_module_locals_t *valk_module_locals_new(void) {
  return calloc(1, sizeof(valk_module_locals_t));
}

void valk_module_locals_collect(valk_module_locals_t *locals,
                                valk_lval_t *form) {
  const char *name = extract_unqualified_def_name(form);
  if (name) name_set_add(&locals->set, name);
}

void valk_module_locals_free(valk_module_locals_t *locals) {
  name_set_free(&locals->set);
  free(locals);
}

typedef struct {
  const char *prefix;
  name_set_t *locals;
  bool use_aliases;
} rw_ctx_t;

static void push_formals(valk_lval_t *formals, name_set_t *shadows) {
  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    if (LVAL_TYPE(cur->cons.head) == LVAL_SYM)
      name_set_add(shadows, cur->cons.head->str);
    cur = cur->cons.tail;
  }
}

static void rewrite_node(valk_lval_t *cell, const rw_ctx_t *rw,
                         name_set_t *shadows);

static void rewrite_list(valk_lval_t *list, const rw_ctx_t *rw,
                         name_set_t *shadows) {
  valk_lval_t *cur = list;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    rewrite_node(cur, rw, shadows);
    cur = cur->cons.tail;
  }
}

static void rewrite_node(valk_lval_t *cell, const rw_ctx_t *rw,
                         name_set_t *shadows) {
  valk_lval_t *expr = cell->cons.head;
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    if (expr->str[0] == ':') return;
    if (name_set_has(shadows, expr->str)) return;
    if (strchr(expr->str, '/')) {
      if (rw->use_aliases) {
        char *repl = valk_load_resolve_alias(expr->str);
        if (repl) {
          valk_lval_t *sym = valk_lval_sym(repl);
          LVAL_SRC_POS_SET(sym, LVAL_SRC_POS(expr));
          cell->cons.head = sym;
          free(repl);
        }
      }
      return;
    }
    if (rw->prefix[0] && name_set_has(rw->locals, expr->str))
      cell->cons.head = qualify_sym(rw->prefix, expr->str, LVAL_SRC_POS(expr));
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
        rewrite_list(rest->cons.tail, rw, &inner);
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
          rewrite_list(rest->cons.tail, rw, shadows);
      }
      return;
    }

    if (strcmp(head->str, "def") == 0) {
      // Names of top-level defs are qualified in pass 1; here we only need
      // to walk the value expression for call-site rewriting.
      valk_lval_t *rest = expr->cons.tail;
      if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
        if (rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS)
          rewrite_list(rest->cons.tail, rw, shadows);
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

  rewrite_list(expr, rw, shadows);
}

// If `form` is a top-level (sig 'name ...) whose name matches a local bare
// def, qualify its name to `prefix/name` so it pairs with the qualified def.
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
  if (strchr(sym->str, '/')) return;
  if (!name_set_has(locals, sym->str)) return;

  *slot = qualify_sym(prefix, sym->str, LVAL_SRC_POS(sym));
}

void valk_module_rewrite_form(valk_lval_t *cell, const char *prefix,
                              valk_module_locals_t *locals, bool qualify_defs,
                              bool use_aliases) {
  if (!cell || LVAL_TYPE(cell) != LVAL_CONS) return;
  rw_ctx_t rw = { prefix ? prefix : "", &locals->set, use_aliases };

  valk_lval_t *form = cell->cons.head;
  if (rw.prefix[0] && qualify_defs) {
    if (form && LVAL_TYPE(form) == LVAL_CONS &&
        !(form->flags & LVAL_FLAG_QUOTED) &&
        form->cons.head && LVAL_TYPE(form->cons.head) == LVAL_SYM &&
        strcmp(form->cons.head->str, "def") == 0)
      qualify_def_name(form, rw.prefix);
    else
      qualify_sig_if_local(form, rw.prefix, &locals->set);
  }

  name_set_t shadows = {0};
  rewrite_node(cell, &rw, &shadows);
  name_set_free(&shadows);
}

void valk_module_apply_prefix(valk_lval_t *ast, const char *prefix) {
  if (!prefix || !*prefix) return;

  valk_module_locals_t *locals = valk_module_locals_new();
  for (valk_lval_t *cur = ast; cur && LVAL_TYPE(cur) == LVAL_CONS;
       cur = cur->cons.tail)
    valk_module_locals_collect(locals, cur->cons.head);

  for (valk_lval_t *cur = ast; cur && LVAL_TYPE(cur) == LVAL_CONS;
       cur = cur->cons.tail)
    valk_module_rewrite_form(cur, prefix, locals, true, false);

  valk_module_locals_free(locals);
}
