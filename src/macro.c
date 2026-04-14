#include "macro.h"
#include "memory.h"
#include "module.h"

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

static u64 cons_len(valk_lval_t *list) {
  u64 n = 0;
  while (list && LVAL_TYPE(list) == LVAL_CONS) { n++; list = list->cons.tail; }
  return n;
}

static const char *extract_def_name(valk_lval_t *expr) {
  if (!expr || LVAL_TYPE(expr) != LVAL_CONS) return NULL;
  if (expr->flags & LVAL_FLAG_QUOTED) return NULL;
  valk_lval_t *head = expr->cons.head;
  if (!head || LVAL_TYPE(head) != LVAL_SYM) return NULL;
  if (strcmp(head->str, "def") != 0) return NULL;
  valk_lval_t *rest = expr->cons.tail;
  if (!rest || LVAL_TYPE(rest) != LVAL_CONS) return NULL;
  valk_lval_t *sym_arg = rest->cons.head;
  if (LVAL_TYPE(sym_arg) == LVAL_SYM) return sym_arg->str;
  if (LVAL_TYPE(sym_arg) == LVAL_CONS && cons_len(sym_arg) >= 1) {
    valk_lval_t *first = sym_arg->cons.head;
    if (LVAL_TYPE(first) == LVAL_SYM) return first->str;
  }
  return NULL;
}

void valk_module_register_defs(valk_lval_t *ast, valk_module_t *mod) {
  valk_lval_t *cur = ast;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    const char *name = extract_def_name(cur->cons.head);
    if (name && name[0] != ':')
      valk_mod_def(mod, name, valk_lval_nil());
    cur = cur->cons.tail;
  }
}

static valk_lval_t *qualify_sym(const char *fqn, const char *name,
                                i32 src_pos) {
  char buf[VALK_MOD_PATH_MAX];
  snprintf(buf, sizeof(buf), "%s/%s", fqn, name);
  valk_lval_t *sym = valk_lval_sym(buf);
  if (src_pos >= 0) LVAL_SRC_POS_SET(sym, src_pos);
  return sym;
}



typedef struct {
  char **names;
  int count;
  int cap;
} shadow_set_t;

static void shadow_add(shadow_set_t *s, const char *name) {
  for (int i = 0; i < s->count; i++)
    if (strcmp(s->names[i], name) == 0) return;
  if (s->count >= s->cap) {
    s->cap = s->cap ? s->cap * 2 : 16;
    s->names = realloc(s->names, (u64)s->cap * sizeof(char *));
  }
  s->names[s->count++] = strdup(name);
}

static bool shadow_has(shadow_set_t *s, const char *name) {
  for (int i = 0; i < s->count; i++)
    if (strcmp(s->names[i], name) == 0) return true;
  return false;
}

static void shadow_free(shadow_set_t *s) {
  for (int i = 0; i < s->count; i++) free(s->names[i]);
  free(s->names);
}

static void push_formals(valk_lval_t *formals, shadow_set_t *shadows) {
  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    if (LVAL_TYPE(cur->cons.head) == LVAL_SYM)
      shadow_add(shadows, cur->cons.head->str);
    cur = cur->cons.tail;
  }
}

static void rewrite_node(valk_lval_t *cell, valk_module_t *mod,
                         const char *fqn, valk_lenv_t *root_env,
                         shadow_set_t *shadows);

static void rewrite_list(valk_lval_t *list, valk_module_t *mod,
                         const char *fqn, valk_lenv_t *root_env,
                         shadow_set_t *shadows) {
  valk_lval_t *cur = list;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    rewrite_node(cur, mod, fqn, root_env, shadows);
    cur = cur->cons.tail;
  }
}

static valk_lval_t *resolve_qualified(valk_module_t *mod, const char *name) {
  const char *slash = strchr(name, '/');
  if (!slash) return NULL;

  size_t seg_len = (size_t)(slash - name);
  char seg[256];
  if (seg_len >= sizeof(seg)) return NULL;
  memcpy(seg, name, seg_len);
  seg[seg_len] = '\0';

  valk_module_t *m = mod;
  while (m) {
    valk_module_t *child = valk_mod_child(m, seg);
    if (child) {
      char child_fqn[VALK_MOD_PATH_MAX];
      valk_mod_qualified_path(child, child_fqn, sizeof(child_fqn));
      char qualified[VALK_MOD_PATH_MAX];
      snprintf(qualified, sizeof(qualified), "%s/%s", child_fqn, slash + 1);
      return valk_lval_sym(qualified);
    }
    m = m->parent;
  }
  return NULL;
}

static void rewrite_node(valk_lval_t *cell, valk_module_t *mod,
                         const char *fqn, valk_lenv_t *root_env,
                         shadow_set_t *shadows) {
  valk_lval_t *expr = cell->cons.head;
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    if (expr->str[0] == ':') return;

    if (strchr(expr->str, '/')) {
      valk_lval_t *resolved = resolve_qualified(mod, expr->str);
      if (resolved) cell->cons.head = resolved;
      return;
    }

    if (shadow_has(shadows, expr->str)) return;
    if (valk_mod_get(mod, expr->str)) {
      cell->cons.head = qualify_sym(fqn, expr->str, LVAL_SRC_POS(expr));
      return;
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

  if (!is_lambda && LVAL_TYPE(head) != LVAL_SYM) {
    rewrite_list(expr, mod, fqn, root_env, shadows);
    return;
  }

  if (is_lambda) {
    valk_lval_t *rest = expr->cons.tail;
    if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
      shadow_set_t inner = {0};
      for (int i = 0; i < shadows->count; i++)
        shadow_add(&inner, shadows->names[i]);
      push_formals(rest->cons.head, &inner);
      if (rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS)
        rewrite_list(rest->cons.tail, mod, fqn, root_env, &inner);
      shadow_free(&inner);
    }
    return;
  }

  if (strcmp(head->str, "=") == 0) {
    valk_lval_t *rest = expr->cons.tail;
    if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *bind = rest->cons.head;
      if (LVAL_TYPE(bind) == LVAL_SYM) shadow_add(shadows, bind->str);
      else if (LVAL_TYPE(bind) == LVAL_CONS) push_formals(bind, shadows);
      if (rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS)
        rewrite_list(rest->cons.tail, mod, fqn, root_env, shadows);
    }
    return;
  }

  if (strcmp(head->str, "def") == 0) {
    valk_lval_t *rest = expr->cons.tail;
    if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *sym_arg = rest->cons.head;
      const char *def_name = NULL;
      valk_lval_t **def_cell = NULL;

      if (LVAL_TYPE(sym_arg) == LVAL_SYM) {
        def_name = sym_arg->str;
        def_cell = &rest->cons.head;
      } else if (LVAL_TYPE(sym_arg) == LVAL_CONS && sym_arg->cons.head &&
                 LVAL_TYPE(sym_arg->cons.head) == LVAL_SYM) {
        def_name = sym_arg->cons.head->str;
        def_cell = &sym_arg->cons.head;
      }

      if (def_name && def_name[0] != ':') {
        if (!strchr(def_name, '/') && valk_mod_get(mod, def_name)) {
          *def_cell = qualify_sym(fqn, def_name, LVAL_SRC_POS(*def_cell));
        } else if (strchr(def_name, '/')) {
          valk_lval_t *resolved = resolve_qualified(mod, def_name);
          if (resolved) *def_cell = resolved;
        }
      }

      if (rest->cons.tail && LVAL_TYPE(rest->cons.tail) == LVAL_CONS)
        rewrite_list(rest->cons.tail, mod, fqn, root_env, shadows);
    }
    return;
  }

  rewrite_list(expr, mod, fqn, root_env, shadows);
}

void valk_module_rewrite(valk_lval_t *ast, const char *prefix) {
  (void)prefix;
  valk_module_t *mod = valk_mod_current();
  if (!mod) return;

  valk_module_register_defs(ast, mod);

  char fqn[VALK_MOD_PATH_MAX];
  valk_mod_qualified_path(mod, fqn, sizeof(fqn));

  valk_lenv_t *root = NULL;
  shadow_set_t shadows = {0};
  valk_lval_t *cur = ast;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    rewrite_node(cur, mod, fqn, root, &shadows);
    cur = cur->cons.tail;
  }
  shadow_free(&shadows);
}

void valk_module_rewrite_form(valk_lval_t *form, const char *prefix) {
  valk_lval_t *wrapper = valk_lval_cons(form, valk_lval_nil());
  valk_module_rewrite(wrapper, prefix);
}
