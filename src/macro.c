#include "macro.h"
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

typedef struct {
  char **names;
  int count;
  int cap;
} name_set_t;

static void ns_add(name_set_t *s, const char *name) {
  for (int i = 0; i < s->count; i++)
    if (strcmp(s->names[i], name) == 0) return;
  if (s->count >= s->cap) {
    s->cap = s->cap ? s->cap * 2 : 16;
    s->names = realloc(s->names, (u64)s->cap * sizeof(char *));
  }
  s->names[s->count++] = strdup(name);
}

static bool ns_has(name_set_t *s, const char *name) {
  for (int i = 0; i < s->count; i++)
    if (strcmp(s->names[i], name) == 0) return true;
  return false;
}

static void ns_free(name_set_t *s) {
  for (int i = 0; i < s->count; i++) free(s->names[i]);
  free(s->names);
}

static u64 cons_len(valk_lval_t *list) {
  u64 n = 0;
  while (list && LVAL_TYPE(list) == LVAL_CONS) { n++; list = list->cons.tail; }
  return n;
}

static void collect_defs(valk_lval_t *ast, name_set_t *defs) {
  valk_lval_t *cur = ast;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *expr = cur->cons.head;
    if (expr && LVAL_TYPE(expr) == LVAL_CONS &&
        !(expr->flags & LVAL_FLAG_QUOTED)) {
      valk_lval_t *head = expr->cons.head;
      if (head && LVAL_TYPE(head) == LVAL_SYM &&
          strcmp(head->str, "def") == 0) {
        valk_lval_t *rest = expr->cons.tail;
        if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
          valk_lval_t *sym_arg = rest->cons.head;
          const char *name = NULL;
          if (LVAL_TYPE(sym_arg) == LVAL_SYM)
            name = sym_arg->str;
          else if (LVAL_TYPE(sym_arg) == LVAL_CONS && cons_len(sym_arg) >= 1) {
            valk_lval_t *first = sym_arg->cons.head;
            if (LVAL_TYPE(first) == LVAL_SYM) name = first->str;
          }
          if (name && !strchr(name, '/') && name[0] != ':')
            ns_add(defs, name);
        }
      }
    }
    cur = cur->cons.tail;
  }
}

static valk_lval_t *qualify_sym(const char *prefix, const char *name) {
  size_t len = strlen(prefix) + 1 + strlen(name) + 1;
  char *buf = malloc(len);
  snprintf(buf, len, "%s/%s", prefix, name);
  valk_lval_t *sym = valk_lval_sym(buf);
  free(buf);
  return sym;
}

static void rewrite_node(valk_lval_t *expr, const char *prefix,
                         name_set_t *defs, name_set_t *shadows);

static void rewrite_list(valk_lval_t *list, const char *prefix,
                         name_set_t *defs, name_set_t *shadows) {
  valk_lval_t *cur = list;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    rewrite_node(cur, prefix, defs, shadows);
    cur = cur->cons.tail;
  }
}

static void push_formals(valk_lval_t *formals, name_set_t *shadows) {
  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    if (LVAL_TYPE(cur->cons.head) == LVAL_SYM)
      ns_add(shadows, cur->cons.head->str);
    cur = cur->cons.tail;
  }
}

static void rewrite_node(valk_lval_t *cell, const char *prefix,
                         name_set_t *defs, name_set_t *shadows) {
  valk_lval_t *expr = cell->cons.head;
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    if (expr->str[0] == ':') return;

    const char *slash = strchr(expr->str, '/');
    if (slash) {
      size_t seg_len = (size_t)(slash - expr->str);
      char seg[256];
      if (seg_len < sizeof(seg)) {
        memcpy(seg, expr->str, seg_len);
        seg[seg_len] = '\0';
        valk_module_t *cur = valk_mod_current();
        if (cur && valk_mod_child(cur, seg)) {
          cell->cons.head = qualify_sym(prefix, expr->str);
        }
      }
      return;
    }

    if (!ns_has(defs, expr->str)) return;
    if (ns_has(shadows, expr->str)) return;
    cell->cons.head = qualify_sym(prefix, expr->str);
    return;
  }

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = expr->cons.head;
  if (!head || LVAL_TYPE(head) != LVAL_SYM) {
    rewrite_list(expr, prefix, defs, shadows);
    return;
  }

  if (strcmp(head->str, "\\") == 0) {
    valk_lval_t *rest = expr->cons.tail;
    if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *formals = rest->cons.head;
      valk_lval_t *body_cell = rest->cons.tail;
      name_set_t inner = {0};
      for (int i = 0; i < shadows->count; i++)
        ns_add(&inner, shadows->names[i]);
      push_formals(formals, &inner);
      if (body_cell && LVAL_TYPE(body_cell) == LVAL_CONS)
        rewrite_list(body_cell, prefix, defs, &inner);
      ns_free(&inner);
    }
    return;
  }

  if (strcmp(head->str, "=") == 0) {
    valk_lval_t *rest = expr->cons.tail;
    if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *bind = rest->cons.head;
      if (LVAL_TYPE(bind) == LVAL_SYM)
        ns_add(shadows, bind->str);
      else if (LVAL_TYPE(bind) == LVAL_CONS)
        push_formals(bind, shadows);
      valk_lval_t *val_cell = rest->cons.tail;
      if (val_cell && LVAL_TYPE(val_cell) == LVAL_CONS)
        rewrite_list(val_cell, prefix, defs, shadows);
    }
    return;
  }

  if (strcmp(head->str, "def") == 0) {
    valk_lval_t *rest = expr->cons.tail;
    if (rest && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *sym_arg = rest->cons.head;
      if (LVAL_TYPE(sym_arg) == LVAL_SYM && !strchr(sym_arg->str, '/') &&
          sym_arg->str[0] != ':' && ns_has(defs, sym_arg->str)) {
        rest->cons.head = qualify_sym(prefix, sym_arg->str);
      } else if (LVAL_TYPE(sym_arg) == LVAL_CONS) {
        valk_lval_t *first = sym_arg->cons.head;
        if (first && LVAL_TYPE(first) == LVAL_SYM &&
            !strchr(first->str, '/') && first->str[0] != ':' &&
            ns_has(defs, first->str)) {
          sym_arg->cons.head = qualify_sym(prefix, first->str);
        }
      }
      valk_lval_t *val_cell = rest->cons.tail;
      if (val_cell && LVAL_TYPE(val_cell) == LVAL_CONS)
        rewrite_list(val_cell, prefix, defs, shadows);
    }
    return;
  }

  rewrite_list(expr, prefix, defs, shadows);
}

valk_lval_t *valk_eval_form(valk_lenv_t *env, valk_lval_t *form) {
  valk_lenv_t *menv = valk_macro_env();
  if (valk_macro_is_def(form))
    return valk_lval_eval(menv, form);
  form = valk_macro_expand_one(menv, form);
  return valk_lval_eval(env, form);
}

void valk_module_rewrite(valk_lval_t *ast, const char *prefix) {
  name_set_t defs = {0};
  collect_defs(ast, &defs);
  if (defs.count == 0) { ns_free(&defs); return; }

  name_set_t shadows = {0};
  valk_lval_t *cur = ast;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    rewrite_node(cur, prefix, &defs, &shadows);
    cur = cur->cons.tail;
  }

  ns_free(&defs);
  ns_free(&shadows);
}

void valk_module_rewrite_form(valk_lval_t *form, const char *prefix) {
  valk_lval_t *wrapper = valk_lval_cons(form, valk_lval_nil());
  valk_module_rewrite(wrapper, prefix);
}
