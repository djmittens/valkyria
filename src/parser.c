#include "parser.h"
#include <signal.h>
#include <string.h>

#define LVAL_ASSERT(args, cond, err)                                           \
  if (!(cond)) {                                                               \
    valk_lval_free(args);                                                      \
    return valk_lval_err(err);                                                 \
  }

static valk_lval_t *builtin_op(valk_lval_t *lst, char *op) {
  for (int i = 0; i < lst->count; ++i) {
    if (lst->cell[i]->type != LVAL_NUM) {
      valk_lval_free(lst);
      return valk_lval_err("Sorry can only do math with numbers");
    }
  }

  valk_lval_t *x = valk_lval_pop(lst, 0);

  if (strcmp(op, "-") == 0 && lst->count == 1) {
    // Negate the number if there is only 1
    x->val = -x->val;
  }

  while (lst->count > 0) {
    valk_lval_t *y = valk_lval_pop(lst, 0);

    if (strcmp(op, "+") == 0) {
      x->val += y->val;
    }
    if (strcmp(op, "-") == 0) {
      x->val -= y->val;
    }
    if (strcmp(op, "*") == 0) {
      x->val *= y->val;
    }
    if (strcmp(op, "/") == 0) {
      if (y->val > 0) {
        x->val /= y->val;
      } else {
        valk_lval_free(y);
        valk_lval_free(x);
        x = valk_lval_err("Division By Zero");
        break;
      }
    }

    valk_lval_free(y);
  }
  valk_lval_free(lst);
  return x;
}

static valk_lval_t *valk_builtin_head(valk_lval_t *a) {
  LVAL_ASSERT(a, a->count == 1, "Builtin `head` passed too many arguments");
  LVAL_ASSERT(a, a->cell[0]->type == LVAL_QEXPR,
              "Builtin `head` can only operate on Q-Expressions");
  LVAL_ASSERT(a, a->cell[0]->count != 0,
              "Builtin `head` cannot operate on `{}`");
  valk_lval_t *v = valk_lval_pop(a, 0);
  valk_lval_free(a);
  while (v->count > 1) {
    valk_lval_free(valk_lval_pop(v, 1));
  }
  return v;
}

static valk_lval_t *valk_builtin_tail(valk_lval_t *a) {
  LVAL_ASSERT(a, a->count == 1, "Builtin `tail` passed too many arguments");
  LVAL_ASSERT(a, a->cell[0]->type == LVAL_QEXPR,
              "Builtin `tail` can only operate on Q-Expressions");
  LVAL_ASSERT(a, a->cell[0]->count != 0,
              "Builtin `tail` cannot operate on `{}`");
  valk_lval_t *v = valk_lval_pop(a, 0);

  valk_lval_free(a);
  valk_lval_free(valk_lval_pop(v, 0));
  return v;
}

static valk_lval_t *valk_builtin_join(valk_lval_t *a) {
  LVAL_ASSERT(a, a->cell[0]->type == LVAL_QEXPR,
              "Builtin `join` can only operate on Q-Expressions");
  valk_lval_t *x = valk_lval_pop(a, 0);
  while (a->count) {
    x = valk_lval_join(x, valk_lval_pop(a, 0));
  }
  valk_lval_free(a);
  return x;
}

static valk_lval_t *valk_builtin_list(valk_lval_t *a) {
  a->type = LVAL_QEXPR;
  return a;
}

static valk_lval_t *valk_builtin_eval(valk_lval_t *a) {
  LVAL_ASSERT(a, a->count == 1, "Builtin `eval` passed too many arguments");
  LVAL_ASSERT(a, a->cell[0]->type == LVAL_QEXPR,
              "Builtin `eval` can only operate on Q-Expressions");

  valk_lval_t *v = valk_lval_pop(a, 0);
  v->type = LVAL_SEXPR;
  valk_lval_free(a);
  return valk_lval_eval(v);
}

static valk_lval_t *valk_builtin(valk_lval_t *lval, char *func) {
  if (strcmp("list", func) == 0) {
    return valk_builtin_list(lval);
  }
  if (strcmp("head", func) == 0) {
    return valk_builtin_head(lval);
  }
  if (strcmp("tail", func) == 0) {
    return valk_builtin_tail(lval);
  }
  if (strcmp("join", func) == 0) {
    return valk_builtin_join(lval);
  }
  if (strcmp("eval", func) == 0) {
    return valk_builtin_eval(lval);
  }
  if (strstr("+-/*", func)) {
    return builtin_op(lval, func);
  }
  valk_lval_free(lval);
  return valk_lval_err("Unknown function");
}

valk_lval_t *valk_lval_eval(valk_lval_t *lval) {
  if (lval->type == LVAL_SEXPR) {
    return valk_lval_eval_sexpr(lval);
  }

  return lval;
}

valk_lval_t *valk_lval_eval_sexpr(valk_lval_t *sexpr) {
  LVAL_ASSERT(sexpr, sexpr->type == LVAL_SEXPR,
              "Trying to evaluate something that isnt an sexpr");

  // no children? no problem
  if (sexpr->count == 0) {
    return sexpr;
  }

  // count up the chillen
  for (int i = 0; i < sexpr->count; ++i) {
    sexpr->cell[i] = valk_lval_eval(sexpr->cell[i]);
    if (sexpr->cell[i]->type == LVAL_ERR) {
      valk_lval_t *res = valk_lval_pop(sexpr, i);
      valk_lval_free(sexpr);
      return res;
    }
  }

  // If we have a single node, collapse to it
  if (sexpr->count == 1) {
    valk_lval_t *res = valk_lval_pop(sexpr, 0);
    valk_lval_free(sexpr);
    return res;
  }

  valk_lval_t *sym = valk_lval_pop(sexpr, 0);
  if (sym->type != LVAL_SYM) {
    // Make sure to free this shit.
    valk_lval_free(sym);
    valk_lval_free(sexpr);
    // TODO(main): should add more information here about the symbol
    return valk_lval_err("S-Expression doesnt start with symbol");
  }

  valk_lval_t *res = valk_builtin(sexpr, sym->str);
  valk_lval_free(sym);
  // valk_lval_free(sexpr);
  return res;
}

valk_lval_t *valk_lval_pop(valk_lval_t *lval, size_t i) {
  if (i >= lval->count) {
    printf("ERROR: trying to pop from invalid index: %ld >= %ld\n", i,
           lval->count);
    fflush(stdout);
    raise(SIGABRT);
  }
  valk_lval_t *cell = lval->cell[i];
  // shift dems down
  memmove(&lval->cell[i], &lval->cell[i + 1],
          sizeof(valk_lval_t *) * (lval->count - i - 1));
  lval->count--;
  lval->cell = realloc(lval->cell, sizeof(valk_lval_t *) * lval->count);
  return cell;
}

valk_lval_t *valk_lval_add(valk_lval_t *lval, valk_lval_t *cell) {
  // TODO(main):  this will leak the cell, i need to expand this macro to free
  // more than 1 thing
  LVAL_ASSERT(lval, (lval->type == LVAL_SEXPR) || (lval->type == LVAL_QEXPR),
              "You can only add to QEXPR or SEXPR");
  LVAL_ASSERT(lval, cell != NULL, "Adding null to LVAL is not allowed");

  lval->count++;
  lval->cell = realloc(lval->cell, sizeof(valk_lval_t *) * lval->count);
  lval->cell[lval->count - 1] = cell;
  return lval;
}

valk_lval_t *valk_lval_join(valk_lval_t *a, valk_lval_t *b) {
  while (b->count) {
    a = valk_lval_add(a, valk_lval_pop(b, 0));
  }
  valk_lval_free(b);
  return a;
}
