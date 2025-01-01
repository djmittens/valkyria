#include "parser.h"
#include <signal.h>
#include <string.h>

static valk_lval_t *builtin_op(valk_lval_t *lst, char *op) {
  valk_lval_println(lst);
  fflush(stdout);
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
    printf("the celler %ld\n", lst->count);
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

valk_lval_t *valk_lval_eval(valk_lval_t *lval) {
  if (lval->type == LVAL_SEXPR) {
    return valk_lval_eval_sexpr(lval);
  }

  return lval;
}

valk_lval_t *valk_lval_eval_sexpr(valk_lval_t *sexpr) {
  if (sexpr->type != LVAL_SEXPR) {
    printf("WARN: Trying to evaluate something that isnt an sexpr: ");
    valk_lval_print(sexpr);
    return sexpr;
  }

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
    return valk_lval_err("S-Expression doesnt start with symbol\n");
  }

  valk_lval_println(sexpr);
  valk_lval_t *res = builtin_op(sexpr, sym->str);
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
