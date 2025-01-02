#include "parser.h"
#include <stdio.h>
#include <string.h>

#define LVAL_ASSERT(args, cond, err)                                           \
  if (!(cond)) {                                                               \
    valk_lval_free(args);                                                      \
    return valk_lval_err(err);                                                 \
  }

valk_lval_t *valk_lval_num(long x) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_NUM;
  res->num = x;
  res->count = 0;
  return res;
}

valk_lval_t *valk_lval_err(char *msg) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_ERR;
  // TODO(main): look into UTF-8 support
  int len = strlen(msg);
  res->str = calloc(len + 1, sizeof(char));
  strncpy(res->str, msg, len);
  res->count = 0;
  return res;
}
valk_lval_t *valk_lval_sym(char *sym) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_SYM;
  res->str = strndup(sym, 200);
  res->count = 0;
  return res;
}
valk_lval_t *valk_lval_fun(valk_lval_builtin_t *fun) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_SYM;
  res->fun = fun;
  res->count = 0;
  return res;
}
valk_lval_t *valk_lval_sexpr_empty() {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_SEXPR;
  res->cell = NULL;
  res->count = 0;
  return res;
}
valk_lval_t *valk_lval_qexpr_empty() {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_QEXPR;
  res->cell = NULL;
  res->count = 0;
  return res;
}

valk_lval_t *valk_lval_copy(valk_lval_t *lval) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = lval->type;
  res->count = lval->count;
  switch (lval->type) {
  case LVAL_NUM:
    res->num = lval->num;
    break;
  case LVAL_FUN:
    res->fun = lval->fun;
    break;
  case LVAL_QEXPR:
  case LVAL_SEXPR:
    res->cell = malloc(sizeof(res->cell) * lval->count);
    for (int i = 0; i < lval->count; ++i) {
      res->cell[i] = valk_lval_copy(lval->cell[i]);
    }
    break;
  case LVAL_SYM:
    res->str = strndup(lval->str, 200); //  TODO(main): Whats max symbol length?
    break;
  case LVAL_ERR:
    // Pretty cool functionality in C23
    res->str = strndup(lval->str, 2000); //  TODO(main): Whats max error length?
    break;
  }
  return res;
}

void valk_lval_free(valk_lval_t *lval) {
  switch (lval->type) {
  case LVAL_FUN:
  case LVAL_NUM:
    // nuttin to do but break;
    break;
  case LVAL_SYM:
  case LVAL_ERR:
    free(lval->str);
    break;
  case LVAL_QEXPR:
  case LVAL_SEXPR:
    while (lval->count > 0) {
      valk_lval_free(lval->cell[lval->count - 1]);
      --lval->count;
    }
    // Should play around with valgrind on this. Pretty interesting thing to
    // forget
    free(lval->cell);
    break;
  }
  free(lval);
}

valk_lval_t *valk_lval_eval(valk_lenv_t *env, valk_lval_t *lval) {
  if (lval->type == LVAL_SYM) {
    valk_lval_t *res = valk_lenv_get(env, lval);
    valk_lval_free(lval);
    return res;
  }
  if (lval->type == LVAL_SEXPR) {
    return valk_lval_eval_sexpr(env, lval);
  }

  return lval;
}

valk_lval_t *valk_lval_eval_sexpr(valk_lenv_t *env, valk_lval_t *sexpr) {
  LVAL_ASSERT(sexpr, sexpr->type == LVAL_SEXPR,
              "Trying to evaluate something that isnt an sexpr");

  // no children? no problem
  if (sexpr->count == 0) {
    return sexpr;
  }

  // count up the chillen
  for (int i = 0; i < sexpr->count; ++i) {
    sexpr->cell[i] = valk_lval_eval(env, sexpr->cell[i]);
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

  valk_lval_t *fun = valk_lval_pop(sexpr, 0);
  if (fun->type != LVAL_FUN) {
    // Make sure to free this shit.
    valk_lval_free(fun);
    valk_lval_free(sexpr);
    // TODO(main): should add more information here about the symbol
    return valk_lval_err("S-Expression doesnt start with a <function>");
  }

  valk_lval_t *res = fun->fun(env, sexpr);
  valk_lval_free(fun);
  return res;
}

valk_lval_t *valk_lval_pop(valk_lval_t *lval, size_t i) {
  LVAL_ASSERT(lval, i < lval->count, "Cant pop from list at invalid position");
  LVAL_ASSERT(lval, lval->count > 0, "Cant pop from empty");

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

void valk_lval_print(valk_lval_t *val) {
  switch (val->type) {
  case LVAL_NUM:
    printf("Num[%li]", val->num);
    break;
  case LVAL_SYM:
    printf("Sym[%s]", val->str);
    break;
    // TODO(main): code duplication here, do i actually care??
  case LVAL_QEXPR:
    printf("Qexpr{ ");
    for (int i = 0; i < val->count; ++i) {
      valk_lval_print(val->cell[i]);
      if (i < val->count - 1) {
        putchar(' ');
      }
    }
    printf(" }");
    break;
  case LVAL_SEXPR:
    printf("Sexpr( ");
    for (int i = 0; i < val->count; ++i) {
      valk_lval_print(val->cell[i]);
      if (i < val->count - 1) {
        putchar(' ');
      }
    }
    printf(" )");
    break;
  case LVAL_ERR:
    printf("Error[%s]", val->str);
    break;
  case LVAL_FUN:
    printf("<function>");
    break;
  }
}

//// LEnv ////
valk_lenv_t *valk_lenv_new(void) {
  valk_lenv_t *res = malloc(sizeof(valk_lenv_t));
  valk_lenv_init(res);
  return res;
}
void valk_lenv_init(valk_lenv_t *env) {
  env->count = 0;
  env->labels = NULL;
  env->vals = NULL;
}

void valk_lenv_free(valk_lenv_t *env) {
  for (int i = 0; i < env->count; ++i) {
    valk_lval_free(env->vals[i]);
    free(env->labels[i]);
  }
  free(env->vals);
  free(env->labels);
  free(env);
}

valk_lval_t *valk_lenv_get(valk_lenv_t *env, valk_lval_t *key) {
  LVAL_ASSERT(NULL, key->type == LVAL_SYM, "LEnv only supports symbolic keys");
  for (size_t i = 0; i < env->count; i++) {
    if (strcmp(key->str, env->labels[i]) == 0) {
      return valk_lval_copy(env->vals[i]);
    }
  }
  return valk_lval_err("LEnv does not have requested reference");
}

void valk_lenv_put(valk_lenv_t *env, valk_lval_t *key, valk_lval_t *val) {
  // TODO(main): technically this is a failure condition for us, but the
  // return's void LVAL_ASSERT(NULL, key->type == LVAL_SYM, "LEnv only supports
  // symbolic keys");
  for (size_t i = 0; i < env->count; i++) {
    if (strcmp(key->str, env->labels[i]) == 0) {
      // if we found it, we destroy it
      valk_lval_free(env->vals[i]);
      env->vals[i] = valk_lval_copy(env->vals[i]);
      return;
    }
  }
  // TODO(main): technically we should be able to do the ammortized arraylist
  // where we double the array on overflow, but i guess it doesnt matter for now
  env->labels = realloc(env->labels, sizeof(env->labels) * (env->count + 1));
  env->vals = realloc(env->vals, sizeof(env->vals) * (env->count + 1));

  env->labels[env->count] = strndup(key->str, 200);
  env->vals[env->count] = valk_lval_copy(val);

  ++env->count;
}

void valk_lenv_put_builtin(valk_lenv_t *env, char *key,
                           valk_lval_builtin_t *fun) {
  valk_lval_t lkey = {.type = LVAL_SYM, .str = key};

  valk_lval_t lfun = {.type = LVAL_FUN, .fun = fun};

  valk_lenv_put(env, &lkey, &lfun);
}

static valk_lval_t *builtin_math(valk_lval_t *lst, char *op) {
  for (int i = 0; i < lst->count; ++i) {
    if (lst->cell[i]->type != LVAL_NUM) {
      valk_lval_free(lst);
      return valk_lval_err("Sorry can only do math with numbers");
    }
  }

  valk_lval_t *x = valk_lval_pop(lst, 0);

  if (strcmp(op, "-") == 0 && lst->count == 1) {
    // Negate the number if there is only 1
    x->num = -x->num;
  }

  while (lst->count > 0) {
    valk_lval_t *y = valk_lval_pop(lst, 0);

    if (strcmp(op, "+") == 0) {
      x->num += y->num;
    }
    if (strcmp(op, "-") == 0) {
      x->num -= y->num;
    }
    if (strcmp(op, "*") == 0) {
      x->num *= y->num;
    }
    if (strcmp(op, "/") == 0) {
      if (y->num > 0) {
        x->num /= y->num;
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

static valk_lval_t *valk_builtin_cons(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT(a, a->count == 2,
              "Builtin `cons` passed incorrect number of arguments");
  LVAL_ASSERT(a, a->cell[1]->type == LVAL_QEXPR,
              "Builtin `cons` can only operate on Q-Expressions");
  valk_lval_t *head = valk_lval_pop(a, 0);
  valk_lval_t *tail = valk_lval_pop(a, 0);
  // TODO(main): this should be implmented as push
  tail->cell = realloc(tail->cell, sizeof(tail->cell) * (tail->count + 1));
  memmove(&tail->cell[1], tail->cell, sizeof(tail->cell) * tail->count);
  tail->cell[0] = head;
  tail->count++;
  valk_lval_free(a);
  return tail;
}

static valk_lval_t *valk_builtin_len(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT(a, a->count == 1, "This function requires exactly 1 parameter");
  // TODO(main): should this only work with Q expr?
  LVAL_ASSERT(a, a->cell[0]->type == LVAL_QEXPR,
              "Only works with Q expressions??? it dont have to tho");
  valk_lval_t *res = valk_lval_num(a->cell[0]->count);
  valk_lval_free(a);
  return res;
}

static valk_lval_t *valk_builtin_head(valk_lenv_t *e, valk_lval_t *a) {
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

static valk_lval_t *valk_builtin_tail(valk_lenv_t *e, valk_lval_t *a) {
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

static valk_lval_t *valk_builtin_init(valk_lenv_t *e, valk_lval_t *a) {
  // TODO(main): can i make this more flexible, that way these functions can
  // work over argument list as well? or is that something thats too obvious
  LVAL_ASSERT(a, a->count == 1, "Builtin `tail` works with 1 argument");
  LVAL_ASSERT(a, a->cell[0]->type == LVAL_QEXPR,
              "Builtin `tail` can only operate on Q-Expressions");
  LVAL_ASSERT(a, a->cell[0]->count > 0,
              "Builtin `tail` cannot operate on `{}`");
  valk_lval_free(valk_lval_pop(a->cell[0], a->cell[0]->count - 1));
  valk_lval_t *res = valk_lval_pop(a, 0);
  valk_lval_free(a);
  return res;
}

static valk_lval_t *valk_builtin_join(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT(a, a->cell[0]->type == LVAL_QEXPR,
              "Builtin `join` can only operate on Q-Expressions");
  valk_lval_t *x = valk_lval_pop(a, 0);
  while (a->count) {
    x = valk_lval_join(x, valk_lval_pop(a, 0));
  }
  valk_lval_free(a);
  return x;
}

static valk_lval_t *valk_builtin_list(valk_lenv_t *e, valk_lval_t *a) {
  a->type = LVAL_QEXPR;
  return a;
}

static valk_lval_t *valk_builtin_eval(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT(a, a->count == 1, "Builtin `eval` passed too many arguments");
  LVAL_ASSERT(a, a->cell[0]->type == LVAL_QEXPR,
              "Builtin `eval` can only operate on Q-Expressions");

  valk_lval_t *v = valk_lval_pop(a, 0);
  v->type = LVAL_SEXPR;
  valk_lval_free(a);
  return valk_lval_eval(e, v);
}
static valk_lval_t *valk_builtin_plus(valk_lenv_t *e, valk_lval_t *a) {
  return builtin_math(a, "+");
}
static valk_lval_t *valk_builtin_minus(valk_lenv_t *e, valk_lval_t *a) {
  return builtin_math(a, "-");
}
static valk_lval_t *valk_builtin_divide(valk_lenv_t *e, valk_lval_t *a) {
  return builtin_math(a, "/");
}
static valk_lval_t *valk_builtin_multiply(valk_lenv_t *e, valk_lval_t *a) {
  return builtin_math(a, "*");
}

void valk_lenv_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "list", valk_builtin_list);
  valk_lenv_put_builtin(env, "cons", valk_builtin_cons);
  valk_lenv_put_builtin(env, "len", valk_builtin_len);
  valk_lenv_put_builtin(env, "init", valk_builtin_init);
  valk_lenv_put_builtin(env, "head", valk_builtin_head);
  valk_lenv_put_builtin(env, "tail", valk_builtin_tail);
  valk_lenv_put_builtin(env, "join", valk_builtin_join);
  valk_lenv_put_builtin(env, "eval", valk_builtin_eval);

  valk_lenv_put_builtin(env, "+", valk_builtin_plus);
  valk_lenv_put_builtin(env, "-", valk_builtin_minus);
  valk_lenv_put_builtin(env, "/", valk_builtin_divide);
  valk_lenv_put_builtin(env, "*", valk_builtin_multiply);
}
