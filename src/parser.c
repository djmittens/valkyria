#include "parser.h"
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#define LVAL_RAISE(args, fmt, ...)                                             \
  do {                                                                         \
    char *_fmt =                                                               \
        valk_c_err_format(fmt, __FILE_NAME__, __LINE__, __FUNCTION__);         \
    valk_lval_t *err = valk_lval_err(_fmt, ##__VA_ARGS__);                     \
    valk_lval_free(args);                                                      \
    free(_fmt);                                                                \
    return err;                                                                \
  } while (0)

#define LVAL_ASSERT(args, cond, fmt, ...)                                      \
  if (!(cond)) {                                                               \
    LVAL_RAISE(args, fmt, ##__VA_ARGS__);                                      \
  }

#define LVAL_ASSERT_TYPE(args, lval, _type, ...)                               \
  do {                                                                         \
    char _found = 0;                                                           \
    valk_ltype_t _expected[] = {(_type), __VA_ARGS__};                         \
    size_t _n_expected = sizeof(_expected) / sizeof(valk_ltype_t);             \
                                                                               \
    for (size_t i = 0; i < _n_expected; i++) {                                 \
      if ((lval)->type == _expected[i]) {                                      \
        _found = 1;                                                            \
        break;                                                                 \
      }                                                                        \
    }                                                                          \
    if (!_found) {                                                             \
      char const *_expect_str[_n_expected];                                    \
      for (size_t i = 0; i < _n_expected; i++) {                               \
        _expect_str[i] = valk_ltype_name(_expected[i]);                        \
      }                                                                        \
      char *_estr = valk_str_join(_n_expected, _expect_str, ", ");             \
                                                                               \
      char *_fmt = valk_c_err_format("Actual: %s, Expected(One-Of): [%s]",     \
                                     __FILE_NAME__, __LINE__, __FUNCTION__);   \
      valk_lval_t *err =                                                       \
          valk_lval_err(_fmt, valk_ltype_name((lval)->type), _estr);           \
      free(_estr);                                                             \
      free(_fmt);                                                              \
      valk_lval_free(args);                                                    \
      return err;                                                              \
    }                                                                          \
  } while (0)

#define LVAL_ASSERT_COUNT_NEQ(args, lval, _count)                              \
  LVAL_ASSERT(args, (lval)->expr.count != _count,                              \
              "Invalid argument count, Actual[%d] != Expected[%d]",            \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_EQ(args, lval, _count)                               \
  LVAL_ASSERT(args, (lval)->expr.count == _count,                              \
              "Invalid argument count, Actual[%d] == Expected[%d]",            \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_LT(args, lval, _count)                               \
  LVAL_ASSERT(args, (lval)->expr.count < _count,                               \
              "Invalid argument count, Actual[%d] < Expected[%d]",             \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_LE(args, lval, _count)                               \
  LVAL_ASSERT(args, (lval)->expr.count <= _count,                              \
              "Invalid argument count, Actual[%d] <= Expected[%d]",            \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_GT(args, lval, _count)                               \
  LVAL_ASSERT(args, (lval)->expr.count > _count,                               \
              "Invalid argument count, Actual[%d] > Expected[%d]",             \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_GE(args, lval, _count)                               \
  LVAL_ASSERT(args, (lval)->expr.count >= _count,                              \
              "Invalid argument count, Actual[%d] >= Expected[%d]",            \
              (lval)->expr.count, _count)

static valk_lval_t *valk_builtin_eval(valk_lenv_t *e, valk_lval_t *a);
static valk_lval_t *valk_builtin_list(valk_lenv_t *e, valk_lval_t *a);

static char *valk_c_err_format(const char *fmt, const char *file,
                               const size_t line, const char *function) {
  size_t len = snprintf(NULL, 0, "%s:%ld:%s || %s", file, line, function, fmt);
  char *buf = malloc(len + 1);
  snprintf(buf, len + 1, "%s:%ld:%s || %s", file, line, function, fmt);
  return buf;
}

static char *valk_str_join(const size_t n, const char **strs, const char *sep) {
  // TODO(main): I think i should get my own string type in here
  size_t res_len = 0;
  size_t sep_len = strlen(sep);
  size_t str_lens[n];
  for (size_t i = 0; i < n; i++) {
    size_t _len = strlen(strs[i]);
    res_len += _len;
    str_lens[i] = _len;
    if (i < n - 1) {
      res_len += sep_len;
    }
  }
  char *res = malloc(res_len + 1);
  size_t offset = 0;
  for (size_t i = 0; i < n; i++) {
    memcpy(&res[offset], strs[i], str_lens[i]);
    offset += str_lens[i];
    if (i < n - 1) {
      memcpy(&res[offset], sep, sep_len);
      offset += sep_len;
    }
  }
  res[offset] = '\0';

  return res;
}

const char *valk_ltype_name(valk_ltype_t type) {
  switch (type) {
  case LVAL_NUM:
    return "Number";
  case LVAL_SYM:
    return "Symbol";
  case LVAL_FUN:
    return "Function";
  case LVAL_QEXPR:
    return "Quote-expr";
  case LVAL_SEXPR:
    return "Symbolic-expr";
  case LVAL_ERR:
    return "Error";
  }
}

valk_lval_t *valk_lval_num(long x) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_NUM;
  res->num = x;
  return res;
}

// TODO(main): look into UTF-8 support
valk_lval_t *valk_lval_err(char *fmt, ...) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_ERR;
  va_list va;
  va_start(va, fmt);

  size_t len = vsnprintf(NULL, 0, fmt, va);
  // TODO(main): look into making this into a constant
  len = len < 512 ? len : 511;
  res->str = malloc(len + 1);
  vsnprintf(res->str, len + 1, fmt, va);

  va_end(va);
  return res;
}

valk_lval_t *valk_lval_sym(char *sym) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_SYM;
  res->str = strndup(sym, 200);
  res->expr.count = 0;
  return res;
}

valk_lval_t *valk_lval_builtin(valk_lval_builtin_t *fun) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_SYM;
  res->fun.builtin = fun;
  res->fun.env = NULL;
  return res;
}
valk_lval_t *valk_lval_lambda(valk_lval_t *formals, valk_lval_t *body) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_FUN;
  res->fun.builtin = NULL;
  res->fun.env = valk_lenv_new();
  res->fun.formals = formals;
  res->fun.body = body;
  return res;
}

valk_lval_t *valk_lval_sexpr_empty() {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_SEXPR;
  res->expr.cell = NULL;
  res->expr.count = 0;
  return res;
}

valk_lval_t *valk_lval_qexpr_empty() {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_QEXPR;
  res->expr.cell = NULL;
  res->expr.count = 0;
  return res;
}

valk_lval_t *valk_lval_copy(valk_lval_t *lval) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = lval->type;
  switch (lval->type) {
  case LVAL_NUM:
    res->num = lval->num;
    break;
  case LVAL_FUN:
    if (lval->fun.builtin) {
      res->fun.builtin = lval->fun.builtin;
      res->fun.env = NULL;
      res->fun.body = NULL;
      res->fun.formals = NULL;
    } else {
      res->fun.builtin = NULL;
      res->fun.env = valk_lenv_copy(lval->fun.env);
      res->fun.body = valk_lval_copy(lval->fun.body);
      res->fun.formals = valk_lval_copy(lval->fun.formals);
    }
    break;
  case LVAL_QEXPR:
  case LVAL_SEXPR:
    res->expr.cell = malloc(sizeof(res->expr.cell) * lval->expr.count);
    res->expr.count = lval->expr.count;
    for (int i = 0; i < lval->expr.count; ++i) {
      res->expr.cell[i] = valk_lval_copy(lval->expr.cell[i]);
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
  if (lval == NULL) {
    return;
  }
  switch (lval->type) {
  case LVAL_FUN:
    if (!lval->fun.builtin) {
      valk_lval_free(lval->fun.body);
      valk_lval_free(lval->fun.formals);
      valk_lenv_free(lval->fun.env);
    }
    break;
  case LVAL_NUM:
    // nuttin to do but break;
    break;
  case LVAL_SYM:
  case LVAL_ERR:
    free(lval->str);
    break;
  case LVAL_QEXPR:
  case LVAL_SEXPR:
    while (lval->expr.count > 0) {
      valk_lval_free(lval->expr.cell[lval->expr.count - 1]);
      --lval->expr.count;
    }
    // Should play around with valgrind on this. Pretty interesting thing to
    // forget
    free(lval->expr.cell);
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
  LVAL_ASSERT_TYPE(sexpr, sexpr, LVAL_SEXPR);
  // no children? no problem
  if (sexpr->expr.count == 0) {
    return sexpr;
  }

  // count up the chillen
  for (int i = 0; i < sexpr->expr.count; ++i) {
    sexpr->expr.cell[i] = valk_lval_eval(env, sexpr->expr.cell[i]);
    if (sexpr->expr.cell[i]->type == LVAL_ERR) {
      valk_lval_t *res = valk_lval_pop(sexpr, i);
      valk_lval_free(sexpr);
      return res;
    }
  }

  // If we have a single node, collapse to it
  if (sexpr->expr.count == 1) {
    valk_lval_t *res = valk_lval_pop(sexpr, 0);
    valk_lval_free(sexpr);
    return res;
  }

  valk_lval_t *fun = valk_lval_pop(sexpr, 0);
  if (fun->type != LVAL_FUN) {
    // Make sure to free this shit.
    // TODO(main): should add more information here about the symbol
    valk_lval_t *res = valk_lval_err(
        "S-expr doesnt start with a <function>, Actual: %s Expected: %s",
        valk_ltype_name(fun->type), valk_ltype_name(LVAL_FUN));
    valk_lval_free(fun);
    valk_lval_free(sexpr);
  }

  valk_lval_t *res = valk_lval_eval_call(env, fun, sexpr);
  return res;
}

valk_lval_t *valk_lval_eval_call(valk_lenv_t *env, valk_lval_t *func,
                                 valk_lval_t *args) {
  if (func->fun.builtin) {
    return func->fun.builtin(env, args);
  }
  size_t given = args->expr.count;
  size_t requested = func->fun.formals->expr.count;
  valk_lval_t *res;

  while (args->expr.count) {
    if (func->fun.formals->expr.count == 0) {
      valk_lval_free(args);
      valk_lval_free(func);
      return valk_lval_err(
          "More arguments were given than required Actual: %ld, Expected: %ld",
          given, requested);
    }
    valk_lval_t *sym = valk_lval_pop(func->fun.formals, 0);
    if (strcmp(sym->str, "&") == 0) {
      // if we encountered this, the rest of arguments are varargs
      if (func->fun.formals->expr.count != 1) {
        valk_lval_free(args);
        return valk_lval_err("Invalid  function format, the vararg symbol `&` "
                             "is not followed by others");
      }
      valk_lval_t *nsym = valk_lval_pop(func->fun.formals, 0);
      valk_lenv_put(func->fun.env, nsym, valk_builtin_list(env, args));
      valk_lval_free(sym);
      valk_lval_free(nsym);
      break;
    }
    valk_lval_t *val = valk_lval_pop(args, 0);
    valk_lenv_put(func->fun.env, sym, val);
    valk_lval_free(sym);
    valk_lval_free(val);
  }

  // if whats remaining is the elipsis, then we expand to empty list
  if (func->fun.formals->expr.count > 0 &&
      strcmp(func->fun.formals->expr.cell[0]->str, "&")) {

    if (func->fun.formals->expr.count != 2) {
      valk_lval_free(args);
      return valk_lval_err("Invalid  function format, the vararg symbol `&` "
                           "is not followed by others");
    }

    // discard the &
    valk_lval_free(valk_lval_pop(func->fun.formals, 0));
    valk_lval_t *sym = valk_lval_pop(func->fun.formals, 0);
    valk_lval_t *val = valk_lval_qexpr_empty();
    valk_lenv_put(env, sym, val);
    valk_lval_free(sym);
    valk_lval_free(val);
  }

  // If everything is bound we evalutate
  if (func->fun.formals->expr.count == 0) {
    func->fun.env->parent = env;
    res = valk_builtin_eval(
        func->fun.env,
        valk_lval_add(valk_lval_sexpr_empty(), valk_lval_copy(func->fun.body)));
    valk_lval_free(func);
  } else {
    res = func;
  }
  valk_lval_free(args);
  return res;
}

valk_lval_t *valk_lval_pop(valk_lval_t *lval, size_t i) {
  LVAL_ASSERT(lval, i < lval->expr.count,
              "Cant pop from list at invalid position: [%d] total length: [%d]",
              i, lval->expr.count);
  LVAL_ASSERT(lval, lval->expr.count > 0, "Cant pop from empty");

  valk_lval_t *cell = lval->expr.cell[i];
  // shift dems down
  memmove(&lval->expr.cell[i], &lval->expr.cell[i + 1],
          sizeof(valk_lval_t *) * (lval->expr.count - i - 1));
  lval->expr.count--;
  lval->expr.cell =
      realloc(lval->expr.cell, sizeof(valk_lval_t *) * lval->expr.count);
  return cell;
}

valk_lval_t *valk_lval_add(valk_lval_t *lval, valk_lval_t *cell) {
  // TODO(main):  this will leak the cell, i need to expand this macro to free
  // more than 1 thing
  LVAL_ASSERT_TYPE(lval, lval, LVAL_SEXPR, LVAL_QEXPR);
  // TODO(main): i need to invest more into null checks in this file
  LVAL_ASSERT(lval, cell != NULL, "Adding NULL to LVAL is not allowed");

  lval->expr.count++;
  lval->expr.cell =
      realloc(lval->expr.cell, sizeof(valk_lval_t *) * lval->expr.count);
  lval->expr.cell[lval->expr.count - 1] = cell;
  return lval;
}

valk_lval_t *valk_lval_join(valk_lval_t *a, valk_lval_t *b) {
  while (b->expr.count) {
    a = valk_lval_add(a, valk_lval_pop(b, 0));
  }
  valk_lval_free(b);
  return a;
}

void valk_lval_print(valk_lval_t *val) {
  if (val == NULL) {
    return;
  }
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
    for (int i = 0; i < val->expr.count; ++i) {
      valk_lval_print(val->expr.cell[i]);
      if (i < val->expr.count - 1) {
        putchar(' ');
      }
    }
    printf(" }");
    break;
  case LVAL_SEXPR:
    printf("Sexpr( ");
    for (int i = 0; i < val->expr.count; ++i) {
      valk_lval_print(val->expr.cell[i]);
      if (i < val->expr.count - 1) {
        putchar(' ');
      }
    }
    printf(" )");
    break;
  case LVAL_ERR:
    printf("Error[%s]", val->str);
    break;
  case LVAL_FUN:
    if (val->fun.builtin) {
      printf("<builtin>");
    } else {
      printf("(\\ ");
      valk_lval_print(val->fun.formals);
      putchar(' ');
      valk_lval_print(val->fun.body);
      putchar(')');
    }
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
  env->parent = NULL;
  env->count = 0;
  env->symbols = NULL;
  env->vals = NULL;
}

void valk_lenv_free(valk_lenv_t *env) {
  for (int i = 0; i < env->count; ++i) {
    valk_lval_free(env->vals[i]);
    free(env->symbols[i]);
  }
  free(env->vals);
  free(env->symbols);
  free(env);
}

valk_lenv_t *valk_lenv_copy(valk_lenv_t *env) {
  valk_lenv_t *res = malloc(sizeof(valk_lval_t));
  res->parent = env->parent;
  res->count = env->count;
  res->symbols = malloc(sizeof(env->symbols) * env->count);
  res->vals = malloc(sizeof(env->vals) * env->count);

  for (size_t i = 0; i < env->count; i++) {
    res->symbols[i] = strdup(env->symbols[i]);
    res->vals[i] = valk_lval_copy(env->vals[i]);
  }
  return res;
}

valk_lval_t *valk_lenv_get(valk_lenv_t *env, valk_lval_t *key) {
  LVAL_ASSERT_TYPE(NULL, key, LVAL_SYM);

  for (size_t i = 0; i < env->count; i++) {
    if (strcmp(key->str, env->symbols[i]) == 0) {
      return valk_lval_copy(env->vals[i]);
    }
  }

  if (env->parent) {
    return valk_lenv_get(env->parent, key);
  } else {
    return valk_lval_err("LEnv: Symbol `%s` is not bound", key->str);
  }
}

void valk_lenv_put(valk_lenv_t *env, valk_lval_t *key, valk_lval_t *val) {
  // TODO(main): technically this is a failure condition for us, but the
  // return's void LVAL_ASSERT(NULL, key->type == LVAL_SYM, "LEnv only supports
  // symbolic keys");
  for (size_t i = 0; i < env->count; i++) {
    if (strcmp(key->str, env->symbols[i]) == 0) {
      // if we found it, we destroy it
      valk_lval_free(env->vals[i]);
      env->vals[i] = valk_lval_copy(val);
      return;
    }
  }
  // TODO(main): technically we should be able to do the ammortized arraylist
  // where we double the array on overflow, but i guess it doesnt matter for now
  env->symbols = realloc(env->symbols, sizeof(env->symbols) * (env->count + 1));
  env->vals = realloc(env->vals, sizeof(env->vals) * (env->count + 1));

  env->symbols[env->count] = strndup(key->str, 200);
  env->vals[env->count] = valk_lval_copy(val);

  ++env->count;
}

// Define the key in global scope
void valk_lenv_def(valk_lenv_t *env, valk_lval_t *key, valk_lval_t *val) {
  while (env->parent) {
    env = env->parent;
  }
  valk_lenv_put(env, key, val);
}

void valk_lenv_put_builtin(valk_lenv_t *env, char *key,
                           valk_lval_builtin_t *_fun) {
  valk_lval_t lkey = {.type = LVAL_SYM, .str = key};

  valk_lval_t lfun = {.type = LVAL_FUN, .fun = {.builtin = _fun, .env = NULL}};

  valk_lenv_put(env, &lkey, &lfun);
}

static valk_lval_t *builtin_math(valk_lval_t *lst, char *op) {
  for (int i = 0; i < lst->expr.count; ++i) {
    // TODO(main): Its not very straightforward to assert a type here
    if (lst->expr.cell[i]->type != LVAL_NUM) {
      LVAL_RAISE(lst, "This function only supports Numbers : %s",
                 valk_ltype_name(lst->expr.cell[i]->type));
    }
  }

  valk_lval_t *x = valk_lval_pop(lst, 0);

  if (strcmp(op, "-") == 0 && lst->expr.count == 0) {
    // Negate the number if there is only 1
    x->num = -x->num;
  }

  while (lst->expr.count > 0) {
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
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, a->expr.cell[1], LVAL_QEXPR);

  valk_lval_t *head = valk_lval_pop(a, 0);
  valk_lval_t *tail = valk_lval_pop(a, 0);
  // TODO(main): this should be implmented as push
  tail->expr.cell = realloc(tail->expr.cell,
                            sizeof(tail->expr.cell) * (tail->expr.count + 1));
  memmove(&tail->expr.cell[1], tail->expr.cell,
          sizeof(tail->expr.cell) * tail->expr.count);
  tail->expr.cell[0] = head;
  tail->expr.count++;
  valk_lval_free(a);
  return tail;
}

static valk_lval_t *valk_builtin_len(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  // TODO(main): should this only work with Q expr?
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);

  valk_lval_t *res = valk_lval_num(a->expr.cell[0]->expr.count);
  valk_lval_free(a);
  return res;
}

static valk_lval_t *valk_builtin_head(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT(a, a->expr.count == 1,
              "Builtin `head` passed too many arguments");
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);
  LVAL_ASSERT_COUNT_GT(a, a->expr.cell[0], 0);
  valk_lval_t *v = valk_lval_pop(a, 0);
  valk_lval_free(a);
  while (v->expr.count > 1) {
    valk_lval_free(valk_lval_pop(v, 1));
  }
  return v;
}

static valk_lval_t *valk_builtin_tail(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT(a, a->expr.count == 1,
              "Builtin `tail` passed too many arguments");
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);
  LVAL_ASSERT(a, a->expr.cell[0]->expr.count != 0,
              "Builtin `tail` cannot operate on `{}`");
  valk_lval_t *v = valk_lval_pop(a, 0);

  valk_lval_free(a);
  valk_lval_free(valk_lval_pop(v, 0));
  return v;
}

static valk_lval_t *valk_builtin_init(valk_lenv_t *e, valk_lval_t *a) {
  // TODO(main): can i make this more flexible, that way these functions can
  // work over argument list as well? or is that something thats too obvious
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);
  LVAL_ASSERT_COUNT_GT(a, a->expr.cell[0], 0);
  valk_lval_free(
      valk_lval_pop(a->expr.cell[0], a->expr.cell[0]->expr.count - 1));
  valk_lval_t *res = valk_lval_pop(a, 0);
  valk_lval_free(a);
  return res;
}

static valk_lval_t *valk_builtin_join(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);

  valk_lval_t *x = valk_lval_pop(a, 0);
  while (a->expr.count) {
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
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);

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

static valk_lval_t *valk_builtin_def(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_GT(a, a, 1);

  valk_lval_t *syms = a->expr.cell[0];
  LVAL_ASSERT_TYPE(a, syms, LVAL_QEXPR);

  for (size_t i = 1; i < syms->expr.count; i++) {
    LVAL_ASSERT(a, syms->expr.cell[i]->type == LVAL_SYM,
                "Builtin `def` requires that symbols parameter only has "
                "symbols found: %s",
                valk_ltype_name(a->expr.cell[i]->type));
  }

  LVAL_ASSERT_COUNT_EQ(a, syms, (a->expr.count - 1));

  for (size_t i = 0; i < syms->expr.count; i++) {
    valk_lenv_def(e, syms->expr.cell[i], a->expr.cell[i + 1]);
  }

  valk_lval_free(a);
  return valk_lval_sexpr_empty();
}

static valk_lval_t *valk_builtin_put(valk_lenv_t *e, valk_lval_t *a) {
  // TODO(main): should dedupe these functions perhaps? i dont care right now
  // tho
  LVAL_ASSERT_COUNT_GT(a, a, 1);

  valk_lval_t *syms = a->expr.cell[0];
  LVAL_ASSERT_TYPE(a, syms, LVAL_QEXPR);

  for (size_t i = 1; i < syms->expr.count; i++) {
    LVAL_ASSERT(a, syms->expr.cell[i]->type == LVAL_SYM,
                "Builtin `def` requires that symbols parameter only has "
                "symbols found: %s",
                valk_ltype_name(a->expr.cell[i]->type));
  }

  LVAL_ASSERT_COUNT_EQ(a, syms, (a->expr.count - 1));

  for (size_t i = 0; i < syms->expr.count; i++) {
    valk_lenv_put(e, syms->expr.cell[i], a->expr.cell[i + 1]);
  }

  valk_lval_free(a);
  return valk_lval_sexpr_empty();
}

static valk_lval_t *valk_builtin_lambda(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t *formals = a->expr.cell[0];
  valk_lval_t *body = a->expr.cell[1];

  LVAL_ASSERT_TYPE(a, formals, LVAL_QEXPR);
  LVAL_ASSERT_TYPE(a, body, LVAL_QEXPR);

  for (size_t i = 0; i < formals->expr.count; i++) {
    LVAL_ASSERT(a, formals->expr.cell[i]->type == LVAL_SYM,
                "Cannot use a non symbol[%s] for bind",
                valk_ltype_name(a->expr.cell[0]->expr.cell[i]->type));
  }

  formals = valk_lval_pop(a, 0);
  body = valk_lval_pop(a, 0);
  valk_lval_free(a);

  return valk_lval_lambda(formals, body);
}

static valk_lval_t *valk_builtin_penv(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  valk_lval_t *res = valk_lval_qexpr_empty();
  for (size_t i = 0; i < e->count; i++) {

    valk_lval_t *qexpr = valk_lval_qexpr_empty();
    // TODO(main): So each of these can fail, in that case we want to free the
    // intermediates, im too lazy to do that tho, so memory leaks n such.
    // really i can also check the pre-conditions here to make sure we dont even
    // allocate anything if they arent met
    valk_lval_add(qexpr, valk_lval_sym(e->symbols[i]));
    valk_lval_add(qexpr, valk_lval_copy(e->vals[i]));
    valk_lval_add(res, qexpr);
  }
  valk_lval_free(a);
  return res;
}

static valk_lval_t *valk_builtin_ord(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_SYM);
  LVAL_ASSERT_TYPE(a, a->expr.cell[1], LVAL_NUM);
  LVAL_ASSERT_TYPE(a, a->expr.cell[2], LVAL_NUM);

  const char *op = a->expr.cell[0]->str;

  int r;
  if (strcmp(op, ">") == 0) {
    r = (a->expr.cell[1]->num > a->expr.cell[2]->num);
  }
  if (strcmp(op, "<") == 0) {
    r = (a->expr.cell[1]->num < a->expr.cell[2]->num);
  }
  if (strcmp(op, ">=") == 0) {
    r = (a->expr.cell[1]->num >= a->expr.cell[2]->num);
  }
  if (strcmp(op, "<=") == 0) {
    r = (a->expr.cell[1]->num <= a->expr.cell[2]->num);
  }

  valk_lval_free(a);
  return valk_lval_num(r);
}

static valk_lval_t *valk_builtin_gt(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym(">"));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}
static valk_lval_t *valk_builtin_lt(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("<"));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}
static valk_lval_t *valk_builtin_ge(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym(">="));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}
static valk_lval_t *valk_builtin_le(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("<="));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
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

  valk_lenv_put_builtin(env, "def", valk_builtin_def);
  valk_lenv_put_builtin(env, "=", valk_builtin_put);
  valk_lenv_put_builtin(env, "\\", valk_builtin_lambda);
  valk_lenv_put_builtin(env, "penv", valk_builtin_penv);
  valk_lenv_put_builtin(env, "ord", valk_builtin_ord);
  valk_lenv_put_builtin(env, ">", valk_builtin_gt);
  valk_lenv_put_builtin(env, "<", valk_builtin_lt);
  valk_lenv_put_builtin(env, ">=", valk_builtin_ge);
  valk_lenv_put_builtin(env, "<=", valk_builtin_le);
}
