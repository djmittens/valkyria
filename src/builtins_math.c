#include "builtins_internal.h"

#include <errno.h>
#include <stdlib.h>
#include <string.h>

typedef enum { MATH_ADD, MATH_SUB, MATH_MUL, MATH_DIV } math_op_e;

// LCOV_EXCL_BR_START - math builtin has type validation loop
static valk_lval_t* valk_builtin_math(valk_lval_t* lst, math_op_e op) {
  valk_lval_t* curr = lst;
  while (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    if (LVAL_TYPE(curr->cons.head) != LVAL_NUM) {
      LVAL_RAISE(lst, "This function only supports Numbers : %s",
                 valk_ltype_name(LVAL_TYPE(curr->cons.head)));
    }
    curr = curr->cons.tail;
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t* first = valk_lval_pop(lst, 0);
  long result = first->num;

  if (op == MATH_SUB && valk_lval_list_count(lst) == 0) {
    result = -result;
  } else {
    while (valk_lval_list_count(lst) > 0) {
      valk_lval_t* y = valk_lval_pop(lst, 0);
      switch (op) {
        case MATH_ADD: result += y->num; break;
        case MATH_SUB: result -= y->num; break;
        case MATH_MUL: result *= y->num; break;
        case MATH_DIV:
          if (y->num > 0) {
            result /= y->num;
          } else {
            return valk_lval_err("Division By Zero");
          }
          break;
      }
    }
  }

  return valk_lval_num(result);
}

static valk_lval_t* valk_builtin_plus(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_math(a, MATH_ADD);
}
static valk_lval_t* valk_builtin_minus(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_math(a, MATH_SUB);
}
static valk_lval_t* valk_builtin_divide(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_math(a, MATH_DIV);
}
static valk_lval_t* valk_builtin_multiply(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_math(a, MATH_MUL);
}

typedef enum { ORD_GT, ORD_LT, ORD_GE, ORD_LE } ord_op_e;

// LCOV_EXCL_BR_START - ord internal only called from operator wrappers
static valk_lval_t* valk_builtin_ord_op(valk_lval_t* a, ord_op_e op) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);
  // LCOV_EXCL_BR_STOP
  long x = valk_lval_list_nth(a, 0)->num;
  long y = valk_lval_list_nth(a, 1)->num;
  switch (op) {
    case ORD_GT: return valk_lval_num(x > y);
    case ORD_LT: return valk_lval_num(x < y);
    case ORD_GE: return valk_lval_num(x >= y);
    case ORD_LE: return valk_lval_num(x <= y);
  }
  __builtin_unreachable();
}

static valk_lval_t* valk_builtin_ord(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* x = valk_lval_list_nth(a, 0);
  valk_lval_t* y = valk_lval_list_nth(a, 1);
  if (LVAL_TYPE(x) == LVAL_NUM && LVAL_TYPE(y) == LVAL_NUM) {
    long diff = x->num - y->num;
    return valk_lval_num(diff < 0 ? -1 : diff > 0 ? 1 : 0);
  }
  if (LVAL_TYPE(x) == LVAL_STR && LVAL_TYPE(y) == LVAL_STR) {
    return valk_lval_num(strcmp(x->str, y->str));
  }
  LVAL_RAISE(a, "ord requires two Numbers or two Strings, got %s and %s",
             valk_ltype_name(LVAL_TYPE(x)), valk_ltype_name(LVAL_TYPE(y)));
}

// LCOV_EXCL_BR_START - cmp builtins only called from operator wrappers
static valk_lval_t* valk_builtin_eq(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  // LCOV_EXCL_BR_STOP
  return valk_lval_num(valk_lval_eq(valk_lval_list_nth(a, 0), valk_lval_list_nth(a, 1)));
}
// LCOV_EXCL_BR_START - ne only called from operator wrappers
static valk_lval_t* valk_builtin_ne(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  // LCOV_EXCL_BR_STOP
  return valk_lval_num(!valk_lval_eq(valk_lval_list_nth(a, 0), valk_lval_list_nth(a, 1)));
}
static valk_lval_t* valk_builtin_gt(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_ord_op(a, ORD_GT);
}
static valk_lval_t* valk_builtin_lt(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_ord_op(a, ORD_LT);
}
static valk_lval_t* valk_builtin_ge(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_ord_op(a, ORD_GE);
}
static valk_lval_t* valk_builtin_le(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_ord_op(a, ORD_LE);
}

// LCOV_EXCL_BR_START - str->num arg validation
static valk_lval_t* valk_builtin_str_to_num(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* str = valk_lval_list_nth(a, 0)->str;
  char* endptr;
  errno = 0;
  long num = strtol(str, &endptr, 10);

  if (errno == ERANGE) {
    return valk_lval_err("Number out of range: %s", str);
  }
  if (*endptr != '\0') {
    return valk_lval_err("Invalid number: %s", str);
  }
  return valk_lval_num(num);
}

void valk_register_math_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "+", valk_builtin_plus);
  valk_lenv_put_builtin(env, "-", valk_builtin_minus);
  valk_lenv_put_builtin(env, "/", valk_builtin_divide);
  valk_lenv_put_builtin(env, "*", valk_builtin_multiply);
  valk_lenv_put_builtin(env, "ord", valk_builtin_ord);
  valk_lenv_put_builtin(env, ">", valk_builtin_gt);
  valk_lenv_put_builtin(env, "<", valk_builtin_lt);
  valk_lenv_put_builtin(env, ">=", valk_builtin_ge);
  valk_lenv_put_builtin(env, "<=", valk_builtin_le);
  valk_lenv_put_builtin(env, "==", valk_builtin_eq);
  valk_lenv_put_builtin(env, "!=", valk_builtin_ne);
  valk_lenv_put_builtin(env, "str->num", valk_builtin_str_to_num);
}
