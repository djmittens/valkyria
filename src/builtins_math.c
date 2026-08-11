#include "builtins_internal.h"

#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int rand_seeded = 0;

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

  // Nullary + and * are their identities, so (+) and (apply + {}) fold
  // cleanly over an empty list. Without this the pop below read past the
  // end of an empty list and returned uninitialized memory. `-` and `/`
  // have no identity — negation and reciprocal need an operand.
  if (valk_lval_list_count(lst) == 0) {
    switch (op) { // LCOV_EXCL_BR_LINE - all enum values handled
      case MATH_ADD: return valk_lval_num(0);
      case MATH_MUL: return valk_lval_num(1);
      case MATH_SUB: return valk_lval_err("`-` requires at least one argument");
      case MATH_DIV: return valk_lval_err("`/` requires at least one argument");
    }
  }

  valk_lval_t* first = valk_lval_pop(lst, 0);
  long result = first->num;

  if (op == MATH_SUB && valk_lval_list_count(lst) == 0) {
    result = -result;
  } else {
    while (valk_lval_list_count(lst) > 0) {
      valk_lval_t* y = valk_lval_pop(lst, 0);
      switch (op) { // LCOV_EXCL_BR_LINE - all enum values handled
        case MATH_ADD: result += y->num; break;
        case MATH_SUB: result -= y->num; break;
        case MATH_MUL: result *= y->num; break;
        case MATH_DIV:
          // Only zero is undefined. This used to reject every y <= 0, so
          // (/ 10 -2) raised "Division By Zero"; the JIT then grew a
          // matching y <= 0 guard, and a test pinned the behaviour.
          if (y->num == 0) return valk_lval_err("Division By Zero");
          result /= y->num;
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

// Fold a comparison across every ADJACENT pair: (< 1 2 3) is 1<2 and 2<3.
// Short-circuits on the first false pair. A single argument is vacuously
// true — a chain with no pairs holds.
static valk_lval_t* valk_builtin_chain(valk_lval_t* a, ord_op_e op) {
  LVAL_ASSERT_COUNT_GE(a, a, 1);
  u64 n = valk_lval_list_count(a);
  // Bind the element first: LVAL_ASSERT_TYPE declares its own `i` and
  // re-expands its `lval` argument inside that loop, so passing
  // `valk_lval_list_nth(a, i)` directly would silently re-check element 0
  // every iteration.
  for (u64 idx = 0; idx < n; idx++) {
    valk_lval_t* arg = valk_lval_list_nth(a, idx);
    LVAL_ASSERT_TYPE(a, arg, LVAL_NUM);
  }
  for (u64 i = 0; i + 1 < n; i++) {
    long x = valk_lval_list_nth(a, i)->num;
    long y = valk_lval_list_nth(a, i + 1)->num;
    bool ok;
    switch (op) { // LCOV_EXCL_BR_LINE - all enum values handled
      case ORD_GT: ok = x > y; break;
      case ORD_LT: ok = x < y; break;
      case ORD_GE: ok = x >= y; break;
      case ORD_LE: ok = x <= y; break;
    }
    if (!ok) return valk_lval_num(0);
  }
  return valk_lval_num(1);
}

// (min 3 1 4) / (max 3 1 4). At least one argument: there is no identity
// to return for the empty case that isn't a lie about the number domain.
static valk_lval_t* valk_builtin_minmax(valk_lval_t* a, bool want_max) {
  LVAL_ASSERT_COUNT_GE(a, a, 1);
  u64 n = valk_lval_list_count(a);
  for (u64 idx = 0; idx < n; idx++) {
    valk_lval_t* arg = valk_lval_list_nth(a, idx);
    LVAL_ASSERT_TYPE(a, arg, LVAL_NUM);
  }
  long best = valk_lval_list_nth(a, 0)->num;
  for (u64 i = 1; i < n; i++) {
    long v = valk_lval_list_nth(a, i)->num;
    if (want_max ? (v > best) : (v < best)) best = v;
  }
  return valk_lval_num(best);
}

static valk_lval_t* valk_builtin_ord(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  // LCOV_EXCL_BR_STOP
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

// (== a b c) is "all equal", checked against the first operand so the
// result does not depend on scan order. Short-circuits on the first
// mismatch. Unlike the ordering operators this accepts any type, since
// valk_lval_eq is defined for all of them.
static valk_lval_t* valk_builtin_all_eq(valk_lval_t* a, bool* out) {
  LVAL_ASSERT_COUNT_GE(a, a, 1);
  u64 n = valk_lval_list_count(a);
  valk_lval_t* first = valk_lval_list_nth(a, 0);
  for (u64 i = 1; i < n; i++) {
    if (!valk_lval_eq(first, valk_lval_list_nth(a, i))) {
      *out = false;
      return nullptr;
    }
  }
  *out = true;
  return nullptr;
}

static valk_lval_t* valk_builtin_eq(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  bool all;
  valk_lval_t* err = valk_builtin_all_eq(a, &all);
  if (err) return err; // LCOV_EXCL_BR_LINE - arg validation
  return valk_lval_num(all);
}

// The complement of ==: true when the operands are NOT all equal. For two
// arguments this is the familiar pairwise !=.
static valk_lval_t* valk_builtin_ne(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  bool all;
  valk_lval_t* err = valk_builtin_all_eq(a, &all);
  if (err) return err; // LCOV_EXCL_BR_LINE - arg validation
  return valk_lval_num(!all);
}
static valk_lval_t* valk_builtin_gt(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_chain(a, ORD_GT);
}
static valk_lval_t* valk_builtin_lt(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_chain(a, ORD_LT);
}
static valk_lval_t* valk_builtin_ge(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_chain(a, ORD_GE);
}
static valk_lval_t* valk_builtin_le(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_chain(a, ORD_LE);
}
static valk_lval_t* valk_builtin_min(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_minmax(a, false);
}
static valk_lval_t* valk_builtin_max(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_minmax(a, true);
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

static valk_lval_t* valk_builtin_modulo(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);
  // LCOV_EXCL_BR_STOP
  long x = valk_lval_list_nth(a, 0)->num;
  long y = valk_lval_list_nth(a, 1)->num;
  if (y == 0) return valk_lval_err("Modulo By Zero");
  return valk_lval_num(x % y);
}

static valk_lval_t* valk_builtin_rand(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (!rand_seeded) {
    srand((unsigned)time(nullptr));
    rand_seeded = 1;
  }
  u64 count = valk_lval_list_count(a);
  if (count == 0) {
    return valk_lval_num(rand());
  }
  if (count == 1) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM); // LCOV_EXCL_BR_LINE - type validation
    long n = valk_lval_list_nth(a, 0)->num;
    if (n <= 0) return valk_lval_err("rand: bound must be positive, got %ld", n);
    return valk_lval_num(rand() % n);
  }
  if (count == 2) {
    // LCOV_EXCL_BR_START - type validation
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);
    // LCOV_EXCL_BR_STOP
    long lo = valk_lval_list_nth(a, 0)->num;
    long hi = valk_lval_list_nth(a, 1)->num;
    if (hi <= lo) return valk_lval_err("rand: high must be > low");
    return valk_lval_num(lo + rand() % (hi - lo));
  }
  LVAL_RAISE(a, "rand takes 0-2 arguments, got %zu", count);
}

static valk_lval_t* valk_builtin_rand_seed(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  // LCOV_EXCL_BR_STOP
  srand((unsigned)valk_lval_list_nth(a, 0)->num);
  rand_seeded = 1;
  return valk_lval_num(0);
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
  valk_lenv_put_builtin(env, "min", valk_builtin_min);
  valk_lenv_put_builtin(env, "max", valk_builtin_max);
  valk_lenv_put_builtin(env, "str->num", valk_builtin_str_to_num);
  valk_lenv_put_builtin(env, "%", valk_builtin_modulo);
  valk_lenv_put_builtin(env, "mod", valk_builtin_modulo);
  valk_lenv_put_builtin(env, "rand", valk_builtin_rand);
  valk_lenv_put_builtin(env, "rand-seed", valk_builtin_rand_seed);
}
