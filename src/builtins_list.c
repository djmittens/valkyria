#include "builtins_internal.h"

#include <string.h>

static valk_lval_t* valk_builtin_cons(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* arg1 = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, arg1, LVAL_CONS, LVAL_NIL);

  valk_lval_t* head = valk_lval_list_nth(a, 0);
  valk_lval_t* tail = arg1;

  return valk_lval_cons(head, tail);
}

static valk_lval_t* valk_builtin_len(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* arg = valk_lval_list_nth(a, 0);
  switch (LVAL_TYPE(arg)) {
    case LVAL_CONS:
    case LVAL_NIL: {
      u64 count = valk_lval_list_count(arg);
      return valk_lval_num(count);
    }
    case LVAL_STR: {
      u64 n = strlen(arg->str);
      return valk_lval_num((long)n);
    }
    default:
      LVAL_RAISE(a, "Actual: %s, Expected(One-Of): [List, Nil, String]",
                 valk_ltype_name(LVAL_TYPE(arg)));
      return valk_lval_err("len invalid type");
  }
}

static valk_lval_t* valk_builtin_head(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT(a, valk_lval_list_count(a) == 1,
              "Builtin `head` passed too many arguments");
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_CONS, LVAL_QEXPR);
  LVAL_ASSERT_COUNT_GT(a, arg0, 0);

  return arg0->cons.head;
}

static valk_lval_t* valk_builtin_tail(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT(a, valk_lval_list_count(a) == 1,
              "Builtin `tail` passed too many arguments");
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_CONS, LVAL_QEXPR);
  LVAL_ASSERT(a, !valk_lval_list_is_empty(arg0),
              "Builtin `tail` cannot operate on empty list");

  return arg0->cons.tail;
}

static valk_lval_t* valk_list_init(valk_lval_t* list, bool is_qexpr) {
  if (valk_lval_list_is_empty(list)) {
    return valk_lval_nil();
  }

  if (valk_lval_list_is_empty(list->cons.tail)) {
    return valk_lval_nil();
  }

  if (is_qexpr) {
    return valk_lval_qcons(list->cons.head,
                           valk_list_init(list->cons.tail, is_qexpr));
  } else {
    return valk_lval_cons(list->cons.head,
                          valk_list_init(list->cons.tail, is_qexpr));
  }
}

static valk_lval_t* valk_builtin_init(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_CONS);
  LVAL_ASSERT_COUNT_GT(a, arg0, 0);

  bool is_qexpr = (arg0->flags & LVAL_FLAG_QUOTED) != 0;
  return valk_list_init(arg0, is_qexpr);
}

static valk_lval_t* valk_builtin_join(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  valk_lval_t* x = arg0;
  u64 count = valk_lval_list_count(a);
  for (u64 i = 1; i < count; i++) {
    x = valk_lval_join(x, valk_lval_list_nth(a, i));
  }

  return x;
}

static valk_lval_t* valk_builtin_range(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);

  long start = valk_lval_list_nth(a, 0)->num;
  long end = valk_lval_list_nth(a, 1)->num;

  if (start >= end) {
    return valk_lval_nil();
  }

  valk_lval_t* result = valk_lval_nil();
  for (long i = end - 1; i >= start; i--) {
    result = valk_lval_cons(valk_lval_num(i), result);
  }

  return result;
}

static valk_lval_t* valk_builtin_repeat(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);

  valk_lval_t* func = valk_lval_list_nth(a, 0);
  long count = valk_lval_list_nth(a, 1)->num;

  valk_lval_t* res[count];
  valk_lval_t* nil = valk_lval_nil();

  for (long i = 0; i < count; i++) {
    valk_lval_t* args = valk_lval_cons(valk_lval_num(i), nil);
    res[i] = valk_lval_eval_call(e, func, args);
  }

  return valk_lval_list(res, count);
}

valk_lval_t* valk_builtin_list(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (LVAL_TYPE(a) == LVAL_NIL) {
    return a;
  }
  if (LVAL_TYPE(a) == LVAL_CONS && (a->flags & LVAL_FLAG_QUOTED)) {
    return a;
  }
  u64 count = valk_lval_list_count(a);
  valk_lval_t* items[count];
  valk_lval_t* curr = a;
  for (u64 i = 0; i < count; i++) {
    items[i] = curr->cons.head;
    curr = curr->cons.tail;
  }
  return valk_lval_qlist(items, count);
}

static valk_lval_t* valk_builtin_eval(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(arg0) == LVAL_CONS && (arg0->flags & LVAL_FLAG_QUOTED)) {
    arg0 = valk_qexpr_to_cons(arg0);
  }

  return valk_lval_eval(e, arg0);
}

void valk_register_list_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "list", valk_builtin_list);
  valk_lenv_put_builtin(env, "cons", valk_builtin_cons);
  valk_lenv_put_builtin(env, "len", valk_builtin_len);
  valk_lenv_put_builtin(env, "init", valk_builtin_init);
  valk_lenv_put_builtin(env, "head", valk_builtin_head);
  valk_lenv_put_builtin(env, "tail", valk_builtin_tail);
  valk_lenv_put_builtin(env, "join", valk_builtin_join);
  valk_lenv_put_builtin(env, "range", valk_builtin_range);
  valk_lenv_put_builtin(env, "repeat", valk_builtin_repeat);
  valk_lenv_put_builtin(env, "eval", valk_builtin_eval);
}
