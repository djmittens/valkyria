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

// LCOV_EXCL_BR_START - recursive list init: empty guard validated at API boundary
static valk_lval_t* valk_list_init(valk_lval_t* list, bool is_qexpr) {
  if (valk_lval_list_is_empty(list)) {
    return valk_lval_nil();
  }
  // LCOV_EXCL_BR_STOP

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

// LCOV_EXCL_BR_START - evaluator passes args as unquoted cons
valk_lval_t* valk_builtin_list(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (LVAL_TYPE(a) == LVAL_NIL) {
    return a;
  }
  if (LVAL_TYPE(a) == LVAL_CONS && (a->flags & LVAL_FLAG_QUOTED)) {
    return a;
  }
  // LCOV_EXCL_BR_STOP
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

// LCOV_EXCL_BR_START - internal list traversal null guards
static valk_lval_t* valk_builtin_reverse(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* list = valk_lval_list_nth(a, 0);

  if (!list || LVAL_TYPE(list) == LVAL_NIL)
    return valk_lval_nil();

  LVAL_ASSERT_TYPE(a, list, LVAL_CONS, LVAL_NIL);

  bool is_qexpr = (list->flags & LVAL_FLAG_QUOTED) != 0;
  valk_lval_t* result = valk_lval_nil();
  valk_lval_t* curr = list;
  while (curr && LVAL_TYPE(curr) == LVAL_CONS) {
    if (is_qexpr)
      result = valk_lval_qcons(curr->cons.head, result);
    else
      result = valk_lval_cons(curr->cons.head, result);
    curr = curr->cons.tail;
  }
  return result;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - internal list traversal null guards
static valk_lval_t* valk_builtin_list_group(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  long n = valk_lval_list_nth(a, 0)->num;
  valk_lval_t* list = valk_lval_list_nth(a, 1);
  if (n <= 0) return valk_lval_nil();
  if (LVAL_TYPE(list) == LVAL_NIL) return list;

  valk_lval_t* rev = valk_lval_nil();
  valk_lval_t* curr = list;
  while (curr && LVAL_TYPE(curr) == LVAL_CONS) {
    valk_lval_t* items[n];
    long count = 0;
    for (long i = 0; i < n && curr && LVAL_TYPE(curr) == LVAL_CONS; i++) {
      items[i] = curr->cons.head;
      curr = curr->cons.tail;
      count++;
    }
    if (count == n)
      rev = valk_lval_qcons(valk_lval_qlist(items, count), rev);
  }
  valk_lval_t* result = valk_lval_nil();
  curr = rev;
  while (curr && LVAL_TYPE(curr) == LVAL_CONS) {
    result = valk_lval_qcons(curr->cons.head, result);
    curr = curr->cons.tail;
  }
  // LCOV_EXCL_BR_STOP
  return result;
}

// LCOV_EXCL_BR_START - internal plist traversal null guards
static valk_lval_t* valk_builtin_plist_get(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* plist = valk_lval_list_nth(a, 0);
  valk_lval_t* key = valk_lval_list_nth(a, 1);

  if (!plist || LVAL_TYPE(plist) == LVAL_NIL)
    return valk_lval_nil();

  const char* key_str = NULL;
  if (LVAL_TYPE(key) == LVAL_SYM)
    key_str = key->str;
  else if (LVAL_TYPE(key) == LVAL_STR)
    key_str = key->str;
  else
    return valk_lval_nil();

  valk_lval_t* curr = plist;
  while (curr && LVAL_TYPE(curr) == LVAL_CONS) {
    valk_lval_t* k = curr->cons.head;
    valk_lval_t* rest = curr->cons.tail;
    if (!rest || LVAL_TYPE(rest) != LVAL_CONS) break;
    if ((LVAL_TYPE(k) == LVAL_SYM || LVAL_TYPE(k) == LVAL_STR) &&
        strcmp(k->str, key_str) == 0)
      return rest->cons.head;
    curr = rest->cons.tail;
  }
  return valk_lval_nil();
  // LCOV_EXCL_BR_STOP
}

static valk_lval_t* valk_builtin_nth(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  long n = valk_lval_list_nth(a, 0)->num;
  valk_lval_t* list = valk_lval_list_nth(a, 1);
  if (n <= 0)
    LVAL_RAISE(a, "Invalid array index (should start with 1)");
  valk_lval_t* curr = list;
  // LCOV_EXCL_BR_START - LVAL_QEXPR == LVAL_CONS, redundant check
  for (long i = 1; i < n; i++) {
    if (!curr || (LVAL_TYPE(curr) != LVAL_CONS && LVAL_TYPE(curr) != LVAL_QEXPR))
      LVAL_RAISE(a, "nth: index %ld out of bounds", n);
    curr = curr->cons.tail;
  }
  if (!curr || (LVAL_TYPE(curr) != LVAL_CONS && LVAL_TYPE(curr) != LVAL_QEXPR))
    LVAL_RAISE(a, "nth: index %ld out of bounds", n);
  // LCOV_EXCL_BR_STOP
  return curr->cons.head;
}

#define AST_WRAPPED_BIT (1ULL << 20)

static valk_lval_t* valk_builtin_ast_node_type(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  switch (LVAL_TYPE(v)) {
    case LVAL_SYM: return valk_lval_str("sym");
    case LVAL_NUM: return valk_lval_str("num");
    case LVAL_STR: return valk_lval_str("str");
    case LVAL_CONS:
      if (v->flags & AST_WRAPPED_BIT) return valk_lval_str("sexpr");
      return (v->flags & LVAL_FLAG_QUOTED) ? valk_lval_str("qexpr") : valk_lval_str("sexpr");
    case LVAL_NIL: return valk_lval_str("nil");
    case LVAL_FUN: return valk_lval_str("fun");
    case LVAL_ERR: return valk_lval_str("err");
    default: return valk_lval_str("unknown");
  }
}

static valk_lval_t* valk_builtin_ast_node_name(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(v) == LVAL_SYM) return valk_lval_str(v->str);
  if (LVAL_TYPE(v) == LVAL_STR) return v;
  if (LVAL_TYPE(v) == LVAL_NUM) {
    char buf[32]; snprintf(buf, sizeof(buf), "%ld", (long)v->num);
    return valk_lval_str(buf);
  }
  return valk_lval_nil();
}

// Convert a raw AST lval into a safe data representation.
// Symbols become strings (no evaluation). Lists become quoted.
// Returns a plist: {:type "sym" :name "def" :pos 0}
//                  {:type "num" :val 42 :pos 5}
//                  {:type "sexpr" :children (...) :pos 0}
static valk_lval_t* ast_to_data(valk_lval_t* v);
static valk_lval_t* ast_children_to_data(valk_lval_t* list);

static valk_lval_t* ast_children_to_data(valk_lval_t* list) {
  if (!list || LVAL_TYPE(list) == LVAL_NIL) return valk_lval_nil();
  if (LVAL_TYPE(list) != LVAL_CONS) return valk_lval_cons(ast_to_data(list), valk_lval_nil());
  valk_lval_t* hd = ast_to_data(list->cons.head);
  valk_lval_t* tl = ast_children_to_data(list->cons.tail);
  return valk_lval_cons(hd, tl);
}

static valk_lval_t* ast_to_data(valk_lval_t* v) {
  if (!v || LVAL_TYPE(v) == LVAL_NIL) return valk_lval_nil();
  i64 pos = LVAL_SRC_POS(v);
  switch (LVAL_TYPE(v)) {
    case LVAL_SYM:
      return valk_lval_cons(valk_lval_sym(":type"), valk_lval_cons(valk_lval_str("sym"),
        valk_lval_cons(valk_lval_sym(":name"), valk_lval_cons(valk_lval_str(v->str),
        valk_lval_cons(valk_lval_sym(":pos"), valk_lval_cons(valk_lval_num(pos),
        valk_lval_nil()))))));
    case LVAL_NUM: {
      char buf[32]; snprintf(buf, sizeof(buf), "%ld", (long)v->num);
      return valk_lval_cons(valk_lval_sym(":type"), valk_lval_cons(valk_lval_str("num"),
        valk_lval_cons(valk_lval_sym(":name"), valk_lval_cons(valk_lval_str(buf),
        valk_lval_cons(valk_lval_sym(":pos"), valk_lval_cons(valk_lval_num(pos),
        valk_lval_nil()))))));
    }
    case LVAL_STR:
      return valk_lval_cons(valk_lval_sym(":type"), valk_lval_cons(valk_lval_str("str"),
        valk_lval_cons(valk_lval_sym(":name"), valk_lval_cons(valk_lval_str(v->str),
        valk_lval_cons(valk_lval_sym(":pos"), valk_lval_cons(valk_lval_num(pos),
        valk_lval_cons(valk_lval_sym(":len"), valk_lval_cons(valk_lval_num((i64)strlen(v->str) + 2),
        valk_lval_nil()))))))));
    case LVAL_CONS: {
      const char *kind = (v->flags & LVAL_FLAG_QUOTED) ? "qexpr" : "sexpr";
      valk_lval_t* children = ast_children_to_data(v);
      return valk_lval_cons(valk_lval_sym(":type"), valk_lval_cons(valk_lval_str(kind),
        valk_lval_cons(valk_lval_sym(":children"), valk_lval_cons(children,
        valk_lval_cons(valk_lval_sym(":pos"), valk_lval_cons(valk_lval_num(pos),
        valk_lval_nil()))))));
    }
    default: return valk_lval_nil();
  }
}

static valk_lval_t* valk_builtin_ast_to_data(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return ast_children_to_data(v);
}

static valk_lval_t* valk_builtin_ast_src_pos(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_SRC_POS(v));
}

static valk_lval_t* valk_builtin_ast_nil(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  if (v == NULL || LVAL_TYPE(v) == LVAL_NIL) return valk_lval_num(1);
  if (LVAL_TYPE(v) == LVAL_CONS) return valk_lval_num(valk_lval_list_count(v) == 0 ? 1 : 0);
  return valk_lval_num(0);
}

static valk_lval_t* valk_builtin_ast_len(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num((long)valk_lval_list_count(v));
}



static valk_lval_t* valk_builtin_member(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* needle = valk_lval_list_nth(a, 0);
  valk_lval_t* list = valk_lval_list_nth(a, 1);
  while (list && LVAL_TYPE(list) == LVAL_CONS) {
    if (valk_lval_eq(needle, list->cons.head))
      return valk_lval_num(1);
    list = list->cons.tail;
  }
  // LCOV_EXCL_START - LVAL_QEXPR == LVAL_CONS, first loop handles both
  if (LVAL_TYPE(list) == LVAL_QEXPR) {
    valk_lval_t* curr = list;
    while (curr && LVAL_TYPE(curr) == LVAL_CONS) {
      if (valk_lval_eq(needle, curr->cons.head))
        return valk_lval_num(1);
      curr = curr->cons.tail;
    }
  }
  // LCOV_EXCL_STOP
  return valk_lval_num(0);
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
  valk_lenv_put_builtin(env, "nth", valk_builtin_nth);
  valk_lenv_put_builtin(env, "ast/to-data", valk_builtin_ast_to_data);
  valk_lenv_put_builtin(env, "ast/node-type", valk_builtin_ast_node_type);
  valk_lenv_put_builtin(env, "ast/node-name", valk_builtin_ast_node_name);
  valk_lenv_put_builtin(env, "ast/src-pos", valk_builtin_ast_src_pos);
  valk_lenv_put_builtin(env, "ast/nil?", valk_builtin_ast_nil);
  valk_lenv_put_builtin(env, "ast/len", valk_builtin_ast_len);
  valk_lenv_put_builtin(env, "member?", valk_builtin_member);
  valk_lenv_put_builtin(env, "reverse", valk_builtin_reverse);
  valk_lenv_put_builtin(env, "list/group", valk_builtin_list_group);
  valk_lenv_put_builtin(env, "plist/get", valk_builtin_plist_get);
}
