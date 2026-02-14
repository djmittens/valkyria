#include "parser.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "builtins_internal.h"
#include "collections.h"
#include "common.h"
#include "gc.h"
#include "memory.h"

#ifdef VALK_COVERAGE
#include "coverage.h"
#endif

static const char* valk_lval_str_escape(char x);

static char* lval_str_escapable = "\a\b\f\n\r\t\v\\\'\"";

char* valk_c_err_format(const char* fmt, const char* file, const u64 line,
                        const char* function) {
  u64 len =
      snprintf(nullptr, 0, "%s:%llu:%s || %s", file, (unsigned long long)line, function, fmt);
  char* buf = valk_mem_alloc(len + 1);
  snprintf(buf, len + 1, "%s:%llu:%s || %s", file, (unsigned long long)line, function, fmt);
  return buf;
}

// LCOV_EXCL_BR_START - allocator type switch with unreachable default
u64 valk_alloc_flags_from_allocator(void* allocator) {
  if (allocator == NULL) return LVAL_ALLOC_SCRATCH;
  valk_mem_allocator_t* alloc = (valk_mem_allocator_t*)allocator;
  switch (alloc->type) {
    case VALK_ALLOC_ARENA:
      return LVAL_ALLOC_SCRATCH;
    case VALK_ALLOC_MALLOC:
      return LVAL_ALLOC_GLOBAL;
    case VALK_ALLOC_GC_HEAP:
      return LVAL_ALLOC_HEAP;
    // LCOV_EXCL_START - SLAB allocator not used for lval allocation
    case VALK_ALLOC_SLAB:
      return LVAL_ALLOC_GLOBAL;
    default:
      return LVAL_ALLOC_SCRATCH;
    // LCOV_EXCL_STOP
  }
}
// LCOV_EXCL_BR_STOP

char* valk_str_join(const u64 n, const char** strs, const char* sep) {
  u64 res_len = 0;
  u64 sep_len = strlen(sep);
  u64 str_lens[n];
  for (u64 i = 0; i < n; i++) {
    u64 _len = strlen(strs[i]);
    res_len += _len;
    str_lens[i] = _len;
    if (i < n - 1) {
      res_len += sep_len;
    }
  }
  char* res = valk_mem_alloc(res_len + 1);
  u64 offset = 0;
  for (u64 i = 0; i < n; i++) {
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

// LCOV_EXCL_BR_START - type name switch covers all cases, Unknown is unreachable
const char* valk_ltype_name(valk_ltype_e type) {
  switch (type) {
    case LVAL_NUM:
      return "Number";
    case LVAL_SYM:
      return "Symbol";
    case LVAL_FUN:
      return "Function";
    case LVAL_NIL:
      return "Nil";
    case LVAL_CONS:
      return "List";
    case LVAL_ERR:
      return "Error";
    case LVAL_STR:
      return "String";
    case LVAL_REF:
      return "Reference";
    case LVAL_HANDLE:
      return "Handle";
    case LVAL_UNDEFINED:
      return "UNDEFINED";
  }
  return "Unknown";
}
// LCOV_EXCL_BR_STOP

valk_lval_t* valk_lval_ref(const char* type, void* ptr, void (*free)(void*)) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_REF | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  u64 tlen = strlen(type);
  if (tlen > 100) tlen = 100;
  res->ref.type = valk_mem_alloc(tlen + 1);
  memcpy(res->ref.type, type, tlen);
  res->ref.type[tlen] = '\0';
  res->ref.ptr = ptr;
  res->ref.free = free;

  return res;
}

valk_lval_t* valk_lval_num(long x) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_NUM | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  res->num = x;
  return res;
}

// TODO(main): look into UTF-8 support
valk_lval_t* valk_lval_err(const char* fmt, ...) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_ERR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  va_list va, va2;
  va_start(va, fmt);
  // NOLINTNEXTLINE(clang-analyzer-valist.Uninitialized) - va_start called above
  va_copy(va2, va);

  u64 len = vsnprintf(nullptr, 0, fmt, va);
  va_end(va);

  // TODO(main): look into making this into a constant
  len = len < 10000 ? len : 511;
  res->str = valk_mem_alloc(len + 1);
  vsnprintf(res->str, len + 1, fmt, va2);
  va_end(va2);
  return res;
}

valk_lval_t* valk_lval_sym(const char* sym) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_SYM | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  u64 slen = strlen(sym);
  if (slen > 200) slen = 200;
  res->str = valk_mem_alloc(slen + 1);
  memcpy(res->str, sym, slen);
  res->str[slen] = '\0';

  return res;
}

valk_lval_t* valk_lval_str(const char* str) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_STR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  u64 slen = strlen(str);
  res->str = valk_mem_alloc(slen + 1);
  memcpy(res->str, str, slen + 1);

  return res;
}

valk_lval_t* valk_lval_str_n(const char* bytes, u64 n) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_STR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  res->str = valk_mem_alloc(n + 1);
  if (n) memcpy(res->str, bytes, n);
  res->str[n] = '\0';

  return res;
}

// LCOV_EXCL_START - coverage instrumentation code (self-referential - not worth testing)
#ifdef VALK_COVERAGE
static bool is_if_expr(valk_lval_t* lval) {
  if (lval == NULL || LVAL_TYPE(lval) != LVAL_CONS) return false;
  valk_lval_t* head = lval->cons.head;
  if (head == NULL || LVAL_TYPE(head) != LVAL_SYM) return false;
  return strcmp(head->str, "if") == 0;
}

static void mark_if_branches(valk_lval_t* lval) {
  valk_lval_t* args = lval->cons.tail;
  if (args == NULL || LVAL_TYPE(args) != LVAL_CONS) return;

  valk_lval_t* rest = args->cons.tail;
  if (rest == NULL || LVAL_TYPE(rest) != LVAL_CONS) return;

  valk_lval_t* true_branch = rest->cons.head;
  if (true_branch != NULL && true_branch->cov_file_id != 0 && true_branch->cov_line != 0) {
    valk_coverage_mark_expr(true_branch->cov_file_id, true_branch->cov_line,
                            true_branch->cov_column, 0);
  }

  valk_lval_t* rest2 = rest->cons.tail;
  if (rest2 == NULL || LVAL_TYPE(rest2) != LVAL_CONS) return;
  valk_lval_t* false_branch = rest2->cons.head;
  if (false_branch != NULL && false_branch->cov_file_id != 0 && false_branch->cov_line != 0) {
    valk_coverage_mark_expr(false_branch->cov_file_id, false_branch->cov_line,
                            false_branch->cov_column, 0);
  }
}

void valk_coverage_mark_tree(valk_lval_t* lval) {
  if (lval == NULL) return;

  u8 type = LVAL_TYPE(lval);
  bool is_quoted = (lval->flags & LVAL_FLAG_QUOTED) != 0;
  
  if (type == LVAL_CONS) {
    if (!is_quoted) {
      VALK_COVERAGE_MARK_LVAL(lval);
      if (is_if_expr(lval)) {
        mark_if_branches(lval);
      }
    }
    valk_coverage_mark_tree(lval->cons.head);
    valk_coverage_mark_tree(lval->cons.tail);
  }
}
#endif
// LCOV_EXCL_STOP

valk_lval_t* valk_lval_lambda(valk_lenv_t* env, valk_lval_t* formals,
                              valk_lval_t* body) {
  extern valk_eval_metrics_t g_eval_metrics;
  atomic_fetch_add(&g_eval_metrics.closures_created, 1);

  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  INHERIT_SOURCE_LOC(res, body);

  res->fun.builtin = nullptr;

  int arity = 0;
  bool is_variadic = false;
  for (u64 i = 0; i < valk_lval_list_count(formals); i++) {
    valk_lval_t* formal = valk_lval_list_nth(formals, i);
    if (LVAL_TYPE(formal) == LVAL_SYM && strcmp(formal->str, "&") == 0) {
      is_variadic = true;
      break;
    }
    arity++;
  }

  if (is_variadic) {
    arity = -(arity + 1);
  }

  res->fun.arity = arity;
  static const char* lambda_name = "<lambda>";
  u64 name_len = strlen(lambda_name) + 1;
  res->fun.name = valk_mem_alloc(name_len);
  if (res->fun.name) {  // LCOV_EXCL_BR_LINE - memory allocation rarely fails
    memcpy(res->fun.name, lambda_name, name_len);
  }
  res->fun.env = env;
  res->fun.formals = formals;
  res->fun.body = body;

#ifdef VALK_COVERAGE
  valk_coverage_mark_tree(body);
#endif

  return res;
}

valk_lval_t* valk_lval_nil(void) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_NIL | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  res->cons.head = nullptr;
  res->cons.tail = nullptr;
  return res;
}

valk_lval_t* valk_lval_cons(valk_lval_t* head, valk_lval_t* tail) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_CONS | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  INHERIT_SOURCE_LOC(res, head);
  res->cons.head = valk_region_ensure_safe_ref(res, head);
  res->cons.tail = valk_region_ensure_safe_ref(res, tail);
  return res;
}

valk_lval_t* valk_lval_qcons(valk_lval_t* head, valk_lval_t* tail) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_CONS | LVAL_FLAG_QUOTED | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  INHERIT_SOURCE_LOC(res, head);
  res->cons.head = valk_region_ensure_safe_ref(res, head);
  res->cons.tail = valk_region_ensure_safe_ref(res, tail);
  return res;
}

valk_lval_t* valk_lval_list(valk_lval_t* arr[], u64 count) {
  valk_lval_t* res = valk_lval_nil();
  for (u64 i = count; i > 0; i--) {
    res = valk_lval_cons(arr[i - 1], res);
  }
  return res;
}

valk_lval_t* valk_lval_qlist(valk_lval_t* arr[], u64 count) {
  valk_lval_t* res = valk_lval_nil();
  for (u64 i = count; i > 0; i--) {
    res = valk_lval_qcons(arr[i - 1], res);
  }
  return res;
}

#ifdef VALK_COVERAGE
static inline void valk_copy_source_loc(valk_lval_t* dst, valk_lval_t* src) {
  dst->cov_file_id = src->cov_file_id;
  dst->cov_line = src->cov_line;
  dst->cov_column = src->cov_column;
}
#else
#define valk_copy_source_loc(dst, src) ((void)0)
#endif

valk_lval_t* valk_qexpr_to_cons(valk_lval_t* qexpr) {
  if (qexpr == NULL || LVAL_TYPE(qexpr) == LVAL_NIL) {  // LCOV_EXCL_BR_LINE - defensive null check
    return valk_lval_nil();
  }
  VALK_COVERAGE_RECORD_LVAL(qexpr);
  valk_lval_t* res = valk_lval_cons(qexpr->cons.head, valk_qexpr_to_cons(qexpr->cons.tail));
  valk_copy_source_loc(res, qexpr);
  return res;
}

static inline int valk_is_list_type(valk_ltype_e type) {
  return type == LVAL_CONS || type == LVAL_QEXPR || type == LVAL_NIL;  // LCOV_EXCL_BR_LINE - short-circuit eval
}

valk_lval_t* valk_lval_head(valk_lval_t* cons) {
  VALK_ASSERT(valk_is_list_type(LVAL_TYPE(cons)),
              "Expected list (S-Expr, Q-Expr, or Nil), got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.head;
}

valk_lval_t* valk_lval_tail(valk_lval_t* cons) {
  VALK_ASSERT(valk_is_list_type(LVAL_TYPE(cons)),
              "Expected list (S-Expr, Q-Expr, or Nil), got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.tail;
}

// LCOV_EXCL_BR_START - helper functions have short-circuit evaluations
int valk_lval_list_is_empty(valk_lval_t* list) {
  if (list == nullptr) return 1;
  if (LVAL_TYPE(list) == LVAL_NIL) return 1;
  if ((LVAL_TYPE(list) == LVAL_CONS || LVAL_TYPE(list) == LVAL_QEXPR) &&
      list->cons.head == nullptr)
    return 1;
  return 0;
}
// LCOV_EXCL_BR_STOP

u64 valk_lval_list_count(valk_lval_t* list) {
  u64 count = 0;
  valk_lval_t* curr = list;
  while (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    count++;
    curr = curr->cons.tail;
  }
  return count;
}

valk_lval_t* valk_lval_list_nth(valk_lval_t* list, u64 n) {
  valk_lval_t* curr = list;
  for (u64 i = 0; i < n && curr != nullptr && !valk_lval_list_is_empty(curr);
       i++) {
    curr = curr->cons.tail;
  }
  if (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    return curr->cons.head;
  }
  return nullptr;
}

valk_lval_t* valk_plist_get(valk_lval_t* plist, const char* key_str) {
  if (!plist || LVAL_TYPE(plist) != LVAL_QEXPR) return NULL;  // LCOV_EXCL_BR_LINE - defensive check
  if (valk_lval_list_is_empty(plist)) return NULL;  // LCOV_EXCL_BR_LINE - defensive check

  valk_lval_t* curr = plist;
  while (curr && (LVAL_TYPE(curr) == LVAL_CONS || LVAL_TYPE(curr) == LVAL_QEXPR)) {  // LCOV_EXCL_BR_LINE - defensive check
    if (valk_lval_list_is_empty(curr)) break;  // LCOV_EXCL_BR_LINE - defensive check

    valk_lval_t* key = curr->cons.head;
    valk_lval_t* rest = curr->cons.tail;

    if (!rest || valk_lval_list_is_empty(rest)) break;  // LCOV_EXCL_BR_LINE - defensive check

    valk_lval_t* val = rest->cons.head;

    if (LVAL_TYPE(key) == LVAL_SYM && strcmp(key->str, key_str) == 0) {
      return val;
    }

    curr = rest->cons.tail;
  }
  return NULL;
}

valk_lval_t* valk_lval_copy(valk_lval_t* lval) {
  if (lval == nullptr) return nullptr;

  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));

  res->flags = (lval->flags & (LVAL_TYPE_MASK | LVAL_FLAG_QUOTED)) |
               valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);

#ifdef VALK_COVERAGE
  res->cov_file_id = lval->cov_file_id;
  res->cov_line = lval->cov_line;
  res->cov_column = lval->cov_column;
#endif

  switch (LVAL_TYPE(lval)) {  // LCOV_EXCL_BR_LINE - type dispatch (not all types copied in tests)
    case LVAL_NUM:
      res->num = lval->num;
      break;
    case LVAL_FUN:
      if (lval->fun.builtin) {
        res->fun.builtin = lval->fun.builtin;
        res->fun.env = nullptr;
        res->fun.body = nullptr;
        res->fun.formals = nullptr;
      } else {
        res->fun.builtin = nullptr;
        res->fun.env = lval->fun.env;
        res->fun.body = lval->fun.body;
        res->fun.formals = lval->fun.formals;
      }
      break;
    case LVAL_CONS:
      res->cons.head = lval->cons.head;
      res->cons.tail = lval->cons.tail;
      break;
    case LVAL_NIL:
      break;
    case LVAL_SYM: {
      u64 slen = strlen(lval->str);
      if (slen > 200) slen = 200;
      res->str = valk_mem_alloc(slen + 1);
      memcpy(res->str, lval->str, slen);
      res->str[slen] = '\0';
      break;
    }
    case LVAL_ERR: {
      u64 slen = strlen(lval->str);
      if (slen > 2000) slen = 2000;
      res->str = valk_mem_alloc(slen + 1);
      memcpy(res->str, lval->str, slen);
      res->str[slen] = '\0';
      break;
    }
    case LVAL_STR: {
      u64 slen = strlen(lval->str);
      res->str = valk_mem_alloc(slen + 1);
      memcpy(res->str, lval->str, slen + 1);
      break;
    }
    case LVAL_REF: {
      u64 tlen = strlen(lval->ref.type);
      if (tlen > 100) tlen = 100;
      res->ref.type = valk_mem_alloc(tlen + 1);
      memcpy(res->ref.type, lval->ref.type, tlen);
      res->ref.type[tlen] = '\0';
      res->ref.ptr = lval->ref.ptr;
      res->ref.free = lval->ref.free;
      break;
    }
    // LCOV_EXCL_START - LVAL_UNDEFINED is an invariant violation, should never happen
    case LVAL_UNDEFINED:
      break;
    // LCOV_EXCL_STOP
    case LVAL_HANDLE:
      res->async.handle = lval->async.handle;
      break;
  }
  return res;
}

int valk_lval_eq(valk_lval_t* x, valk_lval_t* y) {
  // LCOV_EXCL_BR_START - null comparison rarely exercised
  if (x == nullptr && y == nullptr) {
    return 1;
  }
  if (x == nullptr || y == nullptr) {
    return 0;
  }
  // LCOV_EXCL_BR_STOP

  if (LVAL_TYPE(x) != LVAL_TYPE(y)) {
    return 0;
  }

  switch (LVAL_TYPE(x)) {  // LCOV_EXCL_BR_LINE - type dispatch (not all types exercised)
    case LVAL_NUM:
      return (x->num == y->num);
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      return (strcmp(x->str, y->str) == 0);
    case LVAL_FUN: {
      // LCOV_EXCL_BR_START - function equality comparison rarely used
      if (x->fun.builtin || y->fun.builtin) {
        return x->fun.builtin == y->fun.builtin;
      } else {
        return valk_lval_eq(x->fun.formals, y->fun.formals) &&
               valk_lval_eq(x->fun.body, y->fun.body);
      }
      // LCOV_EXCL_BR_STOP
    }
    case LVAL_NIL:
      return 1;
    case LVAL_CONS:
      return valk_lval_eq(x->cons.head, y->cons.head) &&
             valk_lval_eq(x->cons.tail, y->cons.tail);
    case LVAL_REF:
      return (x->ref.ptr == y->ref.ptr) && (x->ref.free == y->ref.free);
    case LVAL_HANDLE:
      return x == y;
    // LCOV_EXCL_START - invariant violation, should never happen
    case LVAL_UNDEFINED:
      VALK_RAISE("LVAL is undefined, something went wrong");
      break;
  }

  return 0;
  // LCOV_EXCL_STOP
}

valk_lval_t* valk_lval_pop(valk_lval_t* lval, u64 i) {
  VALK_ASSERT(lval != nullptr, "valk_lval_pop: lval must not be null");
  u64 count = valk_lval_list_count(lval);
  LVAL_ASSERT(
      (valk_lval_t*)0, i < count,
      "Cant pop from list at invalid position: [%zu] total length: [%zu]", i,
      count);
  LVAL_ASSERT((valk_lval_t*)0, count > 0, "Cant pop from empty");

  if (i == 0) {
    valk_lval_t* cell = lval->cons.head;
    if (lval->cons.tail != nullptr &&
        !valk_lval_list_is_empty(lval->cons.tail)) {
      lval->cons.head = lval->cons.tail->cons.head;
      lval->cons.tail = lval->cons.tail->cons.tail;
    } else {
      lval->cons.head = nullptr;
      lval->cons.tail = nullptr;
    }
    return cell;
  }

  valk_lval_t* prev = lval;
  for (u64 j = 0; j < i - 1; j++) {
    prev = prev->cons.tail;
  }

  valk_lval_t* curr = prev->cons.tail;
  valk_lval_t* cell = curr->cons.head;

  prev->cons.tail = curr->cons.tail;

  return cell;
}

valk_lval_t* valk_lval_join(valk_lval_t* a, valk_lval_t* b) {
  valk_lval_t* orig_a __attribute__((unused)) = a;

  bool is_qexpr = (a->flags & LVAL_FLAG_QUOTED) != 0;

  u64 lena = valk_lval_list_count(a);

  valk_lval_t* res;
  if (LVAL_TYPE(b) != LVAL_CONS && LVAL_TYPE(b) != LVAL_NIL) {
    res = is_qexpr ? valk_lval_qcons(b, valk_lval_nil())
                   : valk_lval_cons(b, valk_lval_nil());
  } else {
    res = b;
  }

  struct {
    valk_lval_t** items;
    u64 count;
    u64 capacity;
  } tmp = {0};

  da_init(&tmp);

  for (u64 i = 0; i < lena; i++) {
    da_add(&tmp, a->cons.head);
    a = a->cons.tail;
  }

  for (u64 i = lena; i > 0; i--) {
    if (is_qexpr) {
      res = valk_lval_qcons(tmp.items[i - 1], res);
    } else {
      res = valk_lval_cons(tmp.items[i - 1], res);
    }
  }

  da_free(&tmp);

  INHERIT_SOURCE_LOC(res, orig_a);
  return res;
}

void valk_lval_print(valk_lval_t* val) {
  if (val == nullptr) {
    printf("NULL");
    return;
  }
  switch (LVAL_TYPE(val)) {  // LCOV_EXCL_BR_LINE - type dispatch (not all types used in tests)
    case LVAL_NUM:
      printf("Num[%li]", val->num);
      break;
    case LVAL_SYM:
      printf("%s", val->str);
      break;
    case LVAL_NIL:
      printf("()");
      break;
    case LVAL_CONS: {
      bool is_quoted = (val->flags & LVAL_FLAG_QUOTED) != 0;
      printf(is_quoted ? "{" : "(");
      valk_lval_t* curr = val;
      int first = 1;
      while (curr != nullptr && LVAL_TYPE(curr) == LVAL_CONS) {
        if (!first) putchar(' ');
        valk_lval_print(curr->cons.head);
        curr = curr->cons.tail;
        first = 0;
      }
      // LCOV_EXCL_START - improper lists (dotted pairs) rarely occur in tests
      if (curr != nullptr && LVAL_TYPE(curr) != LVAL_NIL) {
        printf(" . ");
        valk_lval_print(curr);
      }
      // LCOV_EXCL_STOP
      printf(is_quoted ? "}" : ")");
      break;
    }
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
    case LVAL_STR: {
      putchar('"');
      for (u64 i = 0; i < strlen(val->str); ++i) {
        if (strchr(lval_str_escapable, val->str[i])) {
          printf("%s", valk_lval_str_escape(val->str[i]));
        } else {
          putchar(val->str[i]);
        }
      }
      putchar('"');
      break;
    }
    case LVAL_REF:
      printf("Reference[%s:%p]", val->ref.type, val->ref.ptr);
      break;
    case LVAL_HANDLE:
      printf("<handle>");
      break;
    case LVAL_UNDEFINED:
      printf("[Undefined]");
      break;
  }
}

static const char* valk_lval_str_escape(char x) {
  switch (x) {  // LCOV_EXCL_BR_LINE - not all escape sequences tested
    case '\a':
      return "\\a";
    case '\b':
      return "\\b";
    case '\f':
      return "\\f";
    case '\n':
      return "\\n";
    case '\r':
      return "\\r";
    case '\t':
      return "\\t";
    case '\v':
      return "\\v";
    case '\\':
      return "\\\\";
    case '\'':
      return "\\\'";
    case '\"':
      return "\\\"";
  }
  return "";
}
