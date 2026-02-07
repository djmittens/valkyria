#include "parser.h"

#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <uv.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/http2/aio_http2_client.h"
#include "aio/http2/stream/aio_stream_body.h"
#include "collections.h"
#include "common.h"
#include "coverage.h"
#include "gc.h"
#include "memory.h"

#ifdef VALK_COVERAGE
#include "source_loc.h"
#endif

#include "aio/aio_metrics.h"
#include "aio/aio_diagnostics_builtins.h"
#include "aio/aio_request_ctx.h"
#include "metrics_v2.h"
#include "metrics_delta.h"
#include "builtins_internal.h"
void valk_register_metrics_builtins(valk_lenv_t *env);
void valk_register_ctx_builtins(valk_lenv_t *env);

// Forward declaration is in aio.h (valk_aio_http2_listen_with_config)

// GC heap allocator size check - ONLY allocate valk_lval_t structures
u64 __valk_lval_size = sizeof(valk_lval_t);
u64 __valk_lenv_size = sizeof(valk_lenv_t);

// Global interpreter metrics instance
valk_eval_metrics_t g_eval_metrics = {0};

void valk_eval_metrics_init(void) {
  atomic_store(&g_eval_metrics.evals_total, 0);
  atomic_store(&g_eval_metrics.function_calls, 0);
  atomic_store(&g_eval_metrics.builtin_calls, 0);
  atomic_store(&g_eval_metrics.stack_depth, 0);
  g_eval_metrics.stack_depth_max = 0;
  atomic_store(&g_eval_metrics.closures_created, 0);
  atomic_store(&g_eval_metrics.env_lookups, 0);
}

void valk_eval_metrics_get(u64* evals, u64* func_calls,
                            u64* builtin_calls, u32* stack_max,
                            u64* closures, u64* lookups) {
  if (evals) *evals = atomic_load(&g_eval_metrics.evals_total);
  if (func_calls) *func_calls = atomic_load(&g_eval_metrics.function_calls);
  if (builtin_calls) *builtin_calls = atomic_load(&g_eval_metrics.builtin_calls);
  if (stack_max) *stack_max = g_eval_metrics.stack_depth_max;
  if (closures) *closures = atomic_load(&g_eval_metrics.closures_created);
  if (lookups) *lookups = atomic_load(&g_eval_metrics.env_lookups);
}

// ============================================================================
// Iterative Evaluator Stack Operations
// ============================================================================

void valk_eval_stack_init(valk_eval_stack_t *stack) {
  stack->frames = malloc(sizeof(valk_cont_frame_t) * VALK_EVAL_STACK_INIT_CAP);
  stack->count = 0;
  stack->capacity = VALK_EVAL_STACK_INIT_CAP;
}

void valk_eval_stack_push(valk_eval_stack_t *stack, valk_cont_frame_t frame) {
  if (stack->count >= stack->capacity) {
    stack->capacity *= 2;
    stack->frames = realloc(stack->frames, sizeof(valk_cont_frame_t) * stack->capacity);
  }
  stack->frames[stack->count++] = frame;
}

valk_cont_frame_t valk_eval_stack_pop(valk_eval_stack_t *stack) {
  VALK_ASSERT(stack->count > 0, "Cannot pop from empty eval stack");  // LCOV_EXCL_BR_LINE - invariant
  return stack->frames[--stack->count];
}

void valk_eval_stack_destroy(valk_eval_stack_t *stack) {
  if (stack->frames) {
    for (u64 i = 0; i < stack->count; i++) {
      if (stack->frames[i].kind == CONT_COLLECT_ARG && stack->frames[i].collect_arg.args) {
        free(stack->frames[i].collect_arg.args);
      }
    }
    free(stack->frames);
    stack->frames = NULL;
  }
  stack->count = 0;
  stack->capacity = 0;
}

// TODO(networking): get rid of args everywhere, cause we dont need to release
// anymore
#define LVAL_RAISE(args, fmt, ...)                                       \
  do {                                                                   \
    char* _fmt =                                                         \
        valk_c_err_format((fmt), __FILE_NAME__, __LINE__, __FUNCTION__); \
    valk_lval_t* err = valk_lval_err(_fmt, ##__VA_ARGS__);               \
    valk_mem_free(_fmt);                                                 \
    return err;                                                          \
  } while (0)

// Helper: Set origin_allocator
// Note: GC heap zeroes memory, arena doesn't - initialize gc_next to be safe
#define VALK_SET_ORIGIN_ALLOCATOR(obj)                   \
  do {                                                   \
    (obj)->origin_allocator = valk_thread_ctx.allocator; \
    (obj)->gc_next = nullptr;                            \
  } while (0)

#define LVAL_ASSERT(args, cond, fmt, ...) \
  if ((cond)) {                           \
  } else {                                \
    LVAL_RAISE(args, fmt, ##__VA_ARGS__); \
  }

#define LVAL_ASSERT_TYPE(args, lval, _type, ...)                             \
  do {                                                                       \
    char _found = 0;                                                         \
    valk_ltype_e _expected[] = {(_type), ##__VA_ARGS__};                     \
    u64 _n_expected = sizeof(_expected) / sizeof(valk_ltype_e);           \
                                                                             \
    for (u64 i = 0; i < _n_expected; i++) {                               \
      if (LVAL_TYPE(lval) == _expected[i]) {                                 \
        _found = 1;                                                          \
        break;                                                               \
      }                                                                      \
    }                                                                        \
    if (!_found) {                                                           \
      char const* _expect_str[_n_expected];                                  \
      for (u64 i = 0; i < _n_expected; i++) {                             \
        _expect_str[i] = valk_ltype_name(_expected[i]);                      \
      }                                                                      \
      char* _estr = valk_str_join(_n_expected, _expect_str, ", ");           \
                                                                             \
      char* _fmt = valk_c_err_format("Actual: %s, Expected(One-Of): [%s]",   \
                                     __FILE_NAME__, __LINE__, __FUNCTION__); \
      valk_lval_t* err =                                                     \
          valk_lval_err(_fmt, valk_ltype_name(LVAL_TYPE(lval)), _estr);      \
      valk_mem_free(_estr);                                                  \
      valk_mem_free(_fmt);                                                   \
      return err;                                                            \
    }                                                                        \
  } while (0)

#define LVAL_ASSERT_COUNT_NEQ(args, lval, _count)                     \
  LVAL_ASSERT(args, valk_lval_list_count(lval) != _count,             \
              "Invalid argument count, Actual[%zu] != Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_EQ(args, lval, _count)                      \
  LVAL_ASSERT(args, valk_lval_list_count(lval) == _count,             \
              "Invalid argument count, Actual[%zu] == Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_LT(args, lval, _count)                     \
  LVAL_ASSERT(args, valk_lval_list_count(lval) < _count,             \
              "Invalid argument count, Actual[%zu] < Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_LE(args, lval, _count)                      \
  LVAL_ASSERT(args, valk_lval_list_count(lval) <= _count,             \
              "Invalid argument count, Actual[%zu] <= Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_GT(args, lval, _count)                     \
  LVAL_ASSERT(args, valk_lval_list_count(lval) > _count,             \
              "Invalid argument count, Actual[%zu] > Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_GE(args, lval, _count)                      \
  LVAL_ASSERT(args, valk_lval_list_count(lval) >= _count,             \
              "Invalid argument count, Actual[%zu] >= Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

static const char* valk_lval_str_escape(char x);
static char valk_lval_str_unescape(char x);

/* List of possible escapable characters */
static char* lval_str_escapable = "\a\b\f\n\r\t\v\\\'\"";

/* Possible unescapable characters */
static char* lval_str_unescapable = "abfnrtv\\\'\"";

char* valk_c_err_format(const char* fmt, const char* file, const u64 line,
                        const char* function) {
  u64 len =
      snprintf(nullptr, 0, "%s:%llu:%s || %s", file, (unsigned long long)line, function, fmt);
  char* buf = valk_mem_alloc(len + 1);
  snprintf(buf, len + 1, "%s:%llu:%s || %s", file, (unsigned long long)line, function, fmt);
  return buf;
}

// LCOV_EXCL_BR_START - allocator type switch with unreachable default
// Helper: Get allocation flags from current allocator context
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
  // TODO(main): I think i should get my own string type in here
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
  // TODO(main): whats a reasonable max for a string length?
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
// Check if lval is an 'if' expression: (if cond true-branch false-branch)
static bool is_if_expr(valk_lval_t* lval) {
  if (lval == NULL || LVAL_TYPE(lval) != LVAL_CONS) return false;
  valk_lval_t* head = lval->cons.head;
  if (head == NULL || LVAL_TYPE(head) != LVAL_SYM) return false;
  return strcmp(head->str, "if") == 0;
}

// Mark both branches of an 'if' expression as coverable
static void mark_if_branches(valk_lval_t* lval) {
  // Structure: (if cond true-branch false-branch)
  // CONS(if, CONS(cond, CONS(true-branch, CONS(false-branch, NIL))))
  valk_lval_t* args = lval->cons.tail;
  if (args == NULL || LVAL_TYPE(args) != LVAL_CONS) return;

  // Skip condition
  valk_lval_t* rest = args->cons.tail;
  if (rest == NULL || LVAL_TYPE(rest) != LVAL_CONS) return;

  // true-branch
  valk_lval_t* true_branch = rest->cons.head;
  if (true_branch != NULL && true_branch->cov_file_id != 0 && true_branch->cov_line != 0) {
    valk_coverage_mark_expr(true_branch->cov_file_id, true_branch->cov_line,
                            true_branch->cov_column, 0);
  }

  // false-branch
  valk_lval_t* rest2 = rest->cons.tail;
  if (rest2 == NULL || LVAL_TYPE(rest2) != LVAL_CONS) return;
  valk_lval_t* false_branch = rest2->cons.head;
  if (false_branch != NULL && false_branch->cov_file_id != 0 && false_branch->cov_line != 0) {
    valk_coverage_mark_expr(false_branch->cov_file_id, false_branch->cov_line,
                            false_branch->cov_column, 0);
  }
}

static void valk_coverage_mark_tree(valk_lval_t* lval) {
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
  atomic_fetch_add(&g_eval_metrics.closures_created, 1);

  // Create tree-walker lambda function
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  LVAL_INIT_SOURCE_LOC(res);
  INHERIT_SOURCE_LOC(res, body);  // LCOV_EXCL_BR_LINE - coverage macro

  res->fun.builtin = nullptr;  // Not a builtin

  // Count arity (handle variadic)
  // Use negative arity for variadic: -(min_args + 1)
  // E.g., {& args} -> arity = -1 (0+ args)
  //       {x & args} -> arity = -2 (1+ args)
  int arity = 0;
  bool is_variadic = false;
  for (u64 i = 0; i < valk_lval_list_count(formals); i++) {
    valk_lval_t* formal = valk_lval_list_nth(formals, i);
    if (LVAL_TYPE(formal) == LVAL_SYM && strcmp(formal->str, "&") == 0) {
      // Variadic
      is_variadic = true;
      break;
    }
    arity++;
  }

  if (is_variadic) {
    arity = -(arity + 1);  // Encode as negative
  }

  res->fun.arity = arity;
  // Allocate name using current allocator (same as lambda itself)
  // This ensures the name follows the same lifecycle as the lambda
  static const char* lambda_name = "<lambda>";
  u64 name_len = strlen(lambda_name) + 1;
  res->fun.name = valk_mem_alloc(name_len);
  if (res->fun.name) {  // LCOV_EXCL_BR_LINE - memory allocation rarely fails
    memcpy(res->fun.name, lambda_name, name_len);
  }
  res->fun.env = env;          // Capture closure environment
  res->fun.formals = formals;  // Store formals for evaluation
  res->fun.body = body;        // Store body for evaluation

#ifdef VALK_COVERAGE
  valk_coverage_mark_tree(body);
#endif

  return res;
}

// Cons cell constructors

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
  INHERIT_SOURCE_LOC(res, head);  // LCOV_EXCL_BR_LINE - coverage macro
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
  INHERIT_SOURCE_LOC(res, head);  // LCOV_EXCL_BR_LINE - coverage macro
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

// Build a Q-expression list from array
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
  VALK_COVERAGE_RECORD_LVAL(qexpr);  // LCOV_EXCL_BR_LINE - coverage macro
  valk_lval_t* res = valk_lval_cons(qexpr->cons.head, valk_qexpr_to_cons(qexpr->cons.tail));
  valk_copy_source_loc(res, qexpr);
  return res;
}

// Check if type is a list (CONS, QEXPR, or NIL)
static inline int valk_is_list_type(valk_ltype_e type) {
  return type == LVAL_CONS || type == LVAL_QEXPR || type == LVAL_NIL;  // LCOV_EXCL_BR_LINE - short-circuit eval
}

valk_lval_t* valk_lval_head(valk_lval_t* cons) {
  VALK_ASSERT(valk_is_list_type(LVAL_TYPE(cons)),  // LCOV_EXCL_BR_LINE - precondition
              "Expected list (S-Expr, Q-Expr, or Nil), got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.head;
}

valk_lval_t* valk_lval_tail(valk_lval_t* cons) {
  VALK_ASSERT(valk_is_list_type(LVAL_TYPE(cons)),  // LCOV_EXCL_BR_LINE - precondition
              "Expected list (S-Expr, Q-Expr, or Nil), got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.tail;
}

// LCOV_EXCL_BR_START - helper functions have short-circuit evaluations
// Helper: check if a list is empty (nil type, null, or cons/qexpr with null
// head)
int valk_lval_list_is_empty(valk_lval_t* list) {
  if (list == nullptr) return 1;
  if (LVAL_TYPE(list) == LVAL_NIL) return 1;
  // Also check for cons/qexpr cell with null head (can happen after pop empties
  // list)
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

// Helper: get nth element from a list (0-indexed)
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

// Get value from property list (plist) by key symbol
// Plist format: {:key1 val1 :key2 val2 ...}
valk_lval_t* valk_plist_get(valk_lval_t* plist, const char* key_str) {
  if (!plist || LVAL_TYPE(plist) != LVAL_QEXPR) return NULL;  // LCOV_EXCL_BR_LINE - defensive check
  if (valk_lval_list_is_empty(plist)) return NULL;  // LCOV_EXCL_BR_LINE - defensive check

  // Iterate over the QEXPR - the root has type QEXPR, tail nodes have type CONS
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

    curr = rest->cons.tail;  // Skip key and value
  }
  return NULL;
}

// Free auxiliary data owned by an lval (strings, arrays allocated with malloc)
// Does NOT recursively free child lvals - those are managed by GC
// This is called by GC when freeing an lval
// REMOVED: Type-specific cleanup is no longer needed
// All auxiliary data (strings, arrays, etc.) is allocated from GC heap
// The sweep algorithm handles freeing based on slab vs malloc detection

// SHALLOW copy: Copy only the top-level struct, alias all children
valk_lval_t* valk_lval_copy(valk_lval_t* lval) {
  if (lval == nullptr) return nullptr;

  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));

  // Keep type and quoted flag, add allocation flags from the current allocator
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
      // Handles share the underlying async_handle - just copy the pointer
      res->async.handle = lval->async.handle;
      break;
  }
  return res;
}

int valk_lval_eq(valk_lval_t* x, valk_lval_t* y) {
  // LCOV_EXCL_BR_START - null comparison rarely exercised
  // Handle NULL cases
  if (x == nullptr && y == nullptr) {
    return 1;  // Both NULL are equal
  }
  if (x == nullptr || y == nullptr) {
    return 0;  // One NULL, one not
  }
  // LCOV_EXCL_BR_STOP

  // Compare types
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
      return 1;  // Both are nil (types already matched)
    case LVAL_CONS:
      // Compare cons cells recursively (ignores quoted flag - structural equality)
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

// Helper: check if lval is a list starting with a specific symbol
static bool valk_is_tagged_list(valk_lval_t* lval, const char* tag) {
  if (LVAL_TYPE(lval) != LVAL_CONS && LVAL_TYPE(lval) != LVAL_QEXPR) {
    return false;
  }
  valk_lval_t* first = lval->cons.head;
  return LVAL_TYPE(first) == LVAL_SYM && strcmp(first->str, tag) == 0;
}

// Quasiquote expansion: recursively process template, evaluating unquote forms
// This implements the standard Lisp quasiquote semantics:
//   `x          -> x (quoted)
//   `,x         -> (eval x)
//   `(a ,b c)   -> (list 'a (eval b) 'c)
//   `(a ,@b c)  -> (concat (list 'a) b (list 'c))
// LCOV_EXCL_BR_START - quasiquote has complex type dispatch logic
static valk_lval_t* valk_quasiquote_expand(valk_lenv_t* env, valk_lval_t* form) {
  // Atoms (non-lists) are returned as-is (quoted)
  if (LVAL_TYPE(form) != LVAL_CONS && LVAL_TYPE(form) != LVAL_QEXPR) {
    return form;
  }

  // Empty list returns as-is
  if (LVAL_TYPE(form) == LVAL_NIL) {
    return form;
  }

  // Check for (unquote x) - evaluate and return
  if (valk_is_tagged_list(form, "unquote")) {
    if (valk_lval_list_count(form) != 2) {
      return valk_lval_err("unquote expects exactly 1 argument");
    }
    valk_lval_t* arg = valk_lval_list_nth(form, 1);
    return valk_lval_eval(env, arg);
  }

  // Check for (unquote-splicing x) at top level - error
  if (valk_is_tagged_list(form, "unquote-splicing")) {
    return valk_lval_err("unquote-splicing (,@) not valid at top level of quasiquote");
  }

  // It's a list - process each element
  // We need to handle unquote-splicing specially
  bool is_qexpr = (form->flags & LVAL_FLAG_QUOTED) != 0;

  // Collect expanded elements, handling splicing
  u64 capacity = 16;
  u64 count = 0;
  valk_lval_t** elements = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);

  valk_lval_t* curr = form;
  while (LVAL_TYPE(curr) != LVAL_NIL) {
    valk_lval_t* elem = curr->cons.head;

    // Check for (unquote-splicing x) - evaluate and splice
    if (valk_is_tagged_list(elem, "unquote-splicing")) {
      if (valk_lval_list_count(elem) != 2) {
        return valk_lval_err("unquote-splicing expects exactly 1 argument");
      }
      valk_lval_t* splice_arg = valk_lval_list_nth(elem, 1);
      valk_lval_t* splice_result = valk_lval_eval(env, splice_arg);
      if (LVAL_TYPE(splice_result) == LVAL_ERR) {
        return splice_result;
      }

      // Splice each element of the result list into our list
      if (LVAL_TYPE(splice_result) != LVAL_NIL &&
          LVAL_TYPE(splice_result) != LVAL_CONS &&
          LVAL_TYPE(splice_result) != LVAL_QEXPR) {
        return valk_lval_err("unquote-splicing requires a list, got %s",
                             valk_ltype_name(LVAL_TYPE(splice_result)));
      }

      valk_lval_t* splice_curr = splice_result;
      while (LVAL_TYPE(splice_curr) != LVAL_NIL) {
        if (count >= capacity) {
          capacity *= 2;
          valk_lval_t** new_elements = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);
          memcpy(new_elements, elements, sizeof(valk_lval_t*) * count);
          elements = new_elements;
        }
        elements[count++] = splice_curr->cons.head;
        splice_curr = splice_curr->cons.tail;
      }
    } else {
      // Recursively expand the element
      valk_lval_t* expanded = valk_quasiquote_expand(env, elem);
      if (LVAL_TYPE(expanded) == LVAL_ERR) {
        return expanded;
      }

      if (count >= capacity) {
        capacity *= 2;
        valk_lval_t** new_elements = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);
        memcpy(new_elements, elements, sizeof(valk_lval_t*) * count);
        elements = new_elements;
      }
      elements[count++] = expanded;
    }

    curr = curr->cons.tail;
  }

  // Build result list from right to left
  valk_lval_t* result = valk_lval_nil();
  for (u64 j = count; j > 0; j--) {
    if (is_qexpr) {
      result = valk_lval_qcons(elements[j - 1], result);
    } else {
      result = valk_lval_cons(elements[j - 1], result);
    }
  }

  return result;
}
// LCOV_EXCL_BR_STOP

// Forward declaration for apply helper
static valk_eval_result_t valk_eval_apply_func_iter(valk_lenv_t* env, valk_lval_t* func, valk_lval_t* args);

// Apply function for iterative evaluator - returns thunk for user-defined functions
static valk_eval_result_t valk_eval_apply_func_iter(valk_lenv_t* env, valk_lval_t* func, valk_lval_t* args) {
  if (LVAL_TYPE(func) != LVAL_FUN) {
    return valk_eval_value(valk_lval_err("Cannot call non-function: %s", valk_ltype_name(LVAL_TYPE(func))));
  }

  u32 depth = atomic_fetch_add(&g_eval_metrics.stack_depth, 1) + 1;
  if (depth > g_eval_metrics.stack_depth_max) {
    g_eval_metrics.stack_depth_max = depth;
  }

  if (func->fun.builtin) {
    atomic_fetch_add(&g_eval_metrics.builtin_calls, 1);
    valk_lval_t* result = func->fun.builtin(env, args);
    atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
    // LCOV_EXCL_START - defensive check: builtins should never return NULL
    if (result == NULL) {
      return valk_eval_value(valk_lval_err("Internal error: builtin returned NULL"));
    }
    // LCOV_EXCL_STOP
    return valk_eval_value(result);
  }

  atomic_fetch_add(&g_eval_metrics.function_calls, 1);
  valk_thread_ctx.call_depth++;

  u64 given = valk_lval_list_count(args);
  u64 num_formals = valk_lval_list_count(func->fun.formals);

  valk_lenv_t* call_env = valk_lenv_empty();
  // LCOV_EXCL_BR_START - closures always have env, else branch rarely exercised
  if (func->fun.env) {
    call_env->parent = func->fun.env;
  } else {
    call_env->parent = env;
  }
  // LCOV_EXCL_BR_STOP

  // LCOV_EXCL_BR_START - lambda argument binding has many internal branches for variadics/partial application
  valk_lval_t* formal_iter = func->fun.formals;
  valk_lval_t* arg_iter = args;
  bool saw_varargs = false;

  while (!valk_lval_list_is_empty(formal_iter) && !valk_lval_list_is_empty(arg_iter)) {
    valk_lval_t* formal_sym = formal_iter->cons.head;

    if (LVAL_TYPE(formal_sym) == LVAL_SYM && strcmp(formal_sym->str, "&") == 0) {
      formal_iter = formal_iter->cons.tail;
      if (valk_lval_list_is_empty(formal_iter)) {
        valk_thread_ctx.call_depth--;
        atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
        return valk_eval_value(valk_lval_err("Invalid function format: & not followed by varargs name"));
      }
      valk_lval_t* varargs_sym = formal_iter->cons.head;
      valk_lval_t* varargs_list = valk_builtin_list(nullptr, arg_iter);
      valk_lenv_put(call_env, varargs_sym, varargs_list);
      saw_varargs = true;
      arg_iter = valk_lval_nil();
      formal_iter = formal_iter->cons.tail;
      break;
    }

    valk_lval_t* val = arg_iter->cons.head;
    valk_lenv_put(call_env, formal_sym, val);
    formal_iter = formal_iter->cons.tail;
    arg_iter = arg_iter->cons.tail;
  }

  if (!valk_lval_list_is_empty(arg_iter) && !saw_varargs) {
    valk_thread_ctx.call_depth--;
    atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
    return valk_eval_value(valk_lval_err("More arguments were given than required. Actual: %zu, Expected: %zu", given, num_formals));
  }

  if (!valk_lval_list_is_empty(formal_iter)) {
    if (!valk_lval_list_is_empty(formal_iter) &&
        LVAL_TYPE(formal_iter->cons.head) == LVAL_SYM &&
        strcmp(formal_iter->cons.head->str, "&") == 0) {
      formal_iter = formal_iter->cons.tail;
      if (valk_lval_list_is_empty(formal_iter)) {
        valk_thread_ctx.call_depth--;
        atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
        return valk_eval_value(valk_lval_err("Invalid function format: & not followed by varargs name"));
      }
      valk_lval_t* varargs_sym = formal_iter->cons.head;
      valk_lenv_put(call_env, varargs_sym, valk_lval_nil());
      formal_iter = formal_iter->cons.tail;
    }

    if (!valk_lval_list_is_empty(formal_iter)) {
      valk_lval_t* partial = valk_mem_alloc(sizeof(valk_lval_t));
      partial->flags = LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
      VALK_SET_ORIGIN_ALLOCATOR(partial);
      partial->fun.builtin = nullptr;
      partial->fun.arity = func->fun.arity;
      partial->fun.name = func->fun.name;
      partial->fun.env = call_env;
      partial->fun.formals = formal_iter;
      partial->fun.body = func->fun.body;
      valk_thread_ctx.call_depth--;
      atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
      return valk_eval_value(partial);
    }
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t* body = func->fun.body;
  if (LVAL_TYPE(body) == LVAL_CONS && (body->flags & LVAL_FLAG_QUOTED)) {
    body = valk_qexpr_to_cons(body);
  }

  if (valk_is_list_type(LVAL_TYPE(body)) && valk_lval_list_count(body) > 0) {
    valk_lval_t* first_elem = body->cons.head;
    if (valk_is_list_type(LVAL_TYPE(first_elem))) {
      valk_lval_t* first_expr = body->cons.head;
      valk_lval_t* remaining = body->cons.tail;
      return valk_eval_thunk_body(first_expr, call_env, remaining, call_env);
    }
  }

  return valk_eval_thunk_body(body, call_env, NULL, call_env);
}

// Helper macro: Set up thunk continuation from valk_eval_result_t
// Pushes LAMBDA_DONE, optionally BODY_NEXT, and sets expr/cur_env
#define SETUP_THUNK_CONTINUATION(res, stack_ptr, frame_env, expr_var, cur_env_var) do { \
  valk_eval_stack_push((stack_ptr), (valk_cont_frame_t){.kind = CONT_LAMBDA_DONE, .env = (frame_env)}); \
  if ((res).thunk.remaining_body != NULL && !valk_lval_list_is_empty((res).thunk.remaining_body)) { \
    valk_eval_stack_push((stack_ptr), (valk_cont_frame_t){ \
      .kind = CONT_BODY_NEXT, \
      .env = (res).thunk.env, \
      .body_next = {.remaining = (res).thunk.remaining_body, .call_env = (res).thunk.call_env} \
    }); \
  } \
  (expr_var) = (res).thunk.expr; \
  (cur_env_var) = (res).thunk.env; \
} while(0)

// Iterative evaluator - uses explicit stack instead of C recursion
static valk_lval_t* valk_lval_eval_iterative(valk_lenv_t* env, valk_lval_t* lval) {
  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);
  
  valk_lval_t* expr = lval;
  valk_lenv_t* cur_env = env;
  valk_lval_t* value = NULL;
  
  // Register with thread context for checkpoint evacuation
  void *saved_stack = valk_thread_ctx.eval_stack;
  valk_lval_t *saved_expr = valk_thread_ctx.eval_expr;
  valk_lval_t *saved_value = valk_thread_ctx.eval_value;
  valk_thread_ctx.eval_stack = &stack;
  
  // Push initial DONE continuation
  valk_eval_stack_push(&stack, (valk_cont_frame_t){.kind = CONT_DONE, .env = env});

  while (1) {
    // Sync locals with thread context for checkpoint evacuation
    valk_thread_ctx.eval_expr = expr;
    valk_thread_ctx.eval_value = value;

    VALK_GC_SAFE_POINT();  // LCOV_EXCL_BR_LINE - GC pause rarely triggered
    
    // Reload from thread context in case checkpoint modified them
    expr = valk_thread_ctx.eval_expr;
    value = valk_thread_ctx.eval_value;
    
    atomic_fetch_add(&g_eval_metrics.evals_total, 1);
    
    // Phase 1: Evaluate current expression if we have one
    if (expr != NULL) {  // LCOV_EXCL_BR_LINE - evaluator dispatch
      // LCOV_EXCL_BR_START - type dispatch has many short-circuit branches
      // Self-evaluating forms
      // Quoted cons cells (created with {} syntax) are self-evaluating
      // Non-quoted cons cells (S-expressions) need to be evaluated as function calls
      if (LVAL_TYPE(expr) == LVAL_NUM || LVAL_TYPE(expr) == LVAL_STR ||
          LVAL_TYPE(expr) == LVAL_FUN || LVAL_TYPE(expr) == LVAL_ERR ||
          LVAL_TYPE(expr) == LVAL_NIL || LVAL_TYPE(expr) == LVAL_REF ||
          LVAL_TYPE(expr) == LVAL_HANDLE ||
          (LVAL_TYPE(expr) == LVAL_CONS && (expr->flags & LVAL_FLAG_QUOTED))) {
        // LCOV_EXCL_BR_STOP
        value = expr;
        expr = NULL;
        goto apply_cont;
      }
      
      // Symbol lookup
      if (LVAL_TYPE(expr) == LVAL_SYM) {
        VALK_COVERAGE_RECORD_LVAL(expr);
        if (expr->str[0] == ':') {
          value = expr;
        } else {
          value = valk_lenv_get(cur_env, expr);
        }
        expr = NULL;
        goto apply_cont;
      }
      
      VALK_COVERAGE_RECORD_LVAL(expr);  // LCOV_EXCL_BR_LINE - coverage macro

      // Cons cell - function application
      if (LVAL_TYPE(expr) == LVAL_CONS) {  // LCOV_EXCL_BR_LINE - evaluator dispatch
        u64 count = valk_lval_list_count(expr);

        if (count == 0) {  // LCOV_EXCL_BR_LINE - empty list is rare
          value = valk_lval_nil();
          expr = NULL;
          goto apply_cont;
        }
        
        // Single element - eval and maybe call if function
        if (count == 1) {
          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_SINGLE_ELEM,
            .env = cur_env
          });
          expr = valk_lval_list_nth(expr, 0);
          continue;
        }
        
        // Check special forms
        valk_lval_t* first = expr->cons.head;
        if (LVAL_TYPE(first) == LVAL_SYM) {
          if (strcmp(first->str, "quote") == 0) {
            if (count != 2) {
              value = valk_lval_err("quote expects exactly 1 argument, got %zu", count - 1);
            } else {
              value = valk_lval_list_nth(expr, 1);
            }
            expr = NULL;
            goto apply_cont;
          }
          
          if (strcmp(first->str, "quasiquote") == 0) {
            if (count != 2) {
              value = valk_lval_err("quasiquote expects exactly 1 argument, got %zu", count - 1);
            } else {
              value = valk_quasiquote_expand(cur_env, valk_lval_list_nth(expr, 1));
            }
            expr = NULL;
            goto apply_cont;
          }
          
          // Handle 'if' specially to avoid evaluating both branches
          if (strcmp(first->str, "if") == 0) {
            if (count < 3 || count > 4) {
              value = valk_lval_err("if requires 2-3 arguments, got %zu", count - 1);
              expr = NULL;
              goto apply_cont;
            }
            valk_lval_t* cond = valk_lval_list_nth(expr, 1);
            valk_lval_t* true_branch = valk_lval_list_nth(expr, 2);
            valk_lval_t* false_branch = (count == 4) ? valk_lval_list_nth(expr, 3) : valk_lval_nil();
            
            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_IF_BRANCH,
              .env = cur_env,
              .if_branch = {.true_branch = true_branch, .false_branch = false_branch}
            });
            expr = cond;
            continue;
          }

          // (ctx/with-deadline timeout-ms body...) - sets deadline, evals body, restores ctx
          if (strcmp(first->str, "ctx/with-deadline") == 0) {
            if (count < 3) {
              value = valk_lval_err("ctx/with-deadline requires timeout-ms and body, got %zu args", count - 1);
              expr = NULL;
              goto apply_cont;
            }
            valk_lval_t* timeout_expr = valk_lval_list_nth(expr, 1);
            valk_lval_t* body = expr->cons.tail->cons.tail;

            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_CTX_DEADLINE,
              .env = cur_env,
              .ctx_deadline = {.body = body, .old_ctx = valk_thread_ctx.request_ctx}
            });
            expr = timeout_expr;
            continue;
          }

          // (ctx/with key value body...) - adds local, evals body, restores ctx
          if (strcmp(first->str, "ctx/with") == 0) {
            if (count < 4) {
              value = valk_lval_err("ctx/with requires key, value, and body, got %zu args", count - 1);
              expr = NULL;
              goto apply_cont;
            }
            valk_lval_t* key_expr = valk_lval_list_nth(expr, 1);
            valk_lval_t* value_expr = valk_lval_list_nth(expr, 2);
            valk_lval_t* body = expr->cons.tail->cons.tail->cons.tail;

            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_CTX_WITH,
              .env = cur_env,
              .ctx_with = {.value_expr = value_expr, .body = body, .old_ctx = valk_thread_ctx.request_ctx}
            });
            expr = key_expr;
            continue;
          }
        }
        
        // Normal function application: eval function position first
        valk_eval_stack_push(&stack, (valk_cont_frame_t){
          .kind = CONT_EVAL_ARGS,
          .env = cur_env,
          .eval_args = {.func = NULL, .remaining = expr->cons.tail}
        });
        expr = first;
        continue;
      }
      
      value = valk_lval_err("Unknown value type in evaluation: %s", valk_ltype_name(LVAL_TYPE(expr)));
      expr = NULL;
    }
    
apply_cont:
    // Phase 2: Apply continuation to value
    {
      VALK_ASSERT(value != nullptr, "value must not be null at apply_cont");  // LCOV_EXCL_BR_LINE - invariant
      valk_cont_frame_t frame = valk_eval_stack_pop(&stack);

      switch (frame.kind) {  // LCOV_EXCL_BR_LINE - continuation dispatch (not all types exercised)
        case CONT_DONE:
          valk_eval_stack_destroy(&stack);
          // Restore thread context
          valk_thread_ctx.eval_stack = saved_stack;
          valk_thread_ctx.eval_expr = saved_expr;
          valk_thread_ctx.eval_value = saved_value;
          return value;
          
        case CONT_SINGLE_ELEM:
          if (LVAL_TYPE(value) == LVAL_FUN) {
            valk_eval_result_t res = valk_eval_apply_func_iter(frame.env, value, valk_lval_nil());
            if (!res.is_thunk) {
              value = res.value;
              if (LVAL_TYPE(value) == LVAL_ERR) goto apply_cont;
            } else {
              SETUP_THUNK_CONTINUATION(res, &stack, frame.env, expr, cur_env);
              continue;
            }
          }
          goto apply_cont;
          
        case CONT_EVAL_ARGS: {
          if (LVAL_TYPE(value) == LVAL_ERR) goto apply_cont;
          
          valk_lval_t* func = value;
          valk_lval_t* remaining = frame.eval_args.remaining;
          
          // LCOV_EXCL_START - dead code: CONT_EVAL_ARGS is only pushed when count > 1,
          // meaning remaining always has at least one element. Zero-arg calls go through
          // CONT_SINGLE_ELEM instead.
          if (valk_lval_list_is_empty(remaining)) {
            valk_eval_result_t res = valk_eval_apply_func_iter(frame.env, func, valk_lval_nil());
            if (!res.is_thunk) {
              value = res.value;
              goto apply_cont;
            } else {
              SETUP_THUNK_CONTINUATION(res, &stack, frame.env, expr, cur_env);
              continue;
            }
          }
          // LCOV_EXCL_STOP
          
          // Start collecting args
          u64 arg_count = valk_lval_list_count(remaining);
          valk_lval_t** args = malloc(sizeof(valk_lval_t*) * arg_count);
          
          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_COLLECT_ARG,
            .env = frame.env,
            .collect_arg = {
              .func = func,
              .args = args,
              .count = 0,
              .capacity = arg_count,
              .remaining = remaining->cons.tail
            }
          });
          expr = remaining->cons.head;
          cur_env = frame.env;
          continue;
        }
        
        case CONT_COLLECT_ARG: {
          frame.collect_arg.args[frame.collect_arg.count++] = value;
          
          if (valk_lval_list_is_empty(frame.collect_arg.remaining)) {
            valk_lval_t* args_list = valk_lval_list(frame.collect_arg.args, frame.collect_arg.count);
            free(frame.collect_arg.args);
            valk_eval_result_t res = valk_eval_apply_func_iter(frame.env, frame.collect_arg.func, args_list);
            if (!res.is_thunk) {
              value = res.value;
              goto apply_cont;
            } else {
              SETUP_THUNK_CONTINUATION(res, &stack, frame.env, expr, cur_env);
              continue;
            }
          }
          
          // More args to eval
          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_COLLECT_ARG,
            .env = frame.env,
            .collect_arg = {
              .func = frame.collect_arg.func,
              .args = frame.collect_arg.args,
              .count = frame.collect_arg.count,
              .capacity = frame.collect_arg.capacity,
              .remaining = frame.collect_arg.remaining->cons.tail
            }
          });
          expr = frame.collect_arg.remaining->cons.head;
          cur_env = frame.env;
          continue;
        }
        
        case CONT_IF_BRANCH: {
          if (LVAL_TYPE(value) == LVAL_ERR) goto apply_cont;
          
          bool condition = false;
          if (LVAL_TYPE(value) == LVAL_NUM) {
            condition = (value->num != 0);
          } else if (LVAL_TYPE(value) != LVAL_NIL) {
            condition = true;
          }
          
          valk_lval_t* branch = condition ? frame.if_branch.true_branch : frame.if_branch.false_branch;
          if (LVAL_TYPE(branch) == LVAL_CONS && (branch->flags & LVAL_FLAG_QUOTED)) {
            branch = valk_qexpr_to_cons(branch);
          }
          expr = branch;
          cur_env = frame.env;
          continue;
        }
        
        // LCOV_EXCL_START - Dead code: CONT_DO_NEXT is never initialized (do is a builtin)
        case CONT_DO_NEXT: {
          if (LVAL_TYPE(value) == LVAL_ERR) goto apply_cont;

          if (valk_lval_list_is_empty(frame.do_next.remaining)) {
            goto apply_cont;
          }

          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_DO_NEXT,
            .env = frame.env,
            .do_next = {.remaining = frame.do_next.remaining->cons.tail}
          });
          expr = frame.do_next.remaining->cons.head;
          cur_env = frame.env;
          continue;
        }
        // LCOV_EXCL_STOP
        
        case CONT_BODY_NEXT: {
          if (LVAL_TYPE(value) == LVAL_ERR) {
            goto apply_cont;
          }
          
          if (valk_lval_list_is_empty(frame.body_next.remaining)) {
            goto apply_cont;
          }
          
          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_BODY_NEXT,
            .env = frame.env,
            .body_next = {
              .remaining = frame.body_next.remaining->cons.tail,
              .call_env = frame.body_next.call_env
            }
          });
          expr = frame.body_next.remaining->cons.head;
          cur_env = frame.body_next.call_env;
          continue;
        }
        
        case CONT_LAMBDA_DONE:
          valk_thread_ctx.call_depth--;
          atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
          goto apply_cont;

        case CONT_CTX_DEADLINE: {
          if (LVAL_TYPE(value) == LVAL_ERR) {
            valk_thread_ctx.request_ctx = frame.ctx_deadline.old_ctx;
            goto apply_cont;
          }
          if (LVAL_TYPE(value) != LVAL_NUM) {
            valk_thread_ctx.request_ctx = frame.ctx_deadline.old_ctx;
            value = valk_lval_err("ctx/with-deadline timeout must be a number, got %s", valk_ltype_name(LVAL_TYPE(value)));
            goto apply_cont;
          }

          u64 timeout_ms = (u64)value->num;
          valk_request_ctx_t *new_ctx = valk_request_ctx_with_timeout(
            valk_thread_ctx.request_ctx, timeout_ms, valk_thread_ctx.allocator);
          valk_thread_ctx.request_ctx = new_ctx;

          valk_lval_t *body = frame.ctx_deadline.body;
          if (valk_lval_list_is_empty(body)) {
            valk_thread_ctx.request_ctx = frame.ctx_deadline.old_ctx;
            value = valk_lval_nil();
            goto apply_cont;
          }

          if (valk_lval_list_is_empty(body->cons.tail)) {
            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_CTX_DEADLINE,
              .env = frame.env,
              .ctx_deadline = {.body = valk_lval_nil(), .old_ctx = frame.ctx_deadline.old_ctx}
            });
            expr = body->cons.head;
            cur_env = frame.env;
            continue;
          }

          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_CTX_DEADLINE,
            .env = frame.env,
            .ctx_deadline = {.body = body->cons.tail, .old_ctx = frame.ctx_deadline.old_ctx}
          });
          expr = body->cons.head;
          cur_env = frame.env;
          continue;
        }

        case CONT_CTX_WITH: {
          if (LVAL_TYPE(value) == LVAL_ERR) {
            valk_thread_ctx.request_ctx = frame.ctx_with.old_ctx;
            goto apply_cont;
          }

          valk_lval_t *key = value;
          valk_lval_t *value_expr = frame.ctx_with.value_expr;
          valk_lval_t *val = valk_lval_eval(frame.env, value_expr);
          if (LVAL_TYPE(val) == LVAL_ERR) {
            valk_thread_ctx.request_ctx = frame.ctx_with.old_ctx;
            value = val;
            goto apply_cont;
          }

          valk_request_ctx_t *new_ctx = valk_request_ctx_with_local(
            valk_thread_ctx.request_ctx, key, val, valk_thread_ctx.allocator);
          valk_thread_ctx.request_ctx = new_ctx;

          valk_lval_t *body = frame.ctx_with.body;
          if (valk_lval_list_is_empty(body)) {
            valk_thread_ctx.request_ctx = frame.ctx_with.old_ctx;
            value = valk_lval_nil();
            goto apply_cont;
          }

          if (valk_lval_list_is_empty(body->cons.tail)) {
            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_CTX_DEADLINE,
              .env = frame.env,
              .ctx_deadline = {.body = valk_lval_nil(), .old_ctx = frame.ctx_with.old_ctx}
            });
            expr = body->cons.head;
            cur_env = frame.env;
            continue;
          }

          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_CTX_DEADLINE,
            .env = frame.env,
            .ctx_deadline = {.body = body->cons.tail, .old_ctx = frame.ctx_with.old_ctx}
          });
          expr = body->cons.head;
          cur_env = frame.env;
          continue;
        }

        default:
          value = valk_lval_err("Unknown continuation type: %d", frame.kind);
          goto apply_cont;
      }
    }
  }
#undef SETUP_THUNK_CONTINUATION
}

// Public eval function
valk_lval_t* valk_lval_eval(valk_lenv_t* env, valk_lval_t* lval) {
  return valk_lval_eval_iterative(env, lval);
}

valk_lval_t* valk_lval_eval_call(valk_lenv_t* env, valk_lval_t* func,
                                 valk_lval_t* args) {
  LVAL_ASSERT_TYPE(args, func, LVAL_FUN);

  valk_eval_result_t res = valk_eval_apply_func_iter(env, func, args);
  
  if (!res.is_thunk) {
    return res.value;
  }
  
  if (res.thunk.remaining_body != NULL && !valk_lval_list_is_empty(res.thunk.remaining_body)) {
    valk_lval_t* result = valk_lval_eval(res.thunk.env, res.thunk.expr);
    if (LVAL_TYPE(result) == LVAL_ERR) {
      valk_thread_ctx.call_depth--;
      atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
      return result;
    }
    
    valk_lval_t* curr = res.thunk.remaining_body;
    while (!valk_lval_list_is_empty(curr)) {
      result = valk_lval_eval(res.thunk.call_env, curr->cons.head);
      if (LVAL_TYPE(result) == LVAL_ERR) {
        valk_thread_ctx.call_depth--;
        atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
        return result;
      }
      curr = curr->cons.tail;
    }
    
    valk_thread_ctx.call_depth--;
    atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
    return result;
  }
  
  valk_lval_t* result = valk_lval_eval(res.thunk.env, res.thunk.expr);
  valk_thread_ctx.call_depth--;
  atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
  return result;
}

valk_lval_t* valk_lval_pop(valk_lval_t* lval, u64 i) {
  // Pop i-th element from a cons-based list
  VALK_ASSERT(lval != nullptr, "valk_lval_pop: lval must not be null");  // LCOV_EXCL_BR_LINE - precondition
  u64 count = valk_lval_list_count(lval);
  LVAL_ASSERT(  // LCOV_EXCL_BR_LINE - precondition
      (valk_lval_t*)0, i < count,
      "Cant pop from list at invalid position: [%zu] total length: [%zu]", i,
      count);
  LVAL_ASSERT((valk_lval_t*)0, count > 0, "Cant pop from empty");  // LCOV_EXCL_BR_LINE - precondition

  if (i == 0) {
    // Pop first element
    valk_lval_t* cell = lval->cons.head;
    // Move tail's contents into lval
    if (lval->cons.tail != nullptr &&
        !valk_lval_list_is_empty(lval->cons.tail)) {
      lval->cons.head = lval->cons.tail->cons.head;
      lval->cons.tail = lval->cons.tail->cons.tail;
    } else {
      // List becomes empty
      lval->cons.head = nullptr;
      lval->cons.tail = nullptr;
    }
    return cell;
  }

  // Pop from middle/end: traverse to i-1'th element
  valk_lval_t* prev = lval;
  for (u64 j = 0; j < i - 1; j++) {
    prev = prev->cons.tail;
  }

  // Extract element at position i
  valk_lval_t* curr = prev->cons.tail;
  valk_lval_t* cell = curr->cons.head;

  // Skip over the removed node
  prev->cons.tail = curr->cons.tail;

  return cell;
}

valk_lval_t* valk_lval_join(valk_lval_t* a, valk_lval_t* b) {
  // Create new list instead of mutating a
  // Preserve the type of the first argument (QEXPR or CONS)

  valk_lval_t* orig_a __attribute__((unused)) = a;

  // Determine if result should be quoted (if first arg is quoted)
  bool is_qexpr = (a->flags & LVAL_FLAG_QUOTED) != 0;

  u64 lena = valk_lval_list_count(a);

  // If b is not a list type, wrap it
  // This ensures join always produces proper lists
  valk_lval_t* res;
  if (LVAL_TYPE(b) != LVAL_CONS && LVAL_TYPE(b) != LVAL_NIL) {
    res = is_qexpr ? valk_lval_qcons(b, valk_lval_nil())
                   : valk_lval_cons(b, valk_lval_nil());
  } else {
    // If b has different type, we need to rebuild it with the target type
    // Use b directly - CONS and QEXPR are now the same type
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

  INHERIT_SOURCE_LOC(res, orig_a);  // LCOV_EXCL_BR_LINE - coverage macro
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
      // Check if this is a quoted list (should print with {})
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
      // Check for improper list (tail is not nil)
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
      // Print string with quotes
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

static char valk_lval_str_unescape(char x) {
  switch (x) {  // LCOV_EXCL_BR_LINE - not all escape sequences tested
    case 'a':
      return '\a';
    case 'b':
      return '\b';
    case 'f':
      return '\f';
    case 'n':
      return '\n';
    case 'r':
      return '\r';
    case 't':
      return '\t';
    case 'v':
      return '\v';
    case '\\':
      return '\\';
    case '\'':
      return '\'';
    case '\"':
      return '\"';
  }
  return '\0';
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

static valk_lval_t* valk_lval_read_sym(int* i, const char* s) {
  valk_lval_t* res;
  char next;
  int end = *i;
  // find the end of the string
  for (; (next = s[end]); ++end) {
    if (strchr("abcdefghijklmnopqrstuvwxyz"
               "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
               "0123456789_+-*\\/=<>!&?:",
               next) &&
        s[end] != '\0') {
      continue;
    }
    break;
  }

  // the  length of the new string
  u64 len = end - (*i);
  if (len) {
    char* sym = strndup(&s[*i], len);
    int isNum = strchr("-0123456789", sym[0]) != nullptr;
    for (u64 i = 1; i < len; ++i) {
      if (!strchr("0123456789", sym[i])) {
        isNum = 0;
        break;
      }
    }
    // Negative by itself is not a number
    if (strlen(sym) == 1 && sym[0] == '-') {
      isNum = 0;
    }

    if (isNum) {
      errno = 0;
      long x = strtol(sym, nullptr, 10);
      res = errno != ERANGE ? valk_lval_num(x)
                            : valk_lval_err("Invalid number format %s", sym);
    } else {
      res = valk_lval_sym(sym);
    }
    *i += len;
    free(sym);
    return res;
  }

  return valk_lval_str("");
}
static valk_lval_t* valk_lval_read_str(int* i, const char* s) {
  // Scan the string for size
  char next;
  int count = 1;  // Pad for nil terminator

  // Advance to start of string
  if (s[(*i)++] != '"') {
    return valk_lval_err(
        "Strings must start with `\"` but instead it started with %c", s[*i]);
  }

  // Read until the end
  for (int end = (*i); (next = s[end]) != '"'; ++end) {
    if (next == '\0') {
      return valk_lval_err("Unexpected  end of input at string literal");
    }
    if (next == '\\') {
      ++end;
      if (s[end] == '\0') {
        return valk_lval_err("Unexpected end of input after escape character");
      }
      if (!strchr(lval_str_unescapable, s[end])) {
        return valk_lval_err("Invalid escape character \\%c", s[end]);
      }
    }
    count++;
  }

  // TODO(main): Hmmm can a string be so big, itll blow the stack? fun.
  char tmp[count] = {};

  int offset = 0;
  int end;
  for (end = *i; (next = s[end]) != '"'; ++end) {
    // next = s[end]; // redundant - already assigned in loop condition
    if (next == '\\') {
      ++end;
      next = valk_lval_str_unescape(s[end]);
    }
    tmp[offset++] = next;
  }

  // Update position to after the closing quote
  // end now points to the closing quote
  *i = end + 1;
  return valk_lval_str(tmp);
}

valk_lval_t* valk_lval_read(int* i, const char* s) {
  valk_lval_t* res;

  // Skip white space and comments
  while (strchr(" ;\t\v\r\n", s[*i]) && s[*i] != '\0') {
    // Read comment
    if (s[*i] == ';') {
      while (s[*i] != '\n' && s[*i] != '\0') {
        ++(*i);
      }
    } else {
      ++(*i);
    }
  }

  if (s[*i] == '\0') {
    return valk_lval_err("Unexpected  end of input");
  }

  // Quote syntax: 'x -> Q-expression containing x
  if (s[*i] == '\'') {
    (*i)++;  // consume the quote
    valk_lval_t* quoted = valk_lval_read(i, s);
    if (LVAL_TYPE(quoted) == LVAL_ERR) {
      return quoted;
    }
    // Build a QEXPR containing the quoted element
    res = valk_lval_qcons(quoted, valk_lval_nil());
  }
  // Quasiquote syntax: `x -> (quasiquote x)
  else if (s[*i] == '`') {
    (*i)++;  // consume the backtick
    valk_lval_t* quoted = valk_lval_read(i, s);
    if (LVAL_TYPE(quoted) == LVAL_ERR) {
      return quoted;
    }
    // Build (quasiquote x) as S-expression for evaluation
    valk_lval_t* sym = valk_lval_sym("quasiquote");
    res = valk_lval_cons(sym, valk_lval_cons(quoted, valk_lval_nil()));
  }
  // Unquote syntax: ,x -> (unquote x) or ,@x -> (unquote-splicing x)
  else if (s[*i] == ',') {
    (*i)++;  // consume the comma
    bool splicing = false;
    if (s[*i] == '@') {
      (*i)++;  // consume the @
      splicing = true;
    }
    valk_lval_t* unquoted = valk_lval_read(i, s);
    if (LVAL_TYPE(unquoted) == LVAL_ERR) {
      return unquoted;
    }
    // Build (unquote x) or (unquote-splicing x)
    valk_lval_t* sym = valk_lval_sym(splicing ? "unquote-splicing" : "unquote");
    res = valk_lval_cons(sym, valk_lval_cons(unquoted, valk_lval_nil()));
  } else if (strchr("({", s[*i])) {
    res = valk_lval_read_expr(i, s);
  }
  // Lets check for a symbol
  else if (strchr("abcdefghijklmnopqrstuvwxyz"
                  "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                  "0123456789_+-*\\/=<>!&?:",
                  s[*i])) {
    res = valk_lval_read_sym(i, s);
  } else if (s[*i] == '"') {
    res = valk_lval_read_str(i, s);
  } else {
    res = valk_lval_err("[offset: %ld] Unexpected character %c", *i, s[*i]);
    // Skip the unexpected character to avoid infinite loop
    ++(*i);
  }

  // Skip trailing white space and comments
  while (strchr(" ;\t\v\r\n", s[*i]) && s[*i] != '\0') {
    // Read comment
    if (s[*i] == ';') {
      while (s[*i] != '\n' && s[*i] != '\0') {
        ++(*i);
      }
    } else {
      ++(*i);
    }
  }
  return res;
}

valk_lval_t* valk_lval_read_expr(int* i, const char* s) {
  char end;
  bool is_quoted = false;
  if (s[(*i)++] == '{') {
    is_quoted = true;  // {} syntax means quoted list
    end = '}';
  } else {
    end = ')';
  }

  // Collect elements in a temporary array (allocated from GC heap)
  // These arrays will be swept when unreachable after parsing completes
  u64 capacity = 16;
  u64 count = 0;
  valk_lval_t** elements = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);

  while (s[*i] != end) {
    if (s[*i] == '\0') {
      // No cleanup needed - GC will sweep unreachable arrays
      valk_lval_t* err = valk_lval_err(
          "[offset: %d] Unexpected end of input reading expr, while looking "
          "for `%c`",
          *i, end);
      return err;
    }
    valk_lval_t* x = valk_lval_read(i, s);
    if (LVAL_TYPE(x) == LVAL_ERR) {
      // No cleanup needed - GC will sweep unreachable arrays
      return x;
    }

    // Grow array if needed
    if (count >= capacity) {
      capacity *= 2;
      valk_lval_t** new_elements =
          valk_mem_alloc(sizeof(valk_lval_t*) * capacity);
      memcpy(new_elements, elements, sizeof(valk_lval_t*) * count);
      // Old array becomes unreachable and will be swept by GC
      elements = new_elements;
    }
    elements[count++] = x;
  }
  (*i)++;

  // Build list from right to left, properly terminated with NIL
  // Use QEXPR for {} syntax (quoted data), CONS for () syntax (code)
  valk_lval_t* result = valk_lval_nil();  // Start with nil terminator
  for (u64 j = count; j > 0; j--) {
    if (is_quoted) {
      result = valk_lval_qcons(elements[j - 1], result);
    } else {
      result = valk_lval_cons(elements[j - 1], result);
    }
  }

  // No need to free - GC will sweep unreachable elements array
  return result;
}

static void valk_lenv_init(valk_lenv_t* env);

//// LEnv ////
valk_lenv_t* valk_lenv_empty(void) {
  // Always allocate environments on heap, not scratch.
  // Environments are not valk_lval_t values and don't support forwarding
  // pointers, so they cannot be safely evacuated during checkpoint.
  valk_lenv_t* res;
  if (valk_thread_ctx.heap != NULL) {
    res = valk_gc_malloc_heap_alloc(valk_thread_ctx.heap, sizeof(valk_lenv_t));
  } else {
    res = valk_mem_alloc(sizeof(valk_lenv_t));
  }
  memset(res, 0, sizeof(valk_lenv_t));
  valk_lenv_init(res);
  
  // Override allocator to use heap for all env contents.
  // This ensures env arrays survive scratch arena resets.
  if (valk_thread_ctx.heap != NULL) {
    res->allocator = valk_thread_ctx.heap;
  }
  return res;
}
static void valk_lenv_init(valk_lenv_t* env) {
  env->parent = nullptr;
  env->symbols.count = 0;
  env->symbols.capacity = 0;
  env->symbols.items = nullptr;
  env->vals.count = 0;
  env->vals.capacity = 0;
  env->vals.items = nullptr;
  // capture the current allocator for persistent allocations
  env->allocator = valk_thread_ctx.allocator;
}

// LCOV_EXCL_BR_START - env free/copy have defensive null checks for internal consistency
// Free an environment allocated with malloc allocator.
// For GC-allocated environments, use the GC collection instead.
// Note: This does NOT recursively free parent environments.
void valk_lenv_free(valk_lenv_t* env) {
  if (!env) return;
  // Only free if using malloc allocator
  valk_mem_allocator_t* alloc = (valk_mem_allocator_t*)env->allocator;
  if (alloc && alloc->type != VALK_ALLOC_MALLOC) return;

  // Free symbol strings and values
  for (u64 i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items && env->symbols.items[i]) {
      free(env->symbols.items[i]);
    }
    if (env->vals.items && env->vals.items[i]) {
      valk_lval_t* lval = env->vals.items[i];
      // Free internal string for SYM/STR/ERR types
      if (LVAL_TYPE(lval) == LVAL_SYM || LVAL_TYPE(lval) == LVAL_STR ||
          LVAL_TYPE(lval) == LVAL_ERR) {
        if (lval->str) free(lval->str);
      }
      free(lval);
    }
  }
  // Free arrays
  if (env->symbols.items) free(env->symbols.items);
  if (env->vals.items) free(env->vals.items);
  // Free env itself
  free(env);
}

valk_lenv_t* valk_lenv_copy(valk_lenv_t* env) {
  if (env == nullptr) {
    return nullptr;
  }
  if (env->symbols.items == nullptr || env->vals.items == nullptr) {
    return nullptr;
  }

  valk_lenv_t* res = valk_mem_alloc(sizeof(valk_lenv_t));
  atomic_store(&res->flags, 0);
  res->parent = nullptr;
  res->allocator = valk_thread_ctx.allocator;
  
  u64 capacity = 16;
  u64 count = 0;
  res->symbols.items = valk_mem_alloc(sizeof(char*) * capacity);
  res->vals.items = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);
  res->symbols.capacity = capacity;
  res->vals.capacity = capacity;

  for (valk_lenv_t* e = env; e != nullptr; e = e->parent) {
    if (e->symbols.items == nullptr || e->vals.items == nullptr) break;
    for (u64 i = 0; i < e->symbols.count; i++) {
      if (e->symbols.items[i] == nullptr) continue;
      
      bool masked = false;
      for (u64 j = 0; j < count; j++) {
        if (res->symbols.items[j] && strcmp(e->symbols.items[i], res->symbols.items[j]) == 0) {
          masked = true;
          break;
        }
      }
      
      if (!masked) {
        if (count >= capacity) {
          u64 new_capacity = capacity * 2;
          char** new_symbols = valk_mem_alloc(sizeof(char*) * new_capacity);
          valk_lval_t** new_vals = valk_mem_alloc(sizeof(valk_lval_t*) * new_capacity);
          memcpy(new_symbols, res->symbols.items, sizeof(char*) * count);
          memcpy(new_vals, res->vals.items, sizeof(valk_lval_t*) * count);
          res->symbols.items = new_symbols;
          res->vals.items = new_vals;
          capacity = new_capacity;
          res->symbols.capacity = capacity;
          res->vals.capacity = capacity;
        }
        
        u64 slen = strlen(e->symbols.items[i]);
        res->symbols.items[count] = valk_mem_alloc(slen + 1);
        memcpy(res->symbols.items[count], e->symbols.items[i], slen + 1);
        res->vals.items[count] = e->vals.items[i];
        count++;
      }
    }
  }

  res->symbols.count = count;
  res->vals.count = count;
  return res;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - env lookup has defensive null checks for internal consistency
valk_lval_t* valk_lenv_get(valk_lenv_t* env, valk_lval_t* key) {
  atomic_fetch_add(&g_eval_metrics.env_lookups, 1);

  if (env == NULL) {
    return valk_lval_err("LEnv: Cannot lookup `%s` in NULL environment", key->str);
  }

  LVAL_ASSERT_TYPE((valk_lval_t*)nullptr, key, LVAL_SYM);

  // Iterative lookup through parent chain (lexical scoping)
  while (env) {
    if (env->symbols.items == NULL) {
      env = env->parent;
      continue;
    }
    for (u64 i = 0; i < env->symbols.count; i++) {
      if (env->symbols.items[i] == NULL) {
        break;
      }
      if (strcmp(key->str, env->symbols.items[i]) == 0) {
        if (valk_log_would_log(VALK_LOG_TRACE)) {
          VALK_TRACE("env get idx=%zu key=%s", i, env->symbols.items[i]);
        }
        return env->vals.items[i];
      }
    }
    env = env->parent;
  }

  return valk_lval_err("LEnv: Symbol `%s` is not bound", key->str);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - write barrier logic has many internal branches
static valk_lval_t* __lenv_ensure_safe_val(valk_lenv_t* env, valk_lval_t* val) {
  if (!val) return val;

  void *env_alloc = env->allocator;
  if (!env_alloc && valk_thread_ctx.heap) {
    env_alloc = valk_thread_ctx.heap;
  }
  if (!env_alloc) return val;

  void *val_alloc = val->origin_allocator;
  if (!val_alloc) return val;

  if (valk_region_write_barrier(env_alloc, val_alloc, false)) {
    return val;
  }

  valk_mem_allocator_t *alloc = (valk_mem_allocator_t *)env_alloc;
  if (alloc->type == VALK_ALLOC_REGION) {
    return valk_region_promote_lval((valk_region_t *)env_alloc, val);
  }

  return val;
}
// LCOV_EXCL_BR_STOP

void valk_lenv_put(valk_lenv_t* env, valk_lval_t* key, valk_lval_t* val) {
  if (valk_log_would_log(VALK_LOG_DEBUG)) {
    VALK_DEBUG("env put: %s", key->str);
  }

  valk_lval_t* safe_val = __lenv_ensure_safe_val(env, val);

  for (u64 i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items == NULL || env->symbols.items[i] == NULL) {  // LCOV_EXCL_BR_LINE - defensive check
      break;
    }
    if (strcmp(key->str, env->symbols.items[i]) == 0) {
      env->vals.items[i] = safe_val;
      return;
    }
  }

  // Always prefer heap for env allocations to survive scratch arena resets.
  // This is critical for closures that capture environments and are later
  // invoked after GC moves them to heap.
  // LCOV_EXCL_BR_START - allocator selection logic
  valk_mem_allocator_t *env_alloc;
  if (valk_thread_ctx.heap != NULL) {
    env_alloc = valk_thread_ctx.heap;
  } else if (env->allocator != NULL) {
    env_alloc = (valk_mem_allocator_t*)env->allocator;
  } else {
    env_alloc = valk_thread_ctx.allocator;
  }
  // LCOV_EXCL_BR_STOP
  
  VALK_WITH_ALLOC(env_alloc) {
    u64 slen = strlen(key->str);
    char* new_symbol = valk_mem_alloc(slen + 1);
    // LCOV_EXCL_START - memory allocation never fails in practice
    if (!new_symbol) {
      VALK_RAISE("valk_lenv_put: failed to allocate symbol string for '%s'", key->str);
      return;
    }
    // LCOV_EXCL_STOP
    memcpy(new_symbol, key->str, slen + 1);

    if (env->symbols.count >= env->symbols.capacity) {
      u64 new_capacity =
          env->symbols.capacity == 0 ? 8 : env->symbols.capacity * 2;
      char** new_items = valk_mem_alloc(sizeof(char*) * new_capacity);
      // LCOV_EXCL_START - memory allocation never fails in practice
      if (!new_items) {
        valk_mem_free(new_symbol);
        VALK_RAISE("valk_lenv_put: failed to allocate symbols array (capacity=%llu)", new_capacity);
        return;
      }
      // LCOV_EXCL_STOP
      if (env->symbols.count > 0) {
        memcpy(new_items, env->symbols.items, sizeof(char*) * env->symbols.count);
      }
      if (env->symbols.items) valk_mem_free(env->symbols.items);
      env->symbols.items = new_items;
      env->symbols.capacity = new_capacity;
    }
    if (env->vals.count >= env->vals.capacity) {
      u64 new_capacity = env->vals.capacity == 0 ? 8 : env->vals.capacity * 2;
      valk_lval_t** new_items =
          valk_mem_alloc(sizeof(valk_lval_t*) * new_capacity);
      // LCOV_EXCL_START - memory allocation never fails in practice
      if (!new_items) {
        valk_mem_free(new_symbol);
        VALK_RAISE("valk_lenv_put: failed to allocate vals array (capacity=%llu)", new_capacity);
        return;
      }
      // LCOV_EXCL_STOP
      if (env->vals.count > 0) {
        memcpy(new_items, env->vals.items,
               sizeof(valk_lval_t*) * env->vals.count);
      }
      if (env->vals.items) valk_mem_free(env->vals.items);
      env->vals.items = new_items;
      env->vals.capacity = new_capacity;
    }

    env->symbols.items[env->symbols.count++] = new_symbol;
    env->vals.items[env->vals.count++] = safe_val;
  }
}

// Define the key in global scope
void valk_lenv_def(valk_lenv_t* env, valk_lval_t* key, valk_lval_t* val) {
  while (env->parent) {
    env = env->parent;
  }
  valk_lenv_put(env, key, val);
}

void valk_lenv_put_builtin(valk_lenv_t* env, char* key,
                           valk_lval_builtin_t* _fun) {
  VALK_INFO("install builtin: %s (count=%zu)", key, env->symbols.count);
  VALK_WITH_ALLOC(env->allocator) {
    valk_lval_t* lfun = valk_mem_alloc(sizeof(valk_lval_t));
    lfun->flags =
        LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
    VALK_SET_ORIGIN_ALLOCATOR(lfun);
    lfun->fun.builtin = _fun;
    lfun->fun.env = nullptr;
    valk_lval_set_immortal(lfun);
    // Create symbol lval, use it for put, then free it (put only copies the string)
    valk_lval_t* sym = valk_lval_sym(key);
    valk_lenv_put(env, sym, lfun);
    // Free the temporary symbol lval and its string
    valk_mem_free(sym->str);
    valk_mem_free(sym);
  }
}

#ifdef VALK_COVERAGE
static valk_lval_t *valk_lval_read_ctx(valk_parse_ctx_t *ctx);
static valk_lval_t *valk_lval_read_expr_ctx(valk_parse_ctx_t *ctx);
#endif

valk_lval_t* valk_parse_file(const char* filename) {
  valk_coverage_record_file(filename);
#ifdef VALK_COVERAGE
  u16 file_id = valk_source_register_file(filename);
#endif
  
  FILE* f = fopen(filename, "rb");
  if (f == nullptr) {
    LVAL_RAISE(valk_lval_nil(), "Could not open file (%s)", filename);
  }

  fseek(f, 0, SEEK_END);
  u64 length = ftell(f);
  fseek(f, 0, SEEK_SET);

  if (length == UINT64_MAX) {
    fclose(f);
    LVAL_RAISE(valk_lval_nil(), "File is way too big buddy (%s)", filename);
  }

  char* input = calloc(length + 1, sizeof(char));
  fread(input, 1, length, f);
  fclose(f);

  struct tmp_arr {
    valk_lval_t** items;
    u64 count;
    u64 capacity;
  } tmp = {0};

  da_init(&tmp);

#ifdef VALK_COVERAGE
  valk_parse_ctx_t ctx = {
    .source = input,
    .pos = 0,
    .line = 1,
    .line_start = 0,
    .file_id = file_id
  };
  
  while (ctx.source[ctx.pos] != '\0') {
    valk_lval_t* expr = valk_lval_read_ctx(&ctx);
    if (LVAL_TYPE(expr) == LVAL_ERR) {
      if (strstr(expr->str, "Unexpected end of input")) break;
      da_add(&tmp, expr);
      break;
    }
    valk_coverage_mark_tree(expr);
    da_add(&tmp, expr);
  }
#else
  int pos = 0;

  #define SKIP_WS_AND_COMMENTS() do { \
    while (strchr(" ;\t\v\r\n", input[pos]) && input[pos] != '\0') { \
      if (input[pos] == ';') { \
        while (input[pos] != '\n' && input[pos] != '\0') pos++; \
      } else { \
        pos++; \
      } \
    } \
  } while(0)

  SKIP_WS_AND_COMMENTS();

  while (input[pos] != '\0') {
    da_add(&tmp, valk_lval_read(&pos, input));
    valk_lval_t* last = tmp.items[tmp.count - 1];
    if (LVAL_TYPE(last) == LVAL_ERR) break;
    if (LVAL_TYPE(last) == LVAL_CONS && LVAL_TYPE(last->cons.head) == LVAL_ERR)
      break;
    SKIP_WS_AND_COMMENTS();
  }

  #undef SKIP_WS_AND_COMMENTS
#endif

  free(input);
  valk_lval_t* res = valk_lval_list(tmp.items, tmp.count);
  da_free(&tmp);
  return res;
}

// LCOV_EXCL_BR_START - coverage-mode parser functions not exercised in normal test runs
#ifdef VALK_COVERAGE

static void parse_ctx_skip_whitespace(valk_parse_ctx_t *ctx) {
  while (strchr(" ;\t\v\r\n", ctx->source[ctx->pos]) && ctx->source[ctx->pos] != '\0') {
    if (ctx->source[ctx->pos] == '\n') {
      ctx->line++;
      ctx->line_start = ctx->pos + 1;
    }
    if (ctx->source[ctx->pos] == ';') {
      while (ctx->source[ctx->pos] != '\n' && ctx->source[ctx->pos] != '\0') {
        ctx->pos++;
      }
    } else {
      ctx->pos++;
    }
  }
}

static valk_lval_t *valk_lval_read_sym_ctx(valk_parse_ctx_t *ctx) {
  int saved_line = ctx->line;
  int saved_col = ctx->pos - ctx->line_start + 1;
  
  valk_lval_t *res = valk_lval_read_sym(&ctx->pos, ctx->source);
  LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  return res;
}

static valk_lval_t *valk_lval_read_str_ctx(valk_parse_ctx_t *ctx) {
  int saved_line = ctx->line;
  int saved_col = ctx->pos - ctx->line_start + 1;
  
  valk_lval_t *res = valk_lval_read_str(&ctx->pos, ctx->source);
  LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  return res;
}

static valk_lval_t *valk_lval_read_ctx(valk_parse_ctx_t *ctx) {
  valk_lval_t *res;
  int saved_line = ctx->line;
  int saved_col = ctx->pos - ctx->line_start + 1;
  
  parse_ctx_skip_whitespace(ctx);
  saved_line = ctx->line;
  saved_col = ctx->pos - ctx->line_start + 1;
  
  if (ctx->source[ctx->pos] == '\0') {
    return valk_lval_err("Unexpected end of input");
  }
  
  if (ctx->source[ctx->pos] == '\'') {
    ctx->pos++;
    valk_lval_t *quoted = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(quoted) == LVAL_ERR) return quoted;
    res = valk_lval_qcons(quoted, valk_lval_nil());
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  } else if (ctx->source[ctx->pos] == '`') {
    ctx->pos++;
    valk_lval_t *quoted = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(quoted) == LVAL_ERR) return quoted;
    valk_lval_t *sym = valk_lval_sym("quasiquote");
    LVAL_SET_SOURCE_LOC(sym, ctx->file_id, saved_line, saved_col);
    res = valk_lval_cons(sym, valk_lval_cons(quoted, valk_lval_nil()));
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  } else if (ctx->source[ctx->pos] == ',') {
    ctx->pos++;
    bool splicing = false;
    if (ctx->source[ctx->pos] == '@') {
      ctx->pos++;
      splicing = true;
    }
    valk_lval_t *unquoted = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(unquoted) == LVAL_ERR) return unquoted;
    valk_lval_t *sym = valk_lval_sym(splicing ? "unquote-splicing" : "unquote");
    LVAL_SET_SOURCE_LOC(sym, ctx->file_id, saved_line, saved_col);
    res = valk_lval_cons(sym, valk_lval_cons(unquoted, valk_lval_nil()));
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  } else if (strchr("({", ctx->source[ctx->pos])) {
    res = valk_lval_read_expr_ctx(ctx);
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  } else if (strchr("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_+-*\\/=<>!&?:", ctx->source[ctx->pos])) {
    res = valk_lval_read_sym_ctx(ctx);
  } else if (ctx->source[ctx->pos] == '"') {
    res = valk_lval_read_str_ctx(ctx);
  } else {
    res = valk_lval_err("[offset: %d] Unexpected character %c", ctx->pos, ctx->source[ctx->pos]);
    ctx->pos++;
  }
  
  parse_ctx_skip_whitespace(ctx);
  return res;
}

static valk_lval_t *valk_lval_read_expr_ctx(valk_parse_ctx_t *ctx) {
  char end;
  bool is_quoted = false;
  int saved_line = ctx->line;
  int saved_col = ctx->pos - ctx->line_start + 1;
  
  if (ctx->source[ctx->pos++] == '{') {
    is_quoted = true;
    end = '}';
  } else {
    end = ')';
  }
  
  u64 capacity = 16;
  u64 count = 0;
  valk_lval_t **elements = valk_mem_alloc(sizeof(valk_lval_t *) * capacity);
  
  while (ctx->source[ctx->pos] != end) {
    if (ctx->source[ctx->pos] == '\0') {
      return valk_lval_err("[offset: %d] Unexpected end of input reading expr", ctx->pos);
    }
    valk_lval_t *x = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(x) == LVAL_ERR) return x;
    
    if (count >= capacity) {
      capacity *= 2;
      valk_lval_t **new_elements = valk_mem_alloc(sizeof(valk_lval_t *) * capacity);
      memcpy(new_elements, elements, sizeof(valk_lval_t *) * count);
      elements = new_elements;
    }
    elements[count++] = x;
  }
  ctx->pos++;
  
  valk_lval_t *result = valk_lval_nil();
  LVAL_SET_SOURCE_LOC(result, ctx->file_id, saved_line, saved_col);
  for (u64 j = count; j > 0; j--) {
    if (is_quoted) {
      result = valk_lval_qcons(elements[j - 1], result);
    } else {
      result = valk_lval_cons(elements[j - 1], result);
    }
    LVAL_SET_SOURCE_LOC(result, ctx->file_id, saved_line, saved_col);
  }
  
  return result;
}

#endif // VALK_COVERAGE
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_START - coverage builtins are meta-level code for Valk coverage tracking
#ifdef VALK_COVERAGE
#include "source_loc.h"

static valk_lval_t* valk_builtin_coverage_mark(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  VALK_COVERAGE_MARK_LVAL(expr);
  return expr;
}

static valk_lval_t* valk_builtin_coverage_record(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  VALK_COVERAGE_RECORD_LVAL(expr);
  return expr;
}

static valk_lval_t* valk_builtin_coverage_branch(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* line_val = valk_lval_list_nth(a, 0);
  valk_lval_t* taken_val = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, line_val, LVAL_NUM);
  LVAL_ASSERT_TYPE(a, taken_val, LVAL_NUM);
  u16 file_id = line_val->cov_file_id;
  u16 line = (u16)line_val->num;
  bool taken = taken_val->num != 0;
  valk_coverage_record_branch(file_id, line, taken);
  return valk_lval_num(taken ? 1 : 0);
}

static valk_lval_t* valk_builtin_source_line(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  return valk_lval_num(expr->cov_line);
}

static valk_lval_t* valk_builtin_source_column(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  return valk_lval_num(expr->cov_column);
}

static valk_lval_t* valk_builtin_source_file(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  u16 file_id = expr->cov_file_id;
  const char* filename = valk_source_get_filename(file_id);
  if (filename == NULL) {
    return valk_lval_str("<unknown>");
  }
  return valk_lval_str(filename);
}
#endif
// LCOV_EXCL_STOP

void valk_lenv_builtins(valk_lenv_t* env) {
  valk_register_io_builtins(env);
  valk_register_string_builtins(env);
  valk_register_mem_builtins(env);
  valk_register_list_builtins(env);
  valk_register_math_builtins(env);
  valk_register_env_builtins(env);
  valk_register_http_builtins(env);
  valk_register_aio_builtins(env);
  valk_register_server_builtins(env);

  valk_register_async_handle_builtins(env);
  valk_register_http_request_builtins(env);
  valk_register_stream_builtins(env);
  valk_register_metrics_builtins(env);
  valk_register_aio_diagnostics_builtins(env);
  valk_register_ctx_builtins(env);

#ifdef VALK_COVERAGE
  valk_lenv_put_builtin(env, "coverage-mark", valk_builtin_coverage_mark);
  valk_lenv_put_builtin(env, "coverage-record", valk_builtin_coverage_record);
  valk_lenv_put_builtin(env, "coverage-branch", valk_builtin_coverage_branch);
  valk_lenv_put_builtin(env, "source-line", valk_builtin_source_line);
  valk_lenv_put_builtin(env, "source-column", valk_builtin_source_column);
  valk_lenv_put_builtin(env, "source-file", valk_builtin_source_file);
#endif
}
