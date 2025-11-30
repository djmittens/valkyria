#include "parser.h"

#include <errno.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "aio.h"
#include "collections.h"
#include "common.h"
#include "gc.h"
#include "memory.h"

// TODO(networking): temp forward declare for debugging
static valk_lval_t* valk_builtin_penv(valk_lenv_t* e, valk_lval_t* a);

// GC heap allocator size check - ONLY allocate valk_lval_t structures
size_t __valk_lval_size = sizeof(valk_lval_t);

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
// Note: GC heap zeroes memory, malloc doesn't - always set to be safe
#define VALK_SET_ORIGIN_ALLOCATOR(obj)                   \
  do {                                                   \
    (obj)->origin_allocator = valk_thread_ctx.allocator; \
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
    size_t _n_expected = sizeof(_expected) / sizeof(valk_ltype_e);           \
                                                                             \
    for (size_t i = 0; i < _n_expected; i++) {                               \
      if (LVAL_TYPE(lval) == _expected[i]) {                                 \
        _found = 1;                                                          \
        break;                                                               \
      }                                                                      \
    }                                                                        \
    if (!_found) {                                                           \
      char const* _expect_str[_n_expected];                                  \
      for (size_t i = 0; i < _n_expected; i++) {                             \
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
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_EQ(args, lval, _count)                      \
  LVAL_ASSERT(args, valk_lval_list_count(lval) == _count,             \
              "Invalid argument count, Actual[%zu] == Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_LT(args, lval, _count)                     \
  LVAL_ASSERT(args, valk_lval_list_count(lval) < _count,             \
              "Invalid argument count, Actual[%zu] < Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_LE(args, lval, _count)                      \
  LVAL_ASSERT(args, valk_lval_list_count(lval) <= _count,             \
              "Invalid argument count, Actual[%zu] <= Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_GT(args, lval, _count)                     \
  LVAL_ASSERT(args, valk_lval_list_count(lval) > _count,             \
              "Invalid argument count, Actual[%zu] > Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_GE(args, lval, _count)                      \
  LVAL_ASSERT(args, valk_lval_list_count(lval) >= _count,             \
              "Invalid argument count, Actual[%zu] >= Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

static valk_lval_t* valk_builtin_eval(valk_lenv_t* e, valk_lval_t* a);
static valk_lval_t* valk_builtin_list(valk_lenv_t* e, valk_lval_t* a);
static const char* valk_lval_str_escape(char x);
static char valk_lval_str_unescape(char x);

/* List of possible escapable characters */
static char* lval_str_escapable = "\a\b\f\n\r\t\v\\\'\"";

/* Possible unescapable characters */
static char* lval_str_unescapable = "abfnrtv\\\'\"";

char* valk_c_err_format(const char* fmt, const char* file, const size_t line,
                        const char* function) {
  // NOLINTBEGIN(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  size_t len =
      snprintf(nullptr, 0, "%s:%ld:%s || %s", file, line, function, fmt);
  char* buf = valk_mem_alloc(len + 1);
  snprintf(buf, len + 1, "%s:%ld:%s || %s", file, line, function, fmt);
  // NOLINTEND(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  return buf;
}

// Helper: Get allocation flags from current allocator context
uint64_t valk_alloc_flags_from_allocator(void* allocator) {
  if (allocator == NULL) return LVAL_ALLOC_SCRATCH;
  valk_mem_allocator_t* alloc = (valk_mem_allocator_t*)allocator;
  switch (alloc->type) {
    case VALK_ALLOC_ARENA:
      return LVAL_ALLOC_SCRATCH;
    case VALK_ALLOC_MALLOC:
      return LVAL_ALLOC_GLOBAL;
    case VALK_ALLOC_GC_HEAP:
      return LVAL_ALLOC_HEAP;
    case VALK_ALLOC_SLAB:
      return LVAL_ALLOC_GLOBAL;
    default:
      return LVAL_ALLOC_SCRATCH;
  }
}

char* valk_str_join(const size_t n, const char** strs, const char* sep) {
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
  char* res = valk_mem_alloc(res_len + 1);
  size_t offset = 0;
  for (size_t i = 0; i < n; i++) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memcpy(&res[offset], strs[i], str_lens[i]);
    offset += str_lens[i];
    if (i < n - 1) {
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      memcpy(&res[offset], sep, sep_len);
      offset += sep_len;
    }
  }
  res[offset] = '\0';

  return res;
}

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
      return "S-Expr";
    case LVAL_QEXPR:
      return "Q-Expr";
    case LVAL_ERR:
      return "Error";
    case LVAL_STR:
      return "String";
    case LVAL_REF:
      return "Reference";
    case LVAL_ENV:
      return "Environment";
    case LVAL_CONT:
      return "Continuation";
    case LVAL_UNDEFINED:
      return "UNDEFINED";
  }
  return "Unknown";
}

valk_lval_t* valk_lval_ref(const char* type, void* ptr, void (*free)(void*)) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_REF | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  size_t tlen = strlen(type);
  if (tlen > 100) tlen = 100;
  res->ref.type = valk_mem_alloc(tlen + 1);
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memcpy(res->ref.type, type, tlen);
  res->ref.type[tlen] = '\0';
  res->ref.ptr = ptr;
  res->ref.free = free;

  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_num(long x) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_NUM | LVAL_FLAG_FROZEN |
               valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->num = x;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// TODO(main): look into UTF-8 support
valk_lval_t* valk_lval_err(const char* fmt, ...) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_ERR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  va_list va;
  va_start(va, fmt);

  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  size_t len = vsnprintf(nullptr, 0, fmt, va);
  va_end(va);
  va_start(va, fmt);

  // TODO(main): look into making this into a constant
  len = len < 10000 ? len : 511;
  res->str = valk_mem_alloc(len + 1);
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  vsnprintf(res->str, len + 1, fmt, va);
  va_end(va);
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_sym(const char* sym) {
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_SYM | LVAL_FLAG_FROZEN |
               valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  size_t slen = strlen(sym);
  if (slen > 200) slen = 200;
  res->str = valk_mem_alloc(slen + 1);
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memcpy(res->str, sym, slen);
  res->str[slen] = '\0';

  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_str(const char* str) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_STR | LVAL_FLAG_FROZEN |
               valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  // TODO(main): whats a reasonable max for a string length?
  size_t slen = strlen(str);
  res->str = valk_mem_alloc(slen + 1);
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memcpy(res->str, str, slen + 1);

  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_str_n(const char* bytes, size_t n) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_STR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->str = valk_mem_alloc(n + 1);
  if (n) memcpy(res->str, bytes, n);
  res->str[n] = '\0';

  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// valk_lval_t *valk_lval_builtin(valk_lval_builtin_t *fun) {
//   valk_lval_t *res = malloc(sizeof(valk_lval_t));
//   res->type = LVAL_SYM;
//   res->fun.builtin = fun;
//   res->fun.env = nullptr;
//   return res;
// }

valk_lval_t* valk_lval_lambda(valk_lenv_t* env, valk_lval_t* formals,
                              valk_lval_t* body) {
  // Mark formals and body as escaping (they're captured by the lambda)
  formals->flags |= LVAL_FLAG_ESCAPES;
  body->flags |= LVAL_FLAG_ESCAPES;

  // Create tree-walker lambda function
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);

  res->fun.builtin = nullptr;  // Not a builtin

  // Count arity (handle variadic)
  // Use negative arity for variadic: -(min_args + 1)
  // E.g., {& args} -> arity = -1 (0+ args)
  //       {x & args} -> arity = -2 (1+ args)
  int arity = 0;
  bool is_variadic = false;
  for (size_t i = 0; i < valk_lval_list_count(formals); i++) {
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
  res->fun.name = strdup("<lambda>");
  res->fun.env = env;          // Capture closure environment
  res->fun.formals = formals;  // Store formals for evaluation
  res->fun.body = body;        // Store body for evaluation

  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// Cons cell constructors

valk_lval_t* valk_lval_nil(void) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_NIL | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->cons.head = nullptr;
  res->cons.tail = nullptr;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_cons(valk_lval_t* head, valk_lval_t* tail) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_CONS | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->cons.head = head;
  res->cons.tail = tail;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// Q-expression cons cell (quoted data, not code)
valk_lval_t* valk_lval_qcons(valk_lval_t* head, valk_lval_t* tail) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_QEXPR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->cons.head = head;
  res->cons.tail = tail;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_list(valk_lval_t* arr[], size_t count) {
  valk_lval_t* res = valk_lval_nil();
  for (size_t i = count; i > 0; i--) {
    res = valk_lval_cons(arr[i - 1], res);
  }
  return res;
}

// Build a Q-expression list from array
valk_lval_t* valk_lval_qlist(valk_lval_t* arr[], size_t count) {
  valk_lval_t* res = valk_lval_nil();
  for (size_t i = count; i > 0; i--) {
    res = valk_lval_qcons(arr[i - 1], res);
  }
  return res;
}

// Check if type is a list (CONS, QEXPR, or NIL)
static inline int valk_is_list_type(valk_ltype_e type) {
  return type == LVAL_CONS || type == LVAL_QEXPR || type == LVAL_NIL;
}

valk_lval_t* valk_lval_head(valk_lval_t* cons) {
  cons = valk_lval_resolve(cons);
  VALK_ASSERT(valk_is_list_type(LVAL_TYPE(cons)),
              "Expected list (S-Expr, Q-Expr, or Nil), got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.head;
}

valk_lval_t* valk_lval_tail(valk_lval_t* cons) {
  cons = valk_lval_resolve(cons);
  VALK_ASSERT(valk_is_list_type(LVAL_TYPE(cons)),
              "Expected list (S-Expr, Q-Expr, or Nil), got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.tail;
}

// Helper: check if a list is empty (nil type, null, or cons/qexpr with null head)
int valk_lval_list_is_empty(valk_lval_t* list) {
  list = valk_lval_resolve(list);
  if (list == nullptr) return 1;
  if (LVAL_TYPE(list) == LVAL_NIL) return 1;
  // Also check for cons/qexpr cell with null head (can happen after pop empties list)
  if ((LVAL_TYPE(list) == LVAL_CONS || LVAL_TYPE(list) == LVAL_QEXPR) &&
      list->cons.head == nullptr)
    return 1;
  return 0;
}

// Helper: count elements in a cons list
size_t valk_lval_list_count(valk_lval_t* list) {
  list = valk_lval_resolve(list);

  size_t count = 0;
  valk_lval_t* curr = list;

  while (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    count++;
    curr = valk_lval_resolve(curr->cons.tail);
  }

  return count;
}

// Helper: get nth element from a list (0-indexed)
valk_lval_t* valk_lval_list_nth(valk_lval_t* list, size_t n) {
  list = valk_lval_resolve(list);
  valk_lval_t* curr = list;
  for (size_t i = 0; i < n && curr != nullptr && !valk_lval_list_is_empty(curr);
       i++) {
    curr = valk_lval_resolve(curr->cons.tail);
  }
  if (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    return valk_lval_resolve(curr->cons.head);
  }
  return nullptr;
}

// Free auxiliary data owned by an lval (strings, arrays allocated with malloc)
// Does NOT recursively free child lvals - those are managed by GC
// This is called by GC when freeing an lval
// REMOVED: Type-specific cleanup is no longer needed
// All auxiliary data (strings, arrays, etc.) is allocated from GC heap
// The sweep algorithm handles freeing based on slab vs malloc detection

// Recursively freeze a value tree, making it immutable
void valk_lval_freeze(valk_lval_t* lval) {
  if (lval == nullptr) return;
  lval = valk_lval_resolve(lval);
  if (LVAL_IS_FROZEN(lval)) return;  // Already frozen

  // Set freeze bit
  lval->flags |= LVAL_FLAG_FROZEN;

  // Recursively freeze children based on type
  switch (LVAL_TYPE(lval)) {
    case LVAL_CONS:
      valk_lval_freeze(lval->cons.head);
      valk_lval_freeze(lval->cons.tail);
      break;
    case LVAL_NIL:
      // Nil has no children
      break;
    case LVAL_FUN:
      if (!lval->fun.builtin) {
        // Only freeze body, NOT formals - formals get mutated during function
        // calls (see valk_lval_eval_call line 910 where formals are popped)
        valk_lval_freeze(lval->fun.body);
        // Note: Don't freeze env - it may be shared/mutable
      }
      break;
    case LVAL_ENV:
      // Freeze all values in environment
      for (size_t i = 0; i < lval->env.vals.count; i++) {
        valk_lval_freeze(lval->env.vals.items[i]);
      }
      break;
    default:
      // Atoms (NUM, SYM, STR, ERR, NIL, REF) have no children
      break;
  }
}

// Assert that a value is mutable (not frozen) - crash if frozen
void valk_lval_assert_mutable(valk_lval_t* lval) {
  if (lval == nullptr) return;
  lval = valk_lval_resolve(lval);

  VALK_ASSERT(!LVAL_IS_FROZEN(lval),
              "Attempted to mutate frozen value of type %s",
              valk_ltype_name(LVAL_TYPE(lval)));
}

// SHALLOW copy: Copy only the top-level struct, alias all children
// This is the ONLY function that should copy values (called by valk_intern)
// Per immutability design: "only time a copy should happen is during intern,
// and it should be shallow copy" - all child pointers are aliased, not
// recursively copied
valk_lval_t* valk_lval_copy(valk_lval_t* lval) {
  if (lval == nullptr) return nullptr;
  lval = valk_lval_resolve(lval);  // Resolve forwarding pointers

  // Zero-copy optimization: Frozen heap values are immutable and persistent
  // GC heap values won't be freed by arena resets, safe to alias directly
  if (LVAL_IS_FROZEN(lval) && LVAL_ALLOC(lval) == LVAL_ALLOC_HEAP) {
    return lval;  // Alias immutable heap value - no copy needed
  }

  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));

  // Keep type and semantic flags (not allocation flags from source)
  // Add allocation flags from the current allocator
  res->flags =
      (lval->flags & (LVAL_TYPE_MASK | LVAL_FLAG_FROZEN | LVAL_FLAG_ESCAPES)) |
      valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  // NOTE: Don't overwrite origin_allocator - the allocator already set it
  // correctly! (GC heap allocator sets it to heap pointer, which is the
  // authoritative source) Overwriting it with valk_thread_ctx.allocator can
  // introduce corruption if valk_thread_ctx.allocator was corrupted.
  if (res->origin_allocator == NULL) {
    // Only set if allocator didn't set it (e.g., for malloc/arena allocators)
    VALK_SET_ORIGIN_ALLOCATOR(res);
  }

  switch (LVAL_TYPE(lval)) {
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
        // SHALLOW COPY: Alias env/body/formals (resolve forwarding first)
        // Don't recursively copy - immutability means we can safely alias
        res->fun.builtin = nullptr;
        res->fun.env = lval->fun.env;  // Alias environment (no deep copy)
        res->fun.body = valk_lval_resolve(
            lval->fun.body);  // Alias body (resolve forwarding)
        res->fun.formals = valk_lval_resolve(
            lval->fun.formals);  // Alias formals (resolve forwarding)
      }
      break;
    case LVAL_CONS:
    case LVAL_QEXPR:
      // SHALLOW COPY: Alias head/tail (resolve forwarding first)
      // Don't recursively copy - immutability means we can safely alias
      res->cons.head = valk_lval_resolve(lval->cons.head);
      res->cons.tail = valk_lval_resolve(lval->cons.tail);
      break;
    case LVAL_NIL:
      // Nil has no children to copy
      break;
    case LVAL_SYM: {
      size_t slen = strlen(lval->str);
      if (slen > 200) slen = 200;
      res->str = valk_mem_alloc(slen + 1);
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      memcpy(res->str, lval->str, slen);
      res->str[slen] = '\0';
      break;
    }
    case LVAL_ERR: {
      size_t slen = strlen(lval->str);
      if (slen > 2000) slen = 2000;
      res->str = valk_mem_alloc(slen + 1);
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      memcpy(res->str, lval->str, slen);
      res->str[slen] = '\0';
      break;
    }
    case LVAL_STR: {
      size_t slen = strlen(lval->str);
      res->str = valk_mem_alloc(slen + 1);
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      memcpy(res->str, lval->str, slen + 1);
      break;
    }
    case LVAL_REF: {
      // Shallow copy ref payload, but duplicate type string into allocator
      size_t tlen = strlen(lval->ref.type);
      if (tlen > 100) tlen = 100;
      res->ref.type = valk_mem_alloc(tlen + 1);
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      memcpy(res->ref.type, lval->ref.type, tlen);
      res->ref.type[tlen] = '\0';
      res->ref.ptr = lval->ref.ptr;
      res->ref.free = lval->ref.free;
      break;
    }
    case LVAL_ENV:
    case LVAL_CONT:
    case LVAL_UNDEFINED:
      break;
  }
  return res;
}

// Resolve forwarding pointers (follow chain to actual value)
valk_lval_t* valk_lval_resolve(valk_lval_t* val) {
  if (val == nullptr) return nullptr;

  // Follow forwarding chain (limit depth to prevent infinite loops)
  int depth = 0;
  while ((val->flags & LVAL_FLAG_FORWARDED) && depth < 10) {
    // Forwarding pointer is stored in cons.head (repurposed field)
    val = val->cons.head;
    depth++;
  }

  return val;
}

valk_lval_t* valk_intern(valk_lenv_t* env, valk_lval_t* val) {
  if (env == nullptr) return val;

  // Resolve any forwarding first
  val = valk_lval_resolve(val);

  // Zero-copy optimization: Frozen heap values can be shared without copying
  // GC heap values are persistent and won't be freed by arena resets
  if (val != nullptr && LVAL_IS_FROZEN(val) &&
      LVAL_ALLOC(val) == LVAL_ALLOC_HEAP) {
    return val;  // Zero-copy sharing of immutable heap value
  }

  // Check if value is already in the target allocator
  if (val != nullptr && val->origin_allocator == env->allocator) {
    return val;  // Already in the right place - can alias
  }

  // Value is from a different allocator (e.g., scratch arena)
  // We need to copy it to the target allocator (e.g., GC heap)
  // IMPORTANT: Save and restore thread allocator to avoid intermediate
  // allocations in scratch
  void* saved_allocator = valk_thread_ctx.allocator;
  valk_thread_ctx.allocator = env->allocator;
  valk_lval_t* res = valk_lval_copy(val);
  valk_thread_ctx.allocator = saved_allocator;

  if (res) {
    res->origin_allocator = env->allocator;

    // Set up forwarding pointer in original value (if from scratch/arena)
    // This allows existing references to find the new location
    if (LVAL_ALLOC(val) != LVAL_ALLOC_HEAP) {
      val->flags |= LVAL_FLAG_FORWARDED;
      val->cons.head = res;  // Store forwarding pointer
    }
  }

  return res;
}

// void valk_lval_free(valk_lval_t *lval) {
//   if (lval == nullptr) {
//     return;
//   }
//   switch (LVAL_TYPE(lval)) {
//     case LVAL_FUN:
//       if (!lval->fun.builtin) {
//         valk_release(lval->fun.body);
//         valk_release(lval->fun.formals);
//         valk_release(lval->fun.env);
//       }
//       break;
//     case LVAL_NUM:
//       // nuttin to do but break;
//       break;
//     case LVAL_STR:
//     case LVAL_SYM:
//     case LVAL_ERR:
//       // TODO(networking): where should i store these stupid strings?
//       free(lval->str);
//       break;
//     case LVAL_QEXPR:
//     case LVAL_SEXPR:
//       while (lval->expr.count > 0) {
//         valk_release(valk_lval_list_nth(lval, lval->expr.count - 1));
//         --lval->expr.count;
//       }
//       // Should play around with valgrind on this. Pretty interesting thing
//       to
//       // forget
//       free(lval->expr.cell);
//       break;
//     case LVAL_REF:
//       lval->ref.free(lval->ref.ptr);
//       free(lval->ref.type);
//       break;
//   }
//   valk_mem_free(lval);
// }

int valk_lval_eq(valk_lval_t* x, valk_lval_t* y) {
  // Handle NULL cases
  if (x == nullptr && y == nullptr) {
    return 1;  // Both NULL are equal
  }
  if (x == nullptr || y == nullptr) {
    return 0;  // One NULL, one not
  }

  // Resolve forwarding pointers
  x = valk_lval_resolve(x);
  y = valk_lval_resolve(y);

  // Compare only type and semantic flags, not allocation/lifetime flags
  // Values are equal regardless of where they're allocated or if they escape
  // LVAL_FLAG_ESCAPES is a lifetime/allocation flag, not a semantic property
  uint64_t x_semantic = x->flags & (LVAL_TYPE_MASK | LVAL_FLAG_FROZEN);
  uint64_t y_semantic = y->flags & (LVAL_TYPE_MASK | LVAL_FLAG_FROZEN);
  if (x_semantic != y_semantic) {
    return 0;
  }

  switch (LVAL_TYPE(x)) {
    case LVAL_NUM:
      return (x->num == y->num);
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      return (strcmp(x->str, y->str) == 0);
    case LVAL_FUN: {
      if (x->fun.builtin || y->fun.builtin) {
        return x->fun.builtin == y->fun.builtin;
      } else {
        return valk_lval_eq(x->fun.formals, y->fun.formals) &&
               valk_lval_eq(x->fun.body, y->fun.body);
      }
    }
    case LVAL_NIL:
      return 1;  // Both are nil (types already matched)
    case LVAL_CONS:
    case LVAL_QEXPR:
      // Compare cons/qexpr cells recursively
      return valk_lval_eq(x->cons.head, y->cons.head) &&
             valk_lval_eq(x->cons.tail, y->cons.tail);
    case LVAL_REF:
      return (x->ref.ptr == y->ref.ptr) && (x->ref.free == y->ref.free);
    case LVAL_ENV:
      VALK_RAISE(
          "LVAL is LENV, comparison unimplemented, something went wrong");
      break;
    case LVAL_UNDEFINED:
      VALK_RAISE("LVAL is undefined, something went wrong");
      break;
    case LVAL_CONT:
      break;
  }

  return 0;
}

valk_lval_t* valk_lval_eval(valk_lenv_t* env, valk_lval_t* lval) {
  // Tree-walker evaluation

  // Handle NULL gracefully
  if (lval == NULL) {
    return valk_lval_nil();
  }

  // Return literals as-is (self-evaluating forms)
  // QEXPR is quoted data - it evaluates to itself, not executed as code
  if (LVAL_TYPE(lval) == LVAL_NUM || LVAL_TYPE(lval) == LVAL_STR ||
      LVAL_TYPE(lval) == LVAL_FUN || LVAL_TYPE(lval) == LVAL_ERR ||
      LVAL_TYPE(lval) == LVAL_NIL || LVAL_TYPE(lval) == LVAL_REF ||
      LVAL_TYPE(lval) == LVAL_QEXPR) {
    return lval;
  }

  // Symbols are looked up in the environment
  if (LVAL_TYPE(lval) == LVAL_SYM) {
    return valk_lenv_get(env, lval);
  }

  // Cons cells are evaluated as function calls
  if (LVAL_TYPE(lval) == LVAL_CONS) {
    size_t count = valk_lval_list_count(lval);

    // Empty list evaluates to nil
    if (count == 0) {
      return valk_lval_nil();
    }

    // Single element list - evaluate the element
    // If it evaluates to a function, call it with no arguments
    if (count == 1) {
      valk_lval_t* first = valk_lval_eval(env, valk_lval_list_nth(lval, 0));
      if (LVAL_TYPE(first) == LVAL_FUN) {
        // Call function with empty args list
        return valk_lval_eval_call(env, first, valk_lval_nil());
      }
      return first;
    }

    // Check for special forms BEFORE evaluating first element
    valk_lval_t* first = lval->cons.head;
    if (LVAL_TYPE(first) == LVAL_SYM) {
      // quote: return argument unevaluated
      if (strcmp(first->str, "quote") == 0) {
        if (count != 2) {
          return valk_lval_err("quote expects exactly 1 argument, got %zu",
                               count - 1);
        }
        return valk_lval_list_nth(lval, 1);
      }

      // Note: \ (lambda) and def are regular builtins, not special forms
      // They receive evaluated arguments, which works with the prelude's macro patterns
    }

    // Multi-element list is function application
    // First evaluate the function position
    valk_lval_t* func = valk_lval_eval(env, first);
    if (LVAL_TYPE(func) == LVAL_ERR) {
      return func;
    }

    // Evaluate arguments (unless it's a macro)
    valk_lval_t* tmp[count - 1];
    valk_lval_t* h = lval->cons.tail;

    for (size_t i = 0; i < (count - 1); i++) {
      // Evaluate each argument
      tmp[i] = valk_lval_eval(env, h->cons.head);
      if (LVAL_TYPE(tmp[i]) == LVAL_ERR) {
        return tmp[i];
      }
      h = h->cons.tail;
    }

    // Call the function
    valk_lval_t* result =
        valk_lval_eval_call(env, func, valk_lval_list(tmp, count - 1));

    // Mark return value as escaping (it's being returned to caller)
    result->flags |= LVAL_FLAG_ESCAPES;

    return result;
  }

  // Unknown type
  return valk_lval_err("Unknown value type in evaluation: %s",
                       valk_ltype_name(LVAL_TYPE(lval)));
}

valk_lval_t* valk_lval_eval_call(valk_lenv_t* env, valk_lval_t* func,
                                 valk_lval_t* args) {
  // TODO(llvm): Proper tail call optimization requires either:
  // 1. An explicit evaluation stack (stack machine) instead of using C's call stack
  // 2. LLVM backend with tail call attribute
  // The current tree-walking interpreter cannot do TCO for calls through
  // if/do/let/etc because those create C stack frames that we can't eliminate.
  // For now, deep recursion will use stack space. With malloc fallback from slab,
  // reasonable depths are supported.
  LVAL_ASSERT_TYPE(args, func, LVAL_FUN);

  if (func->fun.builtin) {
    return func->fun.builtin(env, args);
  }

  // Track call depth for user-defined functions (not builtins)
  valk_thread_ctx.call_depth++;

  // Immutable function application - NO COPYING, NO MUTATION
  // Walk formals and args together, creating bindings in new environment

  size_t given = valk_lval_list_count(args);
  size_t num_formals = valk_lval_list_count(func->fun.formals);

  // Create new environment for bindings
  // Hybrid scoping using fallback:
  // - Primary lookup: call_env -> func->fun.env chain (lexical/captured bindings)
  // - Fallback lookup: calling env chain (dynamic/caller's bindings)
  // This allows closures to work (curry captures 'f') while also supporting
  // dynamic access to caller's variables (select can see local 'n').
  valk_lenv_t* call_env = valk_lenv_empty();
  if (func->fun.env) {
    // Function has captured environment - use as parent for lexical scoping
    call_env->parent = func->fun.env;
  } else {
    // No captures - parent is calling environment
    call_env->parent = env;
  }
  // Always set fallback to calling environment for dynamic scoping.
  // This is only used when lexical lookup fails.
  call_env->fallback = env;

  // Walk formals and args together without mutation
  valk_lval_t* formal_iter = func->fun.formals;
  valk_lval_t* arg_iter = args;
  bool saw_varargs = false;

  while (!valk_lval_list_is_empty(formal_iter) &&
         !valk_lval_list_is_empty(arg_iter)) {
    valk_lval_t* formal_sym = formal_iter->cons.head;

    // Handle varargs
    if (LVAL_TYPE(formal_sym) == LVAL_SYM &&
        strcmp(formal_sym->str, "&") == 0) {
      // Next formal is the varargs name
      formal_iter = formal_iter->cons.tail;
      if (valk_lval_list_is_empty(formal_iter)) {
        valk_thread_ctx.call_depth--;
        return valk_lval_err(
            "Invalid function format: & not followed by varargs name");
      }
      valk_lval_t* varargs_sym = formal_iter->cons.head;
      valk_lval_t* varargs_list = valk_builtin_list(nullptr, arg_iter);
      valk_lenv_put(call_env, varargs_sym, varargs_list);
      saw_varargs = true;
      arg_iter = valk_lval_nil();            // All remaining args consumed
      formal_iter = formal_iter->cons.tail;  // Should be empty now
      break;
    }

    // Regular formal - bind it
    valk_lval_t* val = arg_iter->cons.head;
    valk_lenv_put(call_env, formal_sym, val);

    formal_iter = formal_iter->cons.tail;
    arg_iter = arg_iter->cons.tail;
  }

  // Check if more args than formals (error unless varargs)
  if (!valk_lval_list_is_empty(arg_iter) && !saw_varargs) {
    valk_thread_ctx.call_depth--;
    return valk_lval_err(
        "More arguments were given than required. Actual: %zu, Expected: %zu",
        given, num_formals);
  }

  // Handle remaining formals (partial application or varargs default)
  if (!valk_lval_list_is_empty(formal_iter)) {
    // Check for varargs with no args provided
    if (!valk_lval_list_is_empty(formal_iter) &&
        LVAL_TYPE(formal_iter->cons.head) == LVAL_SYM &&
        strcmp(formal_iter->cons.head->str, "&") == 0) {
      formal_iter = formal_iter->cons.tail;
      if (valk_lval_list_is_empty(formal_iter)) {
        valk_thread_ctx.call_depth--;
        return valk_lval_err(
            "Invalid function format: & not followed by varargs name");
      }
      valk_lval_t* varargs_sym = formal_iter->cons.head;
      valk_lenv_put(call_env, varargs_sym, valk_lval_nil());
      formal_iter = formal_iter->cons.tail;
    }

    // If still have unbound formals, return partially applied function
    if (!valk_lval_list_is_empty(formal_iter)) {
      valk_lval_t* partial = valk_mem_alloc(sizeof(valk_lval_t));
      partial->flags =
          LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
      VALK_SET_ORIGIN_ALLOCATOR(partial);
      partial->fun.builtin = nullptr;
      partial->fun.arity = func->fun.arity;  // Keep original arity
      partial->fun.name = func->fun.name;    // Keep original name
      partial->fun.env = call_env;
      partial->fun.formals =
          formal_iter;  // Remaining formals (immutable, can alias)
      partial->fun.body = func->fun.body;  // Body (immutable, can alias)
      valk_thread_ctx.call_depth--;
      return partial;
    }
  }

  // All formals bound - evaluate body
  // If body is a QEXPR, convert it to CONS for evaluation
  // The body was stored as QEXPR (quoted) to prevent evaluation during
  // definition, but now we need to execute it
  valk_lval_t* body = func->fun.body;
  if (LVAL_TYPE(body) == LVAL_QEXPR) {
    // Convert QEXPR to CONS for execution
    size_t count = valk_lval_list_count(body);
    valk_lval_t* items[count];
    valk_lval_t* curr = body;
    for (size_t i = 0; i < count; i++) {
      items[i] = curr->cons.head;
      curr = curr->cons.tail;
    }
    body = valk_lval_list(items, count);
  }

  // If body is a list of expressions (first element is also a list),
  // evaluate each expression and return the last result (implicit do)
  if (valk_is_list_type(LVAL_TYPE(body)) && valk_lval_list_count(body) > 0) {
    valk_lval_t* first_elem = body->cons.head;
    // Check if this looks like a sequence (first element is a list, not a symbol)
    // For QEXPR bodies, the first element being a CONS or QEXPR means we have
    // multiple expressions to evaluate
    if (valk_is_list_type(LVAL_TYPE(first_elem))) {
      // Implicit do: evaluate each expression, return last
      valk_lval_t* result = valk_lval_nil();
      valk_lval_t* curr = body;
      while (!valk_lval_list_is_empty(curr)) {
        valk_lval_t* expr = curr->cons.head;
        result = valk_lval_eval(call_env, expr);
        if (LVAL_TYPE(result) == LVAL_ERR) {
          valk_thread_ctx.call_depth--;
          return result;
        }
        curr = curr->cons.tail;
      }
      valk_thread_ctx.call_depth--;
      return result;
    }
  }

  // Single expression body - evaluate it
  valk_lval_t* result = valk_lval_eval(call_env, body);
  valk_thread_ctx.call_depth--;
  return result;
}

valk_lval_t* valk_lval_pop(valk_lval_t* lval, size_t i) {
  // Pop i-th element from a cons-based list
  lval = valk_lval_resolve(lval);
  size_t count = valk_lval_list_count(lval);
  LVAL_ASSERT(
      (valk_lval_t*)0, i < count,
      "Cant pop from list at invalid position: [%zu] total length: [%zu]", i,
      count);
  LVAL_ASSERT((valk_lval_t*)0, count > 0, "Cant pop from empty");

  // Check if value is frozen (immutable)
  valk_lval_assert_mutable(lval);

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
  for (size_t j = 0; j < i - 1; j++) {
    prev = valk_lval_resolve(prev->cons.tail);
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
  a = valk_lval_resolve(a);
  b = valk_lval_resolve(b);

  // Determine if result should be QEXPR (if first arg is QEXPR)
  bool is_qexpr = (LVAL_TYPE(a) == LVAL_QEXPR);

  size_t lena = valk_lval_list_count(a);

  // If b is not a list type, wrap it
  // This ensures join always produces proper lists
  valk_lval_t* res;
  if (LVAL_TYPE(b) != LVAL_CONS && LVAL_TYPE(b) != LVAL_QEXPR &&
      LVAL_TYPE(b) != LVAL_NIL) {
    res = is_qexpr ? valk_lval_qcons(b, valk_lval_nil())
                   : valk_lval_cons(b, valk_lval_nil());
  } else {
    // If b has different type, we need to rebuild it with the target type
    if (is_qexpr && LVAL_TYPE(b) == LVAL_CONS) {
      // Convert CONS to QEXPR - rebuild the list
      size_t lenb = valk_lval_list_count(b);
      res = valk_lval_nil();
      valk_lval_t* items[lenb];
      valk_lval_t* curr = b;
      for (size_t i = 0; i < lenb; i++) {
        items[i] = curr->cons.head;
        curr = curr->cons.tail;
      }
      for (size_t i = lenb; i > 0; i--) {
        res = valk_lval_qcons(items[i - 1], res);
      }
    } else if (!is_qexpr && LVAL_TYPE(b) == LVAL_QEXPR) {
      // Convert QEXPR to CONS - rebuild the list
      size_t lenb = valk_lval_list_count(b);
      res = valk_lval_nil();
      valk_lval_t* items[lenb];
      valk_lval_t* curr = b;
      for (size_t i = 0; i < lenb; i++) {
        items[i] = curr->cons.head;
        curr = curr->cons.tail;
      }
      for (size_t i = lenb; i > 0; i--) {
        res = valk_lval_cons(items[i - 1], res);
      }
    } else {
      res = b;
    }
  }

  struct {
    valk_lval_t** items;
    size_t count;
    size_t capacity;
  } tmp = {0};

  da_init(&tmp);

  for (size_t i = 0; i < lena; i++) {
    da_add(&tmp, a->cons.head);
    a = a->cons.tail;
  }

  for (size_t i = lena; i > 0; i--) {
    if (is_qexpr) {
      res = valk_lval_qcons(tmp.items[i - 1], res);
    } else {
      res = valk_lval_cons(tmp.items[i - 1], res);
    }
  }

  da_free(&tmp);

  return res;
}

void valk_lval_print(valk_lval_t* val) {
  if (val == nullptr) {
    printf("NULL");
    return;
  }
  switch (LVAL_TYPE(val)) {
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
      printf("(");
      valk_lval_t* curr = val;
      int first = 1;
      while (curr != nullptr && LVAL_TYPE(curr) == LVAL_CONS) {
        if (!first) putchar(' ');
        valk_lval_print(curr->cons.head);
        curr = curr->cons.tail;
        first = 0;
      }
      // Check for improper list (tail is not nil)
      if (curr != nullptr && LVAL_TYPE(curr) != LVAL_NIL) {
        printf(" . ");
        valk_lval_print(curr);
      }
      printf(")");
      break;
    }
    case LVAL_QEXPR: {
      // Q-expressions print with {} to show they are quoted data
      printf("{");
      valk_lval_t* curr = val;
      int first = 1;
      while (curr != nullptr && LVAL_TYPE(curr) == LVAL_QEXPR) {
        if (!first) putchar(' ');
        valk_lval_print(curr->cons.head);
        curr = curr->cons.tail;
        first = 0;
      }
      // Check for improper list (tail is not nil)
      if (curr != nullptr && LVAL_TYPE(curr) != LVAL_NIL) {
        printf(" . ");
        valk_lval_print(curr);
      }
      printf("}");
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
      for (size_t i = 0; i < strlen(val->str); ++i) {
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
    case LVAL_CONT:
      printf("Continuation[fn:%p, data:%p]", val->cont.resume_fn,
             val->cont.user_data);
      break;
    case LVAL_ENV:
      printf("[LEnv]");
      break;
    case LVAL_UNDEFINED:
      printf("[Undefined]");
      break;
  }
}

static char valk_lval_str_unescape(char x) {
  switch (x) {
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
  switch (x) {
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
               "0123456789_+-*\\/=<>!&?",
               next) &&
        s[end] != '\0') {
      continue;
    }
    break;
  }

  // the  length of the new string
  size_t len = end - (*i);
  if (len) {
    char* sym = strndup(&s[*i], len);
    int isNum = strchr("-0123456789", sym[0]) != nullptr;
    for (size_t i = 1; i < len; ++i) {
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
      // TODO(main): i dont like that we return this error as a success....
      // this should yield a return 1;
      // but im too lazy to unfuck this function
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
    // next = s[end]; // why the heck is that here
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
  } else if (strchr("({", s[*i])) {
    res = valk_lval_read_expr(i, s);
  }
  // Lets check for a symbol
  else if (strchr("abcdefghijklmnopqrstuvwxyz"
                  "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                  "0123456789_+-*\\/=<>!&?",
                  s[*i])) {
    res = valk_lval_read_sym(i, s);
  } else if (s[*i] == '"') {
    res = valk_lval_read_str(i, s);
  } else {
    res = valk_lval_err("[offset: %ld] Unexpected character %c", *i, s[*i]);
    // Skip the unexpected character to avoid infinite loop
    ++(*i);
  }

  // Skip white space and comments
  while (strchr(" \t\v\r\n", s[*i]) && s[*i] != '\0') {
    // Read comment
    if (s[*i] == ';') {
      while (s[*i] != '\n' && s[*i] != '\0') {
        ++(*i);
      }
    }
    ++(*i);
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
  size_t capacity = 16;
  size_t count = 0;
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
  for (size_t j = count; j > 0; j--) {
    if (is_quoted) {
      result = valk_lval_qcons(elements[j - 1], result);
    } else {
      result = valk_lval_cons(elements[j - 1], result);
    }
  }

  // No need to free - GC will sweep unreachable elements array
  return result;
}

//// LEnv ////
valk_lenv_t* valk_lenv_empty(void) {
  valk_lenv_t* res = valk_mem_alloc(sizeof(valk_lenv_t));
  memset(res, 0, sizeof(valk_lenv_t));
  valk_lenv_init(res);
  return res;
}
void valk_lenv_init(valk_lenv_t* env) {
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

// REMOVED: Type-specific cleanup is no longer needed
// All auxiliary data (symbol arrays, strings, etc.) is allocated from GC heap
// The sweep algorithm handles freeing based on slab vs malloc detection

valk_lenv_t* valk_lenv_copy(valk_lenv_t* env) {
  if (env == nullptr) {
    return nullptr;
  }

  // Performance optimization: Flatten environment chain when copying
  // Instead of preserving parent chain, collect all bindings into flat mapping
  // This eliminates exponential copying through environment chains

  valk_lenv_t* res = valk_mem_alloc(sizeof(valk_lenv_t));
  res->parent = nullptr;  // Flattened environment has no parent
  res->allocator = env->allocator;

  // Count total bindings by walking parent chain (with value masking)
  // Use a simple linear scan - O(n*m) but environments are typically small
  size_t total_count = 0;
  for (valk_lenv_t* e = env; e != nullptr; e = e->parent) {
    for (size_t i = 0; i < e->symbols.count; i++) {
      // Check if this symbol is already counted (masked by child scope)
      bool masked = false;
      for (valk_lenv_t* child = env; child != e; child = child->parent) {
        for (size_t j = 0; j < child->symbols.count; j++) {
          if (strcmp(e->symbols.items[i], child->symbols.items[j]) == 0) {
            masked = true;
            break;
          }
        }
        if (masked) break;
      }
      if (!masked) {
        total_count++;
      }
    }
  }

  // Initialize dynamic arrays from GC heap
  res->symbols.items = valk_mem_alloc(sizeof(char*) * total_count);
  res->symbols.count = total_count;
  res->symbols.capacity = total_count;
  res->vals.items = valk_mem_alloc(sizeof(valk_lval_t*) * total_count);
  res->vals.count = total_count;
  res->vals.capacity = total_count;

  // Collect all bindings with value masking
  size_t idx = 0;
  for (valk_lenv_t* e = env; e != nullptr; e = e->parent) {
    for (size_t i = 0; i < e->symbols.count; i++) {
      // Check if this symbol is masked by child scope
      bool masked = false;
      for (valk_lenv_t* child = env; child != e; child = child->parent) {
        for (size_t j = 0; j < child->symbols.count; j++) {
          if (strcmp(e->symbols.items[i], child->symbols.items[j]) == 0) {
            masked = true;
            break;
          }
        }
        if (masked) break;
      }

      if (!masked) {
        size_t slen = strlen(e->symbols.items[i]);
        res->symbols.items[idx] = valk_mem_alloc(slen + 1);
        memcpy(res->symbols.items[idx], e->symbols.items[i], slen + 1);
        res->vals.items[idx] = valk_intern(res, e->vals.items[i]);
        idx++;
      }
    }
  }

  return res;
}

valk_lval_t* valk_lenv_get(valk_lenv_t* env, valk_lval_t* key) {
  LVAL_ASSERT_TYPE((valk_lval_t*)nullptr, key, LVAL_SYM);

  // Iterative lookup to avoid stack overflow with deep environment chains
  // (important for tail call optimization which creates environment chains)
  valk_lenv_t* start_env = env;  // Remember start for fallback lookup
  while (env) {
    for (size_t i = 0; i < env->symbols.count; i++) {
      if (env->symbols.items == NULL || env->symbols.items[i] == NULL) {
        break;
      }
      if (strcmp(key->str, env->symbols.items[i]) == 0) {
        if (valk_log_would_log(VALK_LOG_TRACE)) {
          VALK_TRACE("env get idx=%zu key=%s", i, env->symbols.items[i]);
        }
        return env->vals.items[i];
      }
    }
    env = env->parent;  // Move to parent environment
  }

  // Parent chain exhausted - try fallback chain (for dynamic scoping).
  // The fallback allows access to caller's environment when lexical lookup fails.
  if (start_env->fallback) {
    return valk_lenv_get(start_env->fallback, key);
  }

  return valk_lval_err("LEnv: Symbol `%s` is not bound", key->str);
}

void valk_lenv_put(valk_lenv_t* env, valk_lval_t* key, valk_lval_t* val) {
  // TODO: obviously this should probably not be void ???
  // especially since i cant assert this shit
  // LVAL_ASSERT_TYPE((valk_lval_t *)nullptr, key, LVAL_SYM);
  if (valk_log_would_log(VALK_LOG_DEBUG)) {
    VALK_DEBUG("env put: %s", key->str);
  }

  // TODO(main): technically this is a failure condition for us, but the
  // return's void LVAL_ASSERT(nullptr, key->type == LVAL_SYM, "LEnv only
  // supports symbolic keys");

  // Check if symbol already exists - if so, update it
  for (size_t i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items == NULL || env->symbols.items[i] == NULL) {
      break;
    }
    if (strcmp(key->str, env->symbols.items[i]) == 0) {
      // if we found it, we update it
      // Mark value as escaping since it's being stored in environment
      val->flags |= LVAL_FLAG_ESCAPES;
      env->vals.items[i] = valk_intern(env, val);
      return;
    }
  }

  // Symbol not found - add new binding using GC heap
  // All auxiliary data (arrays, strings) allocated from GC heap for automatic
  // management

  // Allocate and copy the new key string from GC heap
  size_t slen = strlen(key->str);
  char* new_symbol = valk_mem_alloc(slen + 1);
  memcpy(new_symbol, key->str, slen + 1);

  // Mark value as escaping since it's being stored in environment
  val->flags |= LVAL_FLAG_ESCAPES;
  valk_lval_t* interned_val = valk_intern(env, val);

  // Resize arrays if needed (amortized doubling)
  if (env->symbols.count >= env->symbols.capacity) {
    size_t new_capacity =
        env->symbols.capacity == 0 ? 8 : env->symbols.capacity * 2;
    char** new_items = valk_mem_alloc(sizeof(char*) * new_capacity);
    if (env->symbols.count > 0) {
      memcpy(new_items, env->symbols.items, sizeof(char*) * env->symbols.count);
    }
    // Old array becomes unreachable and will be swept by GC
    env->symbols.items = new_items;
    env->symbols.capacity = new_capacity;
  }
  if (env->vals.count >= env->vals.capacity) {
    size_t new_capacity = env->vals.capacity == 0 ? 8 : env->vals.capacity * 2;
    valk_lval_t** new_items =
        valk_mem_alloc(sizeof(valk_lval_t*) * new_capacity);
    if (env->vals.count > 0) {
      memcpy(new_items, env->vals.items,
             sizeof(valk_lval_t*) * env->vals.count);
    }
    // Old array becomes unreachable and will be swept by GC
    env->vals.items = new_items;
    env->vals.capacity = new_capacity;
  }

  // Add to arrays
  env->symbols.items[env->symbols.count++] = new_symbol;
  env->vals.items[env->vals.count++] = interned_val;
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
    lfun->fun.builtin = _fun;
    lfun->fun.env = nullptr;
    valk_lenv_put(env, valk_lval_sym(key), lfun);
  }
}

static valk_lval_t* valk_builtin_math(valk_lval_t* lst, char* op) {
  // Verify all elements are numbers
  valk_lval_t* curr = lst;
  while (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    if (LVAL_TYPE(curr->cons.head) != LVAL_NUM) {
      LVAL_RAISE(lst, "This function only supports Numbers : %s",
                 valk_ltype_name(LVAL_TYPE(curr->cons.head)));
    }
    curr = curr->cons.tail;
  }

  valk_lval_t* first = valk_lval_pop(lst, 0);
  long result = first->num;

  if (strcmp(op, "-") == 0 && valk_lval_list_count(lst) == 0) {
    // Negate the number if there is only 1
    result = -result;
  } else {
    while (valk_lval_list_count(lst) > 0) {
      valk_lval_t* y = valk_lval_pop(lst, 0);

      if (strcmp(op, "+") == 0) {
        result += y->num;
      }
      if (strcmp(op, "-") == 0) {
        result -= y->num;
      }
      if (strcmp(op, "*") == 0) {
        result *= y->num;
      }
      if (strcmp(op, "/") == 0) {
        if (y->num > 0) {
          result /= y->num;
        } else {
          return valk_lval_err("Division By Zero");
        }
      }
    }
  }

  // Create a new immutable number with the result
  return valk_lval_num(result);
}

static valk_lval_t* valk_builtin_cons(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* arg1 = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, arg1, LVAL_CONS, LVAL_NIL);

  // Extract args without mutating
  valk_lval_t* head = valk_lval_list_nth(a, 0);
  valk_lval_t* tail = arg1;

  // Cons head onto tail
  return valk_lval_cons(head, tail);
}

static valk_lval_t* valk_builtin_len(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* arg = valk_lval_list_nth(a, 0);
  switch (LVAL_TYPE(arg)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
    case LVAL_NIL:
      return valk_lval_num(valk_lval_list_count(arg));
    case LVAL_STR: {
      size_t n = strlen(arg->str);
      return valk_lval_num((long)n);
    }
    default:
      LVAL_RAISE(a, "Actual: %s, Expected(One-Of): [Cons, Qexpr, Nil, String]",
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

  // Preserve the type (QEXPR stays QEXPR, CONS stays CONS)
  // The tail is already the right type since we're just returning the existing tail
  return arg0->cons.tail;
}

// Helper: Build list without last element (all but last)
// Preserves QEXPR vs CONS type
static valk_lval_t* valk_list_init(valk_lval_t* list, bool is_qexpr) {
  if (valk_lval_list_is_empty(list)) {
    return valk_lval_nil();  // Empty list -> empty list
  }

  // If next is nil, we're at the last element - return empty
  if (valk_lval_list_is_empty(list->cons.tail)) {
    return valk_lval_nil();
  }

  // Otherwise cons/qcons current element with init of rest
  if (is_qexpr) {
    return valk_lval_qcons(list->cons.head, valk_list_init(list->cons.tail, is_qexpr));
  } else {
    return valk_lval_cons(list->cons.head, valk_list_init(list->cons.tail, is_qexpr));
  }
}

static valk_lval_t* valk_builtin_init(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_CONS, LVAL_QEXPR);
  LVAL_ASSERT_COUNT_GT(a, arg0, 0);

  // Remove last element, preserving type
  bool is_qexpr = (LVAL_TYPE(arg0) == LVAL_QEXPR);
  return valk_list_init(arg0, is_qexpr);
}

static valk_lval_t* valk_builtin_join(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  // Don't mutate args - extract without popping
  valk_lval_t* x = arg0;
  size_t count = valk_lval_list_count(a);
  for (size_t i = 1; i < count; i++) {
    x = valk_lval_join(x, valk_lval_list_nth(a, i));
  }

  return x;
}

// range: (range start end) -> (start start+1 ... end-1)
// Generate a list of numbers from start (inclusive) to end (exclusive)
// This is a fundamental primitive that enables iteration without recursion
// Usage: (range 0 5) -> (0 1 2 3 4)
//        (range 2 4) -> (2 3)
static valk_lval_t* valk_builtin_range(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);

  long start = valk_lval_list_nth(a, 0)->num;
  long end = valk_lval_list_nth(a, 1)->num;

  // Empty range if start >= end
  if (start >= end) {
    return valk_lval_nil();
  }

  // Build list from end to start (so we can cons efficiently)
  valk_lval_t* result = valk_lval_nil();
  for (long i = end - 1; i >= start; i--) {
    result = valk_lval_cons(valk_lval_num(i), result);
  }

  return result;
}

// repeat: (repeat func n) -> executes func n times without recursion
// Usage: (repeat (\ {_} {printf "."}) 10) prints 10 dots
// This is more efficient than (map func (range 0 n)) for side effects
static valk_lval_t* valk_builtin_repeat(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);

  valk_lval_t* func = valk_lval_list_nth(a, 0);
  long count = valk_lval_list_nth(a, 1)->num;

  valk_lval_t* res[count];
  // TODO(networking): this should be a singleton
  valk_lval_t* nil = valk_lval_nil();

  // Call function count times in C loop (no stack buildup)
  for (long i = 0; i < count; i++) {
    valk_lval_t* args = valk_lval_cons(valk_lval_num(i), nil);
    res[i] = valk_lval_eval_call(e, func, args);
  }

  return valk_lval_list(res, count);
}

static valk_lval_t* valk_builtin_list(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // Convert argument list (CONS) to QEXPR (data, not code)
  // The arguments have already been evaluated, so we just change the type
  if (LVAL_TYPE(a) == LVAL_QEXPR || LVAL_TYPE(a) == LVAL_NIL) {
    return a;  // Already a QEXPR or empty
  }
  // Rebuild as QEXPR
  size_t count = valk_lval_list_count(a);
  valk_lval_t* items[count];
  valk_lval_t* curr = a;
  for (size_t i = 0; i < count; i++) {
    items[i] = curr->cons.head;
    curr = curr->cons.tail;
  }
  return valk_lval_qlist(items, count);
}

static inline valk_lval_t* valk_resolve_symbol(valk_lenv_t* e, valk_lval_t* v) {
  if (LVAL_TYPE(v) == LVAL_SYM) {
    return valk_lenv_get(e, v);
  }
  return v;
}

static valk_lval_t* valk_builtin_eval(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  // Eval can accept any type - numbers, strings, etc evaluate to themselves
  // QEXPR is converted to CONS (code) and then evaluated
  // This is how quoted data becomes executable code

  if (LVAL_TYPE(arg0) == LVAL_QEXPR) {
    // Convert QEXPR to CONS (S-expression) for evaluation
    size_t count = valk_lval_list_count(arg0);
    valk_lval_t* items[count];
    valk_lval_t* curr = arg0;
    for (size_t i = 0; i < count; i++) {
      items[i] = curr->cons.head;
      curr = curr->cons.tail;
    }
    arg0 = valk_lval_list(items, count);
  }

  return valk_lval_eval(e, arg0);
}

static valk_lval_t* valk_builtin_plus(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_math(a, "+");
}
static valk_lval_t* valk_builtin_minus(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_math(a, "-");
}
static valk_lval_t* valk_builtin_divide(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_math(a, "/");
}
static valk_lval_t* valk_builtin_multiply(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_builtin_math(a, "*");
}

static valk_lval_t* valk_builtin_def(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_GT(a, a, 1);

  valk_lval_t* first_arg = valk_lval_list_nth(a, 0);

  // Handle single symbol case: (def sym val) - wrap sym in a list
  if (LVAL_TYPE(first_arg) == LVAL_SYM) {
    first_arg = valk_lval_cons(first_arg, valk_lval_nil());
  }

  valk_lval_t* syms = first_arg;
  // Accept QEXPR for symbol lists like {x y z}
  LVAL_ASSERT_TYPE(a, syms, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  // Verify all elements in syms (starting from index 1) are symbols
  for (size_t i = 1; i < valk_lval_list_count(syms); i++) {
    valk_lval_t* sym_elem = valk_lval_list_nth(syms, i);
    LVAL_ASSERT(a, LVAL_TYPE(sym_elem) == LVAL_SYM,
                "Builtin `def` requires that symbols parameter only has "
                "symbols found: %s",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(a, i))));
  }

  LVAL_ASSERT_COUNT_EQ(a, syms, (valk_lval_list_count(a) - 1));

  for (size_t i = 0; i < valk_lval_list_count(syms); i++) {
    valk_lval_t* sym = valk_lval_list_nth(syms, i);
    valk_lval_t* val = valk_resolve_symbol(e, valk_lval_list_nth(a, i + 1));
    if (LVAL_TYPE(val) == LVAL_ERR) {
      return val;
    }
    valk_lenv_def(e, sym, val);
  }

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_put(valk_lenv_t* e, valk_lval_t* a) {
  // TODO(main): should dedupe these functions perhaps? i dont care right now
  // tho
  LVAL_ASSERT_COUNT_GT(a, a, 1);

  valk_lval_t* syms = valk_lval_list_nth(a, 0);
  // Accept QEXPR for symbol lists like {x y z}
  LVAL_ASSERT_TYPE(a, syms, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  // Verify all elements in syms (starting from index 1) are symbols
  for (size_t i = 1; i < valk_lval_list_count(syms); i++) {
    valk_lval_t* sym_elem = valk_lval_list_nth(syms, i);
    LVAL_ASSERT(a, LVAL_TYPE(sym_elem) == LVAL_SYM,
                "Builtin `def` requires that symbols parameter only has "
                "symbols found: %s",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(a, i))));
  }

  LVAL_ASSERT_COUNT_EQ(a, syms, (valk_lval_list_count(a) - 1));

  for (size_t i = 0; i < valk_lval_list_count(syms); i++) {
    valk_lval_t* val = valk_resolve_symbol(e, valk_lval_list_nth(a, i + 1));
    if (LVAL_TYPE(val) == LVAL_ERR) return val;

    valk_lval_t* sym = valk_lval_list_nth(syms, i);
    valk_lenv_put(e, sym, val);
  }

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_lambda(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* formals = valk_lval_list_nth(a, 0);
  valk_lval_t* body = valk_lval_list_nth(a, 1);

  // Accept both QEXPR and CONS for formals and body
  LVAL_ASSERT_TYPE(a, formals, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);
  LVAL_ASSERT_TYPE(a, body, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  for (size_t i = 0; i < valk_lval_list_count(formals); i++) {
    LVAL_ASSERT(a, LVAL_TYPE(valk_lval_list_nth(formals, i)) == LVAL_SYM,
                "Cannot use a non symbol[%s] for bind",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(formals, i))));
  }

  formals = valk_lval_pop(a, 0);
  body = valk_lval_pop(a, 0);

  // Use tree-walker lambda
  valk_lval_t* func = valk_lval_lambda(e, formals, body);

  return func;
}

static valk_lval_t* valk_builtin_macro(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* formals = valk_lval_list_nth(a, 0);
  valk_lval_t* body = valk_lval_list_nth(a, 1);

  // Accept both QEXPR and CONS for formals and body
  LVAL_ASSERT_TYPE(a, formals, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);
  LVAL_ASSERT_TYPE(a, body, LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  for (size_t i = 0; i < valk_lval_list_count(formals); i++) {
    LVAL_ASSERT(a, LVAL_TYPE(valk_lval_list_nth(formals, i)) == LVAL_SYM,
                "Cannot use a non symbol[%s] for bind",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(formals, i))));
  }

  formals = valk_lval_pop(a, 0);
  body = valk_lval_pop(a, 0);

  // Create lambda and set MACRO flag
  valk_lval_t* mac = valk_lval_lambda(e, formals, body);
  mac->flags |= LVAL_FLAG_MACRO;
  return mac;
}

static valk_lval_t* valk_builtin_penv(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(a);
  valk_lval_t* res = valk_lval_nil();
  for (size_t i = 0; i < e->symbols.count; i++) {
    res = valk_lval_cons(
        valk_lval_cons(valk_lval_sym(e->symbols.items[i]),
                       valk_lval_cons(e->vals.items[i], valk_lval_nil())),
        res);
  }
  return res;
}

static valk_lval_t* valk_builtin_ord(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_SYM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 2), LVAL_NUM);

  const char* op = valk_lval_list_nth(a, 0)->str;

  int r = 0;
  if (strcmp(op, ">") == 0) {
    r = (valk_lval_list_nth(a, 1)->num > valk_lval_list_nth(a, 2)->num);
  }
  if (strcmp(op, "<") == 0) {
    r = (valk_lval_list_nth(a, 1)->num < valk_lval_list_nth(a, 2)->num);
  }
  if (strcmp(op, ">=") == 0) {
    r = (valk_lval_list_nth(a, 1)->num >= valk_lval_list_nth(a, 2)->num);
  }
  if (strcmp(op, "<=") == 0) {
    r = (valk_lval_list_nth(a, 1)->num <= valk_lval_list_nth(a, 2)->num);
  }

  return valk_lval_num(r);
}
static valk_lval_t* valk_builtin_cmp(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_SYM);
  const char* op = valk_lval_list_nth(a, 0)->str;
  int r = 0;
  if (strcmp(op, "==") == 0) {
    r = valk_lval_eq(valk_lval_list_nth(a, 1), valk_lval_list_nth(a, 2));
  }
  if (strcmp(op, "!=") == 0) {
    r = !valk_lval_eq(valk_lval_list_nth(a, 1), valk_lval_list_nth(a, 2));
  }
  return valk_lval_num(r);
}

static valk_lval_t* valk_builtin_eq(valk_lenv_t* e, valk_lval_t* a) {
  return valk_builtin_cmp(e, valk_lval_cons(valk_lval_sym("=="), a));
}
static valk_lval_t* valk_builtin_ne(valk_lenv_t* e, valk_lval_t* a) {
  return valk_builtin_cmp(e, valk_lval_cons(valk_lval_sym("!="), a));
}
static valk_lval_t* valk_builtin_gt(valk_lenv_t* e, valk_lval_t* a) {
  return valk_builtin_ord(e, valk_lval_cons(valk_lval_sym(">"), a));
}
static valk_lval_t* valk_builtin_lt(valk_lenv_t* e, valk_lval_t* a) {
  return valk_builtin_ord(e, valk_lval_cons(valk_lval_sym("<"), a));
}
static valk_lval_t* valk_builtin_ge(valk_lenv_t* e, valk_lval_t* a) {
  return valk_builtin_ord(e, valk_lval_cons(valk_lval_sym(">="), a));
}
static valk_lval_t* valk_builtin_le(valk_lenv_t* e, valk_lval_t* a) {
  return valk_builtin_ord(e, valk_lval_cons(valk_lval_sym("<="), a));
}

static valk_lval_t* valk_builtin_load(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  valk_lval_t* expr = valk_parse_file(valk_lval_list_nth(a, 0)->str);
  if (LVAL_TYPE(expr) == LVAL_ERR) {
    valk_lval_println(expr);
    return expr;
  }
  // Temporarily set mode to a non-repl value during load evaluation so
  // shutdown returns an exit code (ignored by REPL) instead of stopping
  // subsystems.
  valk_lval_t* prev_mode = valk_lenv_get(e, valk_lval_sym("VALK_MODE"));
  valk_lenv_put(e, valk_lval_sym("VALK_MODE"), valk_lval_str("load"));
  valk_lval_t* last = nullptr;
  while (valk_lval_list_count(expr)) {
    valk_lval_t* x = valk_lval_eval(e, valk_lval_pop(expr, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
    } else {
      last = x;
    }
    // GC safe point: expression evaluated, collect if needed
    valk_gc_malloc_heap_t* gc_heap = (valk_gc_malloc_heap_t*)valk_thread_ctx.allocator;
    if (gc_heap->type == VALK_ALLOC_GC_HEAP && valk_gc_malloc_should_collect(gc_heap)) {
      valk_gc_malloc_collect(gc_heap);
    }
  }
  // Restore previous mode
  if (LVAL_TYPE(prev_mode) == LVAL_STR) {
    valk_lenv_put(e, valk_lval_sym("VALK_MODE"), prev_mode);
  } else {
    valk_lenv_put(e, valk_lval_sym("VALK_MODE"), valk_lval_str(""));
  }

  // Persist the last successful value for REPL/script capture
  if (last) {
    valk_lenv_put(e, valk_lval_sym("VALK_LAST_VALUE"), valk_intern(e, last));
  }

  return valk_lval_nil();
}

valk_lval_t* valk_parse_file(const char* filename) {
  FILE* f = fopen(filename, "rb");
  if (f == nullptr) {
    LVAL_RAISE(valk_lval_nil(), "Could not open file (%s)", filename);
  }

  fseek(f, 0, SEEK_END);
  size_t length = ftell(f);
  fseek(f, 0, SEEK_SET);

  if (length == UINT64_MAX) {
    fclose(f);
    LVAL_RAISE(valk_lval_nil(), "File is way too big buddy (%s)",
               filename);
  }

  char* input = calloc(length + 1, sizeof(char));
  fread(input, 1, length, f);
  fclose(f);

  int pos = 0;

  struct tmp_arr {
    valk_lval_t** items;
    size_t count;
    size_t capacity;
  } tmp = {0};

  da_init(&tmp);

  do {
    da_add(&tmp, valk_lval_read(&pos, input));
  } while ((LVAL_TYPE(tmp.items[tmp.count - 1]->cons.head) != LVAL_ERR) &&
           (input[pos] != '\0'));

  free(input);
  valk_lval_t* res = valk_lval_list(tmp.items, tmp.count);
  da_free(&tmp);
  return res;
}

static valk_lval_t* valk_builtin_if(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_CONS, LVAL_QEXPR, LVAL_NIL);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 2), LVAL_CONS, LVAL_QEXPR, LVAL_NIL);

  // Select true or false branch based on condition
  valk_lval_t* branch;
  if (valk_lval_list_nth(a, 0)->num) {
    branch = valk_lval_list_nth(a, 1);
  } else {
    branch = valk_lval_list_nth(a, 2);
  }

  // If branch is QEXPR, convert to CONS for evaluation
  if (LVAL_TYPE(branch) == LVAL_QEXPR) {
    size_t count = valk_lval_list_count(branch);
    valk_lval_t* items[count];
    valk_lval_t* curr = branch;
    for (size_t i = 0; i < count; i++) {
      items[i] = curr->cons.head;
      curr = curr->cons.tail;
    }
    branch = valk_lval_list(items, count);
  }

  // Evaluate the selected branch
  return valk_lval_eval(e, branch);
}

static valk_lval_t* valk_builtin_do(valk_lenv_t* e, valk_lval_t* a) {
  // Evaluate all expressions except the last one for side effects
  size_t count = valk_lval_list_count(a);

  if (count == 0) {
    return valk_lval_nil();
  }

  // Evaluate first n-1 expressions for side effects
  for (size_t i = 0; i < count - 1; i++) {
    valk_lval_t* expr = valk_lval_list_nth(a, i);
    // Evaluate and discard result
    valk_lval_eval(e, expr);
  }

  // Evaluate and return last expression using thread-local VM
  valk_lval_t* last = valk_lval_list_nth(a, count - 1);
  return valk_lval_eval(e, last);
}

static valk_lval_t* valk_builtin_print(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  for (size_t i = 0; i < valk_lval_list_count(a); i++) {
    valk_lval_print(valk_lval_list_nth(a, i));
    putchar(' ');
  }
  putchar('\n');
  return valk_lval_nil();
}

// Printf - formatted output like C printf
// Usage: (printf "format string" arg1 arg2 ...)
// Supports: %s (string), %d/%ld (number), %% (literal %)
static valk_lval_t* valk_builtin_printf(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GT(a, a, 0);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char* fmt = valk_lval_list_nth(a, 0)->str;
  size_t arg_idx = 1;

  for (const char* p = fmt; *p != '\0'; p++) {
    if (*p == '%' && *(p + 1) != '\0') {
      p++;
      switch (*p) {
        case 's': {
          if (arg_idx >= valk_lval_list_count(a)) {
            return valk_lval_err(
                "printf: not enough arguments for format string");
          }
          valk_lval_t* arg = valk_lval_list_nth(a, arg_idx++);
          if (LVAL_TYPE(arg) != LVAL_STR) {
            return valk_lval_err("printf: %%s requires string argument");
          }
          printf("%s", arg->str);
          break;
        }
        case 'd':
        case 'l': {
          if (*p == 'l' && *(p + 1) == 'd') {
            p++;  // Skip the 'd' in %ld
          }
          if (arg_idx >= valk_lval_list_count(a)) {
            return valk_lval_err(
                "printf: not enough arguments for format string");
          }
          valk_lval_t* arg = valk_lval_list_nth(a, arg_idx++);
          if (LVAL_TYPE(arg) != LVAL_NUM) {
            return valk_lval_err("printf: %%d/%%ld requires number argument");
          }
          printf("%ld", arg->num);
          break;
        }
        case '%':
          putchar('%');
          break;
        default:
          putchar('%');
          putchar(*p);
          break;
      }
    } else {
      putchar(*p);
    }
  }

  fflush(stdout);  // Flush output to ensure it's visible immediately
  return valk_lval_nil();
}

// Get current time in microseconds
static valk_lval_t* valk_builtin_time_us(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);  // Ignore args

  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  long us = ts.tv_sec * 1000000 + ts.tv_nsec / 1000;

  return valk_lval_num(us);
}

// stack-depth: Returns current function call depth (for TCO testing)
static valk_lval_t* valk_builtin_stack_depth(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  return valk_lval_num((long)valk_thread_ctx.call_depth);
}

static valk_lval_t* valk_builtin_error(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  valk_lval_t* err = valk_lval_err(valk_lval_list_nth(a, 0)->str);
  return err;
}

static valk_lval_t* valk_builtin_error_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_TYPE(v) == LVAL_ERR ? 1 : 0);
}

// REMOVED: ARC-related functions - no longer using atomic reference counting

// REMOVED: Old futures-based await - replaced with continuation-based
// async/await The old await used pthread_cond_wait and ARCs which we've
// eliminated

// Identity function for mock continuations - just returns first argument
static valk_lval_t* valk_builtin_identity(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  return valk_lval_list_nth(a, 0);
}

// async-shift: Capture continuation and pass to async operation
// (async-shift {k} expr) - k gets bound to the current continuation
static valk_lval_t* valk_builtin_async_shift(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  // First arg should be a QEXPR containing the symbol for continuation variable
  // e.g., {k} from (async-shift {k} {...})
  valk_lval_t* k_arg = valk_lval_list_nth(a, 0);
  valk_lval_t* k_sym;
  if (LVAL_TYPE(k_arg) == LVAL_QEXPR || LVAL_TYPE(k_arg) == LVAL_CONS) {
    // Extract symbol from list
    k_sym = k_arg->cons.head;
  } else {
    k_sym = k_arg;
  }
  LVAL_ASSERT_TYPE(a, k_sym, LVAL_SYM);

  // Create a simple mock continuation that just returns its argument
  // In real implementation, this would capture current stack
  valk_lval_t* cont = valk_mem_alloc(sizeof(valk_lval_t));
  cont->flags =
      LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(cont);
  cont->fun.builtin =
      valk_builtin_identity;  // Mock continuation just returns its argument
  cont->fun.env = NULL;
  cont->fun.formals = NULL;
  cont->fun.body = NULL;

  // Bind continuation to the symbol in environment
  valk_lenv_put(e, k_sym, cont);

  // Evaluate the async expression with continuation available
  valk_lval_t* async_expr = valk_lval_list_nth(a, 1);

  // Handle QEXPR body - may contain multiple expressions
  if (LVAL_TYPE(async_expr) == LVAL_QEXPR && valk_lval_list_count(async_expr) > 0) {
    valk_lval_t* first_elem = async_expr->cons.head;
    // Check if this looks like a sequence (first element is a list, not a symbol)
    if (valk_is_list_type(LVAL_TYPE(first_elem))) {
      // Implicit do: evaluate each expression, return last
      valk_lval_t* result = valk_lval_nil();
      valk_lval_t* curr = async_expr;
      while (!valk_lval_list_is_empty(curr)) {
        result = valk_lval_eval(e, curr->cons.head);
        if (LVAL_TYPE(result) == LVAL_ERR) {
          return result;
        }
        curr = curr->cons.tail;
      }
      return result;
    }
    // Single expression - convert QEXPR to CONS for evaluation
    size_t count = valk_lval_list_count(async_expr);
    valk_lval_t* items[count];
    valk_lval_t* curr = async_expr;
    for (size_t i = 0; i < count; i++) {
      items[i] = curr->cons.head;
      curr = curr->cons.tail;
    }
    async_expr = valk_lval_list(items, count);
  }

  return valk_lval_eval(e, async_expr);
}

// async-reset: Establish async context (delimited continuation boundary)
// (async-reset expr) - evaluates expr in async context
static valk_lval_t* valk_builtin_async_reset(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  // Evaluate the expression in an async context
  // In full implementation, this would set up delimiter/prompt
  valk_lval_t* body = valk_lval_list_nth(a, 0);

  // Handle QEXPR body - may contain multiple expressions
  if (LVAL_TYPE(body) == LVAL_QEXPR && valk_lval_list_count(body) > 0) {
    valk_lval_t* first_elem = body->cons.head;
    // Check if this looks like a sequence (first element is a list, not a symbol)
    if (valk_is_list_type(LVAL_TYPE(first_elem))) {
      // Implicit do: evaluate each expression, return last
      valk_lval_t* result = valk_lval_nil();
      valk_lval_t* curr = body;
      while (!valk_lval_list_is_empty(curr)) {
        result = valk_lval_eval(e, curr->cons.head);
        if (LVAL_TYPE(result) == LVAL_ERR) {
          return result;
        }
        curr = curr->cons.tail;
      }
      return result;
    }
    // Single expression in QEXPR - convert to CONS for evaluation
    size_t count = valk_lval_list_count(body);
    valk_lval_t* items[count];
    valk_lval_t* curr = body;
    for (size_t i = 0; i < count; i++) {
      items[i] = curr->cons.head;
      curr = curr->cons.tail;
    }
    body = valk_lval_list(items, count);
  }

  return valk_lval_eval(e, body);
}

// async-resume: Resume a continuation with a value
// (async-resume cont value) - calls continuation with value
static valk_lval_t* valk_builtin_async_resume(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* cont = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, cont, LVAL_CONT);

  valk_lval_t* value = valk_lval_list_nth(a, 1);

  // If there's a resume function, call it
  if (cont->cont.resume_fn) {
    typedef valk_lval_t* (*resume_fn_t)(valk_lenv_t*, valk_lval_t*);
    resume_fn_t fn = (resume_fn_t)cont->cont.resume_fn;
    return fn(cont->cont.env, value);
  }

  // Otherwise just return the value (simplified for now)
  return value;
}

// http2/connect-async: Async HTTP/2 connect using continuations
// (http2/connect-async aio host port cont) - calls cont when connected
static valk_lval_t* valk_builtin_http2_connect_async(valk_lenv_t* e,
                                                     valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 4);

  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, aio_ref, LVAL_REF);
  LVAL_ASSERT(a, strcmp(aio_ref->ref.type, "aio_system") == 0,
              "First arg must be aio_system");

  valk_lval_t* host = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, host, LVAL_STR);

  valk_lval_t* port = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, port, LVAL_NUM);

  valk_lval_t* cont = valk_lval_list_nth(a, 3);
  LVAL_ASSERT_TYPE(a, cont, LVAL_CONT);

  // For now, simulate async by immediately calling continuation
  // In real implementation, would store cont in libuv handle
  valk_lval_t* mock_client = valk_lval_ref("http2_client", NULL, NULL);

  // Call continuation with result
  valk_lval_t* args = valk_lval_nil();
  args = valk_lval_cons(mock_client, args);
  args = valk_lval_cons(cont, args);
  return valk_builtin_async_resume(e, args);
}

// http2/send-async: Async HTTP/2 send using continuations
// (http2/send-async request client cont) - calls cont when response received
static valk_lval_t* valk_builtin_http2_send_async(valk_lenv_t* e,
                                                  valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);

  valk_lval_t* req = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, req, LVAL_REF);

  valk_lval_t* client = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, client, LVAL_REF);

  valk_lval_t* cont = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, cont, LVAL_CONT);

  // Mock response
  valk_lval_t* mock_response = valk_lval_ref("http2_response", NULL, NULL);

  // Call continuation with response
  valk_lval_t* args = valk_lval_nil();
  args = valk_lval_cons(mock_response, args);
  args = valk_lval_cons(cont, args);
  return valk_builtin_async_resume(e, args);
}

// REMOVED: Old futures-based HTTP/2 functions (listen, connect)
// Replaced with continuation-based async versions (http2/connect-async, etc.)

static void __valk_http2_request_release(void* arg) {
  valk_http2_request_t* req = (valk_http2_request_t*)arg;
  // The request and all of its allocations live inside this arena buffer.
  free((void*)req->allocator);
}

// http2/request: (http2/request method scheme authority path) -> http2_request
static valk_lval_t* valk_builtin_http2_request(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 4);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 2), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 3), LVAL_STR);

  // Allocate a dedicated arena so the request can be freed in one go.
  // HTTP client currently reserves up to ~8MB for response body buffers.
  // Use a generous arena (8 MiB + 64 KiB) to avoid OOM in tests.
  size_t arena_bytes =
      sizeof(valk_mem_arena_t) + (8 * 1024 * 1024) + (64 * 1024);
  valk_mem_arena_t* arena = malloc(arena_bytes);
  valk_mem_arena_init(arena, arena_bytes - sizeof(*arena));

  valk_http2_request_t* req =
      valk_mem_arena_alloc(arena, sizeof(valk_http2_request_t));
  memset(req, 0, sizeof(*req));
  req->allocator = (valk_mem_allocator_t*)arena;

  // Copy strings into request arena scope
  VALK_WITH_ALLOC(req->allocator) {
    size_t len;
    len = strlen(valk_lval_list_nth(a, 0)->str);
    req->method = valk_mem_alloc(len + 1);
    memcpy(req->method, valk_lval_list_nth(a, 0)->str, len + 1);

    len = strlen(valk_lval_list_nth(a, 1)->str);
    req->scheme = valk_mem_alloc(len + 1);
    memcpy(req->scheme, valk_lval_list_nth(a, 1)->str, len + 1);

    len = strlen(valk_lval_list_nth(a, 2)->str);
    req->authority = valk_mem_alloc(len + 1);
    memcpy(req->authority, valk_lval_list_nth(a, 2)->str, len + 1);

    len = strlen(valk_lval_list_nth(a, 3)->str);
    req->path = valk_mem_alloc(len + 1);
    memcpy(req->path, valk_lval_list_nth(a, 3)->str, len + 1);

    req->body = (uint8_t*)"";
    req->bodyLen = 0;
    req->bodyCapacity = 0;
    da_init(&req->headers);
  }

  return valk_lval_ref("http2_request", req, __valk_http2_request_release);
}

// http2/request-add-header: (http2/request-add-header req name value) -> unit
static valk_lval_t* valk_builtin_http2_request_add_header(valk_lenv_t* e,
                                                          valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a,
              strcmp(valk_lval_list_nth(a, 0)->ref.type, "http2_request") == 0,
              "First arg must be http2_request ref, got %s",
              valk_lval_list_nth(a, 0)->ref.type);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 2), LVAL_STR);

  valk_http2_request_t* req = valk_lval_list_nth(a, 0)->ref.ptr;

  VALK_WITH_ALLOC(req->allocator) {
    struct valk_http2_header_t hdr;
    size_t nlen = strlen(valk_lval_list_nth(a, 1)->str);
    size_t vlen = strlen(valk_lval_list_nth(a, 2)->str);
    uint8_t* n = valk_mem_alloc(nlen + 1);
    uint8_t* v = valk_mem_alloc(vlen + 1);
    memcpy(n, valk_lval_list_nth(a, 1)->str, nlen + 1);
    memcpy(v, valk_lval_list_nth(a, 2)->str, vlen + 1);
    hdr.name = n;
    hdr.value = v;
    hdr.nameLen = nlen;
    hdr.valueLen = vlen;
    da_add(&req->headers, hdr);
  }

  return valk_lval_nil();
}

// REMOVED: Old futures-based http2/send - replaced with http2/send-async

// http2/response-body: (http2/response-body res) -> string
static valk_lval_t* valk_builtin_http2_response_body(valk_lenv_t* e,
                                                     valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 0)->ref.type, "success") == 0,
              "Argument must be a success ref holding a response");
  valk_http2_response_t* res = valk_lval_list_nth(a, 0)->ref.ptr;
  if (!res || !res->body) {
    return valk_lval_str("");
  }
  return valk_lval_str_n((const char*)res->body, res->bodyLen);
}

// http2/response-status: (http2/response-status res) -> string
static valk_lval_t* valk_builtin_http2_response_status(valk_lenv_t* e,
                                                       valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 0)->ref.type, "success") == 0,
              "Argument must be a success ref holding a response");
  valk_http2_response_t* res = valk_lval_list_nth(a, 0)->ref.ptr;
  if (!res || !res->status) return valk_lval_str("");
  return valk_lval_str((const char*)res->status);
}

// http2/response-headers: (http2/response-headers res) -> qexpr of [name value]
static valk_lval_t* valk_builtin_http2_response_headers(valk_lenv_t* e,
                                                        valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 0)->ref.type, "success") == 0,
              "Argument must be a success ref holding a response");
  valk_http2_response_t* res = valk_lval_list_nth(a, 0)->ref.ptr;
  valk_lval_t* lst = valk_lval_nil();
  if (!res) return lst;

  for (size_t i = 0; i < res->headers.count; ++i) {
    struct valk_http2_header_t* h = &res->headers.items[i];
    valk_lval_t* pair = valk_lval_nil();
    pair = valk_lval_cons(valk_lval_str((const char*)h->value), pair);
    pair = valk_lval_cons(valk_lval_str((const char*)h->name), pair);
    lst = valk_lval_cons(pair, lst);
  }
  return lst;
}

// exit: (exit code) -> never returns; terminates process with status code
static valk_lval_t* valk_builtin_exit(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  int code = (int)valk_lval_list_nth(a, 0)->num;
  fflush(stdout);
  fflush(stderr);
  exit(code);
}

// shutdown: ([code]) -> never returns; gracefully stops subsystems then exits
static valk_lval_t* valk_builtin_shutdown(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_LE(a, a, 1);
  int code = 0;
  if (valk_lval_list_count(a) == 1) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
    code = (int)valk_lval_list_nth(a, 0)->num;
  }
  // If running inside interactive REPL or test mode, ignore.
  // Also ignore if called while evaluating via `load` (module semantics).
  valk_lval_t* mode = valk_lenv_get(e, valk_lval_sym("VALK_MODE"));
  int has_mode = (LVAL_TYPE(mode) == LVAL_STR);

  // NOOP when in repl or test mode, just return the code
  if (has_mode &&
      (strcmp(mode->str, "repl") == 0 || strcmp(mode->str, "test") == 0)) {
    return valk_lval_num(code);
  }

  // Gracefully stop AIO if present in env under symbol 'aio'
  valk_lval_t* val = valk_lenv_get(e, valk_lval_sym("aio"));
  if (LVAL_TYPE(val) != LVAL_ERR && LVAL_TYPE(val) == LVAL_REF &&
      strcmp(val->ref.type, "aio_system") == 0 && val->ref.ptr) {
    valk_aio_stop((valk_aio_system_t*)val->ref.ptr);
  }

  fflush(stdout);
  fflush(stderr);
  printf("About to exit with code %d\n", code);
  fflush(stdout);
  exit(code);
}

// module: (module value) -> value; captures as VALK_LAST_MODULE
// (no module/program builtins; use VALK_LAST_VALUE set by `load`)

void valk_lenv_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "error", valk_builtin_error);
  valk_lenv_put_builtin(env, "error?", valk_builtin_error_p);
  valk_lenv_put_builtin(env, "load", valk_builtin_load);
  valk_lenv_put_builtin(env, "print", valk_builtin_print);
  valk_lenv_put_builtin(env, "printf", valk_builtin_printf);
  valk_lenv_put_builtin(env, "time-us", valk_builtin_time_us);
  valk_lenv_put_builtin(env, "stack-depth", valk_builtin_stack_depth);

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

  valk_lenv_put_builtin(env, "+", valk_builtin_plus);
  valk_lenv_put_builtin(env, "-", valk_builtin_minus);
  valk_lenv_put_builtin(env, "/", valk_builtin_divide);
  valk_lenv_put_builtin(env, "*", valk_builtin_multiply);

  valk_lenv_put_builtin(env, "def", valk_builtin_def);
  valk_lenv_put_builtin(env, "=", valk_builtin_put);
  valk_lenv_put_builtin(env, "\\", valk_builtin_lambda);
  valk_lenv_put_builtin(env, "macro", valk_builtin_macro);
  valk_lenv_put_builtin(env, "penv", valk_builtin_penv);

  // TODO(main):  Doesnt actually work lols, no idea why
  valk_lenv_put_builtin(env, "ord", valk_builtin_ord);

  valk_lenv_put_builtin(env, "if", valk_builtin_if);
  valk_lenv_put_builtin(env, "do", valk_builtin_do);
  valk_lenv_put_builtin(env, ">", valk_builtin_gt);
  valk_lenv_put_builtin(env, "<", valk_builtin_lt);
  valk_lenv_put_builtin(env, ">=", valk_builtin_ge);
  valk_lenv_put_builtin(env, "<=", valk_builtin_le);
  valk_lenv_put_builtin(env, "==", valk_builtin_eq);
  valk_lenv_put_builtin(env, "!=", valk_builtin_ne);

  // Async - Continuation-based only (futures removed)
  valk_lenv_put_builtin(env, "async-shift", valk_builtin_async_shift);
  valk_lenv_put_builtin(env, "async-reset", valk_builtin_async_reset);
  valk_lenv_put_builtin(env, "async-resume", valk_builtin_async_resume);
  valk_lenv_put_builtin(env, "http2/connect-async",
                        valk_builtin_http2_connect_async);
  valk_lenv_put_builtin(env, "http2/send-async", valk_builtin_http2_send_async);

  // HTTP/2 utility functions (kept for request/response handling)
  valk_lenv_put_builtin(env, "http2/request", valk_builtin_http2_request);
  valk_lenv_put_builtin(env, "http2/request-add-header",
                        valk_builtin_http2_request_add_header);
  valk_lenv_put_builtin(env, "http2/response-body",
                        valk_builtin_http2_response_body);
  // System utilities
  valk_lenv_put_builtin(env, "exit", valk_builtin_exit);
  valk_lenv_put_builtin(env, "shutdown", valk_builtin_shutdown);
  valk_lenv_put_builtin(env, "http2/response-status",
                        valk_builtin_http2_response_status);
  valk_lenv_put_builtin(env, "http2/response-headers",
                        valk_builtin_http2_response_headers);
  // Script classification helpers are implicit via CLI flags; no new builtins

  // HTTP
}
