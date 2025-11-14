#include "parser.h"
#include "bytecode.h"
#include "bc_vm.h"
#include "compiler.h"

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
#include "concurrency.h"
#include "gc.h"
#include "memory.h"

// GC heap allocator size check - ONLY allocate valk_lval_t structures
size_t __valk_lval_size = sizeof(valk_lval_t);

// TODO(networking): get rid of args everywhere, cause we dont need to release
// anymore
#define LVAL_RAISE(args, fmt, ...)                                       \
  do {                                                                   \
    char* _fmt =                                                         \
        valk_c_err_format((fmt), __FILE_NAME__, __LINE__, __FUNCTION__); \
    valk_lval_t* err = valk_lval_err(_fmt, ##__VA_ARGS__);               \
    free(_fmt);                                                          \
    return err;                                                          \
  } while (0)

// Helper: Set origin_allocator
// Note: GC heap zeroes memory, malloc doesn't - always set to be safe
#define VALK_SET_ORIGIN_ALLOCATOR(obj) \
  do { \
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
      free(_estr);                                                           \
      free(_fmt);                                                            \
      return err;                                                            \
    }                                                                        \
  } while (0)

#define LVAL_ASSERT_COUNT_NEQ(args, lval, _count)                   \
  LVAL_ASSERT(args, valk_lval_list_count(lval) != _count,                   \
              "Invalid argument count, Actual[%zu] != Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_EQ(args, lval, _count)                    \
  LVAL_ASSERT(args, valk_lval_list_count(lval) == _count,                   \
              "Invalid argument count, Actual[%zu] == Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_LT(args, lval, _count)                   \
  LVAL_ASSERT(args, valk_lval_list_count(lval) < _count,                   \
              "Invalid argument count, Actual[%zu] < Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_LE(args, lval, _count)                    \
  LVAL_ASSERT(args, valk_lval_list_count(lval) <= _count,                   \
              "Invalid argument count, Actual[%zu] <= Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_GT(args, lval, _count)                   \
  LVAL_ASSERT(args, valk_lval_list_count(lval) > _count,                   \
              "Invalid argument count, Actual[%zu] > Expected[%zu]", \
              valk_lval_list_count(lval), (size_t)_count)

#define LVAL_ASSERT_COUNT_GE(args, lval, _count)                    \
  LVAL_ASSERT(args, valk_lval_list_count(lval) >= _count,                   \
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
    case VALK_ALLOC_ARENA: return LVAL_ALLOC_SCRATCH;
    case VALK_ALLOC_MALLOC: return LVAL_ALLOC_GLOBAL;
    case VALK_ALLOC_GC_HEAP: return LVAL_ALLOC_HEAP;
    case VALK_ALLOC_SLAB: return LVAL_ALLOC_GLOBAL;
    default: return LVAL_ALLOC_SCRATCH;
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
    case LVAL_BC_FUN:
      return "Bytecode-Function";
    case LVAL_QEXPR:
      return "Quote-expr";
    case LVAL_SEXPR:
      return "Symbolic-expr";
    case LVAL_ERR:
      return "Error";
    case LVAL_STR:
      return "String";
    case LVAL_REF:
      return "Reference";
    case LVAL_ENV:
      return "Environment";
    case LVAL_CONS:
      return "Cons";
    case LVAL_NIL:
      return "Nil";
    case LVAL_THUNK:
      return "Thunk";
    case LVAL_UNDEFINED:
      return "UNDEFINED";
  }
  return "Unknown";
}

valk_lval_t* valk_lval_ref(const char* type, void* ptr, void (*free)(void*)) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_REF | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
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
  res->flags = LVAL_NUM | LVAL_FLAG_FROZEN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->num = x;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// TODO(main): look into UTF-8 support
valk_lval_t* valk_lval_err(const char* fmt, ...) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_ERR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
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
  res->flags = LVAL_SYM | LVAL_FLAG_FROZEN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
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
  res->flags = LVAL_STR | LVAL_FLAG_FROZEN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
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
  res->flags = LVAL_STR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
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

valk_lval_t* valk_lval_lambda(valk_lval_t* formals, valk_lval_t* body) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->fun.builtin = nullptr;
  res->fun.env = valk_lenv_empty();
  // Mark formals and body as escaping since they're captured by lambda
  formals->flags |= LVAL_FLAG_ESCAPES;
  body->flags |= LVAL_FLAG_ESCAPES;
  res->fun.formals = formals;
  res->fun.body = body;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_bc_fun(valk_chunk_t* chunk, int arity, const char* name) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_BC_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->bc_fun.chunk = chunk;
  res->bc_fun.arity = arity;
  res->bc_fun.name = name ? strdup(name) : nullptr;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_sexpr_empty(void) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_SEXPR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->cons.head = nullptr;
  res->cons.tail = nullptr;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_qexpr_empty(void) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_QEXPR;
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->cons.head = nullptr;
  res->cons.tail = nullptr;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// Cons cell constructors

valk_lval_t* valk_lval_nil(void) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_NIL | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->cons.head = nullptr;
  res->cons.tail = nullptr;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_cons(valk_lval_t* head, valk_lval_t* tail) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_CONS | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->cons.head = head;
  res->cons.tail = tail;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t* valk_lval_head(valk_lval_t* cons) {
  cons = valk_lval_resolve(cons);
  VALK_ASSERT(LVAL_TYPE(cons) == LVAL_CONS, "Expected cons cell, got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.head;
}

valk_lval_t* valk_lval_tail(valk_lval_t* cons) {
  cons = valk_lval_resolve(cons);
  VALK_ASSERT(LVAL_TYPE(cons) == LVAL_CONS, "Expected cons cell, got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.tail;
}

int valk_lval_is_nil(valk_lval_t* v) {
  v = valk_lval_resolve(v);
  return v != nullptr && LVAL_TYPE(v) == LVAL_NIL;
}

// Thunk constructor (for TCO trampoline)
valk_lval_t* valk_lval_thunk(valk_lenv_t* env, valk_lval_t* expr) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_THUNK | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->thunk.env = env;
  res->thunk.expr = expr;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// Helper: check if a list is empty (head is nullptr)
int valk_lval_list_is_empty(valk_lval_t* list) {
  if (list == nullptr) return 1;
  list = valk_lval_resolve(list);
  valk_ltype_e type = LVAL_TYPE(list);
  if (type == LVAL_NIL) return 1;
  if (type == LVAL_SEXPR || type == LVAL_QEXPR || type == LVAL_CONS) {
    return list->cons.head == nullptr;
  }
  return 0;
}

// Helper: count elements in a cons list
size_t valk_lval_list_count(valk_lval_t* list) {
  list = valk_lval_resolve(list);
  if (valk_lval_list_is_empty(list)) return 0;

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
  for (size_t i = 0; i < n && curr != nullptr && !valk_lval_list_is_empty(curr); i++) {
    curr = valk_lval_resolve(curr->cons.tail);
  }
  if (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    return curr->cons.head;
  }
  return nullptr;
}

// Convert a QEXPR to a pure CONS list (LVAL_CONS type)
valk_lval_t* valk_qexpr_to_cons(valk_lval_t* qexpr) {
  VALK_ASSERT(LVAL_TYPE(qexpr) == LVAL_QEXPR, "Expected QEXPR, got %s",
              valk_ltype_name(LVAL_TYPE(qexpr)));

  // QEXPR is already a cons-based list, just convert empty to NIL or change type to CONS
  if (qexpr->cons.head == nullptr) {
    return valk_lval_nil();
  }

  // Build a pure CONS list from the QEXPR cons list
  valk_lval_t* result = valk_lval_nil();
  valk_lval_t* curr = qexpr;

  // Collect elements first
  size_t count = 0;
  valk_lval_t* temp = curr;
  while (temp != nullptr && temp->cons.head != nullptr) {
    count++;
    temp = temp->cons.tail;
  }

  // Build cons list with LVAL_CONS type
  for (size_t i = count; i > 0; i--) {
    // Walk to i-1'th element
    temp = qexpr;
    for (size_t j = 0; j < i - 1; j++) {
      temp = temp->cons.tail;
    }
    result = valk_lval_cons(temp->cons.head, result);
  }

  return result;
}

// Convert a pure CONS list to QEXPR
valk_lval_t* valk_cons_to_qexpr(valk_lval_t* cons) {
  // Handle NULL or NIL
  if (cons == nullptr || valk_lval_is_nil(cons)) {
    return valk_lval_qexpr_empty();
  }

  // If it's already a QEXPR, return it
  if (LVAL_TYPE(cons) == LVAL_QEXPR) {
    return cons;
  }

  // If it's a SEXPR, convert to QEXPR
  // Always make a shallow copy - type conversions should never mutate the original
  // (function bodies, parameters are immutable and might be referenced elsewhere)
  if (LVAL_TYPE(cons) == LVAL_SEXPR) {
    valk_lval_t* result = valk_lval_copy(cons);
    result->flags = ((result->flags & LVAL_FLAGS_MASK) | LVAL_QEXPR);
    return result;
  }

  // Build QEXPR from CONS
  valk_lval_t* result = nullptr;
  valk_lval_t* curr = cons;

  while (LVAL_TYPE(curr) == LVAL_CONS && curr->cons.head != nullptr) {
    if (result == nullptr) {
      // First element
      result = valk_mem_alloc(sizeof(valk_lval_t));
      result->flags = LVAL_QEXPR;
      VALK_SET_ORIGIN_ALLOCATOR(result);
      result->cons.head = curr->cons.head;
      result->cons.tail = nullptr;
      valk_capture_trace(VALK_TRACE_NEW, 1, result);
    } else {
      // Find the last node and extend
      valk_lval_t* last = result;
      while (last->cons.tail != nullptr && last->cons.tail->cons.head != nullptr) {
        last = last->cons.tail;
      }
      valk_lval_t* new_node = valk_mem_alloc(sizeof(valk_lval_t));
      new_node->flags = LVAL_QEXPR;
      VALK_SET_ORIGIN_ALLOCATOR(new_node);
      new_node->cons.head = curr->cons.head;
      new_node->cons.tail = nullptr;
      valk_capture_trace(VALK_TRACE_NEW, 1, new_node);
      last->cons.tail = new_node;
    }
    curr = curr->cons.tail;
  }

  if (result == nullptr) {
    return valk_lval_qexpr_empty();
  }

  return result;
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
    case LVAL_SEXPR:
    case LVAL_QEXPR:
    case LVAL_CONS:
      // All list types now use cons structure
      valk_lval_freeze(lval->cons.head);
      valk_lval_freeze(lval->cons.tail);
      break;
    case LVAL_FUN:
      if (!lval->fun.builtin) {
        // Only freeze body, NOT formals - formals get mutated during function calls
        // (see valk_lval_eval_call line 910 where formals are popped)
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
// and it should be shallow copy" - all child pointers are aliased, not recursively copied
valk_lval_t* valk_lval_copy(valk_lval_t* lval) {
  if (lval == nullptr) return nullptr;
  lval = valk_lval_resolve(lval);  // Resolve forwarding pointers

  // Zero-copy optimization: Frozen heap values are immutable and persistent
  // GC heap values won't be freed by arena resets, safe to alias directly
  if (LVAL_IS_FROZEN(lval) && LVAL_ALLOC(lval) == LVAL_ALLOC_HEAP) {
    return lval;  // Alias immutable heap value - no copy needed
  }

  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));

  // Keep only type and semantic flags (not allocation flags from source)
  res->flags = lval->flags & (LVAL_TYPE_MASK | LVAL_FLAG_FROZEN | LVAL_FLAG_ESCAPES);
  // NOTE: Don't overwrite origin_allocator - the allocator already set it correctly!
  // (GC heap allocator sets it to heap pointer, which is the authoritative source)
  // Overwriting it with valk_thread_ctx.allocator can introduce corruption if
  // valk_thread_ctx.allocator was corrupted.
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
        res->fun.body = valk_lval_resolve(lval->fun.body);  // Alias body (resolve forwarding)
        res->fun.formals = valk_lval_resolve(lval->fun.formals);  // Alias formals (resolve forwarding)
      }
      break;
    case LVAL_QEXPR:
    case LVAL_SEXPR:
    case LVAL_CONS:
      // SHALLOW COPY: Alias head/tail (resolve forwarding first)
      // Don't recursively copy - immutability means we can safely alias
      res->cons.head = valk_lval_resolve(lval->cons.head);
      res->cons.tail = valk_lval_resolve(lval->cons.tail);
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
    case LVAL_NIL:
      // Nil has no data to copy
      res->cons.head = nullptr;
      res->cons.tail = nullptr;
      break;
    case LVAL_THUNK:
      // Shallow copy thunk fields (resolve forwarding)
      res->thunk.env = lval->thunk.env;
      res->thunk.expr = valk_lval_resolve(lval->thunk.expr);
      break;
    case LVAL_UNDEFINED:
      break;
    case LVAL_ENV:
      res->env = lval->env;
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
  if (val != nullptr && LVAL_IS_FROZEN(val) && LVAL_ALLOC(val) == LVAL_ALLOC_HEAP) {
    return val;  // Zero-copy sharing of immutable heap value
  }

  // Check if value is already in the target allocator
  if (val != nullptr && val->origin_allocator == env->allocator) {
    return val;  // Already in the right place - can alias
  }

  // Value is from a different allocator (e.g., scratch arena)
  // We need to copy it to the target allocator (e.g., GC heap)
  // IMPORTANT: Save and restore thread allocator to avoid intermediate allocations in scratch
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
    case LVAL_QEXPR:
    case LVAL_SEXPR:
    case LVAL_CONS:
      // All list types now use cons structure - compare recursively
      // Handle empty lists (both head and tail nullptr)
      if (x->cons.head == nullptr && y->cons.head == nullptr) {
        return 1;  // Both empty
      }
      if (x->cons.head == nullptr || y->cons.head == nullptr) {
        return 0;  // One empty, one not
      }
      // Both non-empty: compare head and tail
      return valk_lval_eq(x->cons.head, y->cons.head) &&
             valk_lval_eq(x->cons.tail, y->cons.tail);
    case LVAL_NIL:
      return 1;  // All nils are equal
    case LVAL_REF:
      return (x->ref.ptr == y->ref.ptr) && (x->ref.free == y->ref.free);
    case LVAL_ENV:
      VALK_RAISE(
          "LVAL is LENV, comparison unimplemented, something went wrong");
      break;
    case LVAL_UNDEFINED:
      VALK_RAISE("LVAL is undefined, something went wrong");
      break;
  }

  return 0;
}

// Bytecode evaluation: compile and run with bytecode VM
static valk_lval_t* valk_lval_eval_bytecode(valk_lenv_t* env, valk_lval_t* lval) {
  // Compile the expression to bytecode
  valk_chunk_t* chunk = valk_compile(lval, env);

  // Create VM and run
  valk_bc_vm_t vm;
  vm.chunk = NULL;
  vm.ip = NULL;
  vm.stack_top = vm.stack;
  vm.frame_count = 0;
  vm.globals = env;  // Use the passed-in environment (which already has builtins)

  valk_bc_vm_result_e result = valk_bc_vm_run(&vm, chunk);

  // Get result from stack
  valk_lval_t* ret_val;
  if (result == BC_VM_OK && vm.stack_top > vm.stack) {
    ret_val = vm.stack[0];  // Top of stack is the result
  } else if (result == BC_VM_RUNTIME_ERROR) {
    ret_val = valk_lval_err("Bytecode runtime error");
  } else {
    ret_val = valk_lval_nil();  // Empty result
  }

  valk_bc_vm_free(&vm);
  // Note: Don't free chunk yet as it might be referenced by functions
  // TODO: Add proper cleanup when functions are GC'd

  return ret_val;
}

valk_lval_t* valk_lval_eval(valk_lenv_t* env, valk_lval_t* lval) {
  // Check if bytecode mode is enabled
  static int use_bytecode = -1;  // -1 = uninitialized, 0 = no, 1 = yes
  if (use_bytecode == -1) {
    const char* mode = getenv("VALK_BYTECODE");
    use_bytecode = (mode && strcmp(mode, "1") == 0) ? 1 : 0;
    if (use_bytecode) {
      fprintf(stderr, "Bytecode VM enabled (O(1) TCO)\n");
    }
  }

  // Use bytecode VM if enabled
  if (use_bytecode) {
    return valk_lval_eval_bytecode(env, lval);
  }

  // Otherwise use tree-walker (with thunk-based TCO)
  // Trampoline loop: Keep evaluating thunks until we get a final value
  // This enables proper TCO for tail calls inside control flow (if, do, let)
  size_t trampoline_iterations = 0;
  while (1) {
    // Safety check: NULL values should never reach here
    if (lval == nullptr) {
      return valk_lval_err("Internal error: NULL value in eval");
    }

    // GC safepoint: Collect garbage periodically during long-running loops
    // This prevents OOM during deeply recursive tail calls
    if (++trampoline_iterations % 10 == 0) {
      valk_mem_allocator_t* allocator = valk_thread_ctx.allocator;
      if (allocator && allocator->type == VALK_ALLOC_GC_HEAP) {
        valk_gc_malloc_heap_t* heap = (valk_gc_malloc_heap_t*)allocator;
        if (valk_gc_malloc_should_collect(heap)) {
          // Update root to current environment before collecting
          // This ensures we mark from the active execution context
          valk_gc_malloc_set_root(heap, env);
          valk_gc_malloc_collect(heap);
        }
      }
    }

    valk_ltype_e type = LVAL_TYPE(lval);

    // If it's a thunk, unpack and continue evaluating the expression
    if (type == LVAL_THUNK) {
      env = lval->thunk.env;
      lval = lval->thunk.expr;
      continue;  // Loop back to evaluate the expression (might be another thunk)
    }

    // Normal evaluation (not a thunk)
    if (type == LVAL_SYM) {
      lval = valk_lenv_get(env, lval);
      // If symbol resolved to a thunk, continue loop to evaluate it
      // Otherwise we're done
      if (LVAL_TYPE(lval) == LVAL_THUNK) {
        continue;
      }
      return lval;
    }
    if (type == LVAL_SEXPR) {
      lval = valk_lval_eval_sexpr(env, lval);
      // If sexpr evaluated to a thunk, continue loop to evaluate it
      // Otherwise we're done
      if (LVAL_TYPE(lval) == LVAL_THUNK) {
        continue;
      }
      return lval;
    }

    // Base case: return the final value (not a thunk, symbol, or sexpr)
    return lval;
  }
}

valk_lval_t* valk_lval_eval_sexpr(valk_lenv_t* env, valk_lval_t* sexpr) {
  LVAL_ASSERT_TYPE(sexpr, sexpr, LVAL_SEXPR);
  size_t n = valk_lval_list_count(sexpr);
  if (n == 0) {
    return sexpr;
  }

  // Always evaluate the first element (the function/operator)
  valk_lval_t* curr = sexpr;
  valk_lval_t* first = valk_lval_eval(env, curr->cons.head);
  if (LVAL_TYPE(first) == LVAL_ERR) {
    return first;
  }

  if (n == 1) {
    return first;
  }

  // Check if the function is a macro (receives unevaluated arguments)
  bool is_macro = (LVAL_TYPE(first) == LVAL_FUN) && (first->flags & LVAL_FLAG_MACRO);

  // Evaluate remaining arguments (or leave as QEXPR for macros)
  valk_lval_t** vals = valk_mem_alloc(sizeof(valk_lval_t*) * n);
  vals[0] = first;
  curr = sexpr->cons.tail;

  for (size_t i = 1; i < n; ++i) {
    if (is_macro) {
      // For macros, wrap each argument as QEXPR (unevaluated)
      valk_lval_t* arg = curr->cons.head;
      valk_lval_t* quoted = valk_lval_qexpr_empty();
      valk_lval_add(quoted, arg);
      vals[i] = quoted;
    } else {
      // For normal functions, evaluate arguments
      vals[i] = valk_lval_eval(env, curr->cons.head);
      if (LVAL_TYPE(vals[i]) == LVAL_ERR) {
        return vals[i];
      }
    }
    curr = curr->cons.tail;
  }

  if (LVAL_TYPE(vals[0]) != LVAL_FUN) {
    // Sequence semantics: return last evaluated value
    return vals[n - 1];
  }

  // Construct a fresh args list without mutating the original
  valk_lval_t* args = valk_lval_sexpr_empty();
  for (size_t i = 1; i < n; ++i) {
    valk_lval_add(args, vals[i]);
  }

  valk_lval_t* fun = vals[0];
  if (valk_log_would_log(VALK_LOG_TRACE)) {
    VALK_TRACE("EVAL call with args:");
    valk_lval_println(args);
  }
  valk_lval_t* result = valk_lval_eval_call(env, fun, args);
  return result;
}

valk_lval_t* valk_lval_eval_call(valk_lenv_t* env, valk_lval_t* func,
                                 valk_lval_t* args) {
  // Tail call optimization: loop instead of recursing
  tco_restart:

  LVAL_ASSERT_TYPE(args, func, LVAL_FUN);
  LVAL_ASSERT_TYPE(args, args, LVAL_SEXPR);

  if (func->fun.builtin) {
    return func->fun.builtin(env, args);
  }

  // Immutable function application - NO COPYING, NO MUTATION
  // Walk formals and args together, creating bindings in new environment

  size_t given = valk_lval_list_count(args);
  size_t num_formals = valk_lval_list_count(func->fun.formals);

  // Create new environment for bindings
  // Since lambda environments are empty in this implementation, we need to link
  // to the calling environment for variable lookup.
  // Note: This gives dynamic scoping behavior, but that's how the current system works.
  valk_lenv_t* call_env = valk_lenv_empty();
  if (func->fun.env && func->fun.env->symbols.count > 0) {
    // Function has captured bindings - use them
    call_env->parent = func->fun.env;
  } else {
    // Function has no captures - use calling environment directly
    call_env->parent = env;
  }

  // Walk formals and args together without mutation
  valk_lval_t* formal_iter = func->fun.formals;
  valk_lval_t* arg_iter = args;
  valk_lval_t* remaining_formals = valk_lval_qexpr_empty();
  bool saw_varargs = false;

  while (!valk_lval_list_is_empty(formal_iter) && !valk_lval_list_is_empty(arg_iter)) {
    valk_lval_t* formal_sym = formal_iter->cons.head;

    // Handle varargs
    if (LVAL_TYPE(formal_sym) == LVAL_SYM && strcmp(formal_sym->str, "&") == 0) {
      // Next formal is the varargs name
      formal_iter = formal_iter->cons.tail;
      if (valk_lval_list_is_empty(formal_iter)) {
        return valk_lval_err("Invalid function format: & not followed by varargs name");
      }
      valk_lval_t* varargs_sym = formal_iter->cons.head;
      valk_lval_t* varargs_list = valk_builtin_list(nullptr, arg_iter);
      valk_lenv_put(call_env, varargs_sym, varargs_list);
      saw_varargs = true;
      arg_iter = valk_lval_nil();  // All remaining args consumed
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
        return valk_lval_err("Invalid function format: & not followed by varargs name");
      }
      valk_lval_t* varargs_sym = formal_iter->cons.head;
      valk_lenv_put(call_env, varargs_sym, valk_lval_qexpr_empty());
      formal_iter = formal_iter->cons.tail;
    }

    // If still have unbound formals, return partially applied function
    if (!valk_lval_list_is_empty(formal_iter)) {
      valk_lval_t* partial = valk_mem_alloc(sizeof(valk_lval_t));
      partial->flags = LVAL_FUN;
      VALK_SET_ORIGIN_ALLOCATOR(partial);
      partial->fun.builtin = nullptr;
      partial->fun.env = call_env;
      partial->fun.formals = formal_iter;  // Remaining formals (immutable, can alias)
      partial->fun.body = func->fun.body;  // Body (immutable, can alias)
      return partial;
    }
  }

  // All formals bound - evaluate body
  valk_lval_t* wrapped_body = valk_lval_add(valk_lval_sexpr_empty(), func->fun.body);
  return valk_builtin_eval(call_env, wrapped_body);
}

valk_lval_t* valk_lval_pop(valk_lval_t* lval, size_t i) {
  // Pop i-th element from a cons-based list
  lval = valk_lval_resolve(lval);
  size_t count = valk_lval_list_count(lval);
  LVAL_ASSERT((valk_lval_t*)0, i < count,
              "Cant pop from list at invalid position: [%zu] total length: [%zu]",
              i, count);
  LVAL_ASSERT((valk_lval_t*)0, count > 0, "Cant pop from empty");

  // Check if value is frozen (immutable)
  valk_lval_assert_mutable(lval);

  if (i == 0) {
    // Pop first element
    valk_lval_t* cell = lval->cons.head;
    // Move tail's contents into lval
    if (lval->cons.tail != nullptr && !valk_lval_list_is_empty(lval->cons.tail)) {
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

valk_lval_t* valk_lval_add(valk_lval_t* lval, valk_lval_t* cell) {
  // Add element to end of cons-based list
  lval = valk_lval_resolve(lval);
  LVAL_ASSERT_TYPE(lval, lval, LVAL_SEXPR, LVAL_QEXPR);
  LVAL_ASSERT(lval, cell != nullptr, "Adding nullptr to LVAL is not allowed");

  // Check if value is frozen (immutable)
  valk_lval_assert_mutable(lval);

  // If list is empty, set head
  if (valk_lval_list_is_empty(lval)) {
    lval->cons.head = cell;
    lval->cons.tail = nullptr;  // Empty tail
    return lval;
  }

  // Traverse to end of list
  valk_lval_t* curr = lval;
  while (curr->cons.tail != nullptr && !valk_lval_list_is_empty(curr->cons.tail)) {
    curr = valk_lval_resolve(curr->cons.tail);
  }

  // Add new node at end
  valk_lval_t* new_node = valk_mem_alloc(sizeof(valk_lval_t));
  new_node->flags = LVAL_TYPE(lval);  // Preserve list type (SEXPR or QEXPR)
  VALK_SET_ORIGIN_ALLOCATOR(new_node);
  new_node->cons.head = cell;
  new_node->cons.tail = nullptr;
  valk_capture_trace(VALK_TRACE_NEW, 1, new_node);

  curr->cons.tail = new_node;

  return lval;
}

valk_lval_t* valk_lval_join(valk_lval_t* a, valk_lval_t* b) {
  // Create new QEXPR instead of mutating a
  a = valk_lval_resolve(a);
  b = valk_lval_resolve(b);
  valk_lval_t* res = valk_lval_qexpr_empty();

  // Copy all elements from a
  valk_lval_t* curr = a;
  while (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    valk_lval_add(res, curr->cons.head);
    curr = valk_lval_resolve(curr->cons.tail);
  }

  // Copy all elements from b
  curr = b;
  while (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    valk_lval_add(res, curr->cons.head);
    curr = valk_lval_resolve(curr->cons.tail);
  }

  return res;
}

void valk_lval_print(valk_lval_t* val) {
  if (val == nullptr) {
    return;
  }
  switch (LVAL_TYPE(val)) {
    case LVAL_NUM:
      printf("Num[%li]", val->num);
      break;
    case LVAL_SYM:
      printf("Sym[%s]", val->str);
      break;
      // TODO(main): code duplication here, do i actually care??
    case LVAL_QEXPR: {
      printf("Qexpr{ ");
      valk_lval_t* curr = val;
      int first = 1;
      while (curr != nullptr && !valk_lval_list_is_empty(curr)) {
        if (!first) putchar(' ');
        valk_lval_print(curr->cons.head);
        curr = curr->cons.tail;
        first = 0;
      }
      printf(" }");
      break;
    }
    case LVAL_SEXPR: {
      printf("Sexpr( ");
      valk_lval_t* curr = val;
      int first = 1;
      while (curr != nullptr && !valk_lval_list_is_empty(curr)) {
        if (!first) putchar(' ');
        valk_lval_print(curr->cons.head);
        curr = curr->cons.tail;
        first = 0;
      }
      printf(" )");
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
      // We want to escape the string before printing
      printf("String[");
      for (size_t i = 0; i < strlen(val->str); ++i) {
        if (strchr(lval_str_escapable, val->str[i])) {
          printf("%s", valk_lval_str_escape(val->str[i]));
        } else {
          putchar(val->str[i]);
        }
      }
      printf("]");
      break;
    }
    case LVAL_CONS: {
      printf("(");
      valk_lval_t* curr = val;
      while (LVAL_TYPE(curr) == LVAL_CONS) {
        valk_lval_print(curr->cons.head);
        curr = curr->cons.tail;
        if (LVAL_TYPE(curr) == LVAL_CONS) {
          printf(" ");
        }
      }
      if (!valk_lval_is_nil(curr)) {
        // Improper list
        printf(" . ");
        valk_lval_print(curr);
      }
      printf(")");
      break;
    }
    case LVAL_NIL:
      printf("()");
      break;
    case LVAL_REF:
      printf("Reference[%s:%p]", val->ref.type, val->ref.ptr);
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
               "0123456789_+-*\\/=<>!&",
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

  if (strchr("({", s[*i])) {
    res = valk_lval_read_expr(i, s);
  }
  // Lets check for a symbol
  else if (strchr("abcdefghijklmnopqrstuvwxyz"
                  "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                  "0123456789_+-*\\/=<>!&",
                  s[*i])) {
    res = valk_lval_read_sym(i, s);
  } else if (s[*i] == '"') {
    res = valk_lval_read_str(i, s);
  } else {
    res = valk_lval_err("[offset: %ld] Unexpected character %c", *i, s[*i]);
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
  valk_ltype_e type;
  if (s[(*i)++] == '{') {
    type = LVAL_QEXPR;
    end = '}';
  } else {
    type = LVAL_SEXPR;
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
          "[offset: %d] Unexpected end of input reading expr, while looking for `%c`",
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
      valk_lval_t** new_elements = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);
      memcpy(new_elements, elements, sizeof(valk_lval_t*) * count);
      // Old array becomes unreachable and will be swept by GC
      elements = new_elements;
    }
    elements[count++] = x;
  }
  (*i)++;

  // Build cons list from right to left
  valk_lval_t* result = nullptr;
  for (size_t j = count; j > 0; j--) {
    if (result == nullptr) {
      // First iteration: create list with one element
      result = valk_mem_alloc(sizeof(valk_lval_t));
      result->flags = type;
      VALK_SET_ORIGIN_ALLOCATOR(result);
      result->cons.head = elements[j - 1];
      result->cons.tail = nullptr;  // Empty tail
      valk_capture_trace(VALK_TRACE_NEW, 1, result);
    } else {
      // Subsequent iterations: cons element onto existing list
      valk_lval_t* new_node = valk_mem_alloc(sizeof(valk_lval_t));
      new_node->flags = type;
      VALK_SET_ORIGIN_ALLOCATOR(new_node);
      new_node->cons.head = elements[j - 1];
      new_node->cons.tail = result;
      valk_capture_trace(VALK_TRACE_NEW, 1, new_node);
      result = new_node;
    }
  }

  // If no elements, return empty list
  if (result == nullptr) {
    result = valk_mem_alloc(sizeof(valk_lval_t));
    result->flags = type;
    VALK_SET_ORIGIN_ALLOCATOR(result);
    result->cons.head = nullptr;
    result->cons.tail = nullptr;
    valk_capture_trace(VALK_TRACE_NEW, 1, result);
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
  // All auxiliary data (arrays, strings) allocated from GC heap for automatic management

  // Allocate and copy the new key string from GC heap
  size_t slen = strlen(key->str);
  char* new_symbol = valk_mem_alloc(slen + 1);
  memcpy(new_symbol, key->str, slen + 1);

  // Mark value as escaping since it's being stored in environment
  val->flags |= LVAL_FLAG_ESCAPES;
  valk_lval_t* interned_val = valk_intern(env, val);

  // Resize arrays if needed (amortized doubling)
  if (env->symbols.count >= env->symbols.capacity) {
    size_t new_capacity = env->symbols.capacity == 0 ? 8 : env->symbols.capacity * 2;
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
    valk_lval_t** new_items = valk_mem_alloc(sizeof(valk_lval_t*) * new_capacity);
    if (env->vals.count > 0) {
      memcpy(new_items, env->vals.items, sizeof(valk_lval_t*) * env->vals.count);
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
    lfun->flags = LVAL_FUN;
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
  LVAL_ASSERT_TYPE(a, arg1, LVAL_QEXPR);

  // Extract args without mutating
  valk_lval_t* head = valk_lval_list_nth(a, 0);
  valk_lval_t* tail_qexpr = arg1;

  // Convert tail to cons list, prepend head (one allocation!), convert back
  valk_lval_t* tail_cons = valk_qexpr_to_cons(tail_qexpr);
  valk_lval_t* result_cons = valk_lval_cons(head, tail_cons);
  return valk_cons_to_qexpr(result_cons);
}

static valk_lval_t* valk_builtin_len(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* arg = valk_lval_list_nth(a, 0);
  switch (LVAL_TYPE(arg)) {
    case LVAL_QEXPR:
      return valk_lval_num(valk_lval_list_count(arg));
    case LVAL_STR: {
      size_t n = strlen(arg->str);
      return valk_lval_num((long)n);
    }
    default:
      LVAL_RAISE(a, "Actual: %s, Expected(One-Of): [Quote-expr, String]",
                 valk_ltype_name(LVAL_TYPE(arg)));
      return valk_lval_err("len invalid type");
  }
}

static valk_lval_t* valk_builtin_head(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT(a, valk_lval_list_count(a) == 1,
              "Builtin `head` passed too many arguments");
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_QEXPR);
  LVAL_ASSERT_COUNT_GT(a, arg0, 0);

  // Extract head (already cons-based!), convert to QEXPR
  valk_lval_t* head_cons = valk_lval_cons(arg0->cons.head, valk_lval_nil());
  return valk_cons_to_qexpr(head_cons);
}

static valk_lval_t* valk_builtin_tail(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT(a, valk_lval_list_count(a) == 1,
              "Builtin `tail` passed too many arguments");
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_QEXPR);
  LVAL_ASSERT(a, !valk_lval_list_is_empty(arg0),
              "Builtin `tail` cannot operate on `{}`");

  // Extract tail (already cons-based!), convert back to QEXPR
  valk_lval_t* result = valk_cons_to_qexpr(arg0->cons.tail);

  return result;
}

// Helper: Build cons list without last element (all but last)
static valk_lval_t* valk_cons_init(valk_lval_t* cons) {
  if (valk_lval_is_nil(cons)) {
    return valk_lval_nil();  // Empty list -> empty list
  }

  // If next is nil, we're at the last element - return empty
  if (valk_lval_is_nil(cons->cons.tail)) {
    return valk_lval_nil();
  }

  // Otherwise cons current element with init of rest
  return valk_lval_cons(cons->cons.head, valk_cons_init(cons->cons.tail));
}

static valk_lval_t* valk_builtin_init(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_QEXPR);
  LVAL_ASSERT_COUNT_GT(a, arg0, 0);

  // Remove last element - already cons-based
  valk_lval_t* cons = valk_qexpr_to_cons(arg0);
  valk_lval_t* init_cons = valk_cons_init(cons);
  return valk_cons_to_qexpr(init_cons);
}

static valk_lval_t* valk_builtin_join(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  valk_lval_t* arg0 = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg0, LVAL_QEXPR);

  // Don't mutate args - extract without popping
  valk_lval_t* x = arg0;
  size_t count = valk_lval_list_count(a);
  for (size_t i = 1; i < count; i++) {
    x = valk_lval_join(x, valk_lval_list_nth(a, i));
  }

  return x;
}

// range: (range start end) -> {start start+1 ... end-1}
// Generate a list of numbers from start (inclusive) to end (exclusive)
// This is a fundamental primitive that enables iteration without recursion
// Usage: (range 0 5) -> {0 1 2 3 4}
//        (range 2 4) -> {2 3}
static valk_lval_t* valk_builtin_range(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);

  long start = valk_lval_list_nth(a, 0)->num;
  long end = valk_lval_list_nth(a, 1)->num;

  // Empty range if start >= end
  if (start >= end) {
    return valk_lval_qexpr_empty();
  }

  // Build list from end to start (so we can cons efficiently)
  // Create proper QEXPR cons cells
  valk_lval_t* result = valk_lval_qexpr_empty();
  for (long i = end - 1; i >= start; i--) {
    valk_lval_t* num = valk_lval_num(i);
    valk_lval_t* new_node = valk_mem_alloc(sizeof(valk_lval_t));
    new_node->flags = LVAL_QEXPR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
    VALK_SET_ORIGIN_ALLOCATOR(new_node);
    new_node->cons.head = num;
    new_node->cons.tail = result;
    valk_capture_trace(VALK_TRACE_NEW, 1, new_node);
    result = new_node;
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

  // Call function count times in C loop (no stack buildup)
  for (long i = 0; i < count; i++) {
    valk_lval_t* args = valk_lval_sexpr_empty();
    valk_lval_add(args, valk_lval_num(i));
    valk_lval_t* result = valk_lval_eval_call(e, func, args);
    // Ignore result, we're just calling for side effects
    (void)result;
  }

  return valk_lval_qexpr_empty();
}

static valk_lval_t* valk_builtin_list(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);

  // Convert SEXPR to QEXPR
  // Always make a shallow copy - type conversions should never mutate the original
  // (function bodies, parameters are immutable and might be referenced elsewhere)
  valk_lval_t* result = valk_lval_copy(a);
  result->flags = ((result->flags & LVAL_FLAGS_MASK) | LVAL_QEXPR);
  return result;
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
  LVAL_ASSERT_TYPE(a, arg0, LVAL_QEXPR);

  valk_lval_t* v = valk_lval_pop(a, 0);

  // Convert QEXPR to SEXPR for evaluation
  // Always make a shallow copy - type conversions should never mutate the original
  // (function bodies, parameters are immutable and might be referenced elsewhere)
  v = valk_lval_copy(v);
  v->flags = ((v->flags & LVAL_FLAGS_MASK) | LVAL_SEXPR);

  // Return thunk for TCO - function bodies are in tail position when called from eval_call
  // The trampoline will unwrap this without adding a stack frame
  return valk_lval_thunk(e, v);
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

  valk_lval_t* syms = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, syms, LVAL_QEXPR);

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
    valk_lenv_def(e, valk_lval_list_nth(syms, i), val);
  }

  return valk_lval_sexpr_empty();
}

static valk_lval_t* valk_builtin_put(valk_lenv_t* e, valk_lval_t* a) {
  // TODO(main): should dedupe these functions perhaps? i dont care right now
  // tho
  LVAL_ASSERT_COUNT_GT(a, a, 1);

  valk_lval_t* syms = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, syms, LVAL_QEXPR);

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
    valk_lenv_put(e, valk_lval_list_nth(syms, i), val);
  }

  return valk_lval_sexpr_empty();
}

static valk_lval_t* valk_builtin_lambda(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* formals = valk_lval_list_nth(a, 0);
  valk_lval_t* body = valk_lval_list_nth(a, 1);

  LVAL_ASSERT_TYPE(a, formals, LVAL_QEXPR);
  LVAL_ASSERT_TYPE(a, body, LVAL_QEXPR);

  for (size_t i = 0; i < valk_lval_list_count(formals); i++) {
    LVAL_ASSERT(a, LVAL_TYPE(valk_lval_list_nth(formals, i)) == LVAL_SYM,
                "Cannot use a non symbol[%s] for bind",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(formals, i))));
  }

  formals = valk_lval_pop(a, 0);
  body = valk_lval_pop(a, 0);

  return valk_lval_lambda(formals, body);
}

static valk_lval_t* valk_builtin_macro(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* formals = valk_lval_list_nth(a, 0);
  valk_lval_t* body = valk_lval_list_nth(a, 1);

  LVAL_ASSERT_TYPE(a, formals, LVAL_QEXPR);
  LVAL_ASSERT_TYPE(a, body, LVAL_QEXPR);

  for (size_t i = 0; i < valk_lval_list_count(formals); i++) {
    LVAL_ASSERT(a, LVAL_TYPE(valk_lval_list_nth(formals, i)) == LVAL_SYM,
                "Cannot use a non symbol[%s] for bind",
                valk_ltype_name(LVAL_TYPE(valk_lval_list_nth(formals, i))));
  }

  formals = valk_lval_pop(a, 0);
  body = valk_lval_pop(a, 0);

  // Create lambda and set MACRO flag
  valk_lval_t* mac = valk_lval_lambda(formals, body);
  mac->flags |= LVAL_FLAG_MACRO;
  return mac;
}

static valk_lval_t* valk_builtin_penv(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  valk_lval_t* res = valk_lval_qexpr_empty();
  for (size_t i = 0; i < e->symbols.count; i++) {
    valk_lval_t* qexpr = valk_lval_qexpr_empty();
    // TODO(main): So each of these can fail, in that case we want to free the
    // intermediates, im too lazy to do that tho, so memory leaks n such.
    // really i can also check the pre-conditions here to make sure we dont
    // even allocate anything if they arent met
    valk_lval_add(qexpr, valk_lval_sym(e->symbols.items[i]));
    valk_lval_add(qexpr, e->vals.items[i]);
    valk_lval_add(res, qexpr);
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
  valk_lval_t* tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("=="));
  return valk_builtin_cmp(e, valk_lval_join(tmp, a));
}
static valk_lval_t* valk_builtin_ne(valk_lenv_t* e, valk_lval_t* a) {
  valk_lval_t* tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("!="));
  return valk_builtin_cmp(e, valk_lval_join(tmp, a));
}
static valk_lval_t* valk_builtin_gt(valk_lenv_t* e, valk_lval_t* a) {
  valk_lval_t* tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym(">"));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}
static valk_lval_t* valk_builtin_lt(valk_lenv_t* e, valk_lval_t* a) {
  valk_lval_t* tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("<"));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}
static valk_lval_t* valk_builtin_ge(valk_lenv_t* e, valk_lval_t* a) {
  valk_lval_t* tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym(">="));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}
static valk_lval_t* valk_builtin_le(valk_lenv_t* e, valk_lval_t* a) {
  valk_lval_t* tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("<="));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}

static valk_lval_t* valk_builtin_load(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  valk_lval_t* expr = valk_parse_file(valk_lval_list_nth(a, 0)->str);
  if (LVAL_TYPE(expr) == LVAL_ERR) {
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

  return valk_lval_sexpr_empty();
}

valk_lval_t* valk_parse_file(const char* filename) {
  FILE* f = fopen(filename, "rb");
  if (f == nullptr) {
    LVAL_RAISE(valk_lval_sexpr_empty(), "Could not open file (%s)", filename);
  }

  fseek(f, 0, SEEK_END);
  size_t length = ftell(f);
  fseek(f, 0, SEEK_SET);

  if (length == UINT64_MAX) {
    fclose(f);
    LVAL_RAISE(valk_lval_sexpr_empty(), "File is way too big buddy (%s)",
               filename);
  }

  char* input = calloc(length + 1, sizeof(char));
  fread(input, 1, length, f);
  fclose(f);

  int pos = 0;
  valk_lval_t* res = valk_lval_sexpr_empty();
  valk_lval_t* tmp;
  do {
    tmp = valk_lval_read(&pos, input);
    valk_lval_add(res, tmp);
  } while ((LVAL_TYPE(tmp) != LVAL_ERR) && (input[pos] != '\0'));

  free(input);

  return res;
}

static valk_lval_t* valk_builtin_if(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_QEXPR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 2), LVAL_QEXPR);

  // Execute the selected branch
  valk_lval_t* branch;

  // Select true or false branch
  if (valk_lval_list_nth(a, 0)->num) {
    branch = valk_lval_list_nth(a, 1);
  } else {
    branch = valk_lval_list_nth(a, 2);
  }

  // Convert QEXPR to SEXPR for evaluation
  // Always make a shallow copy - type conversions should never mutate the original
  // (function bodies, parameters are immutable and might be referenced elsewhere)
  branch = valk_lval_copy(branch);
  branch->flags = ((branch->flags & LVAL_FLAGS_MASK) | LVAL_SEXPR);

  // Return thunk instead of recursing - enables proper TCO
  return valk_lval_thunk(e, branch);
}

static valk_lval_t* valk_builtin_do(valk_lenv_t* e, valk_lval_t* a) {
  // Evaluate all expressions except the last one for side effects
  size_t count = valk_lval_list_count(a);

  if (count == 0) {
    return valk_lval_sexpr_empty();
  }

  // Evaluate first n-1 expressions for side effects
  for (size_t i = 0; i < count - 1; i++) {
    valk_lval_t* expr = valk_lval_list_nth(a, i);
    // Convert QEXPR to SEXPR if needed
    if (LVAL_TYPE(expr) == LVAL_QEXPR) {
      expr = valk_lval_copy(expr);
      expr->flags = ((expr->flags & LVAL_FLAGS_MASK) | LVAL_SEXPR);
    }
    // Evaluate and discard result
    valk_lval_eval(e, expr);
  }

  // Return last expression as thunk for TCO
  valk_lval_t* last = valk_lval_list_nth(a, count - 1);
  if (LVAL_TYPE(last) == LVAL_QEXPR) {
    last = valk_lval_copy(last);
    last->flags = ((last->flags & LVAL_FLAGS_MASK) | LVAL_SEXPR);
  }
  return valk_lval_thunk(e, last);
}

static valk_lval_t* valk_builtin_print(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  for (size_t i = 0; i < valk_lval_list_count(a); i++) {
    valk_lval_print(valk_lval_list_nth(a, i));
    putchar(' ');
  }
  putchar('\n');
  return valk_lval_sexpr_empty();
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
            return valk_lval_err("printf: not enough arguments for format string");
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
            p++; // Skip the 'd' in %ld
          }
          if (arg_idx >= valk_lval_list_count(a)) {
            return valk_lval_err("printf: not enough arguments for format string");
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

  return valk_lval_sexpr_empty();
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

static valk_lval_t* valk_builtin_error(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  valk_lval_t* err = valk_lval_err(valk_lval_list_nth(a, 0)->str);
  return err;
}

static void __valk_arc_box_release(void* arg) {
  valk_arc_release((valk_arc_box*)arg - 1);
}

static void __valk_future_release(void* arg) {
  valk_arc_release((valk_future*)arg);
}

static valk_lval_t* valk_builtin_await(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 0)->ref.type, "future") == 0,
              "Await only works with futures but received: %s",
              valk_lval_list_nth(a, 0)->ref.type);

  valk_future* fut = valk_lval_list_nth(a, 0)->ref.ptr;
  // Await with a reasonable timeout to prevent long hangs in tests
  valk_arc_box* box = valk_future_await_timeout(fut, 15000);

  valk_lval_t* res;
  if (box->type == VALK_SUC) {
    res = valk_lval_ref("success", box->item, __valk_arc_box_release);
    valk_arc_retain(box);
  } else {
    res = valk_lval_err("ERR: %s", box->item);
  }

  return res;
}

// http2/listen: (http2/listen aio interface port keyfile certfile) -> future
// Returns a future that resolves to an http2_server ref
// Uses a demo handler that returns "Hello from Valk HTTP/2 server!"
static valk_lval_t* valk_builtin_http2_listen(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 5);

  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, aio_ref, LVAL_REF);
  LVAL_ASSERT(a, strcmp(aio_ref->ref.type, "aio_system") == 0,
              "First arg must be an aio_system ref, got %s", aio_ref->ref.type);

  valk_lval_t* interface = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, interface, LVAL_STR);

  valk_lval_t* port = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, port, LVAL_NUM);

  valk_lval_t* keyfile = valk_lval_list_nth(a, 3);
  LVAL_ASSERT_TYPE(a, keyfile, LVAL_STR);

  valk_lval_t* certfile = valk_lval_list_nth(a, 4);
  LVAL_ASSERT_TYPE(a, certfile, LVAL_STR);

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  valk_future* fut = valk_aio_http2_listen(sys, interface->str, (int)port->num,
                                           keyfile->str, certfile->str,
                                           valk_aio_http2_demo_handler());
  return valk_lval_ref("future", fut, __valk_future_release);
}

// http2/connect: (http2/connect aio ip port hostname?) -> future
static valk_lval_t* valk_builtin_http2_connect(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT(a, valk_lval_list_count(a) == 3 || valk_lval_list_count(a) == 4,
              "http2/connect expects 3 or 4 args: (aio ip port [hostname])");
  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, aio_ref, LVAL_REF);
  LVAL_ASSERT(a, strcmp(aio_ref->ref.type, "aio_system") == 0,
              "First arg must be an aio_system ref, got %s", aio_ref->ref.type);

  valk_lval_t* ip = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, ip, LVAL_STR);
  valk_lval_t* port = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, port, LVAL_NUM);

  const char* hostname = NULL;
  if (valk_lval_list_count(a) == 4) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 3), LVAL_STR);
    hostname = valk_lval_list_nth(a, 3)->str;
  }

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  valk_future* fut = valk_aio_http2_connect_host(sys, ip->str, (int)port->num,
                                                 hostname ? hostname : ip->str);
  return valk_lval_ref("future", fut, __valk_future_release);
}

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
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 0)->ref.type, "http2_request") == 0,
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

  return valk_lval_sexpr_empty();
}

// http2/send: (http2/send req client) -> future
static valk_lval_t* valk_builtin_http2_send(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 0)->ref.type, "http2_request") == 0,
              "First arg must be http2_request ref");
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_REF);
  // We expect a client inside a success ref from (await ...)
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 1)->ref.type, "success") == 0,
              "Second arg must be a success ref holding a client");

  valk_http2_request_t* req = valk_lval_list_nth(a, 0)->ref.ptr;
  valk_aio_http2_client* client = valk_lval_list_nth(a, 1)->ref.ptr;
  valk_future* fut = valk_aio_http2_request_send(req, client);
  return valk_lval_ref("future", fut, __valk_future_release);
}

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
  valk_lval_t* lst = valk_lval_qexpr_empty();
  if (!res) return lst;
  for (size_t i = 0; i < res->headers.count; ++i) {
    struct valk_http2_header_t* h = &res->headers.items[i];
    valk_lval_t* pair = valk_lval_qexpr_empty();
    valk_lval_add(pair, valk_lval_str((const char*)h->name));
    valk_lval_add(pair, valk_lval_str((const char*)h->value));
    valk_lval_add(lst, pair);
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
  if (has_mode && (strcmp(mode->str, "repl") == 0 || strcmp(mode->str, "test") == 0)) {
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
  exit(code);
}

// module: (module value) -> value; captures as VALK_LAST_MODULE
// (no module/program builtins; use VALK_LAST_VALUE set by `load`)

void valk_lenv_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "error", valk_builtin_error);
  valk_lenv_put_builtin(env, "load", valk_builtin_load);
  valk_lenv_put_builtin(env, "print", valk_builtin_print);
  valk_lenv_put_builtin(env, "printf", valk_builtin_printf);
  valk_lenv_put_builtin(env, "time-us", valk_builtin_time_us);

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

  // Async
  valk_lenv_put_builtin(env, "await", valk_builtin_await);
  // HTTP/2 client + request API
  valk_lenv_put_builtin(env, "http2/listen", valk_builtin_http2_listen);
  valk_lenv_put_builtin(env, "http2/connect", valk_builtin_http2_connect);
  valk_lenv_put_builtin(env, "http2/request", valk_builtin_http2_request);
  valk_lenv_put_builtin(env, "http2/request-add-header",
                        valk_builtin_http2_request_add_header);
  valk_lenv_put_builtin(env, "http2/send", valk_builtin_http2_send);
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
