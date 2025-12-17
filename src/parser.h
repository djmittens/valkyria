#pragma once
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include "coverage.h"

#define LVAL_TYPE_BITS 8ULL
#define LVAL_TYPE_MASK 0x00000000000000FFULL
#define LVAL_FLAGS_MASK 0xFFFFFFFFFFFFFF00ULL

#define LVAL_TYPE(_lval) ((valk_ltype_e)(_lval->flags & LVAL_TYPE_MASK))

// Allocation flags - where this value was allocated
#define LVAL_ALLOC_BITS 2
#define LVAL_ALLOC_SHIFT (LVAL_TYPE_BITS)
#define LVAL_ALLOC_MASK (0x3ULL << LVAL_ALLOC_SHIFT)

#define LVAL_ALLOC_SCRATCH  (0ULL << LVAL_ALLOC_SHIFT)  // Scratch arena (ephemeral)
#define LVAL_ALLOC_GLOBAL   (1ULL << LVAL_ALLOC_SHIFT)  // Global arena (persistent)
#define LVAL_ALLOC_HEAP     (2ULL << LVAL_ALLOC_SHIFT)  // GC heap (persistent)

// GC mark bit
#define LVAL_FLAG_GC_MARK   (1ULL << (LVAL_TYPE_BITS + LVAL_ALLOC_BITS))

// Helper to get allocation type
#define LVAL_ALLOC(_lval) ((_lval)->flags & LVAL_ALLOC_MASK)

// Helper to get allocation flags from allocator type
// Implemented in parser.c
uint64_t valk_alloc_flags_from_allocator(void* allocator);

// Forward declarations
struct valk_lenv_t;
typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;
typedef struct valk_async_handle_t valk_async_handle_t;  // Async handle (defined in aio_uv.c)
valk_lval_t *valk_parse_file(const char *filename);

typedef enum {
  LVAL_UNDEFINED,
  LVAL_NUM,
  LVAL_SYM,
  LVAL_STR,
  LVAL_FUN,  // Function (bytecode or builtin)
  LVAL_REF,
  LVAL_NIL,    // Empty list / nil value
  LVAL_CONS,   // Cons cell - S-expression (code to execute)
  LVAL_QEXPR,  // Cons cell - Q-expression (quoted data, not code)
  LVAL_ERR,
  LVAL_ENV,
  LVAL_CONT,     // Continuation (for async/await)
  LVAL_HANDLE,   // Async operation handle (cancellable promise)
  LVAL_FORWARD,  // Forwarding pointer - only valid during scratch evacuation
} valk_ltype_e;

const char *valk_ltype_name(valk_ltype_e type);

typedef valk_lval_t *(valk_lval_builtin_t)(valk_lenv_t *, valk_lval_t *);

struct valk_lenv_t {
  uint64_t flags;
  // Dynamic array of symbol names (char*)
  struct {
    char **items;
    size_t count;
    size_t capacity;
  } symbols;
  // Dynamic array of values (valk_lval_t*)
  struct {
    valk_lval_t **items;
    size_t count;
    size_t capacity;
  } vals;
  struct valk_lenv_t *parent;
  // Fallback environment for dynamic scoping - checked when parent chain fails.
  // This allows lexical closures (via parent chain) to coexist with dynamic
  // access to caller's variables (via fallback chain).
  struct valk_lenv_t *fallback;
  // Allocator where persistent env data lives (globals/closures)
  void *allocator;
};

struct valk_lval_t {
  uint64_t flags;
  void *origin_allocator;  // Always track where this value was allocated
  struct valk_lval_t *gc_next;  // Linked list for GC heap tracking
#ifdef VALK_COVERAGE
  uint16_t cov_file_id;
  uint16_t cov_line;
  uint16_t cov_column;
  uint16_t cov_reserved;
#endif
  union {
    struct {
      // Builtin function pointer (NULL for lambdas)
      valk_lval_builtin_t *builtin;
      int arity;
      char *name;
      // For closures
      valk_lenv_t *env;
      // For tree-walker lambdas
      valk_lval_t *formals;
      valk_lval_t *body;
    } fun;
    struct {
      valk_lval_t *head;  // First element
      valk_lval_t *tail;  // Rest of list
    } cons;  // Used by LVAL_CONS
    struct {
      char *type;
      void *ptr;
      void (*free)(void *);
    } ref;
    struct {
      void *resume_fn;    // Function to resume continuation
      valk_lenv_t *env;   // Captured environment
      void *user_data;    // User data (for libuv handle, etc)
    } cont;  // Continuation for async/await
    struct {
      valk_async_handle_t *handle;  // Pointer to the async handle struct
    } async;  // LVAL_HANDLE - async operation handle
    struct valk_lenv_t env;
    long num;
    char *str;
    valk_lval_t *forward;  // Forwarding pointer to new location (for LVAL_FORWARD)
  };
};

//// lval Constructors ////

valk_lval_t *valk_lval_ref(const char *type, void *ptr, void (*free)(void *));

valk_lval_t *valk_lval_num(long x);
valk_lval_t *valk_lval_err(const char *fmt, ...);
valk_lval_t *valk_lval_sym(const char *sym);
valk_lval_t *valk_lval_str(const char *str);
valk_lval_t *valk_lval_str_n(const char *bytes, size_t n);

// valk_lval_t *valk_lval_builtin(valk_lval_builtin_t *fun);
valk_lval_t *valk_lval_lambda(valk_lenv_t *env, valk_lval_t *formals, valk_lval_t *body);

// Cons cell constructors
valk_lval_t *valk_lval_nil(void);                                   // Empty list (LVAL_NIL)
valk_lval_t *valk_lval_cons(valk_lval_t *head, valk_lval_t *tail);  // Cons cell
valk_lval_t *valk_lval_list(valk_lval_t *arr[], size_t count);      // Build list from array
valk_lval_t *valk_lval_qcons(valk_lval_t *head, valk_lval_t *tail); // Q-expression cons cell
valk_lval_t *valk_lval_qlist(valk_lval_t *arr[], size_t count);     // Build qexpr from array

// Cons cell accessors
valk_lval_t *valk_lval_head(valk_lval_t *cons);                     // Get head (car)
valk_lval_t *valk_lval_tail(valk_lval_t *cons);                     // Get tail (cdr)

// Async handle constructor (implemented in aio_uv.c)
valk_lval_t *valk_lval_handle(valk_async_handle_t *handle);

//// END Constructors ////

// valk_lval_t *valk_lval_copy(valk_lval_t *lval);
valk_lval_t *valk_lval_copy(valk_lval_t *lval);

void valk_lval_finalize(valk_lval_t *lval);
int valk_lval_eq(valk_lval_t *x, valk_lval_t *y);

// Helper functions for cons-based lists
int valk_lval_list_is_empty(valk_lval_t* list);
size_t valk_lval_list_count(valk_lval_t* list);
valk_lval_t* valk_lval_list_nth(valk_lval_t* list, size_t n);

valk_lval_t *valk_lval_pop(valk_lval_t *lval, size_t i);
valk_lval_t *valk_lval_join(valk_lval_t *a, valk_lval_t *b);

valk_lval_t *valk_lval_eval(valk_lenv_t *env, valk_lval_t *lval);
valk_lval_t *valk_lval_eval_call(valk_lenv_t *env, valk_lval_t *func,
                                 valk_lval_t *args);

void valk_lval_print(valk_lval_t *val);

valk_lval_t *valk_lval_read(int *i, const char *s);
valk_lval_t *valk_lval_read_expr(int *i, const char *s);

#ifdef VALK_COVERAGE
typedef struct {
  const char *source;
  int pos;
  int line;
  int line_start;
  uint16_t file_id;
} valk_parse_ctx_t;

valk_lval_t *valk_lval_read_ctx(valk_parse_ctx_t *ctx);
valk_lval_t *valk_lval_read_expr_ctx(valk_parse_ctx_t *ctx);

#define LVAL_SET_SOURCE_LOC(lval, fid, ln, col) do { \
  (lval)->cov_file_id = (fid); \
  (lval)->cov_line = (ln); \
  (lval)->cov_column = (col); \
  uint8_t __type = LVAL_TYPE(lval); \
  /* Only mark CONS (s-expressions) for coverage, not QEXPR. */ \
  /* QEXPRs are quoted data not evaluated (e.g., function params, def bindings). */ \
  if (__type == LVAL_CONS) { \
    VALK_COVERAGE_MARK_LINE((fid), (ln)); \
    VALK_COVERAGE_MARK_LVAL(lval); \
  } \
} while(0)
#define LVAL_INIT_SOURCE_LOC(lval) do { \
  (lval)->cov_file_id = 0; \
  (lval)->cov_line = 0; \
  (lval)->cov_column = 0; \
  (lval)->cov_reserved = 0; \
} while(0)
#define INHERIT_SOURCE_LOC(dst, src) do { \
  if ((src) != NULL && (dst) != NULL && (src)->cov_line > 0) { \
    (dst)->cov_file_id = (src)->cov_file_id; \
    (dst)->cov_line = (src)->cov_line; \
    (dst)->cov_column = (src)->cov_column; \
  } \
} while(0)
#else
#define LVAL_SET_SOURCE_LOC(lval, fid, ln, col) ((void)0)
#define LVAL_INIT_SOURCE_LOC(lval) ((void)0)
#define INHERIT_SOURCE_LOC(dst, src) ((void)0)
#endif

static inline void valk_lval_println(valk_lval_t *val) {
  valk_lval_print(val);
  printf("\n");
}


//// LEnv Constructors ////
valk_lenv_t *valk_lenv_empty(void);
valk_lenv_t* valk_lenv_sandboxed(valk_lenv_t* parent);
void valk_lenv_init(valk_lenv_t *env);
void valk_lenv_free(valk_lenv_t *env);  // Free malloc-allocated environments
//// END LEnv Constructors ////
valk_lenv_t *valk_lenv_copy(valk_lenv_t *env);

valk_lval_t *valk_lenv_get(valk_lenv_t *env, valk_lval_t *key);

void valk_lenv_put(valk_lenv_t *env, valk_lval_t *key, valk_lval_t *val);
void valk_lenv_def(valk_lenv_t *env, valk_lval_t *key, valk_lval_t *val);

void valk_lenv_put_builtin(valk_lenv_t *env, char *key,
                           valk_lval_builtin_t *fun);
void valk_lenv_builtins(valk_lenv_t *env);

// UTILS
// These functions should  probably not  be here, but right now they are or
// something. Maybe there should be a string handling lib

char *valk_str_join(size_t n, const char **strs, const char *sep);
char *valk_c_err_format(const char *fmt, const char *file, size_t line,
                        const char *function);

// ============================================================================
// Interpreter Runtime Metrics
// ============================================================================

// Interpreter metrics for observability
typedef struct {
  _Atomic uint64_t evals_total;        // Total lval_eval() calls
  _Atomic uint64_t function_calls;     // User-defined function invocations
  _Atomic uint64_t builtin_calls;      // Builtin function invocations
  _Atomic uint32_t stack_depth;        // Current call stack depth
  uint32_t stack_depth_max;            // Peak call stack depth ever reached
  _Atomic uint64_t closures_created;   // Lambda closures created
  _Atomic uint64_t env_lookups;        // Symbol resolution lookups
} valk_eval_metrics_t;

// Global interpreter metrics instance
extern valk_eval_metrics_t g_eval_metrics;

// Initialize interpreter metrics (call at startup)
void valk_eval_metrics_init(void);

// Get current interpreter metrics (thread-safe)
void valk_eval_metrics_get(uint64_t* evals, uint64_t* func_calls,
                            uint64_t* builtin_calls, uint32_t* stack_max,
                            uint64_t* closures, uint64_t* lookups);
