#pragma once
#include <stdbool.h>
#include <stdatomic.h>
#include <stdio.h>
#include "coverage.h"
#include "types.h"

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

// GC generation counter (7 bits, 0-127 generations survived)
// Used for object survival histogram to detect potential memory leaks
// Objects surviving many GC cycles may indicate retained references
#define LVAL_GC_GEN_BITS    7
#define LVAL_GC_GEN_SHIFT   (LVAL_TYPE_BITS + LVAL_ALLOC_BITS + 1)  // After GC mark bit
#define LVAL_GC_GEN_MASK    (0x7FULL << LVAL_GC_GEN_SHIFT)
#define LVAL_GC_GEN_MAX     127

// Immortal bit - objects that are never collected (builtins, stdlib)
// This allows GC to skip these objects during both mark and sweep
#define LVAL_FLAG_IMMORTAL  (1ULL << (LVAL_GC_GEN_SHIFT + LVAL_GC_GEN_BITS))

// Quoted flag - for cons cells, indicates this should print as {} not ()
// Used to preserve round-trip fidelity for quoted expressions
#define LVAL_FLAG_QUOTED    (1ULL << (LVAL_GC_GEN_SHIFT + LVAL_GC_GEN_BITS + 1))

#define LVAL_GC_GEN(lval) (((lval)->flags & LVAL_GC_GEN_MASK) >> LVAL_GC_GEN_SHIFT)
#define LVAL_GC_GEN_SET(lval, gen) do { \
  (lval)->flags = ((lval)->flags & ~LVAL_GC_GEN_MASK) | \
                  (((u64)(gen) & 0x7FULL) << LVAL_GC_GEN_SHIFT); \
} while(0)
#define LVAL_GC_GEN_INC(lval) do { \
  u64 _gen = LVAL_GC_GEN(lval); \
  if (_gen < LVAL_GC_GEN_MAX) LVAL_GC_GEN_SET(lval, _gen + 1); \
} while(0)

// Helper to get allocation type
#define LVAL_ALLOC(_lval) ((_lval)->flags & LVAL_ALLOC_MASK)

// Helper to get allocation flags from allocator type
// Implemented in parser.c
u64 valk_alloc_flags_from_allocator(void* allocator);

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
  LVAL_CONS,   // Cons cell (list) - use LVAL_FLAG_QUOTED for {} vs () printing
  LVAL_ERR,
  LVAL_HANDLE,   // Async operation handle (cancellable promise)
} valk_ltype_e;

// LVAL_QEXPR is now an alias for LVAL_CONS (deprecated, use LVAL_CONS)
#define LVAL_QEXPR LVAL_CONS

const char *valk_ltype_name(valk_ltype_e type);

typedef valk_lval_t *(valk_lval_builtin_t)(valk_lenv_t *, valk_lval_t *);

struct valk_lenv_t {
  _Atomic u64 flags;
  // Dynamic array of symbol names (char*)
  struct {
    char **items;
    u64 count;
    u64 capacity;
  } symbols;
  // Dynamic array of values (valk_lval_t*)
  struct {
    valk_lval_t **items;
    u64 count;
    u64 capacity;
  } vals;
  struct valk_lenv_t *parent;
  // Allocator where persistent env data lives (globals/closures)
  void *allocator;
};

struct valk_lval_t {
  _Atomic u64 flags;
  void *origin_allocator;  // Always track where this value was allocated
  struct valk_lval_t *gc_next;  // Linked list for GC heap tracking
#ifdef VALK_COVERAGE
  u16 cov_file_id;
  u16 cov_line;
  u16 cov_column;
  u16 cov_reserved;
#endif
  union {
    struct {
      // Builtin function pointer (nullptr for lambdas)
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
      valk_async_handle_t *handle;  // Pointer to the async handle struct
    } async;  // LVAL_HANDLE - async operation handle
    long num;
    char *str;
  };
};

// Immortal object helpers - must be after valk_lval_t definition
static inline bool valk_lval_is_immortal(valk_lval_t *v) {
  return v != nullptr && (v->flags & LVAL_FLAG_IMMORTAL) != 0;
}

static inline void valk_lval_set_immortal(valk_lval_t *v) {
  if (v != nullptr) v->flags |= LVAL_FLAG_IMMORTAL;
}

//// lval Constructors ////

valk_lval_t *valk_lval_ref(const char *type, void *ptr, void (*free)(void *));

valk_lval_t *valk_lval_num(long x);
valk_lval_t *valk_lval_err(const char *fmt, ...);
valk_lval_t *valk_lval_sym(const char *sym);
valk_lval_t *valk_lval_str(const char *str);
valk_lval_t *valk_lval_str_n(const char *bytes, u64 n);

// valk_lval_t *valk_lval_builtin(valk_lval_builtin_t *fun);
valk_lval_t *valk_lval_lambda(valk_lenv_t *env, valk_lval_t *formals, valk_lval_t *body);

// Cons cell constructors
valk_lval_t *valk_lval_nil(void);                                   // Empty list (LVAL_NIL)
valk_lval_t *valk_lval_cons(valk_lval_t *head, valk_lval_t *tail);  // Cons cell
valk_lval_t *valk_lval_list(valk_lval_t *arr[], u64 count);      // Build list from array
valk_lval_t *valk_lval_qcons(valk_lval_t *head, valk_lval_t *tail); // Q-expression cons cell
valk_lval_t *valk_lval_qlist(valk_lval_t *arr[], u64 count);     // Build qexpr from array

// Cons cell accessors
valk_lval_t *valk_lval_head(valk_lval_t *cons);                     // Get head (car)
valk_lval_t *valk_lval_tail(valk_lval_t *cons);                     // Get tail (cdr)

// Async handle constructor (implemented in aio_uv.c)
valk_lval_t *valk_lval_handle(valk_async_handle_t *handle);

//// END Constructors ////

// valk_lval_t *valk_lval_copy(valk_lval_t *lval);
valk_lval_t *valk_lval_copy(valk_lval_t *lval);

int valk_lval_eq(valk_lval_t *x, valk_lval_t *y);

// Helper functions for cons-based lists
int valk_lval_list_is_empty(valk_lval_t* list);
u64 valk_lval_list_count(valk_lval_t* list);
valk_lval_t* valk_lval_list_nth(valk_lval_t* list, u64 n);

valk_lval_t *valk_lval_pop(valk_lval_t *lval, u64 i);
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
  u16 file_id;
} valk_parse_ctx_t;



#define LVAL_SET_SOURCE_LOC(lval, fid, ln, col) do { \
  (lval)->cov_file_id = (fid); \
  (lval)->cov_line = (ln); \
  (lval)->cov_column = (col); \
  u8 __type = LVAL_TYPE(lval); \
  bool __is_quoted = ((lval)->flags & LVAL_FLAG_QUOTED) != 0; \
  if (__type == LVAL_CONS && !__is_quoted) { \
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
  if ((src) != nullptr && (dst) != nullptr && (src)->cov_line > 0) { \
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

char *valk_str_join(u64 n, const char **strs, const char *sep);
char *valk_c_err_format(const char *fmt, const char *file, u64 line,
                        const char *function);

// ============================================================================
// Interpreter Runtime Metrics
// ============================================================================

// Interpreter metrics for observability
typedef struct {
  _Atomic u64 evals_total;        // Total lval_eval() calls
  _Atomic u64 function_calls;     // User-defined function invocations
  _Atomic u64 builtin_calls;      // Builtin function invocations
  _Atomic u32 stack_depth;        // Current call stack depth
  u32 stack_depth_max;            // Peak call stack depth ever reached
  _Atomic u64 closures_created;   // Lambda closures created
  _Atomic u64 env_lookups;        // Symbol resolution lookups
} valk_eval_metrics_t;

// Global interpreter metrics instance
extern valk_eval_metrics_t g_eval_metrics;

// Initialize interpreter metrics (call at startup)
void valk_eval_metrics_init(void);

#include "eval_internal.h"
