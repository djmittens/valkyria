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
  LVAL_CONS,   // Cons cell - S-expression (code to execute)
  LVAL_QEXPR,  // Cons cell - Q-expression (quoted data, not code)
  LVAL_ERR,
  LVAL_HANDLE,   // Async operation handle (cancellable promise)
  LVAL_FORWARD,  // Forwarding pointer - only valid during scratch evacuation
} valk_ltype_e;

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
    valk_lval_t *forward;  // Forwarding pointer to new location (for LVAL_FORWARD)
  };
};

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

void valk_lval_finalize(valk_lval_t *lval);
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

// Quasiquote expansion (used by trampoline eval)
valk_lval_t *valk_quasiquote_expand(valk_lenv_t *env, valk_lval_t *form);

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

valk_lval_t *valk_lval_read_ctx(valk_parse_ctx_t *ctx);
valk_lval_t *valk_lval_read_expr_ctx(valk_parse_ctx_t *ctx);

#define LVAL_SET_SOURCE_LOC(lval, fid, ln, col) do { \
  (lval)->cov_file_id = (fid); \
  (lval)->cov_line = (ln); \
  (lval)->cov_column = (col); \
  u8 __type = LVAL_TYPE(lval); \
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

// ============================================================================
// Iterative Evaluator (Stack-based, no C recursion)
// ============================================================================

// Continuation types - what to do after evaluating an expression
typedef enum {
  CONT_DONE,           // Return final value
  CONT_EVAL_ARGS,      // Function evaluated, now evaluate arguments
  CONT_COLLECT_ARG,    // Collecting evaluated arguments one by one
  CONT_APPLY_FUNC,     // All args collected, apply function
  CONT_IF_BRANCH,      // Condition evaluated, pick and eval branch
  CONT_DO_NEXT,        // Evaluated one expr in do-sequence
  CONT_SELECT_CHECK,   // Evaluated condition in select clause
  CONT_BODY_NEXT,      // Evaluated one expr in function body
  CONT_SINGLE_ELEM,    // Single-element list: if result is function, call it
  CONT_LAMBDA_DONE,    // Lambda body evaluated, decrement call depth
} valk_cont_kind_e;

// Continuation frame - represents pending work after evaluating something
typedef struct valk_cont_frame {
  valk_cont_kind_e kind;
  valk_lenv_t *env;
  
  union {
    // CONT_EVAL_ARGS: function position evaluated, need to eval args
    struct {
      valk_lval_t *func;       // Evaluated function
      valk_lval_t *remaining;  // Remaining unevaluated args (cons list)
    } eval_args;
    
    // CONT_COLLECT_ARG: collecting evaluated args
    struct {
      valk_lval_t *func;       // Function to call
      valk_lval_t **args;      // Array of evaluated args so far
      u64 count;               // Number of args collected
      u64 capacity;            // Capacity of args array
      valk_lval_t *remaining;  // Remaining unevaluated args
    } collect_arg;
    
    // CONT_IF_BRANCH: condition evaluated, branches pending
    struct {
      valk_lval_t *true_branch;
      valk_lval_t *false_branch;
    } if_branch;
    
    // CONT_DO_NEXT: in a do sequence
    struct {
      valk_lval_t *remaining;  // Remaining expressions to evaluate
    } do_next;
    
    // CONT_SELECT_CHECK: checking select clause condition
    struct {
      valk_lval_t *result_expr;   // Result if condition true
      valk_lval_t *remaining;     // Remaining clauses
      valk_lval_t *original_args; // Original args for error messages
    } select_check;
    
    // CONT_BODY_NEXT: function body sequence
    struct {
      valk_lval_t *remaining;  // Remaining body expressions
      valk_lenv_t *call_env;   // Function's local environment
    } body_next;
  };
} valk_cont_frame_t;

// Evaluation stack - explicit stack of continuations
#define VALK_EVAL_STACK_INIT_CAP 64

typedef struct {
  valk_cont_frame_t *frames;
  u64 count;
  u64 capacity;
} valk_eval_stack_t;

// Stack operations
void valk_eval_stack_init(valk_eval_stack_t *stack);
void valk_eval_stack_push(valk_eval_stack_t *stack, valk_cont_frame_t frame);
valk_cont_frame_t valk_eval_stack_pop(valk_eval_stack_t *stack);
void valk_eval_stack_destroy(valk_eval_stack_t *stack);

// Evaluation result - either a value or a thunk (expression to evaluate)
typedef struct {
  bool is_thunk;
  union {
    valk_lval_t *value;
    struct {
      valk_lval_t *expr;
      valk_lenv_t *env;
      valk_lval_t *remaining_body;  // For multi-expression bodies
      valk_lenv_t *call_env;        // Environment for body evaluation
    } thunk;
  };
} valk_eval_result_t;

// Create a value result
static inline valk_eval_result_t valk_eval_value(valk_lval_t *val) {
  return (valk_eval_result_t){.is_thunk = false, .value = val};
}

// Create a thunk result (single expression)
static inline valk_eval_result_t valk_eval_thunk(valk_lval_t *expr, valk_lenv_t *env) {
  return (valk_eval_result_t){
    .is_thunk = true,
    .thunk = {.expr = expr, .env = env, .remaining_body = nullptr, .call_env = nullptr}
  };
}

// Create a thunk result with body sequence
static inline valk_eval_result_t valk_eval_thunk_body(valk_lval_t *expr, valk_lenv_t *env,
                                                       valk_lval_t *remaining, valk_lenv_t *call_env) {
  return (valk_eval_result_t){
    .is_thunk = true,
    .thunk = {.expr = expr, .env = env, .remaining_body = remaining, .call_env = call_env}
  };
}

// Get current interpreter metrics (thread-safe)
void valk_eval_metrics_get(u64* evals, u64* func_calls,
                            u64* builtin_calls, u32* stack_max,
                            u64* closures, u64* lookups);
