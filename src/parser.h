#pragma once
#include <stdint.h>
#include <stdio.h>

#define LVAL_TYPE_BITS 8ULL
#define LVAL_TYPE_MASK 0x00000000000000FFULL
#define LVAL_FLAGS_MASK 0xFFFFFFFFFFFFFF00ULL

#define LVAL_TYPE(_lval) (valk_ltype_e)(_lval->flags & LVAL_TYPE_MASK)

// Allocation flags - where this value was allocated
#define LVAL_ALLOC_BITS 2
#define LVAL_ALLOC_SHIFT (LVAL_TYPE_BITS)
#define LVAL_ALLOC_MASK (0x3ULL << LVAL_ALLOC_SHIFT)

#define LVAL_ALLOC_SCRATCH  (0ULL << LVAL_ALLOC_SHIFT)  // Scratch arena (ephemeral)
#define LVAL_ALLOC_GLOBAL   (1ULL << LVAL_ALLOC_SHIFT)  // Global arena (persistent)
#define LVAL_ALLOC_HEAP     (2ULL << LVAL_ALLOC_SHIFT)  // GC heap (persistent)

// GC mark bit
#define LVAL_FLAG_GC_MARK   (1ULL << (LVAL_TYPE_BITS + LVAL_ALLOC_BITS))

// Freeze bit - marks immutable values
#define LVAL_FLAG_FROZEN    (1ULL << (LVAL_TYPE_BITS + LVAL_ALLOC_BITS + 1))

// Escape bit - marks values that outlive their creation scope
// Escaping values need heap allocation, non-escaping can use scratch
//
// ESCAPE ANALYSIS - When to mark values as escaping:
//
// A value ESCAPES if it:
//   1. Is stored in an environment (def, =, lambda captures)
//      - valk_lenv_put should mark value as escaping
//      - Closure environments should mark captures as escaping
//
//   2. Is captured by a lambda/function closure
//      - valk_builtin_lambda should mark formals/body/env as escaping
//      - Captured variables outlive the function definition scope
//
//   3. Is returned from a function
//      - Function return values may outlive the call frame
//      - valk_lval_eval should mark return values as escaping
//
//   4. Is assigned to a data structure that outlives the current scope
//      - Values added to lists/expressions that escape also escape
//
// A value DOES NOT ESCAPE if it:
//   - Is a temporary during evaluation (intermediate results)
//   - Is used only within the current scope and not stored
//   - Is an argument that's consumed immediately
//
// Optimization strategy:
//   - Non-escaping values can use scratch arena (fast bump allocation)
//   - Escaping values must use GC heap (persistent, garbage collected)
//   - This enables zero-copy sharing of frozen heap values (via valk_intern)
#define LVAL_FLAG_ESCAPES   (1ULL << (LVAL_TYPE_BITS + LVAL_ALLOC_BITS + 2))

// Forwarding flag: value has been moved to new location (pointer forwarding for scratch->heap promotion)
#define LVAL_FLAG_FORWARDED (1ULL << (LVAL_TYPE_BITS + LVAL_ALLOC_BITS + 3))

// Tail call flag: marks expressions that are in tail position (for TCO)
#define LVAL_FLAG_TAIL_CALL (1ULL << (LVAL_TYPE_BITS + LVAL_ALLOC_BITS + 4))

// Macro flag: function receives unevaluated arguments (like Lisp macros)
#define LVAL_FLAG_MACRO     (1ULL << (LVAL_TYPE_BITS + LVAL_ALLOC_BITS + 5))

// Helper to get allocation type
#define LVAL_ALLOC(_lval) ((_lval)->flags & LVAL_ALLOC_MASK)

// Helper to check if frozen
#define LVAL_IS_FROZEN(_lval) ((_lval)->flags & LVAL_FLAG_FROZEN)

// Helper to check if value escapes
#define LVAL_ESCAPES(_lval) ((_lval)->flags & LVAL_FLAG_ESCAPES)

// Helper to get allocation flags from allocator type
// Implemented in parser.c
uint64_t valk_alloc_flags_from_allocator(void* allocator);

// Forward declarations
struct valk_lenv_t;
typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;
valk_lval_t *valk_parse_file(const char *filename);

typedef enum {
  LVAL_UNDEFINED,
  LVAL_NUM,
  LVAL_SYM,
  LVAL_STR,
  LVAL_FUN,  // Function (bytecode or builtin)
  LVAL_REF,
  LVAL_QEXPR,
  LVAL_SEXPR,
  LVAL_ERR,
  LVAL_ENV,
  LVAL_CONS,  // Cons cell (car/cdr linked list)
  LVAL_NIL,   // Empty list
  LVAL_CONT,  // Continuation (for async/await)
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
  // Allocator where persistent env data lives (globals/closures)
  void *allocator;
};

struct valk_lval_t {
  uint64_t flags;
  void *origin_allocator;  // Always track where this value was allocated
  struct valk_lval_t *gc_next;  // Linked list for GC heap tracking
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
    } cons;  // Used by LVAL_CONS, LVAL_SEXPR, LVAL_QEXPR
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
    struct valk_lenv_t env;
    long num;
    char *str;
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
valk_lval_t *valk_lval_sexpr_empty(void);
valk_lval_t *valk_lval_qexpr_empty(void);
valk_lval_t *valk_cons_to_sexpr(valk_lval_t *qexpr);

// Cons cell constructors
valk_lval_t *valk_lval_nil(void);                                   // Empty list
valk_lval_t *valk_lval_cons(valk_lval_t *head, valk_lval_t *tail);  // Cons cell
valk_lval_t *valk_lval_list(valk_lval_t *arr[], size_t count);

// Continuation constructor
valk_lval_t *valk_lval_head(valk_lval_t *cons);                     // Get head
valk_lval_t *valk_lval_tail(valk_lval_t *cons);                     // Get tail
int valk_lval_is_nil(valk_lval_t *v);                               // Check if nil

//// END Constructors ////

// valk_lval_t *valk_lval_copy(valk_lval_t *lval);
valk_lval_t *valk_lval_copy(valk_lval_t *lval);

// Persist a value into the environment's allocator (arena/malloc).
// Returns a deep-copied value owned by `env`.
// Sets up forwarding pointer if value was in scratch arena.
valk_lval_t *valk_intern(valk_lenv_t *env, valk_lval_t *val);

// Resolve forwarding pointers (follow chain to final value)
// Returns the actual value, following any forwarding pointers
valk_lval_t *valk_lval_resolve(valk_lval_t *val);

// Promote a value to GC heap if it's not already there.
// Useful for escaping values that were initially allocated in scratch.
// Returns heap-allocated value (may be same as input if already on heap).
valk_lval_t *valk_lval_promote_to_heap(valk_lval_t *val);

void valk_lval_finalize(valk_lval_t *lval);
int valk_lval_eq(valk_lval_t *x, valk_lval_t *y);

// Memory management
// REMOVED: valk_lval_cleanup - no longer needed with GC heap for all allocations

// Immutability support
void valk_lval_freeze(valk_lval_t *lval);      // Recursively freeze value tree
void valk_lval_assert_mutable(valk_lval_t *lval);  // Crash if frozen

// Helper functions for cons-based lists
int valk_lval_list_is_empty(valk_lval_t* list);
size_t valk_lval_list_count(valk_lval_t* list);
valk_lval_t* valk_lval_list_nth(valk_lval_t* list, size_t n);

valk_lval_t *valk_lval_pop(valk_lval_t *lval, size_t i);
valk_lval_t *valk_lval_join(valk_lval_t *a, valk_lval_t *b);

valk_lval_t *valk_lval_eval(valk_lenv_t *env, valk_lval_t *lval);
valk_lval_t *valk_lval_eval_sexpr(valk_lenv_t *env, valk_lval_t *sexpr);
valk_lval_t *valk_lval_eval_call(valk_lenv_t *env, valk_lval_t *func,
                                 valk_lval_t *args);

void valk_lval_print(valk_lval_t *val);

valk_lval_t *valk_lval_read(int *i, const char *s);
valk_lval_t *valk_lval_read_expr(int *i, const char *s);

static inline void valk_lval_println(valk_lval_t *val) {
  valk_lval_print(val);
  printf("\n");
}


//// LEnv Constructors ////
valk_lenv_t *valk_lenv_empty(void);
void valk_lenv_init(valk_lenv_t *env);
// REMOVED: valk_lenv_cleanup - no longer needed with GC heap for all allocations
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
