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

// Helper to get allocation type
#define LVAL_ALLOC(_lval) ((_lval)->flags & LVAL_ALLOC_MASK)

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
  LVAL_FUN,
  LVAL_REF,
  LVAL_QEXPR,
  LVAL_SEXPR,
  LVAL_ERR,
  LVAL_ENV,
  LVAL_CONS,  // Cons cell (car/cdr linked list)
  LVAL_NIL,   // Empty list
} valk_ltype_e;

const char *valk_ltype_name(valk_ltype_e type);

typedef valk_lval_t *(valk_lval_builtin_t)(valk_lenv_t *, valk_lval_t *);

struct valk_lenv_t {
  uint64_t flags;
  char **symbols;
  valk_lval_t **vals;
  size_t count;
  struct valk_lenv_t *parent;
  // Allocator where persistent env data lives (globals/closures)
  void *allocator;
};

struct valk_lval_t {
  uint64_t flags;
  void *origin_allocator;  // Always track where this value was allocated
  union {
    struct {
      valk_lenv_t *env;
      valk_lval_t *body;
      // formal parameters, to the function, eg names
      valk_lval_t *formals;
      // NULL if its a lambda
      valk_lval_builtin_t *builtin;
    } fun;
    struct {
      struct valk_lval_t **cell;
      size_t count;
      // char* file;
      // size_t line;
    } expr;
    struct {
      valk_lval_t *car;  // Head element
      valk_lval_t *cdr;  // Tail (rest of list)
    } cons;
    struct {
      char *type;
      void *ptr;
      void (*free)(void *);
    } ref;
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
valk_lval_t *valk_lval_lambda(valk_lval_t *formals, valk_lval_t *body);
valk_lval_t *valk_lval_sexpr_empty(void);
valk_lval_t *valk_lval_qexpr_empty(void);

// Cons cell constructors
valk_lval_t *valk_lval_nil(void);                              // Empty list
valk_lval_t *valk_lval_cons(valk_lval_t *car, valk_lval_t *cdr);  // Cons cell
valk_lval_t *valk_lval_car(valk_lval_t *cons);                    // Get head
valk_lval_t *valk_lval_cdr(valk_lval_t *cons);                    // Get tail
int valk_lval_is_nil(valk_lval_t *v);                             // Check if nil

//// END Constructors ////

// valk_lval_t *valk_lval_copy(valk_lval_t *lval);
valk_lval_t *valk_lval_copy(valk_lval_t *lval);

// Persist a value into the environment's allocator (arena/malloc).
// Returns a deep-copied value owned by `env`.
valk_lval_t *valk_intern(valk_lenv_t *env, valk_lval_t *val);
void valk_lval_finalize(valk_lval_t *lval);
int valk_lval_eq(valk_lval_t *x, valk_lval_t *y);

valk_lval_t *valk_lval_add(valk_lval_t *lval, valk_lval_t *cell);
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
