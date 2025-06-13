#pragma once
#include <stdio.h>

#include "memory.h"

#define LVAL_TYPE_BITS 8ULL
#define LVAL_TYPE_MASK 0x00000000000000FFULL
#define LVAL_FLAGS_MASK 0xFFFFFFFFFFFFFF00ULL

#define LVAL_TYPE(_lval) (valk_ltype_e)(_lval->flags & LVAL_TYPE_MASK)

#define LVAL_FLAG_GC  (1 << (LVAL_TYPE_BITS + 1))

// Forward declarations
struct valk_lenv_t;
typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;
valk_lval_t *valk_parse_file(const char *filename);

typedef enum {
  LVAL_NUM,
  LVAL_SYM,
  LVAL_STR,
  LVAL_FUN,
  LVAL_REF,
  LVAL_QEXPR,
  LVAL_SEXPR,
  LVAL_ERR
} valk_ltype_e;

const char *valk_ltype_name(valk_ltype_e type);

typedef valk_lval_t *(valk_lval_builtin_t)(valk_lenv_t *, valk_lval_t *);

struct valk_lval_t {
  uint64_t flags;
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
      // only valid for (s|q)expr
      size_t count;
    } expr;
    struct {
      char *type;
      void *ptr;
      void (*free)(void *);
    } ref;
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
// valk_lval_t *valk_lval_builtin(valk_lval_builtin_t *fun);
valk_lval_t *valk_lval_lambda(valk_lval_t *formals, valk_lval_t *body);
valk_lval_t *valk_lval_sexpr_empty(void);
valk_lval_t *valk_lval_qexpr_empty(void);

//// END Constructors ////

// valk_lval_t *valk_lval_copy(valk_lval_t *lval);
void valk_lval_free(valk_lval_t *lval);
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

struct valk_lenv_t {
  uint64_t flags;
  char **symbols;
  valk_lval_t **vals;
  size_t count;
  struct valk_lenv_t *parent;
};

//// LEnv Constructors ////
valk_lenv_t *valk_lenv_empty(void);
void valk_lenv_init(valk_lenv_t *env);
//// END LEnv Constructors ////
void valk_lenv_free(valk_lenv_t *env);
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
