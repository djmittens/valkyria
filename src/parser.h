#pragma once
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Forward declarations
struct valk_lenv_t;
typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;

typedef enum {
  LVAL_NUM,
  LVAL_SYM,
  LVAL_FUN,
  LVAL_QEXPR,
  LVAL_SEXPR,
  LVAL_ERR
} valk_ltype_t;

const char *valk_ltype_name(valk_ltype_t type);

typedef valk_lval_t *(valk_lval_builtin_t)(valk_lenv_t *, valk_lval_t *);

struct valk_lval_t {
  union {
    struct {
      valk_lenv_t *env;
      valk_lval_t *body;
      valk_lval_t *formals;
      // NULL if its a lambda
      valk_lval_builtin_t *builtin;
    } fun;
    struct {
      struct valk_lval_t **cell;
      // only valid for (s|q)expr
      size_t count;
    } expr;
    long num;
    char *str;
  };
  valk_ltype_t type;
};

//// lval Constructors ////

valk_lval_t *valk_lval_num(long x);
valk_lval_t *valk_lval_err(char *fmt, ...);
valk_lval_t *valk_lval_sym(char *sym);
valk_lval_t *valk_lval_builtin(valk_lval_builtin_t *fun);
valk_lval_t *valk_lval_lambda(valk_lval_t *formals, valk_lval_t *body);
valk_lval_t *valk_lval_sexpr_empty();
valk_lval_t *valk_lval_qexpr_empty();

//// END Constructors ////

valk_lval_t *valk_lval_copy(valk_lval_t *lval);
void valk_lval_free(valk_lval_t *lval);

valk_lval_t *valk_lval_add(valk_lval_t *lval, valk_lval_t *cell);
valk_lval_t *valk_lval_pop(valk_lval_t *lval, size_t i);
valk_lval_t *valk_lval_join(valk_lval_t *a, valk_lval_t *b);

valk_lval_t *valk_lval_eval(valk_lenv_t *env, valk_lval_t *lval);
valk_lval_t *valk_lval_eval_sexpr(valk_lenv_t *env, valk_lval_t *sexpr);
valk_lval_t *valk_lval_eval_call(valk_lenv_t *env, valk_lval_t *func,
                                 valk_lval_t *args);

void valk_lval_print(valk_lval_t *val);
static inline void valk_lval_println(valk_lval_t *val) {
  valk_lval_print(val);
  printf("\n");
}

struct valk_lenv_t {
  char **symbols;
  valk_lval_t **vals;
  size_t count;
  struct valk_lenv_t *parent;
};

//// LEnv Constructors ////
valk_lenv_t *valk_lenv_new(void);
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
