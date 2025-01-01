#pragma once
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
  LVAL_NUM,
  LVAL_SYM,
  LVAL_QEXPR,
  LVAL_SEXPR,
  LVAL_ERR
} valk_lres_t;

typedef struct valk_lval_t {
  valk_lres_t type;
  union {
    long val;
    struct valk_lval_t **cell;
    char *str;
  };
  // only valid for (s|q)expr
  size_t count;
} valk_lval_t;

static inline valk_lval_t *valk_lval_num(long x) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_NUM;
  res->val = x;
  res->count = 0;
  return res;
}

static inline valk_lval_t *valk_lval_err(char *msg) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_ERR;
  // TODO(main): look into UTF-8 support
  int len = strlen(msg);
  res->str = calloc(len + 1, sizeof(char));
  strncpy(res->str, msg, len);
  res->count = 0;
  return res;
}

static inline valk_lval_t *valk_lval_sym(char *sym) {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_SYM;
  int len = strlen(sym);
  res->str = calloc(len + 1, sizeof(char));
  strncpy(res->str, sym, len);
  res->count = 0;
  return res;
}

static inline valk_lval_t *valk_lval_sexpr_empty() {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_SEXPR;
  res->cell = NULL;
  res->count = 0;
  return res;
}

static inline valk_lval_t *valk_lval_qexpr_empty() {
  valk_lval_t *res = malloc(sizeof(valk_lval_t));
  res->type = LVAL_QEXPR;
  res->cell = NULL;
  res->count = 0;
  return res;
}

static inline void valk_lval_free(valk_lval_t *lval) {
  switch (lval->type) {
  case LVAL_NUM:
    // nuttin to do but break;
    break;
  case LVAL_SYM:
  case LVAL_ERR:
    free(lval->str);
    break;
  case LVAL_QEXPR:
  case LVAL_SEXPR:
    while (lval->count > 0) {
      valk_lval_free(lval->cell[lval->count - 1]);
      --lval->count;
    }
    // Should play around with valgrind on this. Pretty interesting thing to
    // forget
    free(lval->cell);
    break;
  }
  free(lval);
}

static inline void valk_lval_print(valk_lval_t *val) {
  switch (val->type) {
  case LVAL_NUM:
    printf("Num[%li]", val->val);
    break;
  case LVAL_SYM:
    printf("Sym[%s]", val->str);
    break;
    // TODO(main): code duplication here, do i actually care??
  case LVAL_QEXPR:
    printf("Qexpr{ ");
    for (int i = 0; i < val->count; ++i) {
      valk_lval_print(val->cell[i]);
      if (i < val->count - 1) {
        putchar(' ');
      }
    }
    printf(" }");
    break;
  case LVAL_SEXPR:
    printf("Sexpr( ");
    for (int i = 0; i < val->count; ++i) {
      valk_lval_print(val->cell[i]);
      if (i < val->count - 1) {
        putchar(' ');
      }
    }
    printf(" )");
    break;
  case LVAL_ERR:
    printf("Error[%s]", val->str);
    break;
  }
}

static inline void valk_lval_println(valk_lval_t *val) {
  valk_lval_print(val);
  printf("\n");
}

valk_lval_t *valk_lval_add(valk_lval_t *lval, valk_lval_t *cell);
valk_lval_t *valk_lval_pop(valk_lval_t *lval, size_t i);
valk_lval_t *valk_lval_eval(valk_lval_t *sexpr);
valk_lval_t *valk_lval_eval_sexpr(valk_lval_t *sexpr);
valk_lval_t *valk_lval_join(valk_lval_t *a, valk_lval_t *b);
