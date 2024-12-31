#pragma once
#include <stdio.h>

typedef enum { LVAL_NUM, LVAL_ERROR } valk_lres_t;
typedef enum { LERR_DIV_ZERO, LERR_BAD_OP, LERR_BAD_NUM } valk_lerr_t;

typedef struct {
  valk_lres_t type;
  union {
    long val;
    valk_lerr_t err;
  };
} valk_lval_t;

static inline valk_lval_t valk_lval_num(long x) {
  valk_lval_t res = {
      .type = LVAL_NUM,
      .val = x,
  };
  return res;
}

static inline valk_lval_t valk_lval_err(valk_lerr_t err) {
  valk_lval_t res = {
      .type = LVAL_ERROR,
      .err = err,
  };
  return res;
}

static inline void valk_lval_print(valk_lval_t val) {
  switch (val.type) {
  case LVAL_NUM:
    printf("%li\n", val.val);
    break;
  case LVAL_ERROR:
    switch (val.err) {
    case LERR_DIV_ZERO:
      printf("Error: Division By Zero\n");
      break;
    case LERR_BAD_OP:
      printf("Error: Invalid Operation\n");
      break;
    case LERR_BAD_NUM:
      printf("Error: Invalid Number\n");
      break;
    }
    break;
  }
}

static inline void valk_lval_println(valk_lval_t val){
  valk_lval_print(val);
  printf("\n");
}
