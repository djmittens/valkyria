#pragma once
#include "../parser.h"

typedef struct valk_jit_t valk_jit_t;

void valk_llvm_init(void);
void valk_llvm_init_reset(void);

valk_jit_t *valk_jit_new(void);
void valk_jit_free(valk_jit_t *jit);

valk_lval_t *valk_jit_eval(valk_jit_t *jit, valk_lenv_t *env,
                           valk_lval_t *expr);

valk_lval_t *valk_jit_eval_string(valk_jit_t *jit, valk_lenv_t *env,
                                  const char *code);

u64 valk_jit_cache_hits(valk_jit_t *jit);
u64 valk_jit_cache_misses(valk_jit_t *jit);
