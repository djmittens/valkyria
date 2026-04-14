#pragma once
#include <stdio.h>
#include "type_infer.h"

void *ti_alloc(valk_ti_ctx_t *ctx, sz bytes);
const char *ti_strdup(valk_ti_ctx_t *ctx, const char *s);
void collect_free_vars(valk_type_t *t, u32 *vars, u32 *count, u32 max);
valk_type_scheme_t ti_scheme_from_type(valk_ti_ctx_t *ctx, valk_type_t *ft);

typedef struct {
  char names[VALK_TI_MAX_VAR_MAP];
  valk_type_t *vars[VALK_TI_MAX_VAR_MAP];
  u32 count;
} ti_var_map_t;

static inline valk_type_t *get_or_create_var(valk_ti_ctx_t *ctx,
                                              ti_var_map_t *vm, char name) {
  for (u32 i = 0; i < vm->count; i++)
    if (vm->names[i] == name) return vm->vars[i];
  if (vm->count < VALK_TI_MAX_VAR_MAP) {
    valk_type_t *v = valk_ti_fresh_var(ctx);
    vm->names[vm->count] = name;
    vm->vars[vm->count] = v;
    vm->count++;
    return v;
  }
  fprintf(stderr, "[type-infer] warning: type variable map full (max %d), creating fresh var for '%c'\n",
          VALK_TI_MAX_VAR_MAP, name);
  return valk_ti_fresh_var(ctx);
}
