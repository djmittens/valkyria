#pragma once
#include "parser.h"

#define VALK_TYPE_MAX_TYPES 256
#define VALK_TYPE_MAX_CONSTRUCTORS 512
#define VALK_TYPE_MAX_FIELDS 16
#define VALK_TYPE_MAX_PARAMS 8

typedef struct {
  char *name;
  char *type_name;
  u64 position;
} valk_field_t;

typedef struct {
  char *name;
  char *type_name;
  valk_field_t fields[VALK_TYPE_MAX_FIELDS];
  u64 field_count;
} valk_constructor_t;

typedef struct {
  char *name;
  char *params[VALK_TYPE_MAX_PARAMS];
  u64 param_count;
  valk_constructor_t *constructors[VALK_TYPE_MAX_CONSTRUCTORS];
  u64 constructor_count;
  bool is_product;
} valk_type_decl_t;

typedef struct {
  valk_type_decl_t *types[VALK_TYPE_MAX_TYPES];
  u64 type_count;
  valk_constructor_t *constructors[VALK_TYPE_MAX_CONSTRUCTORS];
  u64 constructor_count;
} valk_type_env_t;

valk_type_env_t *valk_type_env_new(void);
void valk_type_env_free(valk_type_env_t *env);

valk_type_decl_t *valk_type_env_find_type(valk_type_env_t *env, const char *name);
valk_constructor_t *valk_type_env_find_constructor(valk_type_env_t *env, const char *name);
valk_type_decl_t *valk_type_env_type_for_constructor(valk_type_env_t *env, const char *ctor_name);

valk_lval_t *valk_type_env_register(valk_type_env_t *env, valk_lval_t *type_form);

valk_type_env_t *valk_type_env_global(void);
void valk_type_env_reset(void);

valk_lval_t *valk_type_transform(valk_lval_t *exprs);
valk_lval_t *valk_type_transform_expr(valk_lval_t *expr);
