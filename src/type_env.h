#pragma once
#include "parser.h"

typedef struct {
  char *name;
  char *type_name;
  u64 position;
} valk_field_t;

typedef struct {
  char *name;
  char *type_name;
  valk_field_t *fields;
  u64 field_count;
  u64 field_capacity;
} valk_constructor_t;

typedef struct {
  char *name;
  char **params;
  u64 param_count;
  u64 param_capacity;
  valk_constructor_t **constructors;
  u64 constructor_count;
  u64 constructor_capacity;
  bool is_product;
} valk_type_decl_t;

typedef struct valk_type_scope {
  struct { const char *var; const char *type; } *entries;
  u64 count;
  u64 capacity;
  struct valk_type_scope *parent;
} valk_type_scope_t;

typedef struct {
  char *name;
  char **param_types;
  u64 param_count;
  u64 param_capacity;
  char *return_type;
} valk_type_sig_t;

typedef struct {
  valk_type_decl_t **types;
  u64 type_count;
  u64 type_capacity;
  valk_constructor_t **constructors;
  u64 constructor_count;
  u64 constructor_capacity;
  valk_type_sig_t **sigs;
  u64 sig_count;
  u64 sig_capacity;
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
