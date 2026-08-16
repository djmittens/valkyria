#pragma once
#include "type_env.h"

typedef enum {
  VALK_TY_VAR,
  VALK_TY_CON,
  VALK_TY_FUN,
} valk_ty_kind_e;

typedef struct valk_type valk_type_t;

struct valk_type {
  valk_ty_kind_e kind;
  union {
    struct {
      u32 id;
      valk_type_t *link;
    } var;
    struct {
      const char *name;
      valk_type_t **args;
      u32 arity;
    } con;
    struct {
      valk_type_t **params;
      u32 param_count;
      valk_type_t *ret;
    } fun;
  };
};

typedef struct {
  valk_type_t *type;
  u32 *bound_vars;
  u32 bound_count;
} valk_type_scheme_t;

typedef struct valk_ti_scope {
  struct {
    const char *name;
    valk_type_scheme_t scheme;
    const char *resolved_type;
  } *entries;
  u32 count;
  u32 capacity;
  struct valk_ti_scope *parent;
  struct valk_ti_scope **children;
  u32 child_count;
  u32 child_capacity;
  i32 start_pos;
  i32 end_pos;
} valk_ti_scope_t;

typedef struct {
  int line;
  int col;
  const char *message;
} valk_ti_error_t;

#define VALK_TI_MAX_ERRORS       256
#define VALK_TI_PAGE_SIZE        (256 * 1024)
#define VALK_TI_EXPR_SIZE        (256 * 1024)
#define VALK_TI_MAX_TYPE_ARITY    16    // max args to a type constructor (List, Dict, etc.)
#define VALK_TI_MAX_FUN_PARAMS    64    // max function parameters (some builtins have large sigs)
#define VALK_TI_MAX_SCHEME_VARS  128    // max quantified variables in a type scheme
#define VALK_TI_MAX_VAR_MAP       16    // max entries in var substitution map

typedef struct valk_ti_page {
  u8 *data;
  sz cap;
  sz off;
  struct valk_ti_page *next;
} valk_ti_page_t;

typedef struct {
  valk_ti_page_t *page;
  u8 *expr_buf;
  sz expr_cap;
  sz expr_off;
  bool use_expr;

  u32 next_var;

  valk_ti_error_t errors[VALK_TI_MAX_ERRORS];
  u32 error_count;

  valk_type_env_t *type_env;
  valk_ti_scope_t *base_scope;
  valk_ti_scope_t *scope;

  valk_type_t *t_num;
  valk_type_t *t_str;
  valk_type_t *t_nil;
  valk_type_t *t_bool;

  struct { const char *name; valk_type_t *type; } *all_bindings;
  u32 all_bindings_count;
  u32 all_bindings_cap;

  u64 imported_sig_count;
  u64 imported_type_count;

  char lookup_buf[256];
} valk_ti_ctx_t;

valk_ti_ctx_t *valk_ti_create(valk_type_env_t *type_env);
void valk_ti_destroy(valk_ti_ctx_t *ctx);
void valk_ti_reset(valk_ti_ctx_t *ctx);
void valk_ti_promote_to_base(valk_ti_ctx_t *ctx);

valk_type_t *valk_ti_fresh_var(valk_ti_ctx_t *ctx);
valk_type_t *valk_ti_con(valk_ti_ctx_t *ctx, const char *name,
                         valk_type_t **args, u32 arity);
valk_type_t *valk_ti_fun(valk_ti_ctx_t *ctx, valk_type_t **params,
                         u32 param_count, valk_type_t *ret);

valk_type_t *valk_type_find(valk_type_t *t);
bool valk_type_occurs(valk_type_t *var, valk_type_t *type);
valk_type_t *valk_type_unify(valk_ti_ctx_t *ctx, valk_type_t *a,
                             valk_type_t *b, int line, int col);

valk_type_scheme_t valk_type_generalize(valk_ti_ctx_t *ctx,
                                        valk_ti_scope_t *scope,
                                        valk_type_t *type);
valk_type_t *valk_type_instantiate(valk_ti_ctx_t *ctx,
                                   valk_type_scheme_t *scheme);

valk_ti_scope_t *valk_ti_scope_new(valk_ti_ctx_t *ctx,
                                   valk_ti_scope_t *parent);
void valk_ti_scope_bind(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                        const char *name, valk_type_scheme_t scheme);
valk_type_scheme_t *valk_ti_scope_lookup(valk_ti_scope_t *scope,
                                         const char *name);

valk_type_t *valk_ti_parse_sig_str(valk_ti_ctx_t *ctx, const char *s);
valk_type_t *valk_ti_lookup_binding(valk_ti_ctx_t *ctx, const char *name);
const char *valk_ti_lookup_type_name(valk_ti_ctx_t *ctx, const char *name);
void valk_ti_import_new(valk_ti_ctx_t *ctx);

valk_type_t *valk_ti_infer_expr(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope,
                                valk_lval_t *expr);
void valk_ti_infer_file(valk_ti_ctx_t *ctx, valk_lval_t *exprs);

void valk_ti_populate_type_scope(valk_ti_ctx_t *ctx, valk_ti_scope_t *ti_scope,
                                valk_type_scope_t *out_scope);

sz valk_type_to_str(valk_type_t *t, char *buf, sz buf_size);
