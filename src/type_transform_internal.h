#pragma once
#include "type_env.h"

// ---------------------------------------------------------------------------
// Internal helpers shared between type_transform.c and type_transform_forms.c
// ---------------------------------------------------------------------------

// Scope-based type tracking
void valk_tt_scope_add(valk_type_scope_t *scope, const char *var, const char *type);
const char *valk_tt_scope_find_type(valk_type_scope_t *scope, const char *var);

// AST predicates
bool valk_tt_is_keyword(valk_lval_t *v);
bool valk_tt_is_qexpr(valk_lval_t *v);

// Main dispatcher (mutual recursion with form transformers)
valk_lval_t *valk_tt_transform_expr(valk_type_env_t *env,
                                    valk_type_scope_t *scope,
                                    valk_lval_t *expr);

// Constructor lookup helpers (used by form transformers and binding tracker)
valk_constructor_t *valk_tt_find_constructor_by_short_name(valk_type_env_t *env,
                                                            const char *short_name);

// Form transformers (defined in type_transform_forms.c)
valk_lval_t *valk_tt_transform_constructor_call(valk_type_env_t *env,
                                                 valk_type_scope_t *scope,
                                                 valk_constructor_t *ctor,
                                                 valk_lval_t *args);
valk_lval_t *valk_tt_transform_accessor(valk_type_env_t *env,
                                         valk_type_scope_t *scope,
                                         const char *sym,
                                         valk_lval_t *arg);
valk_lval_t *valk_tt_transform_match(valk_type_env_t *env,
                                      valk_type_scope_t *scope,
                                      valk_lval_t *match_form);
valk_lval_t *valk_tt_transform_record_update(valk_type_env_t *env,
                                              valk_type_scope_t *scope,
                                              const char *var_name,
                                              const char *type_name,
                                              valk_lval_t *expr);
valk_lval_t *valk_tt_resolve_field_access(valk_type_env_t *env,
                                           valk_type_scope_t *scope,
                                           valk_lval_t *var_expr,
                                           const char *var_name,
                                           const char *field_name);
