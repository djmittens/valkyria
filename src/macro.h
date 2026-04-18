#pragma once
#include "parser.h"

valk_lenv_t *valk_macro_env(void);
void valk_macro_env_init(valk_lenv_t *env);
void valk_macro_env_set(const char *key, valk_lval_t *val);
valk_lval_t *valk_macro_expand_one(valk_lenv_t *macro_env, valk_lval_t *expr);
bool valk_macro_is_def(valk_lval_t *expr);

// Apply the module prefix to top-level def/sig/type forms in `ast`.
// Unqualified names get `prefix/` prepended; already-qualified names
// (containing `/`) are left alone. Bare references to locally-defined
// names are rewritten to their qualified form throughout the AST.
void valk_module_apply_prefix(valk_lval_t *ast, const char *prefix);

valk_lval_t *valk_eval_form(valk_lenv_t *env, valk_lval_t *form);
valk_lval_t *valk_load_file(valk_lenv_t *env, const char *path);

// Retrieve (and clear) any module prefix set via `(module X)` during macro
// expansion. Returns a heap-allocated string the caller must free, or NULL.
char *valk_take_pending_module_prefix(void);
