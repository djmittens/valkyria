#pragma once
#include "parser.h"

valk_lenv_t *valk_macro_env(void);
void valk_macro_env_set(const char *key, valk_lval_t *val);
valk_lval_t *valk_macro_expand_one(valk_lenv_t *macro_env, valk_lval_t *expr);
bool valk_macro_is_def(valk_lval_t *expr);

// Apply the module prefix to top-level def/sig/type forms in `ast`.
// Unqualified names get `prefix/` prepended; already-qualified names
// (containing `/`) are left alone — except for sibling references: a
// symbol `X/Y/...` is rewritten to `A/X/Y/...` when some ancestor `A`
// of `prefix` (including `prefix` itself) has a loaded sibling `A/X`.
void valk_module_apply_prefix(valk_lval_t *ast, const char *prefix);

// Registry of module prefixes loaded in the current thread. Populated
// by valk_builtin_load before evaluating each file so sibling rewriting
// in child files can see already-loaded ancestors.
void valk_mod_registry_add(const char *prefix);
bool valk_mod_registry_has(const char *prefix);

valk_lval_t *valk_eval_form(valk_lenv_t *env, valk_lval_t *form);
valk_lval_t *valk_load_file(valk_lenv_t *env, const char *path);
