#pragma once
#include "parser.h"

valk_lenv_t *valk_macro_env(void);
void valk_macro_env_set(const char *key, valk_lval_t *val);
valk_lval_t *valk_macro_expand_one(valk_lenv_t *macro_env, valk_lval_t *expr);
bool valk_macro_is_def(valk_lval_t *expr);
void valk_module_rewrite(valk_lval_t *ast, const char *prefix);

valk_lval_t *valk_eval_form(valk_lenv_t *env, valk_lval_t *form);
valk_lval_t *valk_load_file(valk_lenv_t *env, const char *path);
