#pragma once
#include "parser.h"

valk_lenv_t *valk_macro_env(void);
void valk_macro_env_init(valk_lenv_t *env);
valk_lval_t *valk_macro_expand_one(valk_lenv_t *macro_env, valk_lval_t *expr);
bool valk_macro_is_def(valk_lval_t *expr);

// Apply the module prefix to top-level def/sig/type forms in `ast`.
// Unqualified names get `prefix/` prepended; already-qualified names
// (containing `/`) are left alone. Bare references to locally-defined
// names are rewritten to their qualified form throughout the AST.
// Whole-file variant used by static tooling (compile/process); does not
// resolve load-context aliases.
void valk_module_apply_prefix(valk_lval_t *ast, const char *prefix);

// Per-form rewriting used by the loader. `locals` is the set of bare def
// names in the current file's module region.
typedef struct valk_module_locals valk_module_locals_t;
valk_module_locals_t *valk_module_locals_new(void);
void valk_module_locals_collect(valk_module_locals_t *locals,
                                valk_lval_t *form);
void valk_module_locals_free(valk_module_locals_t *locals);

// Rewrite the top-level form held in `cell` (a cons cell of the file's form
// list) in place: qualify bare def/sig names with `prefix` (when
// qualify_defs), rewrite bare references to `locals` as `prefix/name`, and
// (when use_aliases) resolve qualified references through the module aliases
// of the current load-context chain.
void valk_module_rewrite_form(valk_lval_t *cell, const char *prefix,
                              valk_module_locals_t *locals, bool qualify_defs,
                              bool use_aliases);

// Implemented in load.c: resolve a qualified name against the module aliases
// visible from the current load context. Returns a malloc'd replacement
// (caller frees) or NULL if no alias applies.
char *valk_load_resolve_alias(const char *name);

// Implemented in load.c: resolve a load path exactly as the runtime would
// for a file living in `dir` (NULL when none). `resolved` must hold
// PATH_MAX bytes.
bool valk_load_resolve_from(const char *dir, const char *path,
                            char *resolved);

valk_lval_t *valk_load_file(valk_lenv_t *env, const char *path);
