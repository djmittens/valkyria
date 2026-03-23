#pragma once
#include "parser.h"

#define VALK_MOD_MAX_CHILDREN 128
#define VALK_MOD_MAX_DEFS     1024
#define VALK_MOD_PATH_MAX     512

typedef struct valk_module {
  char *name;
  struct valk_module *parent;
  struct valk_module *children[VALK_MOD_MAX_CHILDREN];
  int child_count;

  char *def_names[VALK_MOD_MAX_DEFS];
  valk_lval_t *def_vals[VALK_MOD_MAX_DEFS];
  int def_count;

  char *resolved_path;
} valk_module_t;

valk_module_t *valk_mod_new(const char *name, valk_module_t *parent);
void valk_mod_free(valk_module_t *mod);

void valk_mod_def(valk_module_t *mod, const char *name, valk_lval_t *val);
valk_lval_t *valk_mod_get(valk_module_t *mod, const char *name);
valk_lval_t *valk_mod_resolve(valk_module_t *mod, const char *name);

valk_module_t *valk_mod_child(valk_module_t *mod, const char *name);
valk_module_t *valk_mod_find_or_create_child(valk_module_t *mod,
                                             const char *name);

void valk_mod_qualified_path(valk_module_t *mod, char *out, size_t out_sz);

valk_module_t *valk_mod_root(void);
valk_module_t *valk_mod_current(void);
void valk_mod_set_current(valk_module_t *mod);
