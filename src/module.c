#include "module.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

static valk_module_t *g_root_mod = NULL;
static _Thread_local valk_module_t *g_current_mod = NULL;

valk_module_t *valk_mod_new(const char *name, valk_module_t *parent) {
  valk_module_t *mod = calloc(1, sizeof(valk_module_t));
  mod->name = strdup(name);
  mod->parent = parent;
  if (parent) {
    if (parent->child_count < VALK_MOD_MAX_CHILDREN)
      parent->children[parent->child_count++] = mod;
  }
  return mod;
}

void valk_mod_free(valk_module_t *mod) {
  if (!mod) return;
  for (int i = 0; i < mod->child_count; i++)
    valk_mod_free(mod->children[i]);
  for (int i = 0; i < mod->def_count; i++)
    free(mod->def_names[i]);
  free(mod->name);
  free(mod->resolved_path);
  free(mod);
}

void valk_mod_def(valk_module_t *mod, const char *name, valk_lval_t *val) {
  for (int i = 0; i < mod->def_count; i++) {
    if (strcmp(mod->def_names[i], name) == 0) {
      mod->def_vals[i] = val;
      return;
    }
  }
  if (mod->def_count < VALK_MOD_MAX_DEFS) {
    mod->def_names[mod->def_count] = strdup(name);
    mod->def_vals[mod->def_count] = val;
    mod->def_count++;
  }
}

valk_lval_t *valk_mod_get(valk_module_t *mod, const char *name) {
  for (int i = 0; i < mod->def_count; i++)
    if (strcmp(mod->def_names[i], name) == 0)
      return mod->def_vals[i];
  return NULL;
}

valk_module_t *valk_mod_child(valk_module_t *mod, const char *name) {
  for (int i = 0; i < mod->child_count; i++)
    if (strcmp(mod->children[i]->name, name) == 0)
      return mod->children[i];
  return NULL;
}

valk_module_t *valk_mod_find_or_create_child(valk_module_t *mod,
                                             const char *name) {
  valk_module_t *child = valk_mod_child(mod, name);
  if (child) return child;
  return valk_mod_new(name, mod);
}

valk_lval_t *valk_mod_resolve(valk_module_t *mod, const char *name) {
  const char *slash = strchr(name, '/');

  if (slash) {
    size_t seg_len = (size_t)(slash - name);
    char seg[256];
    if (seg_len >= sizeof(seg)) return NULL;
    memcpy(seg, name, seg_len);
    seg[seg_len] = '\0';

    valk_module_t *child = valk_mod_child(mod, seg);
    if (child) {
      valk_lval_t *v = valk_mod_resolve(child, slash + 1);
      if (v) return v;
    }

    if (mod->parent) {
      valk_lval_t *v = valk_mod_resolve(mod->parent, name);
      if (v) return v;
    }
    return NULL;
  }

  valk_lval_t *v = valk_mod_get(mod, name);
  if (v) return v;

  if (mod->parent)
    return valk_mod_resolve(mod->parent, name);

  return NULL;
}

void valk_mod_qualified_path(valk_module_t *mod, char *out, size_t out_sz) {
  if (!mod->parent || !mod->parent->parent) {
    snprintf(out, out_sz, "%s", mod->name);
    return;
  }
  char parent_path[VALK_MOD_PATH_MAX];
  valk_mod_qualified_path(mod->parent, parent_path, sizeof(parent_path));
  snprintf(out, out_sz, "%s/%s", parent_path, mod->name);
}

valk_module_t *valk_mod_root(void) {
  if (!g_root_mod)
    g_root_mod = valk_mod_new("root", NULL);
  return g_root_mod;
}

valk_module_t *valk_mod_current(void) {
  return g_current_mod;
}

void valk_mod_set_current(valk_module_t *mod) {
  g_current_mod = mod;
}
