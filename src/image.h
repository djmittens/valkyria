#pragma once
#include "parser.h"

// Phase 1: image dump/load for lvals and environments.
//
// Supported lval types: LVAL_NUM, LVAL_STR, LVAL_SYM, LVAL_ERR, LVAL_NIL,
// LVAL_CONS, LVAL_FUN (lambdas + builtins). Not yet: LVAL_REF, LVAL_HANDLE,
// LVAL_DICT.
//
// Builtins are dumped as stubs carrying only `fun.name`. On load, each stub
// is resolved against a caller-supplied `registry` env (typically built via
// valk_lenv_builtins). If a stub's name is not found in the registry, load
// fails.
//
// Symbols with LVAL_FLAG_INTERNED are re-interned on load so pointer
// comparisons against the live intern table work.

int valk_image_dump(valk_lval_t *val, const char *path);
int valk_image_dump_env(valk_lenv_t *env, const char *path);

// Default load uses no registry — any builtin stub causes failure.
valk_lval_t *valk_image_load(const char *path);
valk_lval_t *valk_image_load_ex(const char *path, valk_lenv_t *registry);
valk_lenv_t *valk_image_load_env(const char *path, valk_lenv_t *registry);

// Load an env image and wrap it in a fresh overlay env suitable for runtime
// mutation. The returned env has parent = the loaded (immortal) env: new
// defs land in the overlay while lookups fall through to the image. The
// image buffer is kept alive by the overlay's parent pointer and released
// by valk_image_load_free_overlay.
valk_lenv_t *valk_image_load_overlay(const char *path, valk_lenv_t *registry);
void valk_image_load_free_overlay(valk_lenv_t *overlay);

// Release a loaded image. Invalidates every object reachable from the root.
void valk_image_load_free(valk_lval_t *root);
void valk_image_load_free_env(valk_lenv_t *root);
