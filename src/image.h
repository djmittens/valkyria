#pragma once
#include "parser.h"

// Phase 0: image dump/load for a single lval (and its reachable subgraph).
// Supports: LVAL_NUM, LVAL_STR, LVAL_SYM, LVAL_NIL, LVAL_CONS.
// Not yet: LVAL_FUN, LVAL_ERR, LVAL_REF, LVAL_HANDLE, LVAL_DICT, envs.
//
// Returns 0 on success, negative on failure.
int valk_image_dump(valk_lval_t *val, const char *path);

// Loads an image. Returned pointer is inside a malloc'd buffer owned by the
// image; call valk_image_load_free to release.
valk_lval_t *valk_image_load(const char *path);

// Release a loaded image. Invalidates every lval reachable from the root.
void valk_image_load_free(valk_lval_t *root);
