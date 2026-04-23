#pragma once
#include "parser.h"

// --build SRC -o OUT
//
// Evaluates SRC in the given env, treats the last-expression value as the
// entry point (must be LVAL_FUN or a quoted LVAL_CONS), binds it as
// `__entry__`, dumps the env to a temporary image, and produces a
// standalone executable at OUT. The produced binary loads the embedded
// image on startup, binds runtime argv into the env, and invokes the entry.
//
// Returns 0 on success, non-zero on error (error already printed to stderr).
int valk_build(valk_lenv_t *env, const char *script_path, const char *out_path);
