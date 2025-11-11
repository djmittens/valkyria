#pragma once

#include <stdbool.h>
#include <stddef.h>
#include "memory.h"

// Forward declaration
typedef struct valk_lenv_t valk_lenv_t;

// Perform garbage collection on the given arena
// Returns number of bytes reclaimed
size_t valk_gc_collect(valk_lenv_t* root_env, valk_mem_arena_t* arena);

// Check if GC should run (arena nearly full)
bool valk_gc_should_collect(valk_mem_arena_t* arena);