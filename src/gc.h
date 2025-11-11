#pragma once

#include <stdbool.h>
#include <stddef.h>
#include "memory.h"

// Forward declaration
typedef struct valk_lenv_t valk_lenv_t;

// Perform mark & sweep garbage collection on an arena
// Returns number of bytes that would be reclaimed (currently informational only)
size_t valk_gc_collect_arena(valk_lenv_t* root_env, valk_mem_arena_t* arena);

// Check if GC should run (arena nearly full)
bool valk_gc_should_collect_arena(valk_mem_arena_t* arena);
