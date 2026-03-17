#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "eval_internal.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>

// LCOV_EXCL_BR_START - checkpoint null checks and iteration
void valk_checkpoint(valk_mem_arena_t* scratch, valk_gc_heap_t* heap,
                     valk_lenv_t* root_env) {
  (void)root_env;
  if (scratch == nullptr || heap == nullptr) {
    VALK_WARN("Checkpoint called with nullptr scratch or heap");
    return;
  }

  if (atomic_load_explicit(&scratch->stats.total_allocations, memory_order_relaxed) == 0) return;

  atomic_fetch_add_explicit(&scratch->stats.num_checkpoints, 1, memory_order_relaxed);
}
// LCOV_EXCL_BR_STOP
