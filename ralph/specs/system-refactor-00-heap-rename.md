# Heap Rename: Remove Vestigial "2" Suffixes

## Overview

Remove all vestigial "2" suffixes from GC heap types and functions. The original malloc-based heap no longer exists — `valk_gc_heap2_t` IS the heap. This is a purely mechanical rename with no logic changes. Also remove the `valk_gc_malloc_*` wrapper functions, inlining callers to direct `valk_gc_heap_*` calls.

## Dependencies

- None. This is the first spec in the system-refactor series.
- Subsequent specs (`system-refactor-01-types.md` through `system-refactor-07-cleanup.md`) depend on this rename being complete.

## Requirements

### Type Renames

Apply these exact text replacements across all `.c` and `.h` files in `src/` and `test/`. Order matters — do longer names first to avoid partial matches.

| Old | New |
|-----|-----|
| `valk_gc_mark_ctx2_t` | `valk_gc_mark_ctx_t` |
| `struct valk_gc_mark_ctx2` | `struct valk_gc_mark_ctx` |
| `valk_gc_stats2_t` | `valk_gc_stats_t` |
| `struct valk_gc_stats2` | `struct valk_gc_stats` |
| `valk_gc_heap2_t` | `valk_gc_heap_t` |
| `struct valk_gc_heap2` | `struct valk_gc_heap` |
| `valk_gc_tlab2_t` | `valk_gc_tlab_t` |
| `struct valk_gc_tlab2` | `struct valk_gc_tlab` |
| `valk_gc_page2_t` | `valk_gc_page_t` |
| `struct valk_gc_page2` | `struct valk_gc_page` |

### Function Renames

| Old prefix/name | New prefix/name |
|-----------------|-----------------|
| `valk_gc_heap2_` | `valk_gc_heap_` |
| `valk_gc_tlab2_` | `valk_gc_tlab_` |
| `valk_gc_page2_` | `valk_gc_page_` |
| `valk_gc_sweep_page2` | `valk_gc_sweep_page` |
| `mark_children2` | `mark_children` |
| `mark_env2` | `mark_env` |
| `mark_lval2` | `mark_lval` |

### Static Variable Renames in gc_mark.c

| Old | New |
|-----|-----|
| `__gc_heap2_offered` | `__gc_heap_offered` |
| `__gc_heap2_terminated` | `__gc_heap_terminated` |
| `__gc_heap2_current` | `__gc_heap_current` |
| `__gc_heap2_term_lock` | `__gc_heap_term_lock` |
| `__gc_heap2_term_cond` | `__gc_heap_term_cond` |

### Remove valk_gc_malloc_* Wrappers

In `src/gc.c` (lines ~331-397), the `valk_gc_malloc_*` functions are thin wrappers. Replace all callers with direct calls:

| Old call | Replace with |
|----------|-------------|
| `valk_gc_malloc_heap_init(size)` | `valk_gc_heap_create(size)` |
| `valk_gc_malloc_heap_alloc(heap, size, type)` | `valk_gc_heap_alloc(heap, size, type)` |
| `valk_gc_malloc_heap_destroy(heap)` | `valk_gc_heap_destroy(heap)` |
| `valk_gc_malloc_collect(heap, root)` | `valk_gc_heap_collect(heap)` |

Functions with their own logic get simple renames:

| Old | New |
|-----|-----|
| `valk_gc_malloc_set_root` | `valk_gc_set_root` |
| `valk_gc_malloc_should_collect` | `valk_gc_should_collect` |
| `valk_gc_malloc_print_stats` | `valk_gc_print_stats` |

Then delete the wrapper function bodies from `src/gc.c`.

### Typedef and Forward Declaration Cleanup

- Remove `typedef valk_gc_heap2_t valk_gc_malloc_heap_t;` from `src/gc_heap.h` (line 279)
- Remove orphaned `struct valk_gc_tlab;` forward declaration from `src/memory.h` (line 301)

### LSAN Suppressions Update

In `lsan_suppressions.txt`, rename:
- `leak:valk_gc_heap2_alloc` to `leak:valk_gc_heap_alloc`
- `leak:valk_gc_malloc_heap_alloc` to `leak:valk_gc_heap_alloc`

### Files Affected

Source: `src/gc_heap.h`, `src/gc_heap.c`, `src/gc_heap_lifecycle.c`, `src/gc_heap_sweep.c`, `src/gc_mark.c`, `src/gc.h`, `src/gc.c`, `src/gc_stats.c`, `src/gc_checkpoint.c`, `src/gc_evacuation.c`, `src/gc_region.c`, `src/memory.h`, `src/memory.c`, `src/lenv.c`, `src/repl.c`, `src/builtins_io.c`, `src/builtins_aio.c`, `src/builtins_mem.c`, `src/aio/aio.h`, `src/aio/aio_uv.c`, `src/aio/aio_internal.h`, `src/aio/aio_metrics.h`, `src/aio/aio_metrics.c`, `src/aio/aio_diagnostics_builtins.c`, `src/aio/system/aio_system.c`, `src/aio/system/aio_system.h`

Tests: `test/test_memory.c`, `test/unit/test_gc.c`

Other: `lsan_suppressions.txt`

## Acceptance Criteria

- [ ] `make build` succeeds with zero warnings related to renamed symbols
- [ ] `make test-c` passes (all existing C tests)
- [ ] `make test-valk` passes (all existing Valk tests)
- [ ] `grep -rE 'heap2|tlab2|page2|stats2|mark_ctx2|valk_gc_malloc_' src/ test/` returns no matches
- [ ] `grep -rn 'valk_gc_malloc_heap_t' src/` returns no matches
- [ ] `grep -n 'struct valk_gc_tlab;' src/memory.h` returns no matches
