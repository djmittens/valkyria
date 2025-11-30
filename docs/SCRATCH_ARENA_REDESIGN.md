# Scratch Arena Redesign: Checkpoint-Based Memory Management

## Executive Summary

This document outlines a comprehensive plan to make scratch arenas the default allocator with periodic checkpoint-based evacuation of escaping values to the GC heap. The design emphasizes simplicity, debuggability, and performance through a two-phase evacuation strategy.

## Problem Statement

Current scratch arena behavior:
1. Scratch arena resets completely between REPL expressions
2. No mechanism to checkpoint/reset during script execution
3. Long-running scripts will exhaust scratch space (4 MiB default)
4. Values stored in environments can become dangling pointers after arena reset
5. No telemetry to understand allocation patterns

### Edge Cases Requiring Careful Handling

| Scenario | Challenge | Impact |
|----------|-----------|--------|
| **Environment bindings** | `(def x 10)` stores value in root env | Value must survive arena reset |
| **Closures** | `(fn (x) (+ x 1))` captures environment | Function, formals, body must survive |
| **Multi-statement scripts** | `(def x 1) (print x)` | `x` needed across statement boundary |
| **Nested function calls** | `(f (g (h x)))` | Intermediate results on call stack |
| **Cons cell chains** | `'(1 2 3 4 5...)` | Deep structures span many allocations |
| **String/symbol interning** | Multiple refs to same string | Avoid duplicate evacuations |
| **Environments chains** | Lexical + fallback parent chains | Must evacuate entire reachable graph |

---

## Design Principles

1. **No flag mutation after allocation** - Values don't change state; we inspect, not mutate
2. **Two-phase evacuation** - First copy all escaping values, then fix all pointers
3. **Root-based reachability** - Escape = reachable from root environment
4. **Explicit checkpoints** - Predictable reset points, not implicit heuristics
5. **Comprehensive telemetry** - Every allocation/evacuation is observable
6. **Graceful overflow** - If scratch is full, fall back to heap with a warning (never crash)

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                         Evaluation Flow                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐     │
│   │  Parse   │───▶│  Eval    │───▶│  Result  │───▶│  Print   │     │
│   │(scratch) │    │(scratch) │    │          │    │          │     │
│   └──────────┘    └──────────┘    └──────────┘    └──────────┘     │
│        │               │               │                            │
│        └───────────────┴───────────────┘                            │
│                        │                                            │
│                        ▼                                            │
│              ┌──────────────────┐                                   │
│              │   CHECKPOINT     │                                   │
│              │   ────────────   │                                   │
│              │ 1. Mark roots    │                                   │
│              │ 2. Evacuate      │                                   │
│              │ 3. Update ptrs   │                                   │
│              │ 4. Reset arena   │                                   │
│              └──────────────────┘                                   │
│                        │                                            │
│                        ▼                                            │
│              ┌──────────────────┐                                   │
│              │   GC Heap        │ (escaping values now here)        │
│              └──────────────────┘                                   │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Implementation Task List

### Phase 1: Telemetry Infrastructure

**Goal**: Build observability before changing behavior

#### Task 1.1: Arena Statistics Structure

**File**: `src/memory.h`

- [ ] Add `stats` struct to `valk_mem_arena_t` with fields:
  - [ ] `size_t total_allocations` - Count of alloc calls
  - [ ] `size_t total_bytes_allocated` - Sum of all requested bytes
  - [ ] `size_t high_water_mark` - Maximum offset reached
  - [ ] `size_t num_resets` - Count of arena_reset calls
  - [ ] `size_t num_checkpoints` - Count of checkpoint evacuations
  - [ ] `size_t bytes_evacuated` - Total bytes copied to heap
  - [ ] `size_t values_evacuated` - Count of values copied to heap
  - [ ] `size_t overflow_fallbacks` - Count of heap fallback allocations due to full arena
  - [ ] `size_t overflow_bytes` - Bytes allocated via heap fallback
- [ ] Initialize all stats fields to 0 in `valk_mem_arena_init()`
- [ ] Update `total_allocations` in `valk_mem_arena_alloc()`
- [ ] Update `total_bytes_allocated` in `valk_mem_arena_alloc()`
- [ ] Update `high_water_mark` in `valk_mem_arena_alloc()` when offset exceeds previous max
- [ ] Increment `num_resets` in `valk_mem_arena_reset()`

#### Task 1.2: Scratch Overflow Fallback to Heap

**File**: `src/memory.c`

When scratch arena is full, fall back to heap allocation with a warning instead of crashing.

- [ ] Modify `valk_mem_arena_alloc()` to detect when allocation would exceed capacity
- [ ] When overflow detected:
  - [ ] Emit warning: `VALK_WARN("Scratch arena full (%zu/%zu bytes), falling back to heap. Consider increasing SCRATCH_ARENA_BYTES.", arena->offset, arena->capacity)`
  - [ ] Only emit warning once per checkpoint cycle (use a `warned_overflow` flag, reset in `valk_mem_arena_reset()`)
  - [ ] Increment `arena->stats.overflow_fallbacks`
  - [ ] Add bytes to `arena->stats.overflow_bytes`
  - [ ] Allocate from `valk_thread_ctx.heap` instead using `valk_gc_malloc_heap_alloc()`
  - [ ] Return the heap-allocated pointer (it will have LVAL_ALLOC_HEAP flag)
- [ ] Add `bool warned_overflow` field to `valk_mem_arena_t`
- [ ] Reset `warned_overflow = false` in `valk_mem_arena_reset()`

**File**: `src/memory.h`

- [ ] Add `valk_gc_malloc_heap_t* fallback_heap` field to `valk_mem_arena_t` (set during init)
- [ ] Or: access heap via `valk_thread_ctx.heap` (simpler, already available)

**Key invariant**: Overflow allocations go directly to heap, so they:
- Already have correct LVAL_ALLOC_HEAP flags
- Are already in GC object list
- Don't need evacuation (already in heap)
- Will be collected by normal GC

#### Task 1.3: GC Heap Hard Limit and Emergency Collection

**File**: `src/gc.h`

Add a hard maximum heap size. When reached, trigger emergency GC. If still insufficient, crash gracefully.

- [ ] Add `size_t hard_limit` field to `valk_gc_malloc_heap_t` (absolute max heap size)
- [ ] Add `size_t emergency_collections` to stats (count of emergency GCs triggered)
- [ ] Add `bool in_emergency_gc` flag to prevent recursive emergency GC

**File**: `src/gc.c`

- [ ] Modify `valk_gc_malloc_heap_init()` to accept `hard_limit` parameter
  - [ ] Default: `gc_threshold * 2` or configurable via env var `VALK_HEAP_HARD_LIMIT`
- [ ] Modify `valk_gc_malloc_heap_alloc()` to check hard limit:
  - [ ] If `allocated_bytes + request > hard_limit`:
    - [ ] If not already `in_emergency_gc`:
      - [ ] Set `in_emergency_gc = true`
      - [ ] Log: `VALK_WARN("Heap at hard limit (%zu/%zu bytes), triggering emergency GC", ...)`
      - [ ] Call `valk_gc_malloc_collect(heap)`
      - [ ] Increment `stats.emergency_collections`
      - [ ] Set `in_emergency_gc = false`
    - [ ] Re-check if allocation now fits
    - [ ] If still doesn't fit after emergency GC:
      - [ ] Log: `VALK_ERROR("FATAL: Heap exhausted after emergency GC. Requested %zu bytes, available %zu/%zu")`
      - [ ] Call `valk_gc_malloc_print_stats(heap)` to dump diagnostics
      - [ ] `abort()` with clear error message
- [ ] Add `void valk_gc_set_hard_limit(valk_gc_malloc_heap_t* heap, size_t limit)`

**File**: `src/repl.c`

- [ ] Check for `VALK_HEAP_HARD_LIMIT` environment variable at startup
- [ ] Pass hard limit to `valk_gc_malloc_heap_init()`
- [ ] Log configured limits at startup: `"GC heap: threshold=%zu, hard_limit=%zu"`

#### Task 1.4: GC Heap Statistics Extension

**File**: `src/gc.h`

- [ ] Add `stats` struct to `valk_gc_malloc_heap_t` with fields:
  - [ ] `size_t overflow_allocations` - Allocations received from scratch overflow
  - [ ] `size_t evacuations_from_scratch` - Values received from scratch
  - [ ] `size_t evacuation_bytes` - Bytes received from scratch
  - [ ] `size_t evacuation_pointer_fixups` - Pointer updates during evacuation
  - [ ] `size_t emergency_collections` - Emergency GCs triggered at hard limit
  - [ ] `size_t peak_usage` - Maximum allocated_bytes ever reached
- [ ] Initialize stats fields to 0 in `valk_gc_malloc_heap_init()`
- [ ] Update `peak_usage` in `valk_gc_malloc_heap_alloc()` when new peak reached

#### Task 1.5: Statistics API

**File**: `src/memory.c`

- [ ] Implement `void valk_mem_arena_print_stats(valk_mem_arena_t* arena, FILE* out)`
  - [ ] Print current usage (offset / capacity)
  - [ ] Print high water mark
  - [ ] Print total allocations count
  - [ ] Print total bytes requested
  - [ ] Print reset count
  - [ ] Print overflow fallback count and bytes (with warning if > 0)
- [ ] Implement `void valk_mem_arena_reset_stats(valk_mem_arena_t* arena)`
  - [ ] Zero all stats fields except high_water_mark

**File**: `src/gc.c`

- [ ] Implement `void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, FILE* out)`
  - [ ] Print scratch arena stats
  - [ ] Print GC heap stats
  - [ ] Print derived metrics (avg values per checkpoint, evacuation rate)

#### Task 1.6: Lisp Builtins for Stats

**File**: `src/parser.c`

- [ ] Add `(memory-stats)` builtin
  - [ ] Call `valk_memory_print_stats()` to stderr
  - [ ] Return nil
- [ ] Add `(arena-usage)` builtin
  - [ ] Return current scratch arena offset as number
- [ ] Add `(heap-usage)` builtin
  - [ ] Return current GC heap allocated_bytes as number
- [ ] Add `(gc-stats)` builtin
  - [ ] Call `valk_gc_malloc_print_stats()` (existing function)
  - [ ] Return nil
- [ ] Add `(heap-hard-limit)` builtin
  - [ ] Return current hard limit as number
- [ ] Add `(set-heap-hard-limit n)` builtin
  - [ ] Validate n > current allocated_bytes
  - [ ] Call `valk_gc_set_hard_limit()`
  - [ ] Return previous limit
- [ ] Register all new builtins in `valk_lenv_builtins()`

#### Task 1.7: Phase 1 Tests

**File**: `test/test_memory_stats.c`

- [ ] Create test file with test harness includes
- [ ] Test `test_arena_stats_init` - verify stats start at 0
- [ ] Test `test_arena_stats_alloc` - verify allocation updates stats
- [ ] Test `test_arena_stats_high_water` - verify high water mark tracking
- [ ] Test `test_arena_stats_reset` - verify reset increments counter
- [ ] Test `test_arena_overflow_fallback` - verify heap fallback when arena full:
  - [ ] Create small arena (e.g., 1KB)
  - [ ] Allocate until full
  - [ ] Verify next allocation succeeds (from heap)
  - [ ] Verify `overflow_fallbacks` stat incremented
  - [ ] Verify warning emitted (check stderr or log)
  - [ ] Verify warning only emitted once per cycle
  - [ ] Verify overflow allocation has LVAL_ALLOC_HEAP flag
- [ ] Test `test_arena_overflow_after_reset` - verify warning resets after checkpoint
- [ ] Test `test_heap_hard_limit_emergency_gc` - verify emergency GC triggers at hard limit:
  - [ ] Create heap with small hard limit (e.g., 64KB)
  - [ ] Allocate until approaching hard limit
  - [ ] Verify emergency GC is triggered
  - [ ] Verify `emergency_collections` stat incremented
  - [ ] Verify allocation succeeds after GC frees memory
- [ ] Test `test_heap_hard_limit_fatal` - verify crash when truly exhausted:
  - [ ] Create heap with tiny hard limit
  - [ ] Fill with values that can't be collected (all reachable from root)
  - [ ] Verify allocation fails with clear error message
  - [ ] (May need to fork() to test crash behavior)
- [ ] Test `test_heap_peak_usage` - verify peak usage tracking
- [ ] Add test file to Makefile

---

### Phase 2: Forwarding Pointer Infrastructure

**Goal**: Enable values to indicate they've moved

#### Task 2.1: Forwarding Pointer Type

**File**: `src/parser.h`

- [ ] Add `LVAL_FORWARD` to `valk_ltype_e` enum (value 12 or next available)
- [ ] Add `valk_lval_t* forward` member to the union in `valk_lval_t`
- [ ] Document that LVAL_FORWARD is only valid during evacuation

**File**: `src/parser.c`

- [ ] Add "forward" case to `valk_ltype_name()` function
- [ ] Add LVAL_FORWARD case to `valk_lval_print()` (print as `<forward:0xADDR>`)

#### Task 2.2: Forwarding Pointer Helpers

**File**: `src/gc.c` (or new `src/evacuate.c`)

- [ ] Implement `static inline void valk_lval_set_forward(valk_lval_t* src, valk_lval_t* dst)`
  - [ ] Set src->flags to LVAL_FORWARD | LVAL_ALLOC_SCRATCH
  - [ ] Set src->forward to dst
- [ ] Implement `static inline bool valk_lval_is_forwarded(valk_lval_t* v)`
  - [ ] Return LVAL_TYPE(v) == LVAL_FORWARD
- [ ] Implement `static inline valk_lval_t* valk_lval_follow_forward(valk_lval_t* v)`
  - [ ] Loop while v != NULL and LVAL_TYPE(v) == LVAL_FORWARD
  - [ ] Return final v

#### Task 2.3: Arena Pointer Check Helper

**File**: `src/memory.c`

- [ ] Implement `bool valk_ptr_in_arena(valk_mem_arena_t* arena, void* ptr)`
  - [ ] Calculate arena start: `(uint8_t*)arena->heap`
  - [ ] Calculate arena end: `(uint8_t*)arena->heap + arena->capacity`
  - [ ] Return true if ptr >= start && ptr < end

**File**: `src/memory.h`

- [ ] Add declaration for `valk_ptr_in_arena()`

#### Task 2.4: Phase 2 Tests

**File**: `test/test_forward.c`

- [ ] Create test file
- [ ] Test `test_set_forward` - verify forwarding pointer is set correctly
- [ ] Test `test_is_forwarded` - verify detection works
- [ ] Test `test_follow_forward` - verify chain following works
- [ ] Test `test_ptr_in_arena` - verify arena range checking
- [ ] Add test file to Makefile

---

### Phase 3: Two-Phase Evacuation Core

**Goal**: Implement the evacuation algorithm

#### Task 3.1: Evacuation Context Structure

**File**: `src/gc.h`

- [ ] Define `valk_evacuation_ctx_t` struct:
  - [ ] `valk_mem_arena_t* scratch` - Source arena
  - [ ] `valk_gc_malloc_heap_t* heap` - Destination heap
  - [ ] `valk_lval_t** worklist` - Stack of values to process children
  - [ ] `size_t worklist_count` - Current worklist size
  - [ ] `size_t worklist_capacity` - Allocated capacity
  - [ ] `size_t values_copied` - Stats for this evacuation
  - [ ] `size_t bytes_copied` - Stats for this evacuation
  - [ ] `size_t pointers_fixed` - Stats for this evacuation

#### Task 3.2: Worklist Management

**File**: `src/gc.c`

- [ ] Implement `static void evac_worklist_push(valk_evacuation_ctx_t* ctx, valk_lval_t* v)`
  - [ ] Grow worklist if at capacity (double size)
  - [ ] Add v to worklist[worklist_count++]
- [ ] Implement `static valk_lval_t* evac_worklist_pop(valk_evacuation_ctx_t* ctx)`
  - [ ] Return NULL if worklist_count == 0
  - [ ] Return worklist[--worklist_count]
- [ ] Implement `static void evac_worklist_init(valk_evacuation_ctx_t* ctx)`
  - [ ] Allocate initial capacity (e.g., 256 pointers)
  - [ ] Set count to 0
- [ ] Implement `static void evac_worklist_free(valk_evacuation_ctx_t* ctx)`
  - [ ] Free worklist array

#### Task 3.3: GC Object List Helper

**File**: `src/gc.c`

- [ ] Implement `void valk_gc_add_to_objects(valk_gc_malloc_heap_t* heap, valk_lval_t* v)`
  - [ ] Get header pointer: `((valk_gc_header_t*)v) - 1`
  - [ ] Set header->gc_next = heap->objects
  - [ ] Set heap->objects = header
  - [ ] Update allocated_bytes

**File**: `src/gc.h`

- [ ] Add declaration for `valk_gc_add_to_objects()`

#### Task 3.4: Phase 1 - Copy Single Value

**File**: `src/gc.c`

- [ ] Implement `static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v)`
  - [ ] Return NULL if v is NULL
  - [ ] Return v->forward if already forwarded (LVAL_TYPE(v) == LVAL_FORWARD)
  - [ ] Return v if not in scratch (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH)
  - [ ] Allocate new_val in heap using VALK_WITH_ALLOC
  - [ ] memcpy(new_val, v, sizeof(valk_lval_t))
  - [ ] Update new_val->flags: clear LVAL_ALLOC_SCRATCH, set LVAL_ALLOC_HEAP
  - [ ] Set new_val->origin_allocator = ctx->heap
  - [ ] Call valk_gc_add_to_objects(ctx->heap, new_val)
  - [ ] Set forwarding pointer: valk_lval_set_forward(v, new_val)
  - [ ] Handle string copy for LVAL_SYM, LVAL_STR, LVAL_ERR:
    - [ ] Allocate new string in heap
    - [ ] Copy string contents
    - [ ] Update new_val->str pointer
  - [ ] Handle function name copy for LVAL_FUN (non-builtin):
    - [ ] Allocate new name string in heap
    - [ ] Copy name contents
    - [ ] Update new_val->fun.name pointer
  - [ ] Increment ctx->values_copied
  - [ ] Add sizeof(valk_lval_t) to ctx->bytes_copied
  - [ ] Return new_val

#### Task 3.5: Phase 1 - Evacuate Reachable from Value

**File**: `src/gc.c`

- [ ] Implement `static void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v)`
  - [ ] Switch on LVAL_TYPE(v):
  - [ ] Case LVAL_CONS / LVAL_QEXPR:
    - [ ] Evacuate head if in scratch, push to worklist
    - [ ] Evacuate tail if in scratch, push to worklist
  - [ ] Case LVAL_FUN (non-builtin):
    - [ ] Evacuate formals if in scratch, push to worklist
    - [ ] Evacuate body if in scratch, push to worklist
    - [ ] Handle fun.env (see Task 3.7)
  - [ ] Case LVAL_ENV:
    - [ ] Handle embedded env (see Task 3.7)
  - [ ] Other cases: no children

#### Task 3.6: Phase 1 - Main Evacuation Loop

**File**: `src/gc.c`

- [ ] Implement `static void valk_evacuate_reachable(valk_evacuation_ctx_t* ctx, valk_lval_t* root)`
  - [ ] Evacuate root value
  - [ ] Push root to worklist
  - [ ] While worklist not empty:
    - [ ] Pop value from worklist
    - [ ] Call valk_evacuate_children(ctx, value)

#### Task 3.7: Environment Evacuation

**File**: `src/gc.c`

- [ ] Implement `static void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env)`
  - [ ] Return if env is NULL
  - [ ] Check if env->symbols.items is in scratch arena:
    - [ ] Allocate new array in heap
    - [ ] Copy array contents
    - [ ] For each symbol string in scratch: allocate and copy to heap
    - [ ] Update env->symbols.items pointer
  - [ ] Check if env->vals.items is in scratch arena:
    - [ ] Allocate new array in heap
    - [ ] Copy array contents
    - [ ] Update env->vals.items pointer
  - [ ] For each value in env->vals.items:
    - [ ] If value is in scratch: evacuate and update pointer
    - [ ] Push evacuated value to worklist for child processing
  - [ ] Recursively call for env->parent
  - [ ] Recursively call for env->fallback

#### Task 3.8: Phase 2 - Fix Pointers in Value

**File**: `src/gc.c`

- [ ] Implement `static void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v)`
  - [ ] Return if v is NULL
  - [ ] Return if LVAL_ALLOC(v) == LVAL_ALLOC_SCRATCH (shouldn't happen post-evac)
  - [ ] Switch on LVAL_TYPE(v):
  - [ ] Case LVAL_CONS / LVAL_QEXPR:
    - [ ] v->cons.head = valk_lval_follow_forward(v->cons.head)
    - [ ] v->cons.tail = valk_lval_follow_forward(v->cons.tail)
    - [ ] ctx->pointers_fixed += 2
  - [ ] Case LVAL_FUN:
    - [ ] v->fun.formals = valk_lval_follow_forward(v->fun.formals)
    - [ ] v->fun.body = valk_lval_follow_forward(v->fun.body)
    - [ ] ctx->pointers_fixed += 2
    - [ ] If v->fun.env: call valk_fix_env_pointers(ctx, v->fun.env)
  - [ ] Case LVAL_ENV:
    - [ ] Call valk_fix_env_pointers(ctx, &v->env)

#### Task 3.9: Phase 2 - Fix Pointers in Environment

**File**: `src/gc.c`

- [ ] Implement `static void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env)`
  - [ ] Return if env is NULL
  - [ ] For each value in env->vals.items:
    - [ ] env->vals.items[i] = valk_lval_follow_forward(env->vals.items[i])
    - [ ] ctx->pointers_fixed++
  - [ ] Recursively call for env->parent
  - [ ] Recursively call for env->fallback

#### Task 3.10: Phase 3 Unit Tests

**File**: `test/test_evacuation.c`

- [ ] Create test file with necessary includes
- [ ] Test `test_evacuate_number` - evacuate single LVAL_NUM
- [ ] Test `test_evacuate_string` - evacuate LVAL_STR with string copy
- [ ] Test `test_evacuate_symbol` - evacuate LVAL_SYM with string copy
- [ ] Test `test_evacuate_cons_simple` - evacuate cons cell with NUM children
- [ ] Test `test_evacuate_cons_nested` - evacuate nested cons cells
- [ ] Test `test_evacuate_list_1000` - evacuate list with 1000 elements
- [ ] Test `test_evacuate_function` - evacuate lambda with formals/body
- [ ] Test `test_evacuate_closure` - evacuate function with captured env
- [ ] Test `test_evacuate_env_simple` - evacuate env with few bindings
- [ ] Test `test_evacuate_env_chain` - evacuate env with parent chain
- [ ] Test `test_forward_prevents_duplicate` - same value evacuated twice returns same pointer
- [ ] Test `test_pointer_fixup_cons` - verify cons pointers updated
- [ ] Test `test_pointer_fixup_function` - verify function pointers updated
- [ ] Test `test_pointer_fixup_env` - verify env value pointers updated
- [ ] Add test file to Makefile

---

### Phase 4: Checkpoint API

**Goal**: Expose checkpointing to evaluation and scripts

#### Task 4.1: Checkpoint Function

**File**: `src/gc.c`

- [ ] Implement `void valk_checkpoint(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, valk_lenv_t* root_env)`
  - [ ] Log checkpoint start with arena usage
  - [ ] Initialize valk_evacuation_ctx_t
  - [ ] Call evac_worklist_init(&ctx)
  - [ ] Phase 1: Call valk_evacuate_env(&ctx, root_env)
  - [ ] Phase 1: Process worklist until empty (evacuate children)
  - [ ] Phase 2: Walk heap->objects list, call valk_fix_pointers for each
  - [ ] Phase 2: Call valk_fix_env_pointers(&ctx, root_env)
  - [ ] Update scratch->stats.num_checkpoints++
  - [ ] Update scratch->stats.bytes_evacuated += ctx.bytes_copied
  - [ ] Update scratch->stats.values_evacuated += ctx.values_copied
  - [ ] Update heap->stats.evacuations_from_scratch += ctx.values_copied
  - [ ] Update heap->stats.evacuation_bytes += ctx.bytes_copied
  - [ ] Update heap->stats.evacuation_pointer_fixups += ctx.pointers_fixed
  - [ ] Log checkpoint complete with stats
  - [ ] Call valk_mem_arena_reset(scratch)
  - [ ] Call evac_worklist_free(&ctx)

**File**: `src/gc.h`

- [ ] Add declaration for `valk_checkpoint()`

#### Task 4.2: Automatic Checkpoint Trigger

**File**: `src/gc.c`

- [ ] Implement `bool valk_should_checkpoint(valk_mem_arena_t* scratch, float threshold)`
  - [ ] Return (float)scratch->offset / scratch->capacity > threshold

**File**: `src/gc.h`

- [ ] Add declaration for `valk_should_checkpoint()`
- [ ] Define `VALK_CHECKPOINT_THRESHOLD_DEFAULT 0.75f`

#### Task 4.3: Lisp Checkpoint Builtins

**File**: `src/parser.c`

- [ ] Add `(checkpoint)` builtin
  - [ ] Access scratch/heap from thread context
  - [ ] Call valk_checkpoint(scratch, heap, root_env)
  - [ ] Return nil
- [ ] Add `(checkpoint-stats)` builtin
  - [ ] Return list with (values-evacuated bytes-evacuated num-checkpoints)
- [ ] Add `(set-checkpoint-threshold n)` builtin
  - [ ] Validate n is number between 0.0 and 1.0
  - [ ] Store in thread context
  - [ ] Return previous threshold
- [ ] Register builtins in valk_lenv_builtins()

#### Task 4.4: Phase 4 Tests

**File**: `test/test_checkpoint.c`

- [ ] Test `test_checkpoint_empty` - checkpoint with empty scratch
- [ ] Test `test_checkpoint_basic` - checkpoint preserves env bindings
- [ ] Test `test_checkpoint_clears_arena` - verify scratch offset is 0 after
- [ ] Test `test_checkpoint_stats_update` - verify stats are updated
- [ ] Test `test_should_checkpoint_threshold` - verify threshold logic

**File**: `test/test_checkpoint.valk`

- [ ] Test basic def survives checkpoint
- [ ] Test function survives checkpoint
- [ ] Test closure with captured value survives
- [ ] Test deep list survives checkpoint
- [ ] Test multiple sequential checkpoints
- [ ] Test checkpoint-stats returns correct values

---

### Phase 5: Integration with Evaluation

**Goal**: Add checkpoints at strategic points

#### Task 5.1: Thread Context Extension

**File**: `src/memory.h` (or where valk_thread_ctx is defined)

- [ ] Add to `valk_thread_ctx_t`:
  - [ ] `valk_mem_arena_t* scratch`
  - [ ] `valk_gc_malloc_heap_t* heap`
  - [ ] `valk_lenv_t* root_env`
  - [ ] `float checkpoint_threshold`
  - [ ] `bool checkpoint_enabled`

**File**: `src/repl.c`

- [ ] Initialize new thread context fields after allocator setup:
  - [ ] `valk_thread_ctx.scratch = scratch`
  - [ ] `valk_thread_ctx.heap = gc_heap`
  - [ ] `valk_thread_ctx.root_env = env`
  - [ ] `valk_thread_ctx.checkpoint_threshold = VALK_CHECKPOINT_THRESHOLD_DEFAULT`
  - [ ] `valk_thread_ctx.checkpoint_enabled = true`

#### Task 5.2: Script Mode Checkpoint Points

**File**: `src/repl.c`

- [ ] In script mode file evaluation loop, after each top-level expression:
  - [ ] Check `if (valk_should_checkpoint(scratch, valk_thread_ctx.checkpoint_threshold))`
  - [ ] Call `valk_checkpoint(scratch, gc_heap, env)`
- [ ] After parsing file (before evaluation loop):
  - [ ] Call checkpoint to move AST to heap

#### Task 5.3: REPL Checkpoint Integration

**File**: `src/repl.c`

- [ ] Replace `valk_mem_arena_reset(scratch)` with `valk_checkpoint(scratch, gc_heap, env)`
- [ ] This handles both evacuation and reset in one call

#### Task 5.4: Optional Loop Iteration Checkpoints

**File**: `src/parser.c`

- [ ] In `builtin_map` after each iteration:
  - [ ] Check if checkpoint enabled and threshold exceeded
  - [ ] Call valk_checkpoint if needed
- [ ] In `builtin_foldl` after each iteration:
  - [ ] Same checkpoint check
- [ ] In `builtin_filter` after each iteration:
  - [ ] Same checkpoint check

#### Task 5.5: Phase 5 Tests

**File**: `test/test_integration.valk`

- [ ] Test script with 1000 top-level expressions
- [ ] Test map over large list doesn't OOM
- [ ] Test recursive function with many calls
- [ ] Test nested function definitions
- [ ] Verify memory-stats shows reasonable evacuation rate

---

### Phase 6: Script Mode Default Scratch

**Goal**: Make scratch the default allocator during script execution

#### Task 6.1: Script Mode Allocator Switch

**File**: `src/repl.c`

- [ ] In script mode, wrap parse in `VALK_WITH_ALLOC((void*)scratch)`
- [ ] In script mode, wrap eval in `VALK_WITH_ALLOC((void*)scratch)`
- [ ] Verify checkpoint is called between expressions
- [ ] Remove direct GC heap allocation during script execution

#### Task 6.2: REPL Mode Allocator Strategy

**File**: `src/repl.c`

- [ ] Verify REPL already uses scratch during eval (existing behavior)
- [ ] Verify checkpoint is called after each expression

#### Task 6.3: Builtin Allocation Strategy Decision

**File**: `src/parser.c`

- [ ] Option A: Let def/defn allocate in scratch, rely on checkpoint
  - [ ] No changes needed
- [ ] Option B: Have def/defn allocate directly in heap
  - [ ] Wrap value creation in `VALK_WITH_ALLOC(valk_thread_ctx.heap)`
  - [ ] Decide based on performance testing

#### Task 6.4: Phase 6 Tests

- [ ] Test large script file runs without OOM
- [ ] Test script with many definitions
- [ ] Test script with closures capturing across expressions
- [ ] Benchmark script execution time vs baseline

---

### Phase 7: Comprehensive Testing

**Goal**: Ensure correctness and stability

#### Task 7.1: Unit Test Suite Completion

**File**: `test/test_evacuation.c`

- [ ] Verify all evacuation unit tests pass
- [ ] Add edge case tests:
  - [ ] Empty cons cell (nil head/tail)
  - [ ] Self-referential structure (if possible)
  - [ ] Very long environment chain (100+ parents)
  - [ ] Environment with 1000+ bindings

#### Task 7.2: Integration Test Suite

**File**: `test/test_checkpoint.valk`

- [ ] Complete all Lisp-level checkpoint tests
- [ ] Add stress tests:
  - [ ] Define 1000 variables, checkpoint, verify all accessible
  - [ ] Create 100 closures, checkpoint, call each
  - [ ] Nested checkpoints (checkpoint inside function that's called)

#### Task 7.3: Memory Leak Testing

- [ ] Run all tests under ASAN with detect_leaks=1
- [ ] Run evacuation tests under Valgrind
- [ ] Verify no leaks in:
  - [ ] Single checkpoint cycle
  - [ ] Multiple checkpoint cycles
  - [ ] Full GC after checkpoint
  - [ ] Program exit after checkpoints

#### Task 7.4: Performance Benchmarks

**File**: `test/bench_checkpoint.c`

- [ ] Implement `bench_evacuate_small` - 100 small values
- [ ] Implement `bench_evacuate_large` - 10000 values
- [ ] Implement `bench_evacuate_deep_list` - 10000 element list
- [ ] Implement `bench_checkpoint_vs_reset` - compare times
- [ ] Implement `bench_script_baseline` - script without checkpoint
- [ ] Implement `bench_script_checkpoint` - same script with checkpoint
- [ ] Document expected overhead (<5% for typical workloads)

#### Task 7.5: Regression Tests

- [ ] Run existing test suite: `make test`
- [ ] Verify all existing tests still pass
- [ ] Run test_prelude.valk successfully
- [ ] Run any other integration scripts

---

### Phase 8: Telemetry Dashboard

**Goal**: Runtime observability

#### Task 8.1: Enhanced Statistics Output

**File**: `src/gc.c`

- [ ] Update `valk_memory_print_stats()` to include:
  - [ ] Section header formatting
  - [ ] Scratch arena: current, high water, total allocs, resets, checkpoints
  - [ ] GC heap: allocated, collections, evacuations received
  - [ ] Derived: avg values/checkpoint, avg bytes/checkpoint, evacuation rate
  - [ ] Format numbers with commas for readability (optional)

#### Task 8.2: SIGUSR1 Signal Handler

**File**: `src/repl.c`

- [ ] Add `#include <signal.h>`
- [ ] Add static globals for signal handler:
  - [ ] `static valk_mem_arena_t* g_scratch_for_signal`
  - [ ] `static valk_gc_malloc_heap_t* g_heap_for_signal`
- [ ] Implement `static void sigusr1_handler(int sig)`
  - [ ] Call valk_memory_print_stats to stderr
- [ ] In main(), after allocator setup:
  - [ ] Set g_scratch_for_signal = scratch
  - [ ] Set g_heap_for_signal = gc_heap
  - [ ] Call signal(SIGUSR1, sigusr1_handler)
- [ ] Document usage: `kill -USR1 <pid>`

#### Task 8.3: Verbose Checkpoint Logging

**File**: `src/gc.c`

- [ ] Add VALK_DEBUG level logs in valk_checkpoint:
  - [ ] Before Phase 1: "Starting evacuation from scratch"
  - [ ] After Phase 1: "Evacuated N values, M bytes"
  - [ ] Before Phase 2: "Starting pointer fixup"
  - [ ] After Phase 2: "Fixed N pointers"
- [ ] Ensure logs respect log level settings

#### Task 8.4: Telemetry Tests

- [ ] Test memory-stats builtin output format
- [ ] Test SIGUSR1 handler doesn't crash
- [ ] Test stats accuracy after known operations

---

## Implementation Order Summary

```
Phase 1: Telemetry Infrastructure
   ├── 1.1 Arena stats structure
   ├── 1.2 GC heap stats extension
   ├── 1.3 Statistics API
   ├── 1.4 Lisp builtins
   └── 1.5 Phase 1 tests
         │
         ▼
Phase 2: Forwarding Pointers
   ├── 2.1 LVAL_FORWARD type
   ├── 2.2 Forwarding helpers
   ├── 2.3 Arena pointer check
   └── 2.4 Phase 2 tests
         │
         ▼
Phase 3: Evacuation Core
   ├── 3.1 Context structure
   ├── 3.2 Worklist management
   ├── 3.3 GC object list helper
   ├── 3.4 Copy single value
   ├── 3.5 Evacuate children
   ├── 3.6 Main evacuation loop
   ├── 3.7 Environment evacuation
   ├── 3.8 Fix pointers in value
   ├── 3.9 Fix pointers in env
   └── 3.10 Phase 3 tests
         │
         ▼
Phase 4: Checkpoint API
   ├── 4.1 valk_checkpoint()
   ├── 4.2 Auto-trigger
   ├── 4.3 Lisp builtins
   └── 4.4 Phase 4 tests
         │
         ▼
Phase 5: Evaluation Integration
   ├── 5.1 Thread context extension
   ├── 5.2 Script mode checkpoints
   ├── 5.3 REPL integration
   ├── 5.4 Loop iteration checkpoints
   └── 5.5 Phase 5 tests
         │
         ▼
Phase 6: Script Mode Default
   ├── 6.1 Script allocator switch
   ├── 6.2 REPL strategy
   ├── 6.3 Builtin strategy
   └── 6.4 Phase 6 tests
         │
         ▼
Phase 7: Testing
   ├── 7.1 Unit test completion
   ├── 7.2 Integration tests
   ├── 7.3 Leak testing
   ├── 7.4 Benchmarks
   └── 7.5 Regression tests
         │
         ▼
Phase 8: Telemetry Dashboard
   ├── 8.1 Enhanced stats output
   ├── 8.2 SIGUSR1 handler
   ├── 8.3 Verbose logging
   └── 8.4 Telemetry tests
```

---

## Risk Mitigation

### Risk 1: Dangling Pointers
**Mitigation**:
- ASAN testing at every phase
- Forwarding pointers catch use-after-evacuate
- Assertions on allocator type in hot paths

### Risk 2: Performance Regression
**Mitigation**:
- Benchmark at each phase
- Checkpoint threshold tuning
- Fast path for non-scratch values

### Risk 3: Incomplete Evacuation
**Mitigation**:
- Exhaustive root traversal
- Test with deeply nested structures
- Verify all pointer types handled

### Risk 4: Memory Growth
**Mitigation**:
- GC runs after evacuation
- Stats track evacuation vs GC reclaim
- Alert if evacuation > threshold

---

## Success Criteria

1. **Correctness**: All existing tests pass
2. **No leaks**: ASAN/Valgrind clean
3. **Performance**: <5% overhead on typical scripts
4. **Observability**: Full telemetry available
5. **Stability**: Scripts can run indefinitely without OOM

---

## Appendix A: Pointer Validity Rules

After checkpoint, the following pointer types are valid:

| Pointer Source | Points To | Valid? |
|----------------|-----------|--------|
| Heap value | Heap value | Yes |
| Heap value | Scratch value | No (was evacuated) |
| Env array | Heap value | Yes |
| Env array | Scratch value | No |
| Forwarding ptr | Heap value | Yes (during evacuation only) |

After checkpoint, the arena is reset, so ALL scratch pointers are invalid.

---

## Appendix B: Evacuation Pseudocode

```
EVACUATE(root_env):
  worklist = empty_stack()

  # Phase 1: Copy all reachable scratch values
  FOR each binding (sym, val) in root_env:
    IF val is in scratch:
      new_val = COPY_TO_HEAP(val)
      SET_FORWARD(val, new_val)
      PUSH(worklist, new_val)

  WHILE worklist not empty:
    v = POP(worklist)
    FOR each child pointer p in v:
      IF *p is in scratch AND not forwarded:
        new_child = COPY_TO_HEAP(*p)
        SET_FORWARD(*p, new_child)
        PUSH(worklist, new_child)

  # Phase 2: Fix all pointers
  FOR each value v in heap:
    FOR each child pointer p in v:
      IF *p is forwarded:
        *p = FOLLOW_FORWARD(*p)

  FOR each binding (sym, val) in root_env:
    IF val is forwarded:
      val = FOLLOW_FORWARD(val)

  RESET(scratch_arena)
```

---

## Appendix C: Memory Layout During Evacuation

```
BEFORE CHECKPOINT:
┌──────────────────┐  ┌──────────────────┐
│  Scratch Arena   │  │     GC Heap      │
├──────────────────┤  ├──────────────────┤
│ ┌──────────────┐ │  │                  │
│ │ CONS A       │ │  │                  │
│ │ head: →B     │ │  │                  │
│ │ tail: →C     │ │  │                  │
│ └──────────────┘ │  │                  │
│ ┌──────────────┐ │  │                  │
│ │ NUM B: 42    │ │  │                  │
│ └──────────────┘ │  │                  │
│ ┌──────────────┐ │  │                  │
│ │ NIL C        │ │  │                  │
│ └──────────────┘ │  │                  │
│ [free space]     │  │                  │
└──────────────────┘  └──────────────────┘

DURING PHASE 1 (copy):
┌──────────────────┐  ┌──────────────────┐
│  Scratch Arena   │  │     GC Heap      │
├──────────────────┤  ├──────────────────┤
│ ┌──────────────┐ │  │ ┌──────────────┐ │
│ │ FORWARD  ────┼─┼──┼─│ CONS A'      │ │
│ │ →A'          │ │  │ │ head: →B(!)  │ │ ← still points to scratch!
│ └──────────────┘ │  │ │ tail: →C(!)  │ │
│ ┌──────────────┐ │  │ └──────────────┘ │
│ │ FORWARD  ────┼─┼──┼─│ NUM B': 42   │ │
│ │ →B'          │ │  │ └──────────────┘ │
│ └──────────────┘ │  │ ┌──────────────┐ │
│ ┌──────────────┐ │  │ │ NIL C'       │ │
│ │ FORWARD  ────┼─┼──┼─└──────────────┘ │
│ │ →C'          │ │  │                  │
│ └──────────────┘ │  │                  │
└──────────────────┘  └──────────────────┘

DURING PHASE 2 (fix pointers):
┌──────────────────┐  ┌──────────────────┐
│  Scratch Arena   │  │     GC Heap      │
├──────────────────┤  ├──────────────────┤
│ ┌──────────────┐ │  │ ┌──────────────┐ │
│ │ FORWARD →A'  │ │  │ │ CONS A'      │ │
│ └──────────────┘ │  │ │ head: →B'  ──┼─┼─ fixed!
│ ┌──────────────┐ │  │ │ tail: →C'  ──┼─┼─ fixed!
│ │ FORWARD →B'  │ │  │ └──────────────┘ │
│ └──────────────┘ │  │ ┌──────────────┐ │
│ ┌──────────────┐ │  │ │ NUM B': 42   │ │
│ │ FORWARD →C'  │ │  │ └──────────────┘ │
│ └──────────────┘ │  │ ┌──────────────┐ │
│                  │  │ │ NIL C'       │ │
└──────────────────┘  │ └──────────────┘ │
                      └──────────────────┘

AFTER ARENA RESET:
┌──────────────────┐  ┌──────────────────┐
│  Scratch Arena   │  │     GC Heap      │
├──────────────────┤  ├──────────────────┤
│ [all free]       │  │ ┌──────────────┐ │
│                  │  │ │ CONS A'      │ │
│                  │  │ │ head: →B'    │ │
│                  │  │ │ tail: →C'    │ │
│                  │  │ └──────────────┘ │
│                  │  │ ┌──────────────┐ │
│                  │  │ │ NUM B': 42   │ │
│                  │  │ └──────────────┘ │
│                  │  │ ┌──────────────┐ │
│                  │  │ │ NIL C'       │ │
│                  │  │ └──────────────┘ │
└──────────────────┘  └──────────────────┘
```

---

## Appendix D: Code Templates

### Template: Statistics Structure (Task 1.1)

```c
// In valk_mem_arena_t struct:
struct {
  size_t total_allocations;
  size_t total_bytes_allocated;
  size_t high_water_mark;
  size_t num_resets;
  size_t num_checkpoints;
  size_t bytes_evacuated;
  size_t values_evacuated;
  size_t overflow_fallbacks;    // Heap fallbacks due to full arena
  size_t overflow_bytes;        // Bytes allocated via fallback
} stats;
bool warned_overflow;           // Reset each checkpoint cycle

// In valk_gc_malloc_heap_t struct:
size_t hard_limit;              // Absolute maximum heap size
bool in_emergency_gc;           // Prevent recursive emergency GC
struct {
  size_t overflow_allocations;  // From scratch overflow
  size_t evacuations_from_scratch;
  size_t evacuation_bytes;
  size_t evacuation_pointer_fixups;
  size_t emergency_collections; // Emergency GCs at hard limit
  size_t peak_usage;            // Maximum allocated_bytes reached
} stats;
```

### Template: Evacuate Value (Task 3.4)

```c
static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx,
                                         valk_lval_t* v) {
  if (v == NULL) return NULL;
  if (LVAL_TYPE(v) == LVAL_FORWARD) return v->forward;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH) return v;

  valk_lval_t* new_val = NULL;
  VALK_WITH_ALLOC(ctx->heap) {
    new_val = valk_mem_alloc(sizeof(valk_lval_t));
    memcpy(new_val, v, sizeof(valk_lval_t));
    new_val->flags = (new_val->flags & ~LVAL_ALLOC_MASK) | LVAL_ALLOC_HEAP;
    new_val->origin_allocator = ctx->heap;
    valk_gc_add_to_objects(ctx->heap, new_val);

    // Copy strings for string types
    switch (LVAL_TYPE(new_val)) {
      case LVAL_SYM:
      case LVAL_STR:
      case LVAL_ERR:
        if (new_val->str) {
          size_t len = strlen(v->str) + 1;
          new_val->str = valk_mem_alloc(len);
          memcpy(new_val->str, v->str, len);
        }
        break;
      case LVAL_FUN:
        if (new_val->fun.name && !new_val->fun.builtin) {
          size_t len = strlen(v->fun.name) + 1;
          new_val->fun.name = valk_mem_alloc(len);
          memcpy(new_val->fun.name, v->fun.name, len);
        }
        break;
      default:
        break;
    }
  }

  valk_lval_set_forward(v, new_val);
  ctx->values_copied++;
  ctx->bytes_copied += sizeof(valk_lval_t);

  return new_val;
}
```

### Template: Heap Hard Limit with Emergency GC (Task 1.3)

```c
void* valk_gc_malloc_heap_alloc(valk_gc_malloc_heap_t* heap, size_t bytes) {
  size_t total_size = sizeof(valk_gc_header_t) + bytes;

  // Check hard limit BEFORE allocation
  if (heap->allocated_bytes + total_size > heap->hard_limit) {
    // Try emergency GC if not already in one
    if (!heap->in_emergency_gc) {
      heap->in_emergency_gc = true;
      VALK_WARN("Heap approaching hard limit (%zu/%zu bytes, %.1f%%), "
                "triggering emergency GC",
                heap->allocated_bytes, heap->hard_limit,
                100.0 * heap->allocated_bytes / heap->hard_limit);

      size_t before = heap->allocated_bytes;
      valk_gc_malloc_collect(heap);
      size_t reclaimed = before - heap->allocated_bytes;

      heap->stats.emergency_collections++;
      heap->in_emergency_gc = false;

      VALK_INFO("Emergency GC reclaimed %zu bytes (%.1f%%)",
                reclaimed, 100.0 * reclaimed / before);
    }

    // Re-check after emergency GC
    if (heap->allocated_bytes + total_size > heap->hard_limit) {
      // Still can't allocate - fatal error
      VALK_ERROR("=== FATAL: HEAP EXHAUSTED ===");
      VALK_ERROR("Requested: %zu bytes", bytes);
      VALK_ERROR("Current:   %zu bytes", heap->allocated_bytes);
      VALK_ERROR("Hard limit: %zu bytes", heap->hard_limit);
      VALK_ERROR("Shortfall: %zu bytes",
                 (heap->allocated_bytes + total_size) - heap->hard_limit);

      // Dump full diagnostics
      valk_gc_malloc_print_stats(heap);

      VALK_ERROR("Consider increasing VALK_HEAP_HARD_LIMIT environment variable");
      VALK_ERROR("Current: VALK_HEAP_HARD_LIMIT=%zu", heap->hard_limit);

      abort();
    }
  }

  // Normal allocation path continues...
  // (existing slab/free-list/malloc logic)

  // Track peak usage
  if (heap->allocated_bytes > heap->stats.peak_usage) {
    heap->stats.peak_usage = heap->allocated_bytes;
  }

  return ptr;
}

valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(size_t gc_threshold, size_t hard_limit) {
  valk_gc_malloc_heap_t* heap = malloc(sizeof(valk_gc_malloc_heap_t));
  // ... existing init ...

  heap->gc_threshold = gc_threshold;
  heap->hard_limit = hard_limit > 0 ? hard_limit : gc_threshold * 2;
  heap->in_emergency_gc = false;

  VALK_INFO("GC heap: threshold=%zu (%.1f MB), hard_limit=%zu (%.1f MB)",
            heap->gc_threshold, heap->gc_threshold / (1024.0 * 1024.0),
            heap->hard_limit, heap->hard_limit / (1024.0 * 1024.0));

  return heap;
}

void valk_gc_set_hard_limit(valk_gc_malloc_heap_t* heap, size_t limit) {
  if (limit < heap->allocated_bytes) {
    VALK_WARN("Cannot set hard limit below current usage (%zu < %zu)",
              limit, heap->allocated_bytes);
    return;
  }
  heap->hard_limit = limit;
  VALK_INFO("GC heap hard limit set to %zu bytes (%.1f MB)",
            limit, limit / (1024.0 * 1024.0));
}
```

### Template: Scratch Overflow Fallback (Task 1.2)

```c
void* valk_mem_arena_alloc(valk_mem_arena_t* arena, size_t bytes) {
  // Align to 8 bytes
  size_t aligned_bytes = (bytes + 7) & ~7;

  // Check if allocation fits in arena
  if (arena->offset + aligned_bytes > arena->capacity) {
    // OVERFLOW: Fall back to heap allocation
    arena->stats.overflow_fallbacks++;
    arena->stats.overflow_bytes += bytes;

    // Emit warning once per checkpoint cycle
    if (!arena->warned_overflow) {
      VALK_WARN("Scratch arena full (%zu/%zu bytes, %.1f%%), "
                "falling back to heap. Consider increasing SCRATCH_ARENA_BYTES.",
                arena->offset, arena->capacity,
                100.0 * arena->offset / arena->capacity);
      arena->warned_overflow = true;
    }

    // Allocate from heap instead - value will have LVAL_ALLOC_HEAP flag
    // and will be in GC object list, so no evacuation needed
    valk_gc_malloc_heap_t* heap = valk_thread_ctx.heap;
    if (heap == NULL) {
      VALK_ERROR("Scratch overflow but no heap available!");
      abort();
    }
    return valk_gc_malloc_heap_alloc(heap, bytes);
  }

  // Normal arena allocation path
  void* ptr = &arena->heap[arena->offset];
  arena->offset += aligned_bytes;

  // Update stats
  arena->stats.total_allocations++;
  arena->stats.total_bytes_allocated += bytes;
  if (arena->offset > arena->stats.high_water_mark) {
    arena->stats.high_water_mark = arena->offset;
  }

  return ptr;
}

void valk_mem_arena_reset(valk_mem_arena_t* arena) {
  arena->offset = 0;
  arena->warned_overflow = false;  // Reset warning flag
  arena->stats.num_resets++;
}
```

### Template: Checkpoint Function (Task 4.1)

```c
void valk_checkpoint(valk_mem_arena_t* scratch,
                     valk_gc_malloc_heap_t* heap,
                     valk_lenv_t* root_env) {
  VALK_INFO("Checkpoint: arena at %zu/%zu bytes (%.1f%%)",
            scratch->offset, scratch->capacity,
            100.0 * scratch->offset / scratch->capacity);

  // Log overflow stats if any occurred
  if (scratch->stats.overflow_fallbacks > 0) {
    VALK_WARN("Checkpoint: %zu allocations (%zu bytes) overflowed to heap",
              scratch->stats.overflow_fallbacks, scratch->stats.overflow_bytes);
  }

  valk_evacuation_ctx_t ctx = {
    .scratch = scratch,
    .heap = heap,
    .worklist = NULL,
    .worklist_count = 0,
    .worklist_capacity = 0,
    .values_copied = 0,
    .bytes_copied = 0,
    .pointers_fixed = 0,
  };

  evac_worklist_init(&ctx);

  // Phase 1: Evacuate
  valk_evacuate_env(&ctx, root_env);
  while (ctx.worklist_count > 0) {
    valk_lval_t* v = evac_worklist_pop(&ctx);
    valk_evacuate_children(&ctx, v);
  }

  // Phase 2: Fix pointers
  for (valk_gc_header_t* h = heap->objects; h; h = h->gc_next) {
    valk_lval_t* v = (valk_lval_t*)(h + 1);
    valk_fix_pointers(&ctx, v);
  }
  valk_fix_env_pointers(&ctx, root_env);

  // Update stats
  scratch->stats.num_checkpoints++;
  scratch->stats.bytes_evacuated += ctx.bytes_copied;
  scratch->stats.values_evacuated += ctx.values_copied;
  heap->stats.evacuations_from_scratch += ctx.values_copied;
  heap->stats.evacuation_bytes += ctx.bytes_copied;
  heap->stats.evacuation_pointer_fixups += ctx.pointers_fixed;

  VALK_INFO("Checkpoint: evacuated %zu values (%zu bytes), fixed %zu ptrs",
            ctx.values_copied, ctx.bytes_copied, ctx.pointers_fixed);

  valk_mem_arena_reset(scratch);
  evac_worklist_free(&ctx);
}
```
