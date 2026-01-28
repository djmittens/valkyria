# Arena and GC Architecture Design

This document outlines the recommended architecture for arena-based memory management and garbage collection in Valkyria, based on research of OCaml, Go, Rust, Zig, and game engine patterns.

## Current State Analysis

### Existing Components

1. **Scratch arena** - bump allocator for ephemeral allocations
2. **GC heap** (heap2) - multi-size-class collector with TLABs
3. **Two-phase checkpoint** - copy values from scratch→heap, then fix pointers
4. **LVAL_FORWARD type** - forwarding pointers for evacuation
5. **Per-stream arenas** - HTTP/2 request-scoped allocations

### Pain Points

1. **Forward pointer chasing** (`valk_lval_follow_forward`) creates chains during multiple checkpoints
2. **Two-phase evacuation** is complex with duplicate traversal logic
3. **`valk_evacuate_env` and `valk_fix_env_pointers`** are near-identical (~150 lines each)
4. **No clear lifetime hierarchy** - everything is scratch vs heap, with ad-hoc per-stream arenas
5. **Atomics remain** despite stop-the-world GC

---

## Research Summary

### OCaml's Memory Model

- **Minor heap**: Fixed-size bump allocator, ~2 CPU instructions per allocation
- **Major heap**: Size-segregated free lists with mark-and-sweep
- **Key insight**: Write barrier maintains "remembered set" for cross-heap references
- **No pointer forwarding during normal operation** - only copying collector uses forwarding

### Go's Design Philosophy

- Rejected generational GC because escape analysis puts young objects on stack
- Write barrier overhead > mark phase savings when heap is large
- **Bet on memory over CPU**: Use larger heaps to reduce GC frequency

### Rust Arena Patterns (Bumpalo, typed-arena)

- No individual deallocation
- Safe cycles: All values share same lifetime, enabling cyclic data structures
- Phase-oriented: allocate → use → bulk-free

### Zig Arena Allocator

- Allocator as first-class parameter
- Composable: arena can wrap any backing allocator
- Explicit lifetime boundaries via `defer`

### Game Engine Patterns

- **Frame allocators**: Reset each frame, O(1) cleanup
- **Handle-based resources**: Replace pointers with index+generation handles
  - Memory can be relocated
  - Dangling access detectable
  - Cache-friendly array lookup

---

## Recommended Architecture

### 1. Explicit Lifetime Hierarchy

```c
typedef enum {
  VALK_LIFETIME_IMMORTAL,   // Builtins, stdlib - never collected
  VALK_LIFETIME_SESSION,    // REPL or server lifetime
  VALK_LIFETIME_REQUEST,    // HTTP request, single eval
  VALK_LIFETIME_SCRATCH,    // Expression evaluation (current scratch arena)
} valk_lifetime_e;
```

**Invariant**: Objects can only point "up" (shorter-lived → longer-lived). This is enforced by evacuation when crossing boundaries.

### 2. Region-Based Memory

Replace the current model with **nested regions** that can be bulk-freed:

```c
typedef struct valk_region {
  valk_mem_arena_t arena;       // Bump allocator
  valk_lifetime_e lifetime;     // Which tier
  struct valk_region *parent;   // Fallback for overflow / promotion
  struct valk_gc_heap2 *gc_heap; // For SESSION lifetime only
} valk_region_t;
```

**Key insight from Go**: Don't pay write barrier cost everywhere. Instead:
- Scratch → heap evacuation is already a "batch write barrier"
- Within a region, no barriers needed (same lifetime)

### 3. Eliminate Forward Pointers with Immutable Evacuation

Current approach mutates source objects with `LVAL_FORWARD`. Instead:

```c
// Returns new root, all internal pointers already point to heap copies
valk_lval_t* valk_region_evacuate(valk_region_t *from, 
                                  valk_gc_heap2_t *to,
                                  valk_lval_t *root);
```

**Pattern**: Copy entire object graph in one pass using a hashmap for deduplication:

```
for each reachable object:
  if already copied (in hashmap): return existing copy
  else: copy to heap, add to hashmap, recursively copy children
```

This eliminates:
- Forward pointer type entirely
- Two-phase (copy, then fix) approach
- Pointer-following chains

### 4. Handle-Based References for Cross-Region

For cases where you *must* reference across lifetimes (e.g., timer callbacks):

```c
typedef struct {
  u32 index;       // Slot in handle table
  u32 generation;  // Detect stale handles
} valk_handle_t;

// Central table per region
valk_lval_t* valk_handle_resolve(valk_handle_t h);
```

**Benefits**:
- Memory can be relocated
- Stale access detectable (generation mismatch)
- Cross-process serializable
- Cache-friendly (array lookup vs pointer chase)

### 5. Immortal Objects (Static Optimization)

For builtins and stdlib that live forever:

```c
#define VALK_LVAL_IMMORTAL_BIT (1 << 15)  // In flags

static inline bool valk_lval_is_immortal(valk_lval_t *v) {
  return (v->flags & VALK_LVAL_IMMORTAL_BIT) != 0;
}
```

GC skips immortal objects during both mark and sweep. Register builtins as immortal at startup.

### 6. Per-Request Arenas (HTTP/Frame)

Formalize the existing per-stream arena pattern:

```c
// Create request-scoped region
valk_region_t* region = valk_region_create(VALK_LIFETIME_REQUEST, session_region);

// All allocations within request use this
VALK_WITH_REGION(region) {
  // Evaluate request...
}

// O(1) cleanup - no GC needed
valk_region_destroy(region);
```

For games:

```c
// Frame allocator pattern
valk_region_t *frame = valk_region_create(VALK_LIFETIME_SCRATCH, session);
// ... render frame ...
valk_region_reset(frame);  // O(1), reuse for next frame
```

---

## API Surface

Keep it minimal (Go's philosophy):

```c
// Configuration (once at startup)
valk_runtime_config_t config = {
  .gc_heap_size = 4ULL * 1024 * 1024 * 1024,
  .scratch_size = 16 * 1024 * 1024,
  .gc_threshold_pct = 75,
};
valk_runtime_init(&config);

// Region management
valk_region_t* valk_region_create(valk_lifetime_e lifetime, valk_region_t *parent);
void valk_region_destroy(valk_region_t *region);
void valk_region_reset(valk_region_t *region);  // For frame allocators

// Handles for cross-region refs
valk_handle_t valk_handle_create(valk_lval_t *val);
valk_lval_t* valk_handle_resolve(valk_handle_t h);
void valk_handle_release(valk_handle_t h);
```

---

## Migration Path

### Phase 1: Unify Evacuation (Low Risk)

Merge `valk_evacuate_env` and `valk_fix_env_pointers` into single-pass with hashmap. This alone eliminates ~200 lines and the forward pointer type.

### Phase 2: Formalize Lifetimes (Medium Risk)

Add `valk_lifetime_e` to regions/arenas. Start with just tagging existing allocations.

### Phase 3: Immortal Objects (Low Risk)

Add immortal bit, mark builtins at registration. Speeds up GC.

### Phase 4: Handle Table for Callbacks (Medium Risk)

Replace direct pointers to callbacks with handles. Resolves the "evacuate timer callback" complexity.

---

## Trade-off Summary

| Approach | Current | Recommended |
|----------|---------|-------------|
| Forward pointers | LVAL_FORWARD type, chains | Hashmap during copy, no mutation |
| Cross-region refs | Eager evacuation | Handle table with generation |
| Lifetime tracking | Implicit (scratch vs heap) | Explicit enum on regions |
| Immortal objects | None | Skip during GC |
| Frame allocators | Ad-hoc per-stream | First-class LIFETIME_SCRATCH |

---

## References

- OCaml GC: https://dev.realworldocaml.org/garbage-collector.html
- Go GC design: https://go.dev/blog/ismmkeynote
- Bumpalo (Rust): https://docs.rs/bumpalo
- Zig allocators: https://ziglang.org/documentation/master/#Allocators
- Handle-based resources: https://floooh.github.io/2018/06/17/handles-vs-pointers.html
