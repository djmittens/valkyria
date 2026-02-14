# Memory Management

Valkyria uses a three-tier memory allocation system optimized for Lisp evaluation patterns.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Memory Allocation Tiers                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐        │
│  │              │   │              │   │              │        │
│  │  Scratch     │   │  GC Heap     │   │  Slab        │        │
│  │  Arena       │   │  (Mark &     │   │  Allocator   │        │
│  │              │   │   Sweep)     │   │              │        │
│  │  Fast bump   │   │  Persistent  │   │  Fixed-size  │        │
│  │  allocator   │   │  values      │   │  blocks      │        │
│  │              │   │              │   │              │        │
│  └──────────────┘   └──────────────┘   └──────────────┘        │
│        │                   ▲                   │                 │
│        └───────────────────┘                   │                 │
│           Checkpoint-based                     │                 │
│           evacuation                      TCP buffers,           │
│                                           connections            │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Scratch Arena

The scratch arena is a bump allocator used for temporary values during evaluation.

**Characteristics:**
- O(1) allocation (pointer bump)
- Automatic reset between REPL expressions
- Checkpoint-based evacuation for values that need to persist

**Usage:**
```lisp
(mem/arena/usage)      ; Current usage in bytes
(mem/arena/capacity)   ; Total capacity in bytes
(mem/arena/high-water) ; Peak usage
```

## GC Heap

Mark-and-sweep garbage collector for persistent values.

**Characteristics:**
- Automatic collection when threshold exceeded
- Values evacuated from scratch arena on checkpoint
- Configurable thresholds and limits

**Usage:**
```lisp
(mem/heap/usage)           ; Current heap usage
(mem/heap/hard-limit)      ; Maximum heap size
(mem/heap/set-hard-limit n) ; Set limit

(mem/gc/collect)           ; Trigger collection
(mem/gc/threshold)         ; Get GC threshold
(mem/gc/set-threshold n)   ; Set threshold
(mem/gc/stats)             ; Collection statistics
```

## Checkpoint System

Checkpoint-based evacuation copies reachable values from scratch arena to GC heap.

**How it works:**
1. Between top-level expressions, checkpoint is triggered
2. Values reachable from root environment are marked
3. Marked values are copied to GC heap
4. Pointers are updated (forwarding)
5. Scratch arena is reset

**Monitoring:**
```lisp
(mem/checkpoint/stats)  ; Returns (values-evac bytes-evac num-checkpoints ptrs-fixed)
```

## Slab Allocator

Fixed-size block allocator for specific structures.

**Uses:**
- `valk_lval_t` objects
- TCP buffers
- HTTP connections

**Characteristics:**
- Lock-free free list (Treiber stack)
- O(1) acquire/release
- No fragmentation

## Memory Statistics

```lisp
(mem/stats)  ; Display comprehensive memory visualization
```

## Configuration

Memory is configured via environment variables:
- `VALK_ARENA_SIZE` - Scratch arena size (default: 4MB)
- `VALK_HEAP_LIMIT` - Hard heap limit (default: 64MB)
- `VALK_GC_THRESHOLD` - GC trigger threshold (default: 16MB)

## Implementation Files

- `src/memory.c`, `src/memory.h` - Allocators
- `src/gc.c`, `src/gc.h` - Garbage collector
