# Concurrency

Valkyria provides thread-based concurrency with futures and promises.

## Thread Pool

A work queue with worker threads for parallel task execution.

**Features:**
- 4 worker threads (default)
- FIFO work queue with mutex coordination
- Drain-before-shutdown semantics

## Futures and Promises

```lisp
; Create future for async computation
(def fut (future (expensive-computation)))

; Wait for result
(await fut)

; Wait with timeout (milliseconds)
(await-timeout fut 1000)
```

## ARC Boxes

Atomic reference counting for thread-safe value sharing:

```lisp
; Values shared between threads use ARC
; Automatic retain/release
```

## Promise Resolution

Promises allow decoupled completion:

```lisp
; Create promise
(def p (promise))

; Resolve later
(resolve! p value)

; Await resolution
(await p)
```

## Implementation

The concurrency system uses:
- pthreads for threads
- Mutex + condition variables for synchronization
- Atomic reference counting for shared values

## Files

- `src/concurrency.c`, `src/concurrency.h` - Thread pool and futures
