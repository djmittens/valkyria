# Monadic Async API

## Overview

This document describes the monadic async API built on top of the continuation-based async/await system. The API provides functional combinators for composing and transforming async operations.

## Core Concepts

All async operations follow this pattern:
```lisp
(def {my-async-op} (\ {args... k} {
  ; Do work
  (k result)  ; Call continuation with result
}))
```

To execute an async operation in a sync context:
```lisp
(def {result} (async-reset {
  (async-shift {k} {(my-async-op args k)})
}))
```

## Implemented Combinators

### Core Monadic Operations

#### `async-pure value`
Wraps a pure value in an async context.
```lisp
(def {op} (async-pure 42))
; Returns async operation that yields 42
```

#### `async-bind async-op f`
Monadic bind (flatMap/chain) - sequences async operations.
```lisp
(async-bind (fetch-user 42) (\ {user} {
  (fetch-posts user)
}))
```

### Collection Operations

#### `async-map-list async-fn items`
Maps an async function over a list sequentially.
```lisp
(async-map-list double-async (list 1 2 3))
; Yields (2 4 6)
```

#### `async-filter-list async-pred items`
Filters a list with an async predicate.
```lisp
(async-filter-list is-valid-async (list 1 2 3 4 5))
```

####  `async-fold-list async-fn init items`
Folds (reduces) over a list with an async function.
```lisp
(async-fold-list sum-async 0 (list 1 2 3 4 5))
; Yields 15
```

#### `async-collect async-ops`
Executes multiple async operations and collects results.
```lisp
(async-collect (list op1 op2 op3))
; Yields list of results
```

#### `async-sequence async-ops`
Executes async operations in sequence, returns last result.
```lisp
(async-sequence (list log-async store-async notify-async))
```

### Conditional Operations

#### `async-when condition async-op`
Executes async op only if condition is true.
```lisp
(async-when (> x 10) save-async)
```

#### `async-unless condition async-op`
Executes async op only if condition is false.
```lisp
(async-unless (< x 0) process-async)
```

### Utility Operations

#### `async-tap value async-op`
Executes async op for side effects, returns original value.
```lisp
(async-tap user log-async)
; Logs user but returns user
```

#### `async-const value async-op`
Always returns same value, ignoring async op result.
```lisp
(async-const 42 some-async-op)
```

### Combinators

#### `async-pipe initial-value async-fns`
Composes async operations left-to-right (pipeline).
```lisp
(async-pipe 5 (list double-async add-ten-async square-async))
; 5 -> 10 -> 20 -> 400
```

#### `async-compose f g`
Function composition for async functions.
```lisp
(def {process} (async-compose double-async add-ten-async))
(process 5)  ; Returns async op yielding 20
```

### Advanced Operations

#### `async-traverse async-fn items`
Alias for `async-map-list` - maps and collects.

#### `async-zip-with async-fn list1 list2`
Zips two lists with an async binary function.
```lisp
(async-zip-with add-async (list 1 2 3) (list 10 20 30))
; Yields (11 22 33)
```

#### `async-replicate n async-op`
Replicates an async operation n times.
```lisp
(async-replicate 5 fetch-random-async)
```

#### `async-take n async-op`
Takes first n results from repeated async operation.
```lisp
(async-take 3 fetch-next-async)
```

## Usage in async-reset Context

To use these combinators, wrap them in `async-reset` and `async-shift`:

```lisp
; Example: Map over a list
(def {result} (async-reset {
  (async-shift {k} {
    (def {map-op} (async-map-list double-async (list 1 2 3)))
    (map-op k)
  })
}))
; result = (2 4 6)
```

## Helper Function: run-async

For convenience, use `run-async` to execute an async operation:

```lisp
(def {run-async} (\ {async-op} {
  (async-reset {
    (async-shift {k} {(async-op k)})
  })
}))

; Usage:
(def {result} (run-async (async-map-list double-async (list 1 2 3))))
```

## Building Higher-Level APIs

These combinators enable building complex backend APIs:

### Example: User Dashboard
```lisp
(def {build-dashboard} (\ {user-id k} {
  ; Fetch user
  (fetch-user user-id (\ {user} {
    ; Fetch posts
    (fetch-posts user-id (\ {posts} {
      ; Fetch analytics
      (fetch-analytics user-id (\ {analytics} {
        ; Combine results
        (k (list user posts analytics))
      }))
    }))
  }))
}))
```

### Example: Batch Processing
```lisp
(def {process-batch} (\ {items k} {
  (def {processor} (async-map-list validate-and-save items))
  (processor k)
}))
```

## Status

✅ **Implemented:**
- Core monadic operations (pure, bind)
- Collection operations (map, filter, fold, collect, sequence)
- Conditional operations (when, unless)
- Utility operations (tap, const)
- Combinators (pipe, compose)
- Advanced operations (zip-with, replicate, take, traverse)

⏳ **Partial:**
- Error handling (async-try, async-recover) - simplified implementation
- async-race - returns first operation only
- async-partition - uses helper functions

🔧 **Future Work:**
- True parallel execution (currently sequential)
- Proper error propagation
- Cancellation support
- Resource cleanup (async-finally)
- Performance optimizations for large collections

## Testing

Comprehensive tests are available in `test/test_async_monadic.valk` covering:
- All core combinators
- Edge cases (empty lists, single items)
- Complex compositions
- Nested operations
- Error scenarios

Run tests with:
```bash
./build/valk test/test_async_monadic.valk
```

## Integration with HTTP APIs

These combinators will be used to build the HTTP backend API:

```lisp
; Request handler pipeline
(def {handle-request} (\ {req k} {
  (async-pipe req (list
    parse-body-async
    validate-async
    authenticate-async
    process-async
    serialize-response-async
  ) k)
}))

; Batch endpoint processing
(def {process-users} (\ {user-ids k} {
  (async-map-list fetch-and-process user-ids k)
}))
```
