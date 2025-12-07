# Fiber/Effect System Design

## Executive Summary

This document specifies a **fiber-based effect system** for Valkyria, inspired by ZIO. This is the **advanced async system** designed for:

- **Dataflow pipelines** - Complex data processing with backpressure
- **Effect reification** - Inspect, transform, and optimize effect trees before execution
- **Lazy composition** - Build computation descriptions, run them multiple times
- **Advanced concurrency** - Structured concurrency with automatic resource cleanup

**For simpler webserver async needs, see [ASYNC_HANDLES_DESIGN.md](ASYNC_HANDLES_DESIGN.md).**

---

## When to Use This vs Async Handles

| Use Case | Async Handles | Effect System |
|----------|---------------|---------------|
| Webserver handlers | ✅ Recommended | Overkill |
| Simple timeouts/retries | ✅ Recommended | Overkill |
| Dataflow pipelines | ❌ Limited | ✅ Recommended |
| Effect inspection/optimization | ❌ Not possible | ✅ Designed for this |
| Rerunnable computations | ❌ Not possible | ✅ Core feature |
| Complex retry/circuit breaker | ⚠️ Manual | ✅ Built-in |

---

## Design Goals

1. **Ultra-light syntax** - Async code looks like sync code
2. **Lock-free concurrency** - Cooperative scheduling with CAS operations
3. **Composability** - Effects are values that can be passed, combined, retried
4. **Lazy evaluation** - Effects describe computation, don't run until interpreted
5. **Dataflow-first** - Designed for streaming data processing pipelines

---

## Core Concepts

### What is an Effect?

An **Effect** is a *description* of a computation that may:
- Perform I/O (network, file, database)
- Fail with an error
- Take time (delay, timeout)
- Fork into parallel computations

**Key insight:** An Effect is NOT a running computation. It's a blueprint.

```lisp
; This does NOT make an HTTP request - it creates a description
(def my-effect (http/get "https://api.com/users"))

; This also does NOT run - it creates a composed description
(def composed (do!
                (def x my-effect)
                (def y (http/get (str "/posts/" x)))
                y))

; Only when interpreted does it actually run
(run! composed)  ; NOW the requests happen
```

### What is a Fiber?

A **Fiber** is the runtime representation of an executing Effect:
- Lightweight (just a data structure, not an OS thread)
- Cooperatively scheduled (yields at well-defined points)
- Can be forked, joined, or cancelled

```lisp
; Fork creates a fiber from an effect
(def fiber (fork! my-effect))

; Fiber runs in background, we can do other work
(do-something-else)

; Join waits for the fiber and gets its result
(def result (join! fiber))
```

---

## Type System

### Effect Type: `LVAL_EFFECT`

An Effect has three type parameters (like ZIO):

```
Effect[R, E, A]
  R = Environment required (dependencies)
  E = Error type (what can go wrong)
  A = Success type (what we get on success)
```

For simplicity, Valkyria uses dynamic typing, so these are implicit:

```lisp
; Effect that succeeds with a number
(pure 42)  ; Effect[Any, Nothing, Num]

; Effect that might fail with a string error
(fail "not found")  ; Effect[Any, Str, Nothing]

; Effect that needs an HTTP client
(http/get url)  ; Effect[HttpClient, HttpError, Response]
```

### Fiber Type: `LVAL_FIBER`

A Fiber wraps an executing Effect:

```c
typedef struct valk_fiber {
  // Identity
  uint64_t id;                      // Unique fiber ID

  // State machine
  enum {
    FIBER_PENDING,                  // Created but not started
    FIBER_RUNNING,                  // Currently executing
    FIBER_SUSPENDED,                // Waiting on I/O or other fiber
    FIBER_SUCCEEDED,                // Completed with value
    FIBER_FAILED,                   // Completed with error
    FIBER_CANCELLED,                // Cancelled before completion
  } status;

  // Computation
  valk_lval_t *effect;              // The Effect being run
  valk_lval_t *value;               // Result (success or error)

  // Execution state
  valk_lval_t *continuation;        // What to do next (CPS)
  valk_lenv_t *env;                 // Captured environment

  // Scheduling
  struct valk_fiber *next;          // Intrusive linked list for run queue

  // Cancellation
  _Atomic int cancel_requested;     // CAS flag for cancellation

  // Parent/child relationships
  struct valk_fiber *parent;        // For structured concurrency
  struct {
    struct valk_fiber **children;
    size_t count;
    size_t capacity;
  } children;
} valk_fiber_t;
```

---

## Syntax Specification

### Primary Constructs

| Syntax | Semantics | Type |
|--------|-----------|------|
| `(do! e1 e2 ... en)` | Sequence effects, return last | `Effect[R, E, A]` where A is type of en |
| `(pure val)` | Wrap value in succeeded effect | `Effect[Any, Nothing, A]` |
| `(fail err)` | Create failed effect | `Effect[Any, E, Nothing]` |
| `(effect expr)` | Suspend expression in effect | `Effect[R, E, A]` |

### Parallelism

| Syntax | Semantics | Type |
|--------|-----------|------|
| `(par! e1 e2 ... en)` | Run in parallel, collect all results | `Effect[R, E, (A1, A2, ..., An)]` |
| `(race! e1 e2 ... en)` | Return first to complete, cancel others | `Effect[R, E, A]` |
| `(fork! e)` | Run in background, return fiber handle | `Effect[R, Nothing, Fiber[E, A]]` |
| `(join! fiber)` | Wait for fiber, get result | `Effect[R, E, A]` |

### Error Handling

| Syntax | Semantics | Type |
|--------|-----------|------|
| `(try! e)` | Catch errors, return `{:ok v}` or `{:err e}` | `Effect[R, Nothing, Either[E, A]]` |
| `(catch! e handler-fn)` | On error, call handler | `Effect[R, E2, A]` |
| `(recover! e fallback-e)` | On error, run fallback effect | `Effect[R, E2, A]` |
| `(finally! e cleanup-e)` | Always run cleanup (even on error) | `Effect[R, E, A]` |

### Timing

| Syntax | Semantics | Type |
|--------|-----------|------|
| `(sleep! ms)` | Delay execution | `Effect[R, Nothing, Nil]` |
| `(timeout! ms e)` | Fail with `:timeout` if not done in time | `Effect[R, E+Timeout, A]` |
| `(delay! ms e)` | Wait ms, then run e | `Effect[R, E, A]` |
| `(retry! n e)` | Retry up to n times on failure | `Effect[R, E, A]` |
| `(retry-backoff! n base-ms e)` | Retry with exponential backoff | `Effect[R, E, A]` |

### Cancellation

| Syntax | Semantics | Type |
|--------|-----------|------|
| `(cancel! fiber)` | Request cancellation | `Effect[R, Nothing, Bool]` |
| `(cancelled?)` | Check if current fiber is cancelled | `Effect[R, Nothing, Bool]` |
| `(uncancellable! e)` | Run e, ignoring cancellation requests | `Effect[R, E, A]` |

### Resource Management

| Syntax | Semantics | Type |
|--------|-----------|------|
| `(bracket! acquire release use-fn)` | Acquire, use, always release | `Effect[R, E, A]` |
| `(with! resource use-fn)` | Shorthand for resources with :close | `Effect[R, E, A]` |

### Collections

| Syntax | Semantics | Type |
|--------|-----------|------|
| `(map! fn items)` | Map effect-returning fn over items (sequential) | `Effect[R, E, [A]]` |
| `(pmap! fn items)` | Parallel map | `Effect[R, E, [A]]` |
| `(filter! pred items)` | Filter with effect predicate | `Effect[R, E, [A]]` |
| `(fold! fn init items)` | Fold with effect accumulator | `Effect[R, E, A]` |

---

## Detailed Semantics

### `do!` Block Semantics

The `do!` block is the primary way to sequence effects. It has special semantics:

```lisp
(do!
  stmt1
  stmt2
  ...
  stmtN)
```

**Evaluation rules:**

1. Each statement is evaluated in order
2. If a statement produces an `Effect`, it is **automatically awaited**
3. If a statement produces a regular value, it is passed through
4. The result of `do!` is an `Effect` containing the last statement's value
5. If any statement fails, the entire `do!` fails (short-circuit)

**Example with expansion:**

```lisp
; This:
(do!
  (def user (http/get "/user"))
  (def posts (http/get (str "/posts/" (user :id))))
  {:user user :posts posts})

; Desugars to:
(flat-map (http/get "/user")
  (fn [user]
    (flat-map (http/get (str "/posts/" (user :id)))
      (fn [posts]
        (pure {:user user :posts posts})))))
```

**Key insight:** `def` inside `do!` binds the **awaited value**, not the Effect itself.

### `def` Inside `do!` vs Outside

```lisp
; OUTSIDE do! - binds the Effect value itself
(def my-effect (http/get "/users"))
; my-effect is an Effect, not a response

; INSIDE do! - binds the awaited result
(do!
  (def response (http/get "/users"))
  ; response is the actual HTTP response, not an Effect
  (print response))
```

### `par!` Semantics

```lisp
(par! e1 e2 e3)
```

**Semantics:**
1. Fork fibers for e1, e2, e3 simultaneously
2. All fibers run concurrently
3. Wait for ALL to complete
4. Return tuple of results `(r1 r2 r3)`
5. If ANY fails, cancel others and propagate first error

**Destructuring:**
```lisp
(do!
  (def [users posts stats] (par!
    (db/get-users)
    (db/get-posts)
    (db/get-stats)))
  ; users, posts, stats are all available here
  {:users users :posts posts :stats stats})
```

### `race!` Semantics

```lisp
(race! e1 e2 e3)
```

**Semantics:**
1. Fork fibers for e1, e2, e3 simultaneously
2. Return result of FIRST to complete
3. Cancel all other fibers
4. If first to complete fails, that error propagates (others still cancelled)

**Use case - timeout:**
```lisp
(race!
  (slow-operation)
  (do! (sleep! 5000) (fail :timeout)))
```

### `fork!` and `join!` Semantics

```lisp
(def fiber (fork! some-effect))
; ... do other work ...
(def result (join! fiber))
```

**`fork!` semantics:**
1. Create new Fiber from Effect
2. Add Fiber to scheduler run queue
3. Return Fiber handle immediately (does not block)
4. Fiber executes in background

**`join!` semantics:**
1. If Fiber is SUCCEEDED, return its value
2. If Fiber is FAILED, propagate its error
3. If Fiber is CANCELLED, propagate cancellation error
4. If Fiber is still running, suspend current fiber until target completes

**Structured concurrency:**
When a parent fiber is cancelled, all child fibers are also cancelled:

```lisp
(do!
  (def f1 (fork! task1))
  (def f2 (fork! task2))
  ; If this do! block is cancelled, f1 and f2 are also cancelled
  (join! f1)
  (join! f2))
```

### Error Propagation

Effects use **short-circuit error propagation** (like Scala Future, unlike Promise.allSettled):

```lisp
(do!
  (def a (might-fail-1))  ; If this fails...
  (def b (might-fail-2))  ; ...this never runs
  (def c (might-fail-3))  ; ...neither does this
  {:a a :b b :c c})        ; ...and the whole do! fails
```

**Catching errors:**

```lisp
(do!
  (def result (try! (might-fail)))
  (if (result :ok)
    (process (result :ok))
    (log-error (result :err))))
```

**Recovery:**

```lisp
(do!
  (def data (recover!
              (http/get primary-url)
              (http/get backup-url)))
  (process data))
```

### Cancellation Semantics

Cancellation is **cooperative** - fibers check for cancellation at yield points:

```lisp
(def fiber (fork!
  (do!
    (step-1)           ; Yield point - can be cancelled here
    (step-2)           ; Yield point
    (uncancellable!    ; This section cannot be cancelled
      (critical-operation))
    (step-3))))        ; Yield point

(sleep! 100)
(cancel! fiber)        ; Request cancellation
```

**Yield points** (where cancellation is checked):
- Before each `do!` step
- Before `join!`
- During `sleep!`
- During I/O operations

**Guarantee:** Resources acquired in `bracket!` are ALWAYS released, even on cancellation:

```lisp
(bracket!
  (db/connect)                    ; Acquire
  (fn [conn] (db/close conn))     ; Release (ALWAYS runs)
  (fn [conn]
    (do!
      (db/query conn "...")       ; Can be cancelled here
      (db/query conn "..."))))    ; Or here
; Connection is closed even if cancelled
```

---

## Runtime Architecture

### Fiber Scheduler

The scheduler is **single-threaded** and **cooperative**:

```c
typedef struct valk_fiber_scheduler {
  // Run queue (fibers ready to execute)
  struct {
    valk_fiber_t *head;
    valk_fiber_t *tail;
    _Atomic size_t count;
  } run_queue;

  // Sleeping fibers (waiting on timer)
  struct {
    valk_fiber_t **fibers;
    uint64_t *wake_times;
    size_t count;
    size_t capacity;
  } sleep_queue;

  // Fibers waiting on I/O (managed by libuv)
  // (tracked in uv_handle->data)

  // Integration with libuv
  uv_loop_t *loop;
  uv_idle_t idle_handle;      // Run fibers when idle
  uv_timer_t timer_handle;    // Wake sleeping fibers

  // Statistics
  _Atomic uint64_t fibers_created;
  _Atomic uint64_t fibers_completed;
} valk_fiber_scheduler_t;
```

### Execution Model

```
┌─────────────────────────────────────────────────────────────┐
│                      libuv Event Loop                        │
│                                                              │
│  ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐     │
│  │  I/O    │   │ Timers  │   │  Idle   │   │ Check   │     │
│  │Callbacks│   │         │   │         │   │         │     │
│  └────┬────┘   └────┬────┘   └────┬────┘   └────┬────┘     │
│       │             │             │             │           │
│       └─────────────┴──────┬──────┴─────────────┘           │
│                            │                                 │
│                            ▼                                 │
│               ┌────────────────────────┐                    │
│               │   Fiber Scheduler      │                    │
│               │                        │                    │
│               │  ┌──────────────────┐  │                    │
│               │  │    Run Queue     │  │                    │
│               │  │  F1 → F2 → F3    │  │                    │
│               │  └──────────────────┘  │                    │
│               │                        │                    │
│               │  ┌──────────────────┐  │                    │
│               │  │   Sleep Queue    │  │                    │
│               │  │  F4 @100ms       │  │                    │
│               │  │  F5 @500ms       │  │                    │
│               │  └──────────────────┘  │                    │
│               └────────────────────────┘                    │
└─────────────────────────────────────────────────────────────┘
```

**Execution cycle:**

1. **I/O Callback** - libuv delivers I/O completion
   - Find waiting fiber, set result, add to run queue

2. **Timer** - Sleeping fiber's wake time reached
   - Remove from sleep queue, add to run queue

3. **Idle** - No I/O pending, run fibers
   - Pop fiber from run queue
   - Execute until yield point (I/O, sleep, fork, join)
   - Re-queue or move to appropriate wait queue

4. **Yield points:**
   - `sleep!` → Move to sleep queue with wake time
   - I/O operation → Move to I/O wait (libuv tracks)
   - `join!` on pending fiber → Add to target's wait list
   - `fork!` → Create child fiber, add to run queue

### CAS Operations (Lock-Free)

The scheduler uses **compare-and-swap** instead of locks:

```c
// Adding to run queue (lock-free)
void scheduler_enqueue(valk_fiber_scheduler_t *s, valk_fiber_t *fiber) {
  valk_fiber_t *old_tail;
  do {
    old_tail = s->run_queue.tail;
    fiber->next = NULL;
  } while (!atomic_compare_exchange_weak(&s->run_queue.tail, &old_tail, fiber));

  if (old_tail) {
    old_tail->next = fiber;
  } else {
    s->run_queue.head = fiber;
  }

  atomic_fetch_add(&s->run_queue.count, 1);
}

// Cancellation request (lock-free)
bool fiber_request_cancel(valk_fiber_t *fiber) {
  int expected = 0;
  return atomic_compare_exchange_strong(&fiber->cancel_requested, &expected, 1);
}
```

---

## C Implementation Details

### Effect Value Type

**File: `src/parser.h`**

```c
// Add to valk_ltype_e enum
typedef enum {
  // ... existing types ...
  LVAL_EFFECT,    // Lazy effect description
  LVAL_FIBER,     // Running/completed fiber
} valk_ltype_e;

// Add to valk_lval_t union
struct {
  enum {
    EFFECT_PURE,       // Immediate value
    EFFECT_FAIL,       // Immediate error
    EFFECT_SUSPEND,    // Suspended computation
    EFFECT_FLAT_MAP,   // Sequenced computation
    EFFECT_FORK,       // Parallel fork
    EFFECT_RACE,       // Racing computations
    EFFECT_SLEEP,      // Timer delay
    EFFECT_BRACKET,    // Resource management
    // ... more effect types
  } tag;

  union {
    // EFFECT_PURE
    struct { valk_lval_t *value; } pure;

    // EFFECT_FAIL
    struct { valk_lval_t *error; } fail;

    // EFFECT_SUSPEND
    struct {
      valk_lval_t *thunk;     // () -> value
      valk_lenv_t *env;
    } suspend;

    // EFFECT_FLAT_MAP
    struct {
      valk_lval_t *source;    // Effect to run first
      valk_lval_t *cont;      // A -> Effect[B]
      valk_lenv_t *env;
    } flat_map;

    // EFFECT_FORK
    struct {
      valk_lval_t *effect;    // Effect to fork
    } fork;

    // EFFECT_RACE
    struct {
      valk_lval_t *effects;   // List of effects
    } race;

    // EFFECT_SLEEP
    struct {
      uint64_t ms;
    } sleep;

    // EFFECT_BRACKET
    struct {
      valk_lval_t *acquire;   // Effect[R]
      valk_lval_t *release;   // R -> Effect[Unit]
      valk_lval_t *use;       // R -> Effect[A]
      valk_lenv_t *env;
    } bracket;
  };
} effect;
```

### Core Builtins

**File: `src/parser.c`**

```c
// (pure value) -> Effect
static valk_lval_t* valk_builtin_pure(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* value = valk_lval_list_nth(a, 0);

  valk_lval_t* effect = valk_lval_effect_new(EFFECT_PURE);
  effect->effect.pure.value = value;
  return effect;
}

// (fail error) -> Effect
static valk_lval_t* valk_builtin_fail(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* error = valk_lval_list_nth(a, 0);

  valk_lval_t* effect = valk_lval_effect_new(EFFECT_FAIL);
  effect->effect.fail.error = error;
  return effect;
}

// (effect thunk) -> Effect (suspend a computation)
static valk_lval_t* valk_builtin_effect(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* thunk = valk_lval_list_nth(a, 0);

  valk_lval_t* effect = valk_lval_effect_new(EFFECT_SUSPEND);
  effect->effect.suspend.thunk = thunk;
  effect->effect.suspend.env = e;
  return effect;
}

// (flat-map effect fn) -> Effect
static valk_lval_t* valk_builtin_flat_map(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* source = valk_lval_list_nth(a, 0);
  valk_lval_t* cont = valk_lval_list_nth(a, 1);

  // Type check: source must be Effect
  if (LVAL_TYPE(source) != LVAL_EFFECT) {
    return valk_lval_err("flat-map: first argument must be an Effect");
  }

  valk_lval_t* effect = valk_lval_effect_new(EFFECT_FLAT_MAP);
  effect->effect.flat_map.source = source;
  effect->effect.flat_map.cont = cont;
  effect->effect.flat_map.env = e;
  return effect;
}

// (sleep! ms) -> Effect
static valk_lval_t* valk_builtin_sleep(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* ms_val = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, ms_val, LVAL_NUM);

  valk_lval_t* effect = valk_lval_effect_new(EFFECT_SLEEP);
  effect->effect.sleep.ms = (uint64_t)ms_val->num;
  return effect;
}
```

### `do!` Macro Implementation

**File: `lib/std/effect.valk`**

```lisp
; do! macro - sequences effects with automatic awaiting
;
; (do! stmt1 stmt2 ... stmtN)
;
; Each stmt can be:
;   - (def name expr)  -> bind awaited result to name
;   - expr             -> evaluate, await if Effect, discard result
;
; Returns: Effect containing value of stmtN

(def {do!} (macro {. stmts} {
  (if (nil? stmts)
    ; Empty do! returns nil
    '(pure nil)
    (if (== (len stmts) 1)
      ; Single statement - wrap in Effect if not already
      (let [stmt (head stmts)]
        (if (is-def? stmt)
          ; (def name expr) at end - weird but allowed
          `(flat-map ~(def-expr stmt) (fn [~(def-name stmt)] (pure ~(def-name stmt))))
          ; Regular expression
          `(as-effect ~stmt)))
      ; Multiple statements - chain with flat-map
      (let [stmt (head stmts)
            rest (tail stmts)]
        (if (is-def? stmt)
          ; (def name expr) - bind result, continue
          `(flat-map (as-effect ~(def-expr stmt))
             (fn [~(def-name stmt)] (do! ~@rest)))
          ; Regular expression - evaluate, discard, continue
          `(flat-map (as-effect ~stmt)
             (fn [_] (do! ~@rest)))))))))

; Helper: check if form is (def name expr)
(def {is-def?} (fn [form] {
  (and (list? form)
       (>= (len form) 3)
       (== (head form) 'def))}))

; Helper: extract name from (def name expr)
(def {def-name} (fn [form] {(nth form 1)}))

; Helper: extract expr from (def name expr)
(def {def-expr} (fn [form] {(nth form 2)}))

; Helper: wrap non-Effect in pure, pass Effect through
(def {as-effect} (fn [x] {
  (if (effect? x)
    x
    (pure x))}))
```

### `par!` Implementation

**File: `lib/std/effect.valk`**

```lisp
; par! - run effects in parallel, collect results
;
; (par! e1 e2 e3) -> Effect containing (r1 r2 r3)
;
; Semantics:
;   - Fork all effects simultaneously
;   - Wait for ALL to complete
;   - If any fails, cancel others, propagate first error

(def {par!} (macro {. effects} {
  (if (nil? effects)
    '(pure '())
    `(do!
       ; Fork all effects
       (def fibers (list ~@(map (fn [e] `(fork! ~e)) effects)))
       ; Join all, collecting results
       ; (This is simplified - real impl needs error handling)
       (map! join! fibers)))}))

; Lower-level parallel implementation with error handling
(def {par-all} (fn [effects] {
  (effect (fn [] {
    ; Create completion tracking
    (def results (make-array (len effects)))
    (def completed (atom 0))
    (def first-error (atom nil))
    (def fibers (atom '()))

    ; Fork all effects
    (each-indexed (fn [i eff] {
      (def fiber (fork-internal! eff
        ; On success
        (fn [val] {
          (array-set! results i {:ok val})
          (atom-swap! completed inc)})
        ; On error
        (fn [err] {
          (atom-compare-and-set! first-error nil err)
          ; Cancel all other fibers
          (each (fn [f] (cancel! f)) @fibers)})))
      (atom-swap! fibers (fn [fs] (cons fiber fs)))
    }) effects)

    ; Wait for completion
    (while (< @completed (len effects))
      (yield!))

    ; Check for errors
    (if @first-error
      (fail @first-error)
      (pure (array->list results)))}))}))
```

### `race!` Implementation

**File: `lib/std/effect.valk`**

```lisp
; race! - run effects in parallel, return first to complete
;
; (race! e1 e2 e3) -> Effect containing first result
;
; Semantics:
;   - Fork all effects simultaneously
;   - Return result of FIRST to complete
;   - Cancel all other fibers

(def {race!} (macro {. effects} {
  `(race-effects (list ~@effects))}))

(def {race-effects} (fn [effects] {
  (effect (fn [] {
    (def winner (atom nil))
    (def fibers (atom '()))

    ; Fork all effects with completion callback
    (each (fn [eff] {
      (def fiber (fork-internal! eff
        ; On complete (success or failure)
        (fn [result] {
          (when (atom-compare-and-set! winner nil result)
            ; We won - cancel all other fibers
            (each (fn [f] (cancel! f)) @fibers))})))
      (atom-swap! fibers (fn [fs] (cons fiber fs)))
    }) effects)

    ; Wait for winner
    (while (nil? @winner)
      (yield!))

    ; Return winner's result
    @winner}))}))
```

### `bracket!` Implementation (Resource Safety)

**File: `lib/std/effect.valk`**

```lisp
; bracket! - safe resource management
;
; (bracket! acquire release use)
;   acquire  : Effect[R]           - how to acquire resource
;   release  : R -> Effect[Unit]   - how to release (ALWAYS runs)
;   use      : R -> Effect[A]      - how to use resource
;
; Returns: Effect[A]
;
; Guarantees: release ALWAYS runs, even on error or cancellation

(def {bracket!} (fn [acquire release use] {
  (do!
    (def resource (uncancellable! acquire))
    (def result (try! (use resource)))
    ; Release always runs
    (uncancellable! (release resource))
    ; Re-raise error if any
    (if (result :err)
      (fail (result :err))
      (pure (result :ok))))}))

; Shorthand for resources with :close method
(def {with!} (fn [acquire use] {
  (bracket!
    acquire
    (fn [r] (r :close))
    use)}))
```

---

## Webserver Integration

### Handler Can Return Effect

**File: `src/aio_uv.c` (modify handler invocation)**

```c
// After handler returns, check type
valk_lval_t* response = valk_lval_eval_call(env, handler, args);

if (LVAL_TYPE(response) == LVAL_EFFECT) {
  // Handler returned an Effect - run it and send response when done
  __http_run_effect_handler(session, stream_id, response,
                            req->stream_arena, conn);
  return 0;  // Response will be sent later
}

if (LVAL_TYPE(response) == LVAL_SYM &&
    strcmp(response->str, ":deferred") == 0) {
  // Legacy :deferred pattern - still supported
  return 0;
}

// Immediate response
__http_send_response(session, stream_id, response, req->stream_arena);
```

### Running Effect Handler

```c
static void __http_run_effect_handler(
    nghttp2_session *session,
    int32_t stream_id,
    valk_lval_t *effect,
    valk_mem_arena_t *arena,
    valk_aio_http_conn *conn) {

  // Create context for when effect completes
  http_effect_ctx_t *ctx = malloc(sizeof(http_effect_ctx_t));
  ctx->session = session;
  ctx->stream_id = stream_id;
  ctx->arena = arena;
  ctx->conn = conn;

  // Create fiber for the effect
  valk_fiber_t *fiber = valk_fiber_new(effect);
  fiber->on_complete = __http_effect_complete_cb;
  fiber->on_complete_ctx = ctx;

  // Add to scheduler
  valk_scheduler_enqueue(conn->scheduler, fiber);
}

static void __http_effect_complete_cb(valk_fiber_t *fiber, void *ctx) {
  http_effect_ctx_t *http_ctx = (http_effect_ctx_t *)ctx;

  valk_lval_t *response;
  if (fiber->status == FIBER_SUCCEEDED) {
    response = fiber->value;
  } else if (fiber->status == FIBER_FAILED) {
    // Convert error to 500 response
    response = valk_lval_map_from(
      "status", valk_lval_str("500"),
      "body", valk_lval_str(fiber->value->str),
      NULL);
  } else {
    // Cancelled - send 499 (client closed request)
    response = valk_lval_map_from(
      "status", valk_lval_str("499"),
      "body", valk_lval_str("Request cancelled"),
      NULL);
  }

  __http_send_response(http_ctx->session, http_ctx->stream_id,
                       response, http_ctx->arena);
  __http_continue_pending_send(http_ctx->conn);

  free(http_ctx);
}
```

---

## Complete Example: Webserver Handler

```lisp
(def {handler} (fn [req sys] {
  (match (req :path)
    ; Immediate response - no Effect needed
    "/health"
    {:status "200" :body "ok"}

    ; Simple async - delay then respond
    "/slow"
    (do!
      (sleep! 2000)
      {:status "200" :body "waited 2 seconds"})

    ; Database query
    "/users/:id"
    (do!
      (def id (path-param req ":id"))
      (def user (db/get-user id))
      (if (nil? user)
        {:status "404" :body "User not found"}
        {:status "200" :body (json user)}))

    ; Parallel fetches with timeout
    "/dashboard"
    (timeout! 5000
      (do!
        (def token (header req "Authorization"))
        (def user (auth/validate token))
        (def [posts stats notifs] (par!
          (api/get-posts user)
          (api/get-stats user)
          (api/get-notifications user)))
        {:status "200"
         :body (json {:user user
                      :posts posts
                      :stats stats
                      :notifications notifs})}))

    ; Error handling with recovery
    "/proxy/:url"
    (do!
      (def url (path-param req ":url"))
      (def response (recover!
        (http/get url)
        (do!
          (log/warn "Primary fetch failed, trying backup")
          (http/get (str "https://backup.com/" url)))))
      {:status "200" :body (response :body)})

    ; Resource management
    "/report"
    (do!
      (def report (with! (db/connect)
        (fn [conn] {
          (do!
            (def data (db/query conn "SELECT * FROM reports"))
            (generate-report data))})))
      {:status "200"
       :body report
       :headers {"Content-Type" "application/pdf"}})

    ; Streaming with retry
    "/events"
    (do!
      (def stream (retry! 3 (event-stream/connect)))
      ; Return SSE response
      {:status "200"
       :headers {"Content-Type" "text/event-stream"}
       :body-stream stream})

    ; Fallback
    _
    {:status "404" :body "Not found"})}))
```

---

## GC Integration

### Marking Effects and Fibers

**File: `src/gc.c`**

```c
case LVAL_EFFECT:
  switch (v->effect.tag) {
    case EFFECT_PURE:
      valk_gc_mark_value(v->effect.pure.value);
      break;
    case EFFECT_FAIL:
      valk_gc_mark_value(v->effect.fail.error);
      break;
    case EFFECT_SUSPEND:
      valk_gc_mark_value(v->effect.suspend.thunk);
      valk_gc_mark_env(v->effect.suspend.env);
      break;
    case EFFECT_FLAT_MAP:
      valk_gc_mark_value(v->effect.flat_map.source);
      valk_gc_mark_value(v->effect.flat_map.cont);
      valk_gc_mark_env(v->effect.flat_map.env);
      break;
    case EFFECT_FORK:
      valk_gc_mark_value(v->effect.fork.effect);
      break;
    case EFFECT_RACE:
      valk_gc_mark_value(v->effect.race.effects);
      break;
    case EFFECT_BRACKET:
      valk_gc_mark_value(v->effect.bracket.acquire);
      valk_gc_mark_value(v->effect.bracket.release);
      valk_gc_mark_value(v->effect.bracket.use);
      valk_gc_mark_env(v->effect.bracket.env);
      break;
    // ... other cases
  }
  break;

case LVAL_FIBER:
  if (v->fiber.effect) valk_gc_mark_value(v->fiber.effect);
  if (v->fiber.value) valk_gc_mark_value(v->fiber.value);
  if (v->fiber.continuation) valk_gc_mark_value(v->fiber.continuation);
  if (v->fiber.env) valk_gc_mark_env(v->fiber.env);
  // Mark children
  for (size_t i = 0; i < v->fiber.children.count; i++) {
    valk_gc_mark_fiber(v->fiber.children.children[i]);
  }
  break;
```

### Scheduler Root Marking

The scheduler's run queue and sleep queue are GC roots:

```c
void valk_gc_mark_roots(void) {
  // ... existing roots ...

  // Mark all fibers in scheduler
  valk_fiber_scheduler_t *sched = valk_get_scheduler();

  // Run queue
  for (valk_fiber_t *f = sched->run_queue.head; f; f = f->next) {
    valk_gc_mark_fiber(f);
  }

  // Sleep queue
  for (size_t i = 0; i < sched->sleep_queue.count; i++) {
    valk_gc_mark_fiber(sched->sleep_queue.fibers[i]);
  }
}
```

---

## Task Breakdown

### Phase 1: Core Effect Type

| Task | File | Description |
|------|------|-------------|
| 1.1 | `parser.h` | Add `LVAL_EFFECT` enum and struct |
| 1.2 | `parser.c` | Implement `valk_lval_effect_new()` |
| 1.3 | `parser.c` | Implement `pure` builtin |
| 1.4 | `parser.c` | Implement `fail` builtin |
| 1.5 | `parser.c` | Implement `effect` builtin |
| 1.6 | `parser.c` | Implement `flat-map` builtin |
| 1.7 | `parser.c` | Implement `effect?` predicate |
| 1.8 | `parser.c` | Implement `as-effect` helper |
| 1.9 | `gc.c` | Add Effect to GC marking |
| 1.10 | `parser.c` | Add Effect print format |

### Phase 2: Fiber Runtime

| Task | File | Description |
|------|------|-------------|
| 2.1 | `fiber.h` | Define `valk_fiber_t` struct |
| 2.2 | `fiber.c` | Implement `valk_fiber_new()` |
| 2.3 | `fiber.c` | Implement fiber state machine |
| 2.4 | `scheduler.h` | Define scheduler struct |
| 2.5 | `scheduler.c` | Implement run queue (CAS-based) |
| 2.6 | `scheduler.c` | Implement sleep queue |
| 2.7 | `scheduler.c` | Implement main execution loop |
| 2.8 | `aio_uv.c` | Integrate scheduler with libuv |
| 2.9 | `gc.c` | Add Fiber and scheduler to GC |

### Phase 3: Effect Interpreter

| Task | File | Description |
|------|------|-------------|
| 3.1 | `fiber.c` | Interpret EFFECT_PURE |
| 3.2 | `fiber.c` | Interpret EFFECT_FAIL |
| 3.3 | `fiber.c` | Interpret EFFECT_SUSPEND |
| 3.4 | `fiber.c` | Interpret EFFECT_FLAT_MAP |
| 3.5 | `fiber.c` | Interpret EFFECT_FORK |
| 3.6 | `fiber.c` | Interpret EFFECT_RACE |
| 3.7 | `fiber.c` | Interpret EFFECT_SLEEP |
| 3.8 | `fiber.c` | Interpret EFFECT_BRACKET |

### Phase 4: Lisp API

| Task | File | Description |
|------|------|-------------|
| 4.1 | `lib/std/effect.valk` | Implement `do!` macro |
| 4.2 | `lib/std/effect.valk` | Implement `par!` macro |
| 4.3 | `lib/std/effect.valk` | Implement `race!` macro |
| 4.4 | `lib/std/effect.valk` | Implement `fork!`, `join!` |
| 4.5 | `lib/std/effect.valk` | Implement `try!`, `catch!`, `recover!` |
| 4.6 | `lib/std/effect.valk` | Implement `timeout!`, `retry!` |
| 4.7 | `lib/std/effect.valk` | Implement `bracket!`, `with!` |
| 4.8 | `lib/std/effect.valk` | Implement `map!`, `pmap!`, etc. |

### Phase 5: Webserver Integration

| Task | File | Description |
|------|------|-------------|
| 5.1 | `aio_uv.c` | Detect Effect return from handler |
| 5.2 | `aio_uv.c` | Implement `__http_run_effect_handler` |
| 5.3 | `aio_uv.c` | Implement completion callback |
| 5.4 | `examples/webserver_demo.valk` | Convert to Effect-based |

### Phase 6: I/O Effects

| Task | File | Description |
|------|------|-------------|
| 6.1 | `aio_uv.c` | `http/get` returns Effect |
| 6.2 | `aio_uv.c` | `http/post` returns Effect |
| 6.3 | `aio_uv.c` | `db/query` returns Effect |
| 6.4 | `aio_uv.c` | `fs/read` returns Effect |
| 6.5 | `aio_uv.c` | `fs/write` returns Effect |

### Phase 7: Testing

| Task | File | Description |
|------|------|-------------|
| 7.1 | `test/test_effect.c` | Unit tests for Effect type |
| 7.2 | `test/test_fiber.c` | Unit tests for Fiber runtime |
| 7.3 | `test/test_scheduler.c` | Scheduler tests |
| 7.4 | `test/test_effect.valk` | Lisp-level Effect tests |
| 7.5 | `test/test_webserver_effect.c` | Integration tests |

---

## Dataflow Pipeline Support

The Effect system is designed to power complex dataflow pipelines with backpressure, windowing, and stream processing.

### Stream Effects

```lisp
; A Stream is an Effect that produces multiple values
; Stream[R, E, A] = Effect[R, E, Chunk[A]] with continuation

; Create a stream from a source
(def numbers (stream/range 1 1000000))

; Transform streams (lazy - nothing runs yet)
(def pipeline
  (-> numbers
      (stream/filter even?)
      (stream/map (fn [x] (* x x)))
      (stream/take 100)
      (stream/chunk 10)))  ; Batch into chunks of 10

; Run the stream, collecting results
(run! (stream/collect pipeline))  ; => ((4 16 36 ...) (... ) ...)
```

### Backpressure

Streams automatically handle backpressure:

```lisp
(def slow-consumer
  (-> (stream/from-queue fast-producer-queue)
      (stream/map-effect (fn [item]
        (do!
          (process-slowly item)  ; Takes 100ms
          item)))
      (stream/run-drain)))

; Producer automatically slows down when consumer can't keep up
```

### Windowing

```lisp
; Time-based windows
(def windowed
  (-> events
      (stream/window-time 5000)  ; 5 second windows
      (stream/map aggregate-window)))

; Count-based windows
(def batched
  (-> events
      (stream/window-count 100)  ; Every 100 items
      (stream/map process-batch)))

; Sliding windows
(def sliding
  (-> events
      (stream/window-sliding 100 10)  ; Size 100, slide 10
      (stream/map compute-average)))
```

### Dataflow Operators

| Operator | Description |
|----------|-------------|
| `stream/map` | Transform each element |
| `stream/filter` | Keep elements matching predicate |
| `stream/flat-map` | Transform and flatten |
| `stream/take` | Take first N elements |
| `stream/drop` | Skip first N elements |
| `stream/chunk` | Batch into fixed-size chunks |
| `stream/window-time` | Time-based windows |
| `stream/window-count` | Count-based windows |
| `stream/merge` | Merge multiple streams |
| `stream/zip` | Pair elements from two streams |
| `stream/broadcast` | Send to multiple consumers |
| `stream/balance` | Load-balance across consumers |

### Effect Graph Optimization

Because Effects are lazy descriptions, we can optimize before execution:

```lisp
; This pipeline:
(def naive
  (-> data
      (stream/map f)
      (stream/map g)
      (stream/filter p)
      (stream/map h)))

; Can be automatically fused to:
(def optimized
  (-> data
      (stream/filter-map (fn [x]
        (let [fx (f x)
              gfx (g fx)]
          (if (p gfx)
            (some (h gfx))
            none))))))

; The optimizer sees the effect tree and combines operations
(run! (effect/optimize naive))  ; Runs optimized version
```

### Dataflow Example: ETL Pipeline

```lisp
(def etl-pipeline
  (do!
    ; Source: Read from Kafka
    (def source (kafka/subscribe "input-topic"))

    ; Transform: Parse, validate, enrich
    (def transformed
      (-> source
          (stream/map json/parse)
          (stream/filter valid?)
          (stream/map-effect enrich-from-db)
          (stream/window-time 10000)))

    ; Sink: Write to multiple destinations
    (def written
      (stream/broadcast transformed
        (list
          (stream/sink-kafka "output-topic")
          (stream/sink-postgres "events" db-conn)
          (stream/sink-s3 "bucket/events/"))))

    ; Run with backpressure and error handling
    (stream/run-with-restart written
      {:restart-delay 5000
       :max-restarts 10
       :on-error log-and-continue})))

; Execute the entire pipeline
(run! etl-pipeline)
```

---

## Comparison: Handles vs Effects for Dataflow

| Aspect | Async Handles | Effect System |
|--------|---------------|---------------|
| **Rerunnable** | ❌ Handle is consumed | ✅ Effect can run multiple times |
| **Optimization** | ❌ Eager, can't inspect | ✅ Lazy, can fuse operations |
| **Backpressure** | ❌ Manual | ✅ Automatic via fibers |
| **Stream processing** | ❌ Not designed for this | ✅ First-class streams |
| **Memory** | ✅ Lower overhead | ⚠️ Effect tree in memory |
| **Complexity** | ✅ Simple | ⚠️ Requires evaluator changes |

**Bottom line:** Use Handles for request/response patterns, Effects for streaming data pipelines.

---

## Migration Path

### Relationship to Async Handles

The Effect system and Async Handles can coexist:

```lisp
; In webserver handler - use handles (simpler)
(def {handler} (\ {req sys}
  (aio/then
    (aio/delay 1000)
    (\ {_} {:status "200" :body "ok"}))))

; In dataflow pipeline - use effects (more powerful)
(def {pipeline}
  (do!
    (def data (stream/from-kafka topic))
    (stream/run-drain (stream/map process data))))
```

### Backward Compatibility

The `:deferred` pattern continues to work:

```lisp
; OLD - still works
(aio/delay sys 2000 (fn [] {:status "200" :body "..."}))

; HANDLES - preferred for webserver
(aio/delay 2000 (fn [] {:status "200" :body "..."}))

; EFFECTS - for dataflow
(do! (sleep! 2000) {:status "200" :body "..."})
```

### Deprecation

1. **Phase 1:** Add Async Handles for webserver (see ASYNC_HANDLES_DESIGN.md)
2. **Phase 2:** Add Effect system for dataflow
3. **Phase 3:** Deprecate `:deferred` pattern
4. **Phase 4:** Remove `:deferred` support

---

## Prerequisites

Before implementing the Effect system, complete:

1. **Async Handles** (ASYNC_HANDLES_DESIGN.md) - Proves the async model works
2. **CPS Evaluator** - Required for fiber suspension (or trampoline approach)
3. **GC Fiber Awareness** - Scheduler queues as GC roots

---

## References

### Existing Code

| File | Lines | Description |
|------|-------|-------------|
| `src/parser.h` | 49, 105-109 | Current LVAL_CONT type |
| `src/parser.c` | 3095-3282 | async-shift, async-reset |
| `src/aio_uv.c` | 1302-1330 | Handler response check |
| `src/aio_uv.c` | 3143-3240 | aio/delay implementation |

### External References

- [ZIO Documentation](https://zio.dev/reference/)
- [ZIO Fibers](https://zio.dev/reference/fiber/)
- [Cats Effect](https://typelevel.org/cats-effect/)
- [Effect-TS](https://effect.website/)
