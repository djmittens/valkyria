# Async API Implementation Plan: Manifold-Style `aio/let`

## Executive Summary

This plan details the implementation of an ergonomic, Manifold-inspired async API for Valkyria's HTTP handlers. The goal is to transform callback-based async code into clean, sequential-looking code with explicit parallel execution markers.

**Current (callback-based):**
```lisp
(aio/delay sys 2000 (\ {} {{:status "200" :body "slept 2s"}}))
```

**Target (monadic with `aio/let`):**
```lisp
(aio/let
  ((_ (aio/sleep 2000)))
  {:status "200" :body "slept 2s"})
```

**Complex handler example:**
```lisp
(aio/let
  ((user (db/fetch-user id))
   (settings (db/fetch-settings id))  ; Runs parallel with user
   :then                               ; Barrier: wait for above
   (posts (db/fetch-posts (user :id)))) ; Sequential: needs user
  {:status "200" :body {:user user :settings settings :posts posts}})
```

---

## Barrier Syntax: Why `:then` Instead of `&`

**Problem:** The `&` symbol is reserved in Valkyria for variadic arguments:
```lisp
(fun {pack f & xs} {f xs})    ; & captures rest args
(\ {& args} {f args})          ; & in lambda formals
```

**Alternative Barrier Symbols Considered:**

| Symbol | Pros | Cons | Decision |
|--------|------|------|----------|
| `&` | Familiar from other languages | **Reserved for varargs** | ❌ Rejected |
| `:then` | Keyword, clear semantics | Slightly verbose | ✅ **Chosen** |
| `:await` | Explicit waiting | Could confuse with async/await | ❌ |
| `---` | Visual separator | Not a valid symbol | ❌ |
| `:seq` | Short for sequential | Less intuitive | ❌ |
| `>>` | Arrow-like flow | Could conflict with future operators | ❌ |
| `:barrier` | Very explicit | Too long | ❌ |

**Why `:then`:**
1. **Keywords are self-evaluating** - `:then` won't be confused with a binding variable
2. **Clear semantics** - "do these, THEN do those"
3. **No conflicts** - Keywords starting with `:` are reserved for data
4. **Matches mental model** - Sequential operations happen "then" after parallel ones

**Final Syntax:**
```lisp
(aio/let
  ((a (fetch-a))     ; ┐
   (b (fetch-b))     ; ├── Parallel group 1
   (c (fetch-c))     ; ┘
   :then             ; ◄── Barrier: wait for group 1
   (d (use-a-b a b)) ; ┐
   (e (use-c c))     ; ├── Parallel group 2
   :then             ; ◄── Barrier: wait for group 2
   (f (combine d e))); Sequential group 3
  (final-result a b c d e f))
```

---

## Table of Contents

1. [Architecture Overview](#1-architecture-overview)
2. [Phase 1: Core Primitives](#2-phase-1-core-primitives)
3. [Phase 2: `aio/let` Macro Implementation](#3-phase-2-aiolet-macro-implementation)
4. [Phase 3: Demo Server Update](#4-phase-3-demo-server-update)
5. [Phase 4: Testing](#5-phase-4-testing)
6. [Phase 5: Cleanup Redundant Code](#6-phase-5-cleanup-redundant-code)
7. [Phase 6: Thread Safety for Future Multi-threading](#7-phase-6-thread-safety)
8. [File Reference](#8-file-reference)
9. [Test Plan](#9-test-plan)

---

## 1. Architecture Overview

### Current Async Infrastructure

Valkyria has a robust C-level async handle system:

| Component | File | Lines | Status |
|-----------|------|-------|--------|
| Handle struct | `src/aio.h` | 41-93 | Production |
| Core builtins | `src/aio_uv.c` | 3600-4514 | Production |
| HTTP integration | `src/aio_uv.c` | 1300-1385 | Production |
| Lisp helpers | `src/async_handles.valk` | 1-136 | Staged |

**C Builtins available:**
- `aio/pure` - Wrap value in completed handle
- `aio/fail` - Create failed handle
- `aio/then` - Chain operations (monadic bind)
- `aio/catch` - Error handling
- `aio/finally` - Cleanup
- `aio/all` - Wait for all handles (parallel)
- `aio/race` - First to complete wins
- `aio/any` - First success wins
- `aio/cancel` - Cancel operation
- `aio/delay` - Timer (callback-based, needs wrapper)

### Target Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    User Code                             │
│  (aio/let ((user (fetch-user)) ...) body)               │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│               aio/let Macro (Lisp)                       │
│  - Parses bindings with :then barriers                   │
│  - Generates aio/then + aio/all chains                   │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│            Core Primitives (Lisp + C)                    │
│  aio/sleep, aio/pure, aio/then, aio/all                 │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│            C Handle System (aio_uv.c)                    │
│  valk_async_handle_t lifecycle                          │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│                  libuv Event Loop                        │
│  Timers, I/O, HTTP/2                                    │
└─────────────────────────────────────────────────────────┘
```

---

## 2. Phase 1: Core Primitives

### 2.1 Add `aio/sleep` Builtin

**Problem:** Current `aio/delay` requires callback syntax:
```lisp
(aio/delay sys 2000 (\ {} result))  ; Ugly callback
```

**Solution:** Add `aio/sleep` that returns a handle:
```lisp
(aio/sleep 2000)  ; Returns handle that completes after 2000ms
```

**File:** `src/aio_uv.c`

**Implementation (add after line 3313):**

```c
// ============================================================================
// aio/sleep - Timer that returns a handle (no callback)
// ============================================================================
// Usage: (aio/sleep ms) -> handle that completes with nil after ms milliseconds
//
// This is the handle-based equivalent of aio/delay. Instead of taking a
// callback, it returns a handle that can be composed with aio/then.
//
// Example:
//   (aio/then (aio/sleep 2000) (\ {_} {:status "200" :body "done"}))

static void __sleep_timer_cb(uv_timer_t *handle) {
  valk_async_handle_uv_data_t *data = (valk_async_handle_uv_data_t *)handle->data;
  valk_async_handle_t *async_handle = data->async_handle;

  // Complete with nil value
  valk_lval_t *result = valk_lval_nil();
  valk_async_handle_complete(async_handle, result);

  // Cleanup timer
  uv_timer_stop(handle);
  uv_close((uv_handle_t *)handle, NULL);
}

static valk_lval_t* valk_builtin_aio_sleep(valk_lenv_t* e, valk_lval_t* a) {
  // Validate: (aio/sleep ms)
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);

  uint64_t delay_ms = (uint64_t)valk_lval_list_nth(a, 0)->num;

  // Get event loop from current context
  if (!current_request_ctx) {
    return valk_lval_err("aio/sleep can only be used within an HTTP request handler");
  }

  valk_aio_system_t *sys = current_request_ctx->conn->server->sys;
  uv_loop_t *loop = sys->eventloop;

  // Create async handle
  valk_async_handle_t *handle = valk_async_handle_new(loop, e);
  handle->session = current_request_ctx->session;
  handle->stream_id = current_request_ctx->stream_id;
  handle->conn = current_request_ctx->conn;
  handle->stream_arena = (struct valk_mem_arena*)current_request_ctx->req->stream_arena;

  // Allocate timer data
  valk_async_handle_uv_data_t *timer_data = malloc(sizeof(valk_async_handle_uv_data_t));
  timer_data->async_handle = handle;
  timer_data->uv.timer.data = timer_data;

  handle->uv_handle_ptr = timer_data;
  handle->status = VALK_ASYNC_RUNNING;

  // Initialize and start timer
  uv_timer_init(loop, &timer_data->uv.timer);
  uv_timer_start(&timer_data->uv.timer, __sleep_timer_cb, delay_ms, 0);

  VALK_INFO("aio/sleep started: %lu ms, handle id=%lu", delay_ms, handle->id);

  return valk_lval_handle(handle);
}
```

**Register builtin (add to line ~4043):**
```c
valk_lenv_put_builtin(env, "aio/sleep", valk_builtin_aio_sleep);
```

### 2.2 Add `as-handle` Helper

**File:** `src/async_handles.valk`

**Add after line 24:**
```lisp
; ============================================================================
; as-handle: Ensure value is wrapped in a handle
; ============================================================================
; If x is already a handle, return it unchanged.
; If x is a regular value, wrap it in aio/pure.
; This allows mixing sync and async values in aio/let bindings.

(def {as-handle} (\ {x}
  (if (handle? x)
    x
    (aio/pure x))))
```

### 2.3 Add `aio/map` Helper

**File:** `src/async_handles.valk`

**Add after `as-handle`:**
```lisp
; ============================================================================
; aio/map: Transform the result of a handle
; ============================================================================
; Like aio/then but for pure functions (no async in transform)
; Usage: (aio/map handle (\ {x} (* x 2)))

(def {aio/map} (\ {handle fn}
  (aio/then handle (\ {x} (aio/pure (fn x))))))
```

---

## 3. Phase 2: `aio/let` Macro Implementation

### 3.1 Design: Explicit `:then` Barrier Syntax

Unlike Manifold's implicit dependency analysis, we use **explicit `:then` barriers** for parallelism:

```lisp
(aio/let
  ((a (fetch-a))       ; ┐
   (b (fetch-b))       ; ├── Parallel group 1
   (c (fetch-c))       ; ┘
   :then               ; Barrier: wait for group 1
   (d (use-a-b a b))   ; ┐
   (e (use-c c))       ; ├── Parallel group 2
   :then               ; Barrier: wait for group 2
   (f (combine d e)))  ; Sequential group 3
  (final-result a b c d e f))
```

**Rationale:**
- Simpler implementation (no AST walking for dependency detection)
- Explicit control for developer
- No surprising blocking behavior
- Works with Valkyria's limited macro system
- `:then` is a keyword (self-evaluating), avoiding conflicts with `&` varargs

### 3.2 Implementation: C Builtin (Primary)

The barrier detection and code generation happens in C for:
- **Performance** - No Lisp interpretation overhead for parsing bindings
- **Simplicity** - C string comparison is trivial
- **Consistency** - Matches other `aio/*` builtins

**File:** `src/aio_uv.c` (alongside other `aio/*` builtins)

**Add after `valk_builtin_aio_sleep` (~line 3350):**

```c
// ============================================================================
// aio/let - Monadic let-bindings for async operations
// ============================================================================
//
// Syntax: (aio/let bindings body)
//   bindings: ((var1 expr1) (var2 expr2) :then (var3 expr3) ...)
//   body: expression to evaluate with all bindings in scope
//
// Behavior:
//   - Bindings in same group (before :then) run in PARALLEL via aio/all
//   - Groups separated by :then run SEQUENTIALLY
//   - Body evaluates after all bindings complete
//
// Example:
//   (aio/let ((user (fetch-user id))
//             (settings (fetch-settings id))
//             :then
//             (posts (fetch-posts (user :id))))
//     {:user user :settings settings :posts posts})

// Helper: Check if lval is the :then barrier keyword
static inline bool is_then_barrier(valk_lval_t *item) {
  return LVAL_TYPE(item) == LVAL_SYM && strcmp(item->str, ":then") == 0;
}

// Binding group for parallel execution
typedef struct {
  valk_lval_t **bindings;  // Array of (var expr) pairs
  size_t count;
  size_t capacity;
} aio_let_group_t;

// Parsed binding groups
typedef struct {
  aio_let_group_t *groups;
  size_t count;
  size_t capacity;
} aio_let_parsed_t;

static aio_let_parsed_t* aio_let_parse_bindings(valk_lval_t *bindings) {
  aio_let_parsed_t *result = malloc(sizeof(aio_let_parsed_t));
  result->groups = malloc(sizeof(aio_let_group_t) * 16);
  result->count = 1;
  result->capacity = 16;

  // Initialize first group
  aio_let_group_t *current = &result->groups[0];
  current->bindings = malloc(sizeof(valk_lval_t*) * 32);
  current->count = 0;
  current->capacity = 32;

  // Walk bindings list
  valk_lval_t *curr = bindings;
  while (LVAL_TYPE(curr) == LVAL_CONS && !valk_lval_list_is_empty(curr)) {
    valk_lval_t *item = curr->cons.head;

    if (is_then_barrier(item)) {
      // Start new group (only if current has bindings)
      if (current->count > 0) {
        result->count++;
        if (result->count >= result->capacity) {
          result->capacity *= 2;
          result->groups = realloc(result->groups,
                                   sizeof(aio_let_group_t) * result->capacity);
        }
        current = &result->groups[result->count - 1];
        current->bindings = malloc(sizeof(valk_lval_t*) * 32);
        current->count = 0;
        current->capacity = 32;
      }
    } else {
      // Add binding to current group
      if (current->count >= current->capacity) {
        current->capacity *= 2;
        current->bindings = realloc(current->bindings,
                                    sizeof(valk_lval_t*) * current->capacity);
      }
      current->bindings[current->count++] = item;
    }

    curr = curr->cons.tail;
  }

  return result;
}

static void aio_let_free_parsed(aio_let_parsed_t *parsed) {
  for (size_t i = 0; i < parsed->count; i++) {
    free(parsed->groups[i].bindings);
  }
  free(parsed->groups);
  free(parsed);
}

// Generate code for a single group of bindings
// Returns: (aio/then (aio/all exprs) (\ {results} (def vars) inner))
static valk_lval_t* aio_let_gen_group(valk_lenv_t *env,
                                       aio_let_group_t *group,
                                       valk_lval_t *inner) {
  if (group->count == 0) {
    return inner;
  }

  if (group->count == 1) {
    // Single binding: (aio/then expr (\ {var} inner))
    valk_lval_t *binding = group->bindings[0];
    valk_lval_t *var = valk_lval_list_nth(binding, 0);
    valk_lval_t *expr = valk_lval_list_nth(binding, 1);

    // Build: (aio/then expr (\ {var} inner))
    valk_lval_t *formals = valk_lval_qexpr_new();
    formals = valk_lval_append(formals, valk_lval_copy(var));

    valk_lval_t *lambda = valk_lval_lambda(env, formals, inner);

    valk_lval_t *then_call = valk_lval_cons(
      valk_lval_sym("aio/then"),
      valk_lval_cons(expr,
        valk_lval_cons(lambda, valk_lval_nil())));

    return then_call;
  }

  // Multiple bindings: use aio/all for parallel execution
  // Build: (aio/then (aio/all (list e1 e2 ...)) (\ {_r} (def v1) (def v2) ... inner))

  // Build expression list for aio/all
  valk_lval_t *expr_list = valk_lval_nil();
  for (int i = group->count - 1; i >= 0; i--) {
    valk_lval_t *binding = group->bindings[i];
    valk_lval_t *expr = valk_lval_list_nth(binding, 1);
    expr_list = valk_lval_cons(valk_lval_copy(expr), expr_list);
  }

  // (list e1 e2 ...)
  valk_lval_t *list_call = valk_lval_cons(valk_lval_sym("list"), expr_list);

  // (aio/all (list ...))
  valk_lval_t *all_call = valk_lval_cons(
    valk_lval_sym("aio/all"),
    valk_lval_cons(list_call, valk_lval_nil()));

  // Build lambda body: (do (= {v1} (nth _r 0)) (= {v2} (nth _r 1)) ... inner)
  valk_lval_t *body = valk_lval_cons(valk_lval_sym("do"), valk_lval_nil());
  valk_lval_t *body_tail = body;

  for (size_t i = 0; i < group->count; i++) {
    valk_lval_t *binding = group->bindings[i];
    valk_lval_t *var = valk_lval_list_nth(binding, 0);

    // (= {var} (nth _results i))
    valk_lval_t *var_qexpr = valk_lval_qexpr_new();
    var_qexpr = valk_lval_append(var_qexpr, valk_lval_copy(var));

    valk_lval_t *nth_call = valk_lval_cons(
      valk_lval_sym("nth"),
      valk_lval_cons(valk_lval_sym("_results"),
        valk_lval_cons(valk_lval_num(i), valk_lval_nil())));

    valk_lval_t *assign = valk_lval_cons(
      valk_lval_sym("="),
      valk_lval_cons(var_qexpr,
        valk_lval_cons(nth_call, valk_lval_nil())));

    body_tail->cons.tail = valk_lval_cons(assign, valk_lval_nil());
    body_tail = body_tail->cons.tail;
  }

  // Add inner expression at end
  body_tail->cons.tail = valk_lval_cons(inner, valk_lval_nil());

  // Build lambda: (\ {_results} body)
  valk_lval_t *formals = valk_lval_qexpr_new();
  formals = valk_lval_append(formals, valk_lval_sym("_results"));
  valk_lval_t *lambda = valk_lval_lambda(env, formals, body);

  // (aio/then (aio/all ...) lambda)
  valk_lval_t *then_call = valk_lval_cons(
    valk_lval_sym("aio/then"),
    valk_lval_cons(all_call,
      valk_lval_cons(lambda, valk_lval_nil())));

  return then_call;
}

static valk_lval_t* valk_builtin_aio_let(valk_lenv_t* e, valk_lval_t* a) {
  // aio/let receives: (bindings body)
  // bindings is evaluated (list of binding pairs + :then barriers)
  // body is a QEXPR to prevent premature evaluation

  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t *bindings = valk_lval_list_nth(a, 0);
  valk_lval_t *body = valk_lval_list_nth(a, 1);

  // Parse bindings into groups separated by :then
  aio_let_parsed_t *parsed = aio_let_parse_bindings(bindings);

  if (parsed->count == 0) {
    aio_let_free_parsed(parsed);
    // No bindings - wrap body in aio/pure
    valk_lval_t *pure_call = valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(body, valk_lval_nil()));
    return valk_lval_eval(e, pure_call);
  }

  // Build nested aio/then chain from innermost (body) outward
  // Work backwards: last group wraps body, previous groups wrap that, etc.
  valk_lval_t *result = valk_lval_cons(
    valk_lval_sym("aio/pure"),
    valk_lval_cons(valk_lval_copy(body), valk_lval_nil()));

  for (int g = parsed->count - 1; g >= 0; g--) {
    result = aio_let_gen_group(e, &parsed->groups[g], result);
  }

  aio_let_free_parsed(parsed);

  // Evaluate the generated code
  return valk_lval_eval(e, result);
}
```

**Register the builtin (add to `valk_register_async_handle_builtins` ~line 4510):**
```c
valk_lenv_put_builtin(env, "aio/let", valk_builtin_aio_let);
```

---

## 4. Phase 3: Demo Server Update

### 4.1 Update `examples/webserver_demo.valk`

**File:** `examples/webserver_demo.valk`

**Change lines 186-210 to:**

```lisp
; Request handler using new aio/let syntax
(def {request-handler}
  (\ {req}
    ; Extract request info
    (= {method} (plist/get req (head {:method})))
    (= {path} (plist/get req (head {:path})))
    (= {start} (time-us))

    ; Log request
    (metrics/counter-inc "http_demo_requests_total" "method" method "path" path)
    (printf "┌─ %s %s (%dµs)\n└─\n" method path (- (time-us) start))

    ; Route based on path
    (select
      ; ================================================================
      ; /slow - Demonstrates aio/let with single async binding
      ; ================================================================
      {(== path "/slow")
       (aio/let
         {((_ (aio/sleep 2000)))}  ; Sleep 2 seconds
         {:status "200" :content-type "text/plain" :body "slept 2s (async)"})}

      ; ================================================================
      ; /slow-chain - Demonstrates sequential async operations
      ; ================================================================
      {(== path "/slow-chain")
       (aio/let
         {((step1 (aio/sleep 1000))  ; First sleep
           :then                      ; Wait for step1
           (step2 (aio/sleep 1000)))} ; Then second sleep
         {:status "200" :content-type "text/plain"
          :body "slept 2s (1s + 1s sequential)"})}

      ; ================================================================
      ; /slow-parallel - Demonstrates parallel async operations
      ; ================================================================
      {(== path "/slow-parallel")
       (aio/let
         {((a (aio/sleep 1000))   ; These three run in parallel
           (b (aio/sleep 1000))
           (c (aio/sleep 1000)))}
         {:status "200" :content-type "text/plain"
          :body "slept ~1s (3x1s parallel)"})}

      ; ================================================================
      ; /complex - Demonstrates mixed parallel/sequential
      ; ================================================================
      {(== path "/complex")
       (aio/let
         {((user-data (aio/sleep 500))      ; Simulate user fetch
           (settings-data (aio/sleep 500))  ; Parallel: settings fetch
           :then                             ; Wait for both
           (posts-data (aio/sleep 300)))}   ; Sequential: needs user
         {:status "200" :content-type "application/json"
          :body "{\"user\":\"loaded\",\"settings\":\"loaded\",\"posts\":\"loaded\"}"})}

      ; Static routes (unchanged)
      {(== path "/favicon.svg")
       `{:status "200" :content-type "image/svg+xml" :body ,favicon-svg}}
      {(== path "/stress/100mb")
       `{:status "200" :content-type "text/plain" :body ,stress-100mb}}
      {otherwise
       `{:status "200" :content-type "text/html; charset=utf-8" :body ,html-body}})))
```

### 4.2 Load the Async Library

**File:** `examples/webserver_demo.valk`

**Add after line 33:**
```lisp
(load "src/async_handles.valk")
```

---

## 5. Phase 4: Testing

### 5.1 Unit Tests for Primitives

**File:** `test/test_async_let.valk` (new file)

```lisp
; Test suite for aio/let and async primitives
(load "src/prelude.valk")
(load "src/modules/test.valk")
(load "src/async_handles.valk")

; ============================================================================
; Test: as-handle wraps non-handles
; ============================================================================
(test "as-handle wraps pure values"
  (let ((h (as-handle 42)))
    (assert (handle? h) "as-handle should return a handle")))

(test "as-handle passes through handles"
  (let ((h1 (aio/pure 42))
        (h2 (as-handle h1)))
    (assert (== h1 h2) "as-handle should return same handle")))

; ============================================================================
; Test: split-at-barriers
; ============================================================================
(test "split-at-barriers with no barriers"
  (let ((groups (split-at-barriers '((a 1) (b 2) (c 3)))))
    (assert (== (len groups) 1) "should have 1 group")
    (assert (== (len (head groups)) 3) "group should have 3 bindings")))

(test "split-at-barriers with one barrier"
  (let ((groups (split-at-barriers '((a 1) (b 2) :then (c 3) (d 4)))))
    (assert (== (len groups) 2) "should have 2 groups")
    (assert (== (len (nth groups 0)) 2) "first group should have 2")
    (assert (== (len (nth groups 1)) 2) "second group should have 2")))

(test "split-at-barriers with multiple barriers"
  (let ((groups (split-at-barriers '((a 1) :then (b 2) :then (c 3)))))
    (assert (== (len groups) 3) "should have 3 groups")))

; ============================================================================
; Test: aio/let basic usage
; ============================================================================
(test "aio/let with single sync binding"
  (aio/then
    (aio/let {((x (aio/pure 42)))} {x})
    (\ {result}
      (assert (== result 42) "should bind x to 42"))))

(test "aio/let with multiple sync bindings"
  (aio/then
    (aio/let {((x (aio/pure 10))
               (y (aio/pure 20)))}
             {(+ x y)})
    (\ {result}
      (assert (== result 30) "should sum to 30"))))

(test "aio/let with barrier"
  (aio/then
    (aio/let {((x (aio/pure 10))
               :then
               (y (aio/pure (+ x 5))))}
             {y})
    (\ {result}
      (assert (== result 15) "y should depend on x"))))

; ============================================================================
; Integration tests (require running server)
; ============================================================================
(println "Async let tests completed")
```

### 5.2 Integration Tests

**File:** `test/test_async_integration.sh` (new file)

```bash
#!/bin/bash
# Integration tests for async API

set -e

echo "=== Building ==="
make build

echo "=== Starting server ==="
pkill -9 valk 2>/dev/null || true
sleep 1
./build/valk examples/webserver_demo.valk &
SERVER_PID=$!
sleep 3

cleanup() {
  kill $SERVER_PID 2>/dev/null || true
}
trap cleanup EXIT

echo "=== Test: /slow endpoint (should take ~2s) ==="
START=$(date +%s%N)
RESULT=$(curl -sk https://localhost:8443/slow)
END=$(date +%s%N)
DURATION=$(( (END - START) / 1000000 ))
echo "Duration: ${DURATION}ms"
echo "Result: $RESULT"
[ $DURATION -ge 1900 ] && [ $DURATION -le 2500 ] || { echo "FAIL: Duration outside range"; exit 1; }
echo "$RESULT" | grep -q "slept 2s" || { echo "FAIL: Wrong response"; exit 1; }
echo "PASS"

echo "=== Test: /slow-chain endpoint (should take ~2s) ==="
START=$(date +%s%N)
RESULT=$(curl -sk https://localhost:8443/slow-chain)
END=$(date +%s%N)
DURATION=$(( (END - START) / 1000000 ))
echo "Duration: ${DURATION}ms"
[ $DURATION -ge 1900 ] && [ $DURATION -le 2500 ] || { echo "FAIL: Duration outside range"; exit 1; }
echo "PASS"

echo "=== Test: /slow-parallel endpoint (should take ~1s, not 3s) ==="
START=$(date +%s%N)
RESULT=$(curl -sk https://localhost:8443/slow-parallel)
END=$(date +%s%N)
DURATION=$(( (END - START) / 1000000 ))
echo "Duration: ${DURATION}ms"
[ $DURATION -ge 900 ] && [ $DURATION -le 1500 ] || { echo "FAIL: Parallel not working, took ${DURATION}ms"; exit 1; }
echo "PASS"

echo "=== Test: /complex endpoint (should take ~800ms) ==="
START=$(date +%s%N)
RESULT=$(curl -sk https://localhost:8443/complex)
END=$(date +%s%N)
DURATION=$(( (END - START) / 1000000 ))
echo "Duration: ${DURATION}ms"
# 500ms parallel + 300ms sequential = 800ms
[ $DURATION -ge 700 ] && [ $DURATION -le 1200 ] || { echo "FAIL: Duration outside range"; exit 1; }
echo "PASS"

echo "=== All tests passed ==="
```

---

## 6. Phase 5: Cleanup Redundant Code

### 6.1 Files to DELETE

Based on the research, these files are dead code:

| File | Reason | Action |
|------|--------|--------|
| `src/async.valk` | References non-existent `future-*` functions | DELETE |
| `src/async_simple.valk` | Unused prototype | DELETE |
| `src/async_await_new.valk` | Unused prototype with mocks | DELETE |
| `src/async_lib.valk` | Comprehensive but unused | DELETE |

**Commands:**
```bash
git rm src/async.valk
git rm src/async_simple.valk
git rm src/async_await_new.valk
git rm src/async_lib.valk
```

### 6.2 Files to EVALUATE

| File | Status | Decision Criteria |
|------|--------|-------------------|
| `src/async_monadic.valk` | Used by `http_api.valk` | Keep if HTTP client needed |
| `src/http_api.valk` | HTTP client library | Keep if HTTP client needed |

**Recommendation:** Keep both for now. They provide a complete HTTP client API that may be needed for:
- HTTP/2 client operations
- External API calls from handlers
- Testing with external services

### 6.3 Code to Keep

| File | Status | Notes |
|------|--------|-------|
| `src/async_handles.valk` | KEEP + EXTEND | Primary async library |
| `src/concurrency.c` | KEEP | Core C infrastructure |
| `src/concurrency.h` | KEEP | Thread pool, futures, ARC |
| `src/aio_uv.c` async handles | KEEP | Production handle system |
| `parser.c` shift/reset | KEEP | Foundation for future |

---

## 7. Phase 6: Thread Safety

### 7.1 Current Thread Model

```
Main Thread                    Event Loop Thread
============                   =================
                              uv_run() loop
                                   │
                              HTTP request received
                                   │
                              Handler evaluated ◄── Lisp runs HERE
                                   │
                              aio/sleep timer set
                                   │
                              (returns :deferred)
                                   │
                              ... time passes ...
                                   │
                              Timer fires
                                   │
                              Handler continuation ◄── Lisp runs HERE
                                   │
                              HTTP response sent
```

**Key insight:** All Lisp execution happens on the **event loop thread**.

### 7.2 Current Safety Mechanisms

| Mechanism | Location | Purpose |
|-----------|----------|---------|
| `__thread` TLS | `aio_uv.c:98,249-251,268` | Per-thread state |
| Atomic handle ID | `aio_uv.c:150,3403` | Unique IDs across threads |
| Atomic cancel flag | `aio_uv.c:3405,3486,3592` | Safe cancellation |
| Mutex for queues | `aio_uv.c:501-514` | Cross-thread messages |
| `uv_async_send` | `aio_uv.c:2174,3136` | Thread-safe wakeup |

### 7.3 Design for Future Multi-threading

When implementing multi-threaded handlers, these changes are needed:

**A. Per-Worker GC Heaps:**
```c
// Each worker thread gets its own heap
__thread valk_gc_malloc_heap_t *worker_heap;

void worker_init() {
  worker_heap = valk_gc_malloc_heap_new();
}
```

**B. Cross-Worker Value Transfer:**
```c
// Values must be copied when sent between workers
valk_lval_t* send_to_worker(valk_lval_t *val, worker_t *target) {
  valk_lval_t *copy;
  VALK_WITH_ALLOC(target->allocator) {
    copy = valk_lval_deep_copy(val);
  }
  return copy;
}
```

**C. Environment Locking:**
```c
// Add read-write lock to environments
typedef struct valk_lenv_t {
  pthread_rwlock_t lock;
  // ... existing fields ...
} valk_lenv_t;

// Read path (concurrent)
valk_lval_t* valk_lenv_get(valk_lenv_t *env, char *sym) {
  pthread_rwlock_rdlock(&env->lock);
  valk_lval_t *val = lookup(env, sym);
  pthread_rwlock_unlock(&env->lock);
  return val;
}

// Write path (exclusive)
void valk_lenv_put(valk_lenv_t *env, char *sym, valk_lval_t *val) {
  pthread_rwlock_wrlock(&env->lock);
  insert(env, sym, val);
  pthread_rwlock_unlock(&env->lock);
}
```

**D. Async Handle Thread Safety:**

The current handle system is already thread-safe for:
- Handle ID generation (atomic)
- Cancellation flag (atomic with proper memory ordering)
- Status transitions (single-threaded, happens on event loop)

For multi-threading, add:
```c
// Protect status transitions
pthread_mutex_t status_mutex;

void valk_async_handle_complete(handle, result) {
  pthread_mutex_lock(&handle->status_mutex);
  if (handle->status == RUNNING) {
    handle->status = COMPLETED;
    handle->result = result;
    // ... callbacks ...
  }
  pthread_mutex_unlock(&handle->status_mutex);
}
```

### 7.4 API Design Principles for Thread Safety

1. **Immutable by default** - Async results should be treated as immutable
2. **Copy on transfer** - Values crossing thread boundaries must be deep-copied
3. **Handle locality** - Handles should be used by the thread that created them
4. **Explicit sharing** - Use channels/queues for cross-thread communication

---

## 8. File Reference

### Files to Modify

| File | Changes | Lines |
|------|---------|-------|
| `src/aio_uv.c` | Add `aio/sleep` builtin | After 3313 |
| `src/aio_uv.c` | Register `aio/sleep` | ~4043 |
| `src/async_handles.valk` | Add `as-handle`, `aio/map`, `aio/let` | After 24 |
| `examples/webserver_demo.valk` | Load library, update handlers | 33, 186-210 |

### New Files

| File | Purpose |
|------|---------|
| `test/test_async_let.valk` | Unit tests for aio/let |
| `test/test_async_integration.sh` | Integration tests |

### Files to Delete

| File | Reason |
|------|--------|
| `src/async.valk` | Dead code |
| `src/async_simple.valk` | Dead code |
| `src/async_await_new.valk` | Dead code |
| `src/async_lib.valk` | Dead code |

---

## 9. Test Plan

### Unit Tests

| Test | Description | Expected |
|------|-------------|----------|
| `as-handle wraps values` | `(as-handle 42)` | Returns handle |
| `as-handle passthrough` | `(as-handle (aio/pure 42))` | Same handle |
| `split-at-barriers no barrier` | `((a 1) (b 2))` | 1 group |
| `split-at-barriers one barrier` | `((a 1) :then (b 2))` | 2 groups |
| `aio/let single binding` | `(aio/let ((x 42)) x)` | 42 |
| `aio/let parallel` | `(aio/let ((a h1) (b h2)) ...)` | Parallel exec |
| `aio/let sequential` | `(aio/let ((a h1) :then (b h2)) ...)` | Sequential exec |

### Integration Tests

| Endpoint | Expected Duration | Validates |
|----------|------------------|-----------|
| `/slow` | ~2000ms | Basic aio/sleep |
| `/slow-chain` | ~2000ms | Sequential (1s + 1s) |
| `/slow-parallel` | ~1000ms | Parallel (3x1s) |
| `/complex` | ~800ms | Mixed (500ms‖500ms + 300ms) |

### Load Tests

```bash
# Test with hey (HTTP load generator)
hey -n 1000 -c 50 https://localhost:8443/slow-parallel

# Expected:
# - ~1s per request
# - 50 concurrent connections
# - Total time ~20s (1000 requests / 50 concurrency)
```

---

## Implementation Order

1. **Phase 1** (1-2 hours)
   - [ ] Add `aio/sleep` to `aio_uv.c`
   - [ ] Add `as-handle` to `async_handles.valk`
   - [ ] Add `aio/map` to `async_handles.valk`
   - [ ] Test primitives manually

2. **Phase 2** (2-4 hours)
   - [ ] Implement `split-at-barriers` helper
   - [ ] Implement `gen-group-code` helper
   - [ ] Implement `aio/let` macro
   - [ ] Unit test the macro

3. **Phase 3** (1 hour)
   - [ ] Update webserver demo
   - [ ] Add new endpoints
   - [ ] Manual testing

4. **Phase 4** (1-2 hours)
   - [ ] Write unit tests
   - [ ] Write integration tests
   - [ ] Run full test suite

5. **Phase 5** (30 min)
   - [ ] Delete dead code files
   - [ ] Commit cleanup

6. **Phase 6** (Future)
   - [ ] Document thread safety requirements
   - [ ] Add locking where needed for multi-threading
   - [ ] Test with multi-threaded handlers

---

## Appendix: Syntax Reference

### `aio/sleep`
```lisp
(aio/sleep ms) -> handle
```
Returns a handle that completes with `nil` after `ms` milliseconds.

### `as-handle`
```lisp
(as-handle value) -> handle
```
If `value` is a handle, returns it unchanged. Otherwise wraps in `aio/pure`.

### `aio/map`
```lisp
(aio/map handle fn) -> handle
```
Transforms the result of a handle using a pure function.

### `aio/let`
```lisp
(aio/let
  {((var1 expr1)
    (var2 expr2)    ; Parallel with var1
    :then           ; Barrier
    (var3 expr3))}  ; Sequential after barrier
  {body})
```
Monadic let-bindings with explicit parallel/sequential control.

- Bindings in the same group (before `:then`) run in parallel
- Groups separated by `:then` run sequentially
- Body has access to all bound variables
- Returns a handle that completes with body's value
