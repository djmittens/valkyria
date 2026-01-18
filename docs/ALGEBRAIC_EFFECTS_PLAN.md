# Algebraic Effects Implementation Plan

## Executive Summary

This plan details the implementation of **algebraic effects with one-shot delimited continuations** for Valkyria. This approach unifies all existing async patterns under a single, state-of-the-art control flow mechanism.

**Goal**: Replace the fragmented async APIs (CPS monadic, broken shift/reset, aio/do) with a unified effect system that subsumes async/await, exceptions, generators, and more.

**Key Insight**: The `lenv` environment chain is already heap-allocated. By adding a continuation field, we can capture continuations without copying - just keep the reference alive.

---

## Current State Analysis

### Existing Async Approaches

| Approach | Files | Status | Issues |
|----------|-------|--------|--------|
| CPS Monadic | `async_monadic.valk` | Working | Verbose, no direct style |
| `aio/do` macro | `aio_uv.c:5361+` | Working | Macro expansion, not true continuations |
| `async-shift/reset` | `parser.c:3512-3625` | **Broken** | Creates `LVAL_FUN`, expects `LVAL_CONT` |
| `LVAL_CONT` type | `parser.h:51` | **Unused** | Defined but never created |
| `aio/let` | `aio_uv.c` (planned) | Not implemented | Described in ASYNC_API_PLAN.md |

### Type Mismatch Bug

```c
// async-shift creates LVAL_FUN (parser.c:3532-3533)
cont->flags = LVAL_FUN | ...;

// async-resume expects LVAL_CONT (parser.c:3612)
LVAL_ASSERT_TYPE(a, cont, LVAL_CONT);
```

**Result**: `async-resume` and `http2/*-async` cannot work with `async-shift` continuations.

### Architecture Insight

The C call stack currently holds "what to do next":

```c
valk_lval_eval("(+ 1 (foo))")
  └→ valk_lval_eval("(foo)")  // "add 1" is on C stack, not lenv
```

**Solution**: Store continuation in `lenv->cont` as a closure. No copying needed - it's already on the heap.

---

## Target Architecture

### Effect System Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                         User Code                                │
│  (with-handler                                                   │
│    {Async (await h k) -> (aio/then h k)}                        │
│    (let ((data (perform Async/await (fetch-data))))             │
│      (process data)))                                            │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Effect Runtime (C)                            │
│  perform: capture continuation, invoke handler                   │
│  resume: restore continuation, continue execution                │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                 Continuation Representation                      │
│  lenv->cont: closure representing "what to do next"             │
│  Heap-allocated, GC-managed, no copying                         │
└─────────────────────────────────────────────────────────────────┘
```

### Unified API Surface

```lisp
; === Core Effect Primitives ===
(perform effect-op value)           ; Perform effect, capture continuation
(with-handler handlers body)        ; Install effect handlers
(resume k value)                    ; Resume continuation with value

; === Built-in Effects ===
(perform Async/await handle)        ; Await async operation
(perform Async/sleep ms)            ; Sleep for ms
(perform Exn/throw error)           ; Throw exception
(perform Yield/yield value)         ; Generator yield
(perform State/get)                 ; Get state
(perform State/put value)           ; Put state

; === Convenience Syntax (macros over effects) ===
(async body)                        ; Async block with Async handler
(await handle)                      ; Sugar for (perform Async/await handle)
(try body catch handler)            ; Sugar for Exn handler
(yield value)                       ; Sugar for (perform Yield/yield value)
```

---

## Implementation Phases

### Phase 0: Trampoline-Based Eval (CRITICAL FOUNDATION) ✅ COMPLETE

**Status**: Complete (2025-12-17). All tests pass. Runtime flag allows switching between trampoline and recursive eval.

**Goal**: Replace recursive C-stack eval with explicit frame stack. This is the foundation for all continuation support.

#### 0.1 Frame Types

Every "what to do next" situation needs a frame type:

```c
typedef enum {
  // Expression evaluation
  FRAME_EVAL,              // Evaluate an expression, return result

  // Function call frames
  FRAME_CALL_EVAL_FN,      // Evaluating function position of a call
  FRAME_CALL_EVAL_ARGS,    // Evaluating arguments
  FRAME_CALL_APPLY,        // All args ready, apply function

  // Special form frames
  FRAME_IF_COND,           // Evaluated condition, pick branch
  FRAME_DO_SEQUENCE,       // Sequence of expressions
  FRAME_DEF_VALUE,         // Binding a value
  FRAME_LET_BINDINGS,      // Processing let bindings

  // Effect frames
  FRAME_HANDLER_BODY,      // Inside with-handler body
  FRAME_PERFORM,           // Performing an effect

} valk_frame_type_t;
```

#### 0.2 Frame Structure

```c
typedef struct valk_eval_frame {
  valk_frame_type_t type;
  valk_lenv_t *env;              // Environment for this frame

  union {
    // FRAME_EVAL
    struct {
      valk_lval_t *expr;
    } eval;

    // FRAME_CALL_EVAL_FN, FRAME_CALL_EVAL_ARGS, FRAME_CALL_APPLY
    struct {
      valk_lval_t *fn;           // Evaluated function (NULL until ready)
      valk_lval_t **args;        // Array of evaluated args
      size_t args_capacity;
      size_t args_count;         // How many args evaluated so far
      valk_lval_t *remaining;    // Unevaluated args list
      valk_lval_t *original_expr; // For error messages
    } call;

    // FRAME_IF_COND
    struct {
      valk_lval_t *then_branch;
      valk_lval_t *else_branch;
    } if_cond;

    // FRAME_DO_SEQUENCE
    struct {
      valk_lval_t *remaining;    // Remaining expressions to evaluate
    } seq;

    // FRAME_DEF_VALUE
    struct {
      valk_lval_t *symbol;
    } def;

    // FRAME_LET_BINDINGS
    struct {
      valk_lval_t *remaining_bindings;
      valk_lval_t *body;
      valk_lenv_t *let_env;
    } let;

    // FRAME_HANDLER_BODY
    struct {
      valk_lval_t *handlers;     // Handler definitions
      valk_lval_t *prev_handlers; // Previous handler stack (for restore)
    } handler;
  };
} valk_eval_frame_t;
```

#### 0.3 Eval Stack Structure

```c
typedef struct {
  valk_eval_frame_t *frames;
  size_t count;
  size_t capacity;

  // For continuation capture
  uint64_t version;              // Incremented on push/pop for cache invalidation
} valk_eval_stack_t;

// Stack operations
void valk_eval_stack_init(valk_eval_stack_t *stack);
void valk_eval_stack_free(valk_eval_stack_t *stack);
void valk_eval_stack_push(valk_eval_stack_t *stack, valk_eval_frame_t frame);
valk_eval_frame_t *valk_eval_stack_top(valk_eval_stack_t *stack);
void valk_eval_stack_pop(valk_eval_stack_t *stack);
bool valk_eval_stack_empty(valk_eval_stack_t *stack);

// For continuations - shallow copy (frames reference heap-allocated data)
valk_eval_stack_t *valk_eval_stack_copy(valk_eval_stack_t *stack);
```

#### 0.4 Trampoline Main Loop

```c
valk_lval_t *valk_eval_trampoline(valk_lenv_t *env, valk_lval_t *expr) {
  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);

  // Initial frame: evaluate the expression
  valk_eval_stack_push(&stack, (valk_eval_frame_t){
    .type = FRAME_EVAL,
    .env = env,
    .eval = { .expr = expr }
  });

  valk_lval_t *value = NULL;  // Current value being threaded through

  while (!valk_eval_stack_empty(&stack)) {
    valk_eval_frame_t *frame = valk_eval_stack_top(&stack);

    switch (frame->type) {
      case FRAME_EVAL:
        value = eval_step_expr(&stack, frame, value);
        break;

      case FRAME_CALL_EVAL_FN:
        value = eval_step_call_fn(&stack, frame, value);
        break;

      case FRAME_CALL_EVAL_ARGS:
        value = eval_step_call_args(&stack, frame, value);
        break;

      case FRAME_CALL_APPLY:
        value = eval_step_call_apply(&stack, frame, value);
        break;

      case FRAME_IF_COND:
        value = eval_step_if(&stack, frame, value);
        break;

      case FRAME_DO_SEQUENCE:
        value = eval_step_sequence(&stack, frame, value);
        break;

      case FRAME_DEF_VALUE:
        value = eval_step_def(&stack, frame, value);
        break;

      case FRAME_HANDLER_BODY:
        value = eval_step_handler(&stack, frame, value);
        break;

      // ... other frame types
    }

    // Check for errors
    if (value && LVAL_TYPE(value) == LVAL_ERR) {
      valk_eval_stack_free(&stack);
      return value;
    }
  }

  valk_eval_stack_free(&stack);
  return value;
}
```

#### 0.5 Step Functions

Each frame type has a step function. Example for FRAME_EVAL:

```c
static valk_lval_t *eval_step_expr(valk_eval_stack_t *stack,
                                    valk_eval_frame_t *frame,
                                    valk_lval_t *prev_value) {
  valk_lval_t *expr = frame->eval.expr;
  valk_lenv_t *env = frame->env;

  // Pop this frame - we're handling it now
  valk_eval_stack_pop(stack);

  switch (LVAL_TYPE(expr)) {
    // Self-evaluating
    case LVAL_NUM:
    case LVAL_STR:
    case LVAL_NIL:
    case LVAL_QEXPR:
    case LVAL_FUN:
    case LVAL_HANDLE:
      return expr;

    // Symbol lookup
    case LVAL_SYM:
      return valk_lenv_get(env, expr);

    // Function call
    case LVAL_CONS: {
      if (valk_lval_list_is_empty(expr)) {
        return valk_lval_nil();
      }

      valk_lval_t *first = expr->cons.head;

      // Check for special forms
      if (LVAL_TYPE(first) == LVAL_SYM) {
        // quote
        if (strcmp(first->str, "quote") == 0) {
          return valk_lval_list_nth(expr, 1);
        }

        // if - push IF_COND frame, then eval condition
        if (strcmp(first->str, "if") == 0) {
          valk_eval_stack_push(stack, (valk_eval_frame_t){
            .type = FRAME_IF_COND,
            .env = env,
            .if_cond = {
              .then_branch = valk_lval_list_nth(expr, 2),
              .else_branch = valk_lval_list_count(expr) > 3
                ? valk_lval_list_nth(expr, 3)
                : valk_lval_nil()
            }
          });
          // Push eval frame for condition
          valk_eval_stack_push(stack, (valk_eval_frame_t){
            .type = FRAME_EVAL,
            .env = env,
            .eval = { .expr = valk_lval_list_nth(expr, 1) }
          });
          return NULL;  // Continue loop
        }

        // do - push sequence frame
        if (strcmp(first->str, "do") == 0) {
          valk_lval_t *body = expr->cons.tail;
          if (valk_lval_list_is_empty(body)) {
            return valk_lval_nil();
          }
          valk_eval_stack_push(stack, (valk_eval_frame_t){
            .type = FRAME_DO_SEQUENCE,
            .env = env,
            .seq = { .remaining = body->cons.tail }
          });
          valk_eval_stack_push(stack, (valk_eval_frame_t){
            .type = FRAME_EVAL,
            .env = env,
            .eval = { .expr = body->cons.head }
          });
          return NULL;
        }

        // with-handler - push handler frame
        if (strcmp(first->str, "with-handler") == 0) {
          valk_lval_t *handlers = valk_lval_list_nth(expr, 1);
          valk_lval_t *body = valk_lval_list_nth(expr, 2);

          // Install handlers in environment
          valk_lenv_t *handler_env = valk_lenv_new();
          handler_env->parent = env;
          handler_env->handler_stack = valk_lval_cons(handlers, env->handler_stack);

          valk_eval_stack_push(stack, (valk_eval_frame_t){
            .type = FRAME_HANDLER_BODY,
            .env = env,  // Original env for restore
            .handler = {
              .handlers = handlers,
              .prev_handlers = env->handler_stack
            }
          });
          valk_eval_stack_push(stack, (valk_eval_frame_t){
            .type = FRAME_EVAL,
            .env = handler_env,
            .eval = { .expr = body }
          });
          return NULL;
        }

        // perform - capture continuation and call handler
        if (strcmp(first->str, "perform") == 0) {
          return eval_perform(stack, env, expr);
        }
      }

      // Regular function call
      // Push CALL_EVAL_ARGS frame, then eval function position
      valk_lval_t *args_list = expr->cons.tail;
      size_t arg_count = valk_lval_list_count(args_list);

      valk_eval_stack_push(stack, (valk_eval_frame_t){
        .type = FRAME_CALL_EVAL_FN,
        .env = env,
        .call = {
          .fn = NULL,
          .args = arg_count > 0 ? malloc(sizeof(valk_lval_t*) * arg_count) : NULL,
          .args_capacity = arg_count,
          .args_count = 0,
          .remaining = args_list,
          .original_expr = expr
        }
      });
      valk_eval_stack_push(stack, (valk_eval_frame_t){
        .type = FRAME_EVAL,
        .env = env,
        .eval = { .expr = first }
      });
      return NULL;
    }

    default:
      return valk_lval_err("Cannot evaluate type: %s", valk_ltype_name(LVAL_TYPE(expr)));
  }
}
```

#### 0.6 Continuation Capture (perform)

```c
static valk_lval_t *eval_perform(valk_eval_stack_t *stack,
                                  valk_lenv_t *env,
                                  valk_lval_t *expr) {
  valk_lval_t *effect_op = valk_lval_list_nth(expr, 1);
  valk_lval_t *value = valk_lval_list_count(expr) > 2
    ? valk_lval_list_nth(expr, 2)
    : valk_lval_nil();

  // Find handler for this effect
  valk_lval_t *handler = find_handler(env, effect_op->str);
  if (!handler) {
    return valk_lval_err("Unhandled effect: %s", effect_op->str);
  }

  // Capture continuation = copy of current stack
  valk_lval_t *k = valk_lval_cont_new();
  k->cont.stack = valk_eval_stack_copy(stack);
  k->cont.env = env;

  // Clear current stack - handler takes over
  stack->count = 0;

  // Call handler with (value, k)
  // Handler is a function: (lambda (value k) ...)
  valk_lval_t *handler_args = valk_lval_cons(value, valk_lval_cons(k, valk_lval_nil()));

  // Push frame to call handler
  valk_eval_stack_push(stack, (valk_eval_frame_t){
    .type = FRAME_CALL_APPLY,
    .env = env,
    .call = {
      .fn = handler,
      .args = (valk_lval_t*[]){value, k},
      .args_count = 2,
    }
  });

  return NULL;  // Continue with handler
}
```

#### 0.7 Continuation Resume

```c
// (resume k value) - restore stack and continue with value
static valk_lval_t *builtin_resume(valk_lenv_t *env, valk_lval_t *args) {
  valk_lval_t *k = valk_lval_list_nth(args, 0);
  valk_lval_t *value = valk_lval_list_nth(args, 1);

  if (LVAL_TYPE(k) != LVAL_CONT) {
    return valk_lval_err("resume: first argument must be a continuation");
  }

  // One-shot check
  if (k->cont.consumed) {
    return valk_lval_err("resume: continuation already consumed (one-shot)");
  }
  k->cont.consumed = true;

  // Get the captured stack
  valk_eval_stack_t *captured = k->cont.stack;

  // Continue evaluation with the captured stack and value
  return valk_eval_trampoline_with_stack(captured, value);
}

// Trampoline variant that starts with existing stack and value
valk_lval_t *valk_eval_trampoline_with_stack(valk_eval_stack_t *stack,
                                              valk_lval_t *initial_value) {
  valk_lval_t *value = initial_value;

  while (!valk_eval_stack_empty(stack)) {
    // ... same loop as valk_eval_trampoline
  }

  return value;
}
```

#### 0.8 LVAL_CONT Structure Update

```c
// In parser.h, update the cont union member:
struct {
  valk_eval_stack_t *stack;   // Captured evaluation stack
  valk_lenv_t *env;           // Environment at capture point
  bool consumed;              // One-shot: true after resume
} cont;
```

#### 0.9 GC Integration

The eval stack contains pointers to heap objects. GC must trace:

```c
void valk_gc_mark_eval_stack(valk_eval_stack_t *stack) {
  for (size_t i = 0; i < stack->count; i++) {
    valk_eval_frame_t *frame = &stack->frames[i];

    // Mark environment
    valk_gc_mark_env(frame->env);

    // Mark frame-specific data
    switch (frame->type) {
      case FRAME_EVAL:
        valk_gc_mark_lval(frame->eval.expr);
        break;

      case FRAME_CALL_EVAL_FN:
      case FRAME_CALL_EVAL_ARGS:
      case FRAME_CALL_APPLY:
        if (frame->call.fn) valk_gc_mark_lval(frame->call.fn);
        for (size_t j = 0; j < frame->call.args_count; j++) {
          valk_gc_mark_lval(frame->call.args[j]);
        }
        valk_gc_mark_lval(frame->call.remaining);
        break;

      case FRAME_IF_COND:
        valk_gc_mark_lval(frame->if_cond.then_branch);
        valk_gc_mark_lval(frame->if_cond.else_branch);
        break;

      // ... other frame types
    }
  }
}

// Update valk_gc_mark_lval for LVAL_CONT:
case LVAL_CONT:
  if (v->cont.stack) {
    valk_gc_mark_eval_stack(v->cont.stack);
  }
  if (v->cont.env) {
    valk_gc_mark_env(v->cont.env);
  }
  break;
```

#### 0.10 Migration Strategy

1. **Create new file**: `src/eval_trampoline.c` with trampoline implementation
2. **Keep old eval**: Rename to `valk_lval_eval_recursive` for comparison
3. **Feature flag**: `#define VALK_TRAMPOLINE_EVAL 1`
4. **Test both**: Run test suite with both implementations
5. **Benchmark**: Compare performance
6. **Switch**: Once stable, make trampoline the default
7. **Remove**: Delete recursive eval after confidence

**Tasks for Phase 0**:
- [x] Create `src/eval_trampoline.h` with frame types and stack API
- [x] Create `src/eval_trampoline.c` with trampoline implementation
- [x] Implement all frame step functions
- [x] Add GC marking for eval stack
- [x] Update LVAL_CONT to hold stack pointer
- [x] Add feature flag to switch between eval modes (compile-time and runtime)
- [x] Port all special forms (if, do, def, let, lambda, etc.)
- [x] Port builtins that call eval (map, filter, etc.) - N/A, builtins call back via recursive
- [x] Run full test suite with trampoline eval (28 tests pass)
- [ ] Benchmark trampoline vs recursive

**Tests** (`test/test_eval_trampoline.c`):
- [x] `test_trampoline_self_eval` - numbers, strings, nil
- [x] `test_trampoline_symbol_lookup` - covered in matches_recursive test
- [x] `test_trampoline_function_call`
- [x] `test_trampoline_nested_calls`
- [x] `test_trampoline_if`
- [x] `test_trampoline_do_sequence`
- [x] `test_trampoline_lambda`
- [x] `test_trampoline_recursion` - verify deep recursion works (5000+ depth)
- [x] `test_trampoline_matches_recursive` - same results as old eval
- [x] `test_stack_copy`
- [x] `test_gc_marks_stack`
- [x] `test_runtime_flag_dispatch` - test runtime switching between eval modes
- [x] `test_trampoline_comprehensive` - higher-order functions, closures, varargs

---

### Phase 1: Core Infrastructure (lenv Continuation Support) ✅ COMPLETE

**Status**: Complete (2025-12-17). All tests pass.

**Goal**: Add continuation field to `lenv`, make continuations first-class.

#### 1.1 Extend lenv Structure

**File**: `src/parser.h`

```c
struct valk_lenv_t {
  uint64_t flags;
  struct {
    char **items;
    size_t count;
    size_t capacity;
  } symbols;
  struct {
    valk_lval_t **items;
    size_t count;
    size_t capacity;
  } vals;
  struct valk_lenv_t *parent;
  struct valk_lenv_t *fallback;
  void *allocator;

  // NEW: Continuation support for effects
  valk_lval_t *cont;              // Continuation closure (what to do with result)
  valk_lval_t *handler_stack;     // Stack of effect handlers (list of handler envs)
};
```

#### 1.2 Update lenv Functions

**File**: `src/parser.c`

- `valk_lenv_new()`: Initialize `cont = NULL`, `handler_stack = NULL`
- `valk_lenv_copy()`: Copy continuation fields
- `valk_lenv_del()`: No special handling (GC manages closures)

#### 1.3 Update GC Marking

**File**: `src/gc.c`

```c
static void valk_gc_mark_env(valk_lenv_t* env) {
  // ... existing marking ...

  // Mark continuation if present
  if (env->cont) {
    valk_gc_mark_lval(env->cont);
  }

  // Mark handler stack
  if (env->handler_stack) {
    valk_gc_mark_lval(env->handler_stack);
  }
}
```

#### 1.4 Repurpose LVAL_CONT

**File**: `src/parser.h`

```c
// Continuation now stores:
struct {
  valk_lenv_t *env;           // Environment at capture point
  valk_lval_t *expr;          // Expression to evaluate (body after perform)
  valk_lval_t *handler_stack; // Handler stack at capture point
} cont;
```

**Tasks**:
- [x] Add `cont` and `handler_stack` fields to `valk_lenv_t`
- [x] Update `valk_lenv_new()` to initialize new fields (`valk_lenv_init()`)
- [x] Update `valk_lenv_copy()` to copy new fields
- [x] Update GC marking in `valk_gc_mark_env_contents()`
- [x] `LVAL_CONT` struct already holds proper continuation data (from Phase 0)
- [x] `valk_lval_cont()` constructor already exists (from Phase 0)
- [x] `valk_lval_copy()` for `LVAL_CONT` - N/A, handled in Phase 0
- [x] `valk_lval_print()` for `LVAL_CONT` - already implemented

**Tests** (`test/test_continuations.c`):
- [x] `test_lenv_cont_field_initialized_null`
- [x] `test_lenv_cont_field_preserved_on_copy`
- [x] `test_gc_marks_lenv_cont`
- [x] `test_gc_marks_handler_stack`
- [x] `test_lval_cont_creation`
- [x] `test_lval_cont_copy` - covered by creation tests

---

### Phase 2: Effect Handler Infrastructure ✅ COMPLETE

**Status**: Complete (2025-12-17). All 13 tests pass.

**Goal**: Implement `with-handler` and handler lookup.

**Important Note**: The body of `with-handler` must be a QEXPR `{body}` because arguments are eagerly evaluated. The body is then converted to CONS and evaluated inside the handler scope.

#### 2.1 Handler Representation

Handlers are stored as an association list in `handler_stack`:

```lisp
; Handler stack structure (list of handler entries)
(({Async/await handler-fn} {Async/sleep handler-fn}) ; Current handler set
 ({Exn/throw handler-fn})                            ; Outer handler set
 ...)
```

#### 2.2 Syntax

```lisp
; Install handlers and run body
(with-handler
  {(Effect/op {formals} body) ...}  ; Handler definitions
  {body-expr})                       ; Body (QEXPR, evaluated in handler scope)

; Look up handler (for testing/debugging)
(find-handler 'Effect/op)

; Get current handler stack
(handler-stack)
```

#### 2.3 Implementation Summary

**Files modified**:
- `src/parser.c`: Added `valk_effect_parse_handlers()`, `valk_effect_find_handler()`, `valk_builtin_with_handler()`, `valk_builtin_find_handler()`, `valk_builtin_handler_stack()`
- `CMakeLists.txt`: Added `test_effects` executable

**Key implementation details**:
- `parse_handlers()` converts handler syntax `{(Effect/op {formals} body) ...}` to a list of `(effect-op-sym handler-lambda)` pairs
- `find_handler()` searches up the environment parent chain for handler_stacks, then searches each handler set
- `with-handler` creates a new environment with updated handler_stack, then evaluates body in that scope
- Handler stack automatically "pops" when with-handler returns (the handler_env goes out of scope)

**Tasks**:
- [x] Implement `parse_handlers()` to convert handler syntax to internal rep
- [x] Implement `valk_builtin_with_handler()`
- [x] Implement `find_handler()` for handler lookup (walks env parent chain)
- [x] Register `with-handler`, `find-handler`, `handler-stack` builtins
- [x] Add handler stack manipulation helpers

**Tests** (`test/test_effects.c`):
- [x] `test_with_handler_installs_handler`
- [x] `test_with_handler_pops_on_return`
- [x] `test_handler_lookup_finds_inner`
- [x] `test_handler_lookup_finds_outer`
- [x] `test_handler_lookup_returns_null_if_missing`
- [x] `test_with_handler_multiple_handlers`
- [x] `test_handler_stack_returns_nil_when_empty`
- [x] `test_handler_stack_returns_stack_inside_handler`
- [x] `test_with_handler_body_can_access_outer_vars`
- [x] `test_with_handler_body_can_define_vars`
- [x] `test_with_handler_error_propagation`
- [x] `test_with_handler_invalid_handler_syntax`
- [x] `test_gc_preserves_handler_stack`

---

### Phase 3: Perform and Resume ✅ COMPLETE

**Goal**: Implement `perform` (capture continuation) and `resume` (restore continuation).

**Status**: Complete. Implemented using trampoline-based continuation capture.

**Key Implementation Details**:
- `perform` captures the eval stack via thread-local pointer and creates LVAL_CONT
- `resume` restores the stack and continues with `valk_eval_trampoline_with_stack`
- `with-handler` now uses trampoline eval to enable stack capture
- One-shot semantics enforced by clearing stack pointer after first resume
- Effect name must be quoted: `(perform 'Effect/op value)`

**Files Modified**:
- `src/eval_trampoline.c`: Added thread-local stack pointer, stack save/restore in trampoline
- `src/eval_trampoline.h`: Added `valk_eval_get_current_stack()` declaration
- `src/parser.c`: Added `valk_builtin_perform()`, `valk_builtin_resume()`, updated `with-handler` to use trampoline

**Tests**: `test/test_effects.c` - Phase 3 tests for perform/resume semantics

#### 3.1 Builtin: perform

```c
// (perform Effect/op value)
static valk_lval_t* valk_builtin_perform(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_GE(a, a, 1);

  valk_lval_t* effect_op = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, effect_op, LVAL_SYM);

  valk_lval_t* value = valk_lval_list_count(a) > 1
    ? valk_lval_list_nth(a, 1)
    : valk_lval_nil();

  // Find handler for this effect
  valk_lval_t* handler = find_handler(e, effect_op->str);
  if (!handler) {
    return valk_lval_err("Unhandled effect: %s", effect_op->str);
  }

  // Capture continuation
  valk_lval_t* k = valk_lval_cont_new(e);

  // Call handler with (value, k)
  valk_lval_t* args = valk_lval_cons(value, valk_lval_cons(k, valk_lval_nil()));
  return valk_lval_eval_call(e, handler, args);
}
```

#### 3.2 Builtin: resume

```c
// (resume k value)
static valk_lval_t* valk_builtin_resume(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* k = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, k, LVAL_CONT);

  valk_lval_t* value = valk_lval_list_nth(a, 1);

  // Restore continuation environment
  valk_lenv_t* cont_env = k->cont.env;

  // Bind the value to a fresh variable or return directly
  // The continuation's env->cont closure expects the value
  if (cont_env->cont) {
    valk_lval_t* cont_closure = cont_env->cont;
    valk_lval_t* args = valk_lval_cons(value, valk_lval_nil());
    return valk_lval_eval_call(cont_env, cont_closure, args);
  }

  return value;
}
```

#### 3.3 Continuation Capture Strategy

When `perform` is called, we need to capture "what happens after this expression returns". Two approaches:

**Approach A: Explicit Continuation Passing**

Transform code at handler installation to pass continuations explicitly:

```lisp
; Original
(with-handler {(Async/await (h k) -> (aio/then h k))}
  (+ 1 (perform Async/await (fetch-data))))

; Transformed (conceptually)
(with-handler ...
  (perform Async/await (fetch-data)
    (lambda (result) (+ 1 result))))
```

**Approach B: Environment-Based Continuation**

Store continuation in `env->cont` at each step:

```c
// During eval of (+ 1 (foo)):
// 1. Create env with cont = (lambda (x) (+ 1 x))
// 2. Eval (foo) in that env
// 3. If (foo) performs effect, capture env (which includes cont)
```

**Recommendation**: Start with Approach A (simpler), migrate to B if needed.

**Tasks**:
- [x] Implement `valk_lval_cont_new()` to capture current env state
- [x] Implement `valk_builtin_perform()`
- [x] Implement `valk_builtin_resume()`
- [x] Register `perform` and `resume` builtins
- [x] Handle nested performs correctly
- [x] Ensure one-shot semantics (warn/error on multi-resume)

**Tests** (`test/test_effects.c`):
- [x] `test_perform_calls_handler`
- [x] `test_perform_passes_value_to_handler`
- [x] `test_perform_passes_continuation_to_handler`
- [x] `test_resume_continues_execution`
- [x] `test_resume_with_value`
- [x] `test_unhandled_effect_errors`
- [x] `test_nested_performs`
- [x] `test_one_shot_continuation_enforcement`

---

### Phase 4: Built-in Effect Handlers

**Goal**: Implement standard effects for async, exceptions, and generators.

#### 4.1 Async Effect

**File**: `src/effects/async.valk`

```lisp
; Async effect operations
(def {Async/await} "Async/await")
(def {Async/sleep} "Async/sleep")

; Default async handler (integrates with aio system)
(def {async-handler}
  {(Async/await (handle k)
     (aio/then handle (\ {result} (resume k result))))
   (Async/sleep (ms k)
     (aio/then (aio/sleep ms) (\ {_} (resume k nil))))})

; Async block macro
(defmacro async {body}
  `(with-handler ,async-handler ,body))

; Await sugar
(defmacro await {handle}
  `(perform Async/await ,handle))
```

#### 4.2 Exception Effect

**File**: `src/effects/exception.valk`

```lisp
; Exception effect
(def {Exn/throw} "Exn/throw")

; Default exception handler (no resume, just return error)
(def {exn-handler}
  {(Exn/throw (error k)
     {:error error})})  ; Don't resume, return error value

; Try-catch macro
(defmacro try {body catch-clause}
  `(with-handler
     {(Exn/throw (error k) ,catch-clause)}
     ,body))

; Throw sugar
(defmacro throw {error}
  `(perform Exn/throw ,error))
```

#### 4.3 Generator Effect

**File**: `src/effects/generator.valk`

```lisp
; Generator effect
(def {Yield/yield} "Yield/yield")

; Generator constructor
(def {make-generator}
  (\ {body}
    ; Returns a stateful generator object
    (let ((cont nil)
          (done false))
      {:next (\ {}
               (if done
                 {:done true}
                 (with-handler
                   {(Yield/yield (value k)
                      (set! cont k)
                      {:value value :done false})}
                   (if cont
                     (resume cont nil)
                     (do
                       (body)
                       (set! done true)
                       {:done true})))))})))

; Yield sugar
(defmacro yield {value}
  `(perform Yield/yield ,value))
```

**Tasks**:
- [ ] Create `src/effects/` directory
- [ ] Implement `async.valk` with Async effect
- [ ] Implement `exception.valk` with Exn effect
- [ ] Implement `generator.valk` with Yield effect
- [ ] Create `src/effects/prelude.valk` that loads all effects
- [ ] Update `src/prelude.valk` to load effects

**Tests** (`test/test_effects_stdlib.valk`):
- [ ] `test_async_await_basic`
- [ ] `test_async_await_sequential`
- [ ] `test_async_await_error`
- [ ] `test_try_catch_basic`
- [ ] `test_try_catch_no_error`
- [ ] `test_try_nested`
- [ ] `test_generator_basic`
- [ ] `test_generator_multiple_yields`
- [ ] `test_generator_exhaustion`

---

### Phase 5: Unify Existing APIs

**Goal**: Migrate existing async code to use effects, deprecate old APIs.

#### 5.1 Migration: aio/do to Effects

**Before** (current):
```lisp
(aio/do
  (println "start")
  (<- result (aio/sleep 1000))
  (println "done")
  result)
```

**After** (effects):
```lisp
(async
  (println "start")
  (def {result} (await (aio/sleep 1000)))
  (println "done")
  result)
```

#### 5.2 Migration: async_monadic.valk

**Before**:
```lisp
(async/bind (fetch-data) (\ {data}
  (async/bind (process data) (\ {result}
    (async/pure result)))))
```

**After**:
```lisp
(async
  (def {data} (await (fetch-data)))
  (def {result} (await (process data)))
  result)
```

#### 5.3 Deprecation Plan

| Old API | New API | Timeline |
|---------|---------|----------|
| `async-shift` | `perform` | Remove in Phase 5 |
| `async-reset` | `with-handler` | Remove in Phase 5 |
| `async-resume` | `resume` | Remove in Phase 5 |
| `async/bind` | `await` + `async` | Deprecate, keep for compat |
| `aio/do` | `async` | Deprecate, keep for compat |

**Tasks**:
- [ ] Add deprecation warnings to old APIs
- [ ] Update all examples to use new API
- [ ] Update documentation
- [ ] Remove broken `async-shift/reset/resume` code
- [ ] Keep `aio/do` as compatibility layer (implemented via effects)

**Tests**:
- [ ] `test_migration_aio_do_equivalent`
- [ ] `test_migration_async_bind_equivalent`
- [ ] `test_deprecation_warnings_shown`

---

### Phase 6: HTTP Handler Integration

**Goal**: Make HTTP handlers use the effect system natively.

#### 6.1 HTTP Handler with Effects

```lisp
(http/handler {req}
  (async
    (def {user} (await (db/fetch-user (req :user-id))))
    (def {posts} (await (db/fetch-posts user)))
    {:status 200
     :body {:user user :posts posts}}))
```

#### 6.2 Automatic Handler Wrapping

When registering HTTP handlers, automatically wrap in async context:

```c
// In valk_aio_http2_server_set_handler
valk_lval_t* wrapped_handler = wrap_with_async_handler(handler_fn);
```

**Tasks**:
- [ ] Modify HTTP handler invocation to install async handler
- [ ] Handle `:deferred` responses via effects
- [ ] Update SSE to use effects
- [ ] Update examples/webserver_demo.valk

**Tests** (`test/test_http_effects.valk`):
- [ ] `test_http_handler_with_await`
- [ ] `test_http_handler_sequential_awaits`
- [ ] `test_http_handler_error_handling`
- [ ] `test_http_handler_sse_with_effects`

---

### Phase 7: Performance Optimization

**Goal**: Ensure effect system is performant for production use.

#### 7.1 Fast Path for No Effects

Most code doesn't use effects. Optimize the common case:

```c
valk_lval_t* valk_lval_eval(valk_lenv_t* env, valk_lval_t* expr) {
  // Fast path: no handlers installed
  if (!env->handler_stack) {
    return valk_lval_eval_fast(env, expr);
  }
  // Slow path: handlers present
  return valk_lval_eval_with_effects(env, expr);
}
```

#### 7.2 Handler Caching

Cache handler lookups to avoid repeated stack traversal:

```c
typedef struct {
  const char* effect_op;
  valk_lval_t* handler;
  uint32_t stack_version;
} handler_cache_entry_t;
```

#### 7.3 One-Shot Optimization

Since continuations are one-shot, we can avoid copying:

```c
// Mark continuation as consumed after resume
void valk_lval_cont_consume(valk_lval_t* k) {
  k->cont.consumed = true;
}

// Error if resumed twice
if (k->cont.consumed) {
  return valk_lval_err("Continuation already resumed (one-shot)");
}
```

**Tasks**:
- [ ] Implement fast path for handler-free code
- [ ] Add handler lookup caching
- [ ] Implement one-shot continuation enforcement
- [ ] Benchmark effect overhead
- [ ] Profile and optimize hot paths

**Tests**:
- [ ] `test_no_handler_fast_path`
- [ ] `test_handler_cache_hit`
- [ ] `test_one_shot_enforcement`
- [ ] `bench_effect_overhead`

---

### Phase 8: Documentation and Examples

**Goal**: Comprehensive documentation for the effect system.

#### 8.1 Documentation Files

- [ ] `docs/EFFECTS.md` - Effect system overview
- [ ] `docs/EFFECTS_API.md` - API reference
- [ ] `docs/EFFECTS_TUTORIAL.md` - Tutorial with examples
- [ ] Update `docs/LANGUAGE.md` with effect syntax

#### 8.2 Examples

- [ ] `examples/async_effects.valk` - Basic async examples
- [ ] `examples/error_handling.valk` - Exception examples
- [ ] `examples/generators.valk` - Generator examples
- [ ] `examples/custom_effects.valk` - Custom effect examples
- [ ] Update `examples/webserver_demo.valk` to use effects

---

## Test Plan

### Coverage Requirements

Per `docs/COVERAGE_REQUIREMENTS.md`:
- **src/ runtime code**: 90% line, 85% branch
- All new C code must meet these requirements

### Test Categories

#### Unit Tests (C)

| File | Tests | Coverage Target |
|------|-------|-----------------|
| `test/test_continuations.c` | lenv cont field, LVAL_CONT | 90% |
| `test/test_effects.c` | perform, resume, with-handler | 90% |
| `test/test_effects_gc.c` | GC marking of continuations | 90% |

#### Unit Tests (Valk)

| File | Tests | Coverage Target |
|------|-------|-----------------|
| `test/test_effects_basic.valk` | Basic effect operations | 90% |
| `test/test_effects_async.valk` | Async effect | 90% |
| `test/test_effects_exception.valk` | Exception effect | 90% |
| `test/test_effects_generator.valk` | Generator effect | 90% |
| `test/test_effects_nested.valk` | Nested handlers | 90% |

#### Integration Tests

| File | Tests | Coverage Target |
|------|-------|-----------------|
| `test/test_http_effects.valk` | HTTP + effects | 85% |
| `test/test_effects_integration.valk` | Cross-effect interactions | 85% |

#### Stress Tests

| File | Purpose |
|------|---------|
| `test/stress/test_effects_stress.valk` | Many concurrent effects |
| `test/stress/test_continuation_gc.valk` | GC under continuation load |

### Test Execution

```bash
# Run all effect tests
make test-effects

# Run with coverage
make coverage-effects

# Run stress tests
make stress-effects
```

---

## Implementation Schedule

### Milestone 1: Core Infrastructure (Phase 1-2)
- lenv continuation field
- Handler stack
- with-handler builtin
- **Deliverable**: Handlers can be installed and looked up

### Milestone 2: Effect Operations (Phase 3)
- perform builtin
- resume builtin
- Continuation capture
- **Deliverable**: Effects can be performed and resumed

### Milestone 3: Standard Library (Phase 4)
- Async effect
- Exception effect
- Generator effect
- **Deliverable**: Common patterns work out of box

### Milestone 4: Migration (Phase 5-6)
- Deprecate old APIs
- Update HTTP handlers
- Update examples
- **Deliverable**: Unified async API

### Milestone 5: Production Ready (Phase 7-8)
- Performance optimization
- Documentation
- 90% coverage
- **Deliverable**: Production-ready effect system

---

## Risk Mitigation

### Risk: Performance Regression

**Mitigation**:
- Fast path for non-effect code
- Benchmark before/after
- Handler caching

### Risk: GC Complexity

**Mitigation**:
- Continuations are just closures (already GC-managed)
- One-shot semantics simplify lifetime
- Extensive GC tests

### Risk: Breaking Existing Code

**Mitigation**:
- Keep old APIs as deprecated compatibility layer
- Gradual migration path
- Comprehensive test suite

### Risk: Complexity

**Mitigation**:
- Start simple (one-shot, explicit continuations)
- Add features incrementally
- Clear documentation

---

## Success Criteria

1. **Unified API**: Single way to do async (`async`/`await`)
2. **Effects Work**: Can define and handle custom effects
3. **90% Coverage**: All new code meets coverage requirements
4. **No Regression**: Existing tests pass
5. **Performance**: <10% overhead for non-effect code
6. **Documentation**: Complete API docs and tutorial

---

## Appendix: Syntax Reference

### Effect Declaration (Future)

```lisp
(defeffect Async
  (await handle)    ; Await async handle
  (sleep ms))       ; Sleep for milliseconds

(defeffect State
  (get)             ; Get current state
  (put value))      ; Set current state
```

### Handler Syntax

```lisp
(with-handler
  {(Effect/op (arg1 arg2 k)
     handler-body)}
  body-expr)
```

### Perform Syntax

```lisp
(perform Effect/op arg1 arg2 ...)
```

### Resume Syntax

```lisp
(resume k value)
```

---

## References

- [Koka Language](https://koka-lang.github.io/) - Algebraic effects in practice
- [Multicore OCaml](https://github.com/ocaml-multicore/ocaml-multicore) - Production effects
- [Eff Language](https://www.eff-lang.org/) - Research language for effects
- [Handlers in Action](https://homepages.inf.ed.ac.uk/slindley/papers/handlers.pdf) - Academic paper
- [One-Shot Continuations](https://www.cs.indiana.edu/~dyb/pubs/call1cc.pdf) - Implementation strategies
