# Async Callback Environment Capture

This document explains how async callbacks in Valkyria capture and preserve their lexical environment for deferred execution.

## 1. Lambda Captures Environment at Creation Time

When a lambda is created via `valk_lval_lambda()`, it captures the current environment:

```c
// src/parser.c:487
res->fun.env = env;  // Capture closure environment
```

This captured environment contains all bindings visible at the lambda's definition site. The lambda stores references to:
- `fun.env` - the captured closure environment
- `fun.formals` - parameter names
- `fun.body` - the function body AST

## 2. valk_evacuate_to_heap Preserves Lambda for Async Callbacks

When a lambda is used as an async callback (timer, HTTP handler, etc.), it must survive beyond the current checkpoint. `valk_evacuate_to_heap()` copies the lambda and its environment from scratch arena to the GC heap:

```c
// src/gc.c:2408
valk_lval_t* valk_evacuate_to_heap(valk_lval_t* v) {
  // ...copy value to heap...
  
  // If it's a function, evacuate its environment too
  if (new_val && LVAL_TYPE(new_val) == LVAL_FUN && 
      new_val->fun.builtin == nullptr && new_val->fun.env != nullptr) {
    valk_evacuate_env(&ctx, new_val->fun.env);
  }
}
```

This ensures the entire closure (lambda + captured environment) is preserved on the heap where it won't be reclaimed until the callback executes.

## 3. Function Application Uses Closure Environment as Parent

When a lambda is called, `valk_builtin_apply()` creates a new call environment with the closure's captured environment as its parent:

```c
// src/parser.c:1001-1005
valk_lenv_t* call_env = valk_lenv_empty();
if (func->fun.env) {
  call_env->parent = func->fun.env;  // Use closure env as parent
} else {
  call_env->parent = env;
}
```

This makes the captured bindings visible during function execution.

## 4. Environment Chain

The full environment chain during async callback execution:

```
call_env (local bindings from current call)
    |
    v
lambda closure env (bindings captured at definition time)
    |
    v
parent envs... (enclosing scopes at definition time)
    |
    v
prelude (standard library bindings)
    |
    v
global (top-level definitions)
```

This chain ensures that:
- Parameters and local `let` bindings are in `call_env`
- Variables from enclosing scopes (captured at definition) are in `lambda closure env`
- Standard library functions like `+`, `map`, etc. are in `prelude`
- Top-level definitions from user code are in `global`

## Example

```lisp
(def make-counter {initial}
  (let {count initial}
    (fn {} 
      (set! count (+ count 1))
      count)))

(def my-counter (make-counter 10))
(aio/schedule aio 100 my-counter)  ; Callback fires in 100ms
```

When `aio/schedule` is called:
1. `my-counter` is a lambda with `fun.env` pointing to the `let` environment containing `count`
2. `valk_evacuate_to_heap` copies both the lambda and its environment to the heap
3. After 100ms, when the callback fires, it looks up `count` through the preserved environment chain
4. The `set!` mutates `count` in the evacuated environment
