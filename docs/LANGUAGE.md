# Valkyria Language Reference

This document describes the Valkyria programming language - its features, semantics, and syntax.

## Overview

Valkyria is a Lisp dialect with:
- S-expression syntax
- Lexical scoping with dynamic fallback
- First-class functions and closures
- Delimited continuations (shift/reset)
- Built-in HTTP/2 networking
- Garbage collection

## Syntax

### Basic Types

```lisp
; Numbers
42
-17
3.14

; Strings
"hello world"
"with \"escapes\""

; Symbols
foo
my-variable
namespace/function

; Lists (S-expressions) - evaluated as function calls
(+ 1 2)
(print "hello")

; Quoted expressions (Q-expressions) - data, not evaluated
{1 2 3}
{+ 1 2}
```

### Comments

```lisp
; Single line comment
```

### Quoting

Q-expressions `{...}` prevent evaluation. This is used for:
- Data that shouldn't be executed
- Delayed evaluation (macros, conditionals)
- List literals

```lisp
{1 2 3}           ; A list containing 1, 2, 3
(eval {+ 1 2})    ; Evaluates to 3
(head {a b c})    ; Returns a
```

## Core Forms

### def - Global Definition

```lisp
(def {x} 42)           ; Define x as 42
(def {a b} 1 2)        ; Define a=1, b=2
```

### = - Local Assignment

```lisp
(= {x} 42)             ; Assign x in current scope
```

### \ - Lambda

```lisp
(\ {x} {(* x x)})                    ; Anonymous function
(\ {x y} {(+ x y)})                  ; Multiple parameters
(\ {x & rest} {(print x rest)})      ; Variadic with &
```

### fun - Named Function Definition

```lisp
(fun {square x} {(* x x)})           ; Define named function
(fun {add x y} {(+ x y)})
(fun {greet & names} {               ; Variadic function
  (map print names)
})
```

### if - Conditional

```lisp
(if (> x 0)
  {"positive"}
  {"non-positive"})
```

### do - Sequential Execution

```lisp
(do
  (print "first")
  (print "second")
  (+ 1 2))              ; Returns 3 (last expression)
```

### let - Local Bindings

```lisp
(let {x 10 y 20}
  {(+ x y)})            ; Returns 30
```

## Built-in Functions

### Arithmetic

```lisp
(+ 1 2 3)       ; 6
(- 10 3)        ; 7
(* 2 3 4)       ; 24
(/ 10 2)        ; 5
(% 10 3)        ; 1 (modulo)
```

### Comparison

```lisp
(== 1 1)        ; 1 (true)
(!= 1 2)        ; 1 (true)
(< 1 2)         ; 1 (true)
(> 2 1)         ; 1 (true)
(<= 1 1)        ; 1 (true)
(>= 2 1)        ; 1 (true)
```

### Logic

```lisp
(and 1 1)       ; 1
(or 0 1)        ; 1
(not 0)         ; 1
```

### List Operations

```lisp
(list 1 2 3)           ; Create list {1 2 3}
(head {1 2 3})         ; 1
(tail {1 2 3})         ; {2 3}
(join {1 2} {3 4})     ; {1 2 3 4}
(len {1 2 3})          ; 3
(cons 0 {1 2 3})       ; {0 1 2 3}
(nth 1 {a b c})        ; b (0-indexed)
```

### String Operations

```lisp
(len "hello")          ; 5
(join-str "a" "b")     ; "ab"
```

### I/O

```lisp
(print "hello")        ; Print with newline
(printf "%d" 42)       ; Formatted print (no newline)
(read-file "path")     ; Read file contents
```

### Control Flow

```lisp
(if cond {then} {else})
(do expr1 expr2 ...)
(eval {quoted expr})
```

### Type Checking

```lisp
(type x)               ; Returns type as string
(error? x)             ; Check if error
(nil? x)               ; Check if nil
```

## Delimited Continuations

Valkyria supports shift/reset style delimited continuations for advanced control flow.

### async-reset - Establish Delimiter

```lisp
(async-reset
  (print "before")
  (async-shift k
    (print "captured continuation")
    (k 42))             ; Resume with value 42
  (print "after"))
```

### async-shift - Capture Continuation

Within an `async-reset`, `async-shift` captures the continuation up to the delimiter:

```lisp
(async-reset
  (+ 1 (async-shift k
         (k (k 5)))))   ; Returns 7: (+ 1 (+ 1 5))
```

### Async/Await Pattern

Continuations enable async/await style programming:

```lisp
(async-reset
  (= {response} (await (fetch "example.com")))
  (print (response-body response)))
```

## HTTP/2 Networking

### Creating Requests

```lisp
(def {req} (http2/request "GET" "https" "example.com" "/"))
(http2/request-add-header req "authorization" "Bearer token")
```

### High-Level API

```lisp
(load "src/http_api.valk")

; Simple GET
(def {resp} (fetch-sync "example.com"))

; POST with body
(def {req} (http-post "api.example.com" "{\"name\":\"Alice\"}"))

; Add headers
(def {req2} (with-header req "content-type" "application/json"))

; Response handling
(response-status resp)    ; 200
(response-body resp)      ; "..."
(response-ok resp)        ; 1 if 2xx status
```

### Middleware

```lisp
(def {auth} (with-auth "Bearer token"))
(def {ua} (with-user-agent "MyApp/1.0"))
(def {middleware} (compose-middleware (list auth ua)))
(def {req} (middleware (http-get "api.example.com")))
```

## Standard Library (Prelude)

The prelude (`src/prelude.valk`) provides common utilities:

### Higher-Order Functions

```lisp
(map f list)            ; Apply f to each element
(filter pred list)      ; Keep elements where pred is true
(foldl f init list)     ; Left fold
(foldr f init list)     ; Right fold
```

### List Utilities

```lisp
(first list)            ; Alias for head
(rest list)             ; Alias for tail
(last list)             ; Last element
(init list)             ; All but last
(take n list)           ; First n elements
(drop n list)           ; Remove first n elements
(reverse list)          ; Reverse list
(exists pred list)      ; Any element matches pred?
```

### Function Utilities

```lisp
(curry f x)             ; Partial application
(flip f)                ; Swap first two arguments
(compose f g)           ; Function composition
```

### Control Flow

```lisp
(case val clauses...)   ; Pattern matching
(select pairs...)       ; Conditional selection
```

## Memory Model

Valkyria uses a hybrid memory management approach:

- **GC Heap**: Mark-and-sweep garbage collector for persistent values (environments, definitions)
- **Scratch Arena**: Bump allocator for temporary values during REPL evaluation, reset after each expression
- **Slab Allocator**: Fixed-size blocks for concurrency structures (futures, promises)

**How it works in the REPL:**
1. Parsing and evaluation happen in the scratch arena (fast bump allocation)
2. Values that "escape" (stored in env, captured by closures) are marked with `LVAL_FLAG_ESCAPES`
3. `valk_intern()` copies escaping values from scratch to GC heap with forwarding pointers
4. After each expression, scratch arena is reset (all temporaries freed instantly)
5. GC runs at safe points between expressions (never during evaluation)

**In script mode:** Everything goes directly to GC heap (no scratch arena optimization).

**Note:** Escape analysis is partially implemented. Basic escape marking works, but automatic promotion on function return is not yet complete (see `test_escape.c` for status).

## Scoping Rules

Valkyria uses lexical scoping with dynamic fallback:

1. **Lexical scope**: Variables bound in the enclosing function
2. **Parent chain**: Follow parent environment links
3. **Dynamic fallback**: If not found lexically, check caller's scope

This allows closures to capture their definition environment while still allowing flexible access patterns.

## Known Limitations

### No Tail Call Optimization (TCO)

The tree-walking interpreter doesn't implement TCO. Deep recursion will use stack space proportional to depth. This will be addressed with the LLVM backend.

### Type System

Currently dynamically typed. A gradual type system is planned for future phases.

### Pattern Matching

Only basic `case`/`select` matching. Full pattern matching is planned.

## Examples

### Factorial

```lisp
(fun {factorial n}
  {if (<= n 1)
    {1}
    {(* n (factorial (- n 1)))}})

(factorial 5)  ; 120
```

### Map Implementation

```lisp
(fun {map f lst}
  {if (nil? lst)
    {()}
    {(cons (f (head lst)) (map f (tail lst)))}})
```

### HTTP Request with Error Handling

```lisp
(load "src/http_api.valk")

(def {result} (run-async
  (async-or-default
    (fetch-text "api.example.com/data")
    "Service unavailable")))

(print result)
```

### Fibonacci

```lisp
(fun {fib n}
  {if (< n 2)
    {n}
    {(+ (fib (- n 1)) (fib (- n 2)))}})
```

Note: This is naive recursive Fibonacci (O(2^n)). Memoization would require a hash table or similar data structure not yet implemented.

## See Also

- [CONTRIBUTING.md](CONTRIBUTING.md) - Development guide
- [ROADMAP.md](ROADMAP.md) - Project roadmap
- `src/prelude.valk` - Standard library source
- `src/http_api.valk` - HTTP API source
