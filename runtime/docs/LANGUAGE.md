# Valkyria Language Reference

This document describes the Valkyria programming language - its features, semantics, and syntax.

## Overview

Valkyria is a Lisp dialect with:
- S-expression syntax
- Lexical scoping with dynamic fallback
- First-class functions and closures
- Async I/O with composable handles and combinators
- Built-in HTTP/2 networking
- Garbage collection
- Macros and a module system
- Optional LLVM AOT/JIT compilation

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
(mod 10 3)      ; 1 - modulo; note `%` is not a valid token
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
(len "hello")               ; 5
(str "a" "b")               ; "ab" - concatenate
(str/join list sep)         ; Join with separator (list first)
(str/split s sep)           ; Split into list
(str/slice s start end)     ; Substring
(str/upper s)  (str/lower s)
(str/trim s)   (str/trim-left s)  (str/trim-right s)
(str/replace s from to)
(str/index-of s needle)     (str/last-index-of s needle)
(str/starts-with? s p)      (str/ends-with? s p)     (str/contains? s sub)
(str->num s)                ; Parse number
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

Predicates return `1`/`()` for true/false:

```lisp
(num? x)   (str? x)   (list? x)   (fun? x)   (sym? x)   (dict? x)
(ref? x)   (quoted? x)
(error? x)             ; Check if error
(nil? x)               ; Check if nil
```

`type` is not a runtime inspector — it is the (unimplemented) type
*declaration* form and evaluates to nil. See [TYPE_SYSTEM_DESIGN.md](TYPE_SYSTEM_DESIGN.md).

## Async Programming

Async work runs on an AIO system created with `(aio/start)`. Callbacks are
continuation-passing; combinators build graphs of async handles.

```lisp
(def {aio} (aio/await (aio/start)))

(aio/then (aio/sleep aio 100) (\ {_} {
  (print "slept")
}))

(aio/run aio)
```

### Core Combinators

```lisp
(aio/pure v)              ; Immediately-resolved handle
(aio/then h f)            ; Continue with f when h resolves
(aio/await h)             ; Block until resolved (main thread only)
(aio/all handles)         ; Wait for all
(aio/race handles)        ; First to resolve wins
(aio/any handles)         ; First success
(aio/within ms h)         ; Timeout
(aio/retry ...)           ; Retry on failure
(aio/catch h f)           ; Handle errors
(aio/finally h f)         ; Always run
(aio/cancel h)            ; Cancel
```

### Sequencing Sugar

```lisp
(aio/do ...)              ; Sequential async block
(aio/let {...} ...)       ; Bind async results in sequence
```

### Monadic Layer

`stdlib/aio/monadic.valk` adds a pure monadic interface:

```lisp
(async/pure v)
(async/bind op f)
(async/map-list f xs)
(async/collect ops)
(async/sequence ops)
(async/try op)            ; -> (list "ok" v) | (list "error" e)
(async/recover op fallback)
```

There is no `shift`/`reset` operator. Delimited continuations exist only as an
internal evaluator mechanism, not as a user-facing form.

## HTTP/2 Networking

### Creating Requests

```lisp
(def {req} (http2/request "GET" "https" "example.com" "/"))
(http2/request-add-header req "authorization" "Bearer token")
```

### High-Level API

```lisp
(load "stdlib/http/api.valk")

(def {aio} (aio/await (aio/start)))

; Fetch takes aio, host, port, path - not a URL
(aio/then (http2/client-request aio "example.com" 443 "/") (\ {resp} {
  (print (http2/response-status resp))   ; "200" (a string)
  (print (http2/response-body resp))
}))

; Async helpers from the high-level layer
(http2/fetch aio "example.com" 443 "/")        ; Async Response
(http2/fetch-text aio "example.com" 443 "/")   ; Async body
(http2/response-ok? resp)                      ; true when 2xx
```

### Middleware

```lisp
(def {auth} (http2/with-auth "Bearer token"))
(def {ua} (http2/with-user-agent "MyApp/1.0"))
(def {middleware} (http2/compose-middleware (list auth ua)))
(def {req} (middleware (http2/get "api.example.com")))
```

See [HTTP_API.md](HTTP_API.md) for the full surface.

## Standard Library (Prelude)

The prelude (`stdlib/prelude.valk`) provides common utilities:

### Higher-Order Functions

```lisp
(map f list)            ; Apply f to each element
(filter pred list)      ; Keep elements where pred is true
(foldl f init list)     ; Left fold (there is no foldr)
```

### List Utilities

```lisp
(last list)             ; Last element
(init list)             ; All but last
(take n list)           ; First n elements
(drop n list)           ; Remove first n elements
(reverse list)          ; Reverse list
(exists pred list)      ; Any element matches pred?
(flatten list)          ; Flatten one level
(sum list)              ; Sum of elements
(product list)          ; Product of elements
```

Use `head`/`tail` for the first element and remainder; there are no `first`/`rest`
aliases.

### Function Utilities

```lisp
(comp f g)              ; Function composition
(flip f)                ; Swap first two arguments
(uncurry f)             ; Convert to list-taking form
(id x)                  ; Identity
```

### Positional List Accessors

`fst`/`snd`/`trd` index a **list** (1st, 2nd, 3rd element) — they are not pair
accessors:

```lisp
(fst {7 8 9})   ; 7
(snd {7 8 9})   ; 8
(trd {7 8 9})   ; 9
```

### Pairs, Options, Results

`pair` builds a tagged struct, accessed with the `pair/` helpers:

```lisp
(pair 1 2)              ; {Pair 1 2}
(pair/map-fst p f)      (pair/map-snd p f)      (pair/bimap p f g)

Options and Results are tagged values built with constructors:

```lisp
(Some 5)                ; {Option::Some 5}
(None)                  ; {Option::None}
(Ok 1)                  ; {Result::Ok 1}
(Err "boom")            ; {Result::Err boom}

(some? (Some 5))                      ; 1
(none? (None))                        ; 1
(option/unwrap-or (Some 5) 99)        ; 5
(option/unwrap-or (None) 99)          ; 99
(option/map (Some 5) (\ {v} {* v 2})) ; {Option::Some 10}
(option/from-nullable nil)            ; {Option::None}
(option/flat-map o f)  (option/or a b)  (option/filter o pred)
(option/to-result o)   (option/sequence os)  (option/traverse xs f)

(ok? (Ok 1))                          ; 1
(err? (Err "e"))                      ; 1
(result/unwrap-or (Err "e") 0)        ; 0
(result/map r f)       (result/flat-map r f)   (result/map-err r f)
(result/or a b)        (result/to-option r)
```

Deconstruct with `match`:

```lisp
(match opt
  {(Some :value v) v}
  {(None) "empty"})
```

### Control Flow

```lisp
; case - match a value against literals, `_` is the catch-all
(case 2 {1 "one"} {2 "two"} {_ "other"})        ; "two"

; select - first clause whose condition is truthy
(select {(> 1 2) "a"} {(< 1 2) "b"})            ; "b"

; match - destructure tagged constructors
(match (pair 1 2) {(Pair :fst a :snd b) (+ a b)} {_ 0})   ; 3
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

Currently dynamically typed. `sig` declarations exist in the prelude but are not
enforced. Algebraic data types are designed but unimplemented — see
[TYPE_SYSTEM_DESIGN.md](TYPE_SYSTEM_DESIGN.md).

### Pattern Matching

`case` matches literals, `select` picks the first truthy clause, and `match`
destructures tagged constructors (`Some`, `Ok`, `Pair`, ...). Richer patterns
(nested, guards, exhaustiveness checking) are not implemented.

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
(load "stdlib/http/api.valk")

(def {aio} (aio/await (aio/start)))

(aio/then (http2/client-request aio "api.example.com" 443 "/data") (\ {resp} {
  (if (error? resp)
    {(print "Service unavailable")}
    {(print (http2/response-body resp))})
}))

(aio/run aio)
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

- [CONTRIBUTING.md](../../docs/CONTRIBUTING.md) - Development guide
- [ROADMAP.md](../../docs/ROADMAP.md) - Project roadmap
- [HTTP_API.md](HTTP_API.md) - HTTP/2 API reference
- [TYPE_SYSTEM_DESIGN.md](TYPE_SYSTEM_DESIGN.md) - Planned algebraic data types
- `stdlib/prelude.valk` - Standard library source
- `stdlib/http/api.valk` - HTTP API source
