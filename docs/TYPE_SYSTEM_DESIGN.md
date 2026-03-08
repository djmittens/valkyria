# Valkyria Type System Design

## Overview

Algebraic data types (sum and product types) as first-class language constructs.
Types are declared in source, checked at load time, and erased before execution.

**Philosophy**: Types exist for correctness, not runtime overhead. After the
load phase validates that everything hooks up, the runtime operates on untyped
tagged cons cells. When a compiler arrives, types compile away entirely.

**Inspiration**: Haskell (ADTs, erasure), Scala 3 (enum, case class, named args),
Typed Racket (gradual types in a Lisp), TypeScript (structural erasure).

## Syntax

### Product Types (single constructor)

A product type has no constructor name — the type name IS the constructor.
Fields are keyword-type pairs (plist style).

```lisp
(type {Person}
  {:name Str :age Num :email Str})

; Construction — keyword (any order)
(def {p} (Person :name "Alice" :age 30 :email "a@b.com"))

; Construction — positional (declaration order)
(def {p} (Person "Alice" 30 "a@b.com"))

; Field access
(Person:name p)    ; → "Alice"
(Person:age p)     ; → 30

; Destructuring via match
(match p
  {(Person :name n :age a) (print n a)})

; Positional match
(match p
  {(Person n a e) (print n)})
```

### Sum Types (multiple constructors)

Each variant is a constructor with its own field plist.

```lisp
(type {HttpRequest}
  {Get :path Str :query Str}
  {Post :path Str :body Str}
  {Delete :path Str})

; Construction
(def {req} (Get :path "/api" :query "x=1"))
(def {req} (Post "/api" "{}"))  ; positional

; Field access (constructor-qualified)
(Get:path req)     ; → "/api"
(Get:query req)    ; → "x=1"

; Pattern matching
(match req
  {(Get :path p :query q)  (handle-get p q)}
  {(Post :path p :body b)  (handle-post p b)}
  {(Delete :path p)        (handle-delete p)})
```

### Enums (no fields)

```lisp
(type {Color}
  {Red}
  {Green}
  {Blue})

(def {c} (Red))

(match c
  {(Red)   "red"}
  {(Green) "green"}
  {(Blue)  "blue"})
```

### Parametric Types

Type parameters follow the type name in the declaration qexpr.

```lisp
(type {Option a}
  {None}
  {Some :value a})

(type {Result ok err}
  {Ok :value ok}
  {Err :error err})

(type {Pair a b}
  {:fst a :snd b})

; Usage
(def {x} (Some :value 42))    ; Option Num
(def {x} (Some 42))           ; positional — same thing
(def {y} (None))               ; Option a (polymorphic)

(def {p} (Pair :fst 1 :snd "hello"))
(def {p} (Pair 1 "hello"))    ; positional

(Pair:fst p)                   ; → 1
(Some:value x)                 ; → 42
```

### Recursive Types

```lisp
(type {List a}
  {Nil}
  {Cons :head a :tail (List a)})

(def {xs} (Cons 1 (Cons 2 (Cons 3 (Nil)))))

(fun {sum-list xs}
  {match xs
    {(Nil)                  0}
    {(Cons :head h :tail t) (+ h (sum-list t))}})
```

## Disambiguation Rules

### Keyword vs Positional Construction

The first argument after the constructor determines the mode:

- Starts with `:` keyword → keyword mode (order-independent)
- Otherwise → positional mode (declaration order)

```lisp
(Person :name "Alice" :age 30)   ; keyword — :name is first
(Person "Alice" 30)              ; positional — "Alice" is not a keyword
```

Mixing keyword and positional in a single call is an error.

### Product vs Sum Declaration

- **Product**: single qexpr after type name, starting with `:` keyword
- **Sum**: multiple qexprs after type name, each starting with a constructor name

```lisp
(type {Person}           ; product — one qexpr, starts with :name
  {:name Str :age Num})

(type {Shape}            ; sum — two qexprs, start with Circle/Rect
  {Circle :radius Num}
  {Rect :w Num :h Num})
```

### Accessor Syntax

`Constructor:field` is a single symbol parsed by the lexer. The `:` separates
constructor name from field name. Resolved at type-check time to a positional
index access.

```lisp
(Person:name p)   ; → access field :name of Person
(Get:path req)    ; → access field :path of Get variant
```

For product types, the type name is the constructor:
```lisp
(Person:name p)   ; Person is both the type and constructor
```

## Two-Pass Load Semantics

### Pass 1: Parse

Standard parsing produces AST. New syntax elements:

- `type` special form → `TYPE_DECL` AST node
- `match` special form → `MATCH` AST node
- Constructor calls → regular function calls (resolved in pass 2)
- `Constructor:field` → single symbol (resolved in pass 2)
- Keywords (`:name`) → `LVAL_SYM` starting with `:`

### Pass 2: Validate + Substitute

After parsing, before evaluation:

1. **Collect type declarations** — build type environment
   - Map type name → constructors, type params, field names/types
   - Map constructor name → type, field positions
   - Detect duplicate type/constructor names

2. **Validate constructor calls** — for each constructor invocation:
   - Verify constructor exists
   - Check field count (positional) or field names (keyword)
   - Unify type parameters across the call site
   - Report type errors with source locations

3. **Validate match expressions**
   - Verify all patterns reference valid constructors
   - Check exhaustiveness (all variants covered)
   - Bind pattern variables in branch scope
   - Verify field names in named patterns

4. **Resolve accessors** — `Person:name` → positional index lookup

5. **Substitute (erase)** — rewrite AST for execution:
   - `(type ...)` → removed (no runtime effect)
   - `(Some 42)` → `(list 'Some 42)` (tagged cons cell)
   - `(Person :name "Alice" :age 30)` → `(list 'Person "Alice" 30)`
   - `(Person:name p)` → `(nth 1 p)` (index past tag)
   - `(match ...)` → nested `if`/`cond` on `(head expr)`

## Runtime Representation

After erasure, values are regular tagged cons cells. No new lval types needed.

```
(Some 42)
→ LVAL_CONS: [sym("Some"), num(42)]

(Person "Alice" 30 "a@b.com")
→ LVAL_CONS: [sym("Person"), str("Alice"), num(30), str("a@b.com")]

(None)
→ LVAL_CONS: [sym("None")]

(Red)
→ LVAL_CONS: [sym("Red")]
```

Match desugars to tag dispatch:

```lisp
; Before (source)
(match x
  {(Some :value v) (+ v 1)}
  {(None)          0})

; After (substituted)
(if (== (head x) 'Some)
  {(do (= {v} (nth 1 x)) (+ v 1))}
  {(if (== (head x) 'None)
    {0}
    {(error "match: no pattern matched")})})
```

## Type Checking Details

### Unification with Type Parameters

```lisp
(type {Option a}
  {None}
  {Some :value a})

(fun {unwrap-or opt default}
  {match opt
    {(Some :value v) v}
    {(None) default}})
```

The type checker infers:
- `opt : Option a`
- `v : a` (from Some's field type)
- `default : a` (must match return type)
- Return type: `a`
- Therefore: `unwrap-or : Option a → a → a`

### Exhaustiveness Checking

Hard error if match doesn't cover all variants:

```lisp
(type {Color} {Red} {Green} {Blue})

(match c
  {(Red) 1}
  {(Green) 2})
; ERROR: non-exhaustive match — missing: Blue
```

Wildcard `_` catches remaining variants:

```lisp
(match c
  {(Red) 1}
  {_ 0})       ; catches Green, Blue
```

### Constructor Scoping

Constructors are module-scoped — visible in the declaring file and any file
that `(load ...)`s it. Constructors share the value namespace (they're
functions). A constructor name must be unique across all loaded types.

## LSP Integration

The LSP type checker (`lsp_types.c`, `lsp_analysis.c`) will:

1. Parse `type` declarations from source
2. Register constructor type schemes automatically:
   - `Some : ∀a. a → Option a`
   - `None : ∀a. Option a`
   - `Person : Str → Num → Str → Person`
3. Type-check constructor calls and match expressions
4. Provide completion for constructors, field names, accessors
5. Show hover info with field types
6. Diagnose non-exhaustive matches

This replaces hardcoded schemes — types are derived from source declarations.

## Implementation Plan

### Phase 1: Parser (2-3 days)
- Keywords (`:foo`) in lexer — symbols starting with `:`
- `type` special form → parse type/constructor/field declarations
- `match` special form → parse clauses with patterns
- `Constructor:field` → parse as single symbol

### Phase 2: Type Environment (2-3 days)
- `type_env_t` — registry of declared types
- Map: type name → params, constructors
- Map: constructor name → type, fields (name, type, position)
- Map: `Constructor:field` → position index
- Built during pass 2, before eval

### Phase 3: Validation (3-4 days)
- Constructor arity/field checking
- Type parameter unification at call sites
- Match exhaustiveness checking
- Accessor resolution

### Phase 4: Substitution / Erasure (2-3 days)
- Rewrite constructor calls to `list` with tag
- Rewrite accessors to `nth` with index
- Rewrite `match` to nested `if`/`cond`
- Remove `type` declarations from AST

### Phase 5: LSP Integration (2-3 days)
- Read `type` declarations from source files
- Generate constructor type schemes
- Completion for constructors, fields, accessors
- Exhaustiveness diagnostics

### Phase 6: Tests (2-3 days)
- C tests: parser, type env, validation, substitution
- Valk tests: construction, access, match, nested types, recursive types
- Error tests: bad constructor, missing field, non-exhaustive match

## Future: Compiler Erasure

When the LLVM compiler (layer 6) arrives, types erase completely:

- No tag symbols in compiled output
- Constructor calls become direct struct allocation
- `match` becomes a branch on integer tag (0, 1, 2...)
- Accessors become struct field loads (GEP)
- Product types with one field can unbox entirely
- Type parameters are phantom (zero cost)

The runtime representation section above is for the interpreter phase only.
The compiler has full type information and can optimize representations.

## Examples

### Option/Result Chaining

```lisp
(type {Option a} {None} {Some :value a})
(type {Result a e} {Ok :value a} {Err :error e})

(fun {map-option opt f}
  {match opt
    {(Some :value v) (Some (f v))}
    {(None) (None)}})

(fun {flat-map-option opt f}
  {match opt
    {(Some :value v) (f v)}
    {(None) (None)}})

(fun {option-to-result opt err}
  {match opt
    {(Some :value v) (Ok v)}
    {(None) (Err err)}})
```

### Binary Tree

```lisp
(type {Tree a}
  {Leaf}
  {Node :value a :left (Tree a) :right (Tree a)})

(fun {tree-insert tree val}
  {match tree
    {(Leaf) (Node val (Leaf) (Leaf))}
    {(Node :value v :left l :right r)
      (if (< val v)
        {(Node v (tree-insert l val) r)}
        {(Node v l (tree-insert r val))})}})

(fun {tree-sum tree}
  {match tree
    {(Leaf) 0}
    {(Node :value v :left l :right r)
      (+ v (tree-sum l) (tree-sum r))}})
```

### HTTP Router

```lisp
(type {Route}
  {Static :path Str :handler Fun}
  {Param :prefix Str :param-name Str :handler Fun}
  {NotFound})

(type {Response}
  {:status Num :body Str :headers (List (Pair Str Str))})

(fun {route-match route path}
  {match route
    {(Static :path p :handler h)
      (if (== p path)
        {(Some h)}
        {(None)})}
    {(Param :prefix pfx :param-name _ :handler h)
      (if (str/starts-with path pfx)
        {(Some (h (str/drop (len pfx) path)))}
        {(None)})}
    {(NotFound) (None)}})
```
