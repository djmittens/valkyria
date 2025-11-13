# Valkyria Architecture Overview

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    REPL / Main Entry Point                       │
│                       (src/repl.c)                               │
└─────────────────────────────────────────────────────────────────┘
                                 │
                    ┌────────────┴────────────┐
                    ▼                         ▼
          ┌──────────────────┐       ┌──────────────────┐
          │ Global Arena     │       │ Scratch Arena    │
          │ (16 MiB)         │       │ (4 MiB)          │
          │ Persistent       │       │ Ephemeral        │
          └──────────────────┘       └──────────────────┘
                    │                         │
                    └────────────┬────────────┘
                                 ▼
          ┌─────────────────────────────────────────┐
          │   Parser & Evaluator (src/parser.c)     │
          │  - Read: Tokenize → AST construction    │
          │  - Eval: Tree-walking interpreter       │
          │  - 35+ builtins (math, list, I/O)       │
          └─────────────────────────────────────────┘
                                 │
                    ┌────────────┴────────────┐
                    ▼                         ▼
          ┌──────────────────┐       ┌──────────────────┐
          │  GC Heap         │       │ Environments     │
          │ (Mark & Sweep)   │       │ (Symbol Table)   │
          │  Phase 5         │       │ (Lexical Scopes) │
          └──────────────────┘       └──────────────────┘
                    │                         │
                    └────────────┬────────────┘
                                 ▼
          ┌─────────────────────────────────────────┐
          │      Value System (src/parser.h)        │
          │  - Type: valk_lval_t (tagged union)     │
          │  - 11 types: NUM, SYM, STR, FUN, etc.   │
          │  - Bit-packed flags (GC, frozen, etc.)  │
          └─────────────────────────────────────────┘
                                 │
              ┌──────────────────┼──────────────────┐
              ▼                  ▼                  ▼
    ┌──────────────────┐ ┌──────────────────┐ ┌──────────────┐
    │  Concurrency     │ │  HTTP/2 Support  │ │   VM Frame   │
    │  (Futures/Pool)  │ │  (Networking)    │ │  (Scaffolding)│
    │  src/concurrency │ │  src/aio_uv.c    │ │  src/vm.c    │
    └──────────────────┘ └──────────────────┘ └──────────────┘
            │                    │
            ▼                    ▼
    ┌──────────────────┐ ┌──────────────────┐
    │ Worker Pool      │ │ libuv Event Loop │
    │ Task Queue       │ │ TLS/OpenSSL      │
    │ (Thread Pool)    │ │ nghttp2 Protocol │
    └──────────────────┘ └──────────────────┘
```

## Memory Architecture

### Three-Tier Allocator System

```
┌─────────────────────────────────────────────────────────┐
│              Thread-Local Context                       │
│  (valk_thread_ctx.allocator points to one of:)         │
└─────────────────────────────────────────────────────────┘
                        │
        ┌───────────────┼───────────────┐
        ▼               ▼               ▼
   ┌─────────┐   ┌─────────┐   ┌─────────────┐
   │  SCRATCH│   │ GLOBAL  │   │    HEAP     │
   │  ARENA  │   │ ARENA   │   │ GC Malloc   │
   └─────────┘   └─────────┘   └─────────────┘
   4 MiB          16 MiB        Dynamic
   Bump-Ptr       Bump-Ptr      Mark/Sweep
   
   Ephemeral     Persistent     Persistent
   Eval temps    Functions      GC'ed values
   Reset/iter    Definitions    Slab-based
```

### Value Lifecycle

```
1. Parse → Scratch Arena (temporary)
   - VALK_WITH_ALLOC(scratch)
   - Fast O(1) bump-pointer allocation
   - Non-escaping values stay here

2. Escape Analysis
   - Value stored in env? → Mark ESCAPES
   - Captured by lambda? → Mark ESCAPES
   - Returned from function? → Mark ESCAPES
   - Otherwise → remains in scratch

3. Non-Escaping Values
   - Scratch reset after REPL iteration
   - O(1) cleanup (just reset pointer)
   - No GC overhead

4. Escaping Values
   - Promoted to GC heap
   - Forwarding pointer created
   - GC manages collection
   - Mark & sweep when threshold exceeded

5. GC Collection (Safepoint-Based)
   - Between REPL expressions only
   - Mark live objects from root env
   - Sweep dead objects
   - Return to free list
```

## Execution Flow

### REPL Iteration

```
User Input
    │
    ▼
┌──────────────────────────┐
│ Allocate → scratch arena │
└──────────────────────────┘
    │
    ▼
┌──────────────────────────┐
│ Parse S-expression       │
│ (Read phase)             │
└──────────────────────────┘
    │
    ▼
┌──────────────────────────┐
│ Evaluate AST             │
│ (Eval phase via          │
│  valk_lval_eval)         │
└──────────────────────────┘
    │
    ▼
┌──────────────────────────┐
│ Print result             │
│ (Print phase)            │
└──────────────────────────┘
    │
    ▼
┌──────────────────────────┐
│ Reset scratch arena      │
│ (O(1) operation)         │
└──────────────────────────┘
    │
    ▼
┌──────────────────────────┐
│ Check GC threshold       │
│ if allocated > threshold │
│   → Mark & Sweep         │
└──────────────────────────┘
    │
    ▼
Next iteration or exit
```

### Evaluation (Tree-Walking)

```
valk_lval_eval(env, expr)
    │
    ├─ If NUMBER → return (no eval)
    ├─ If SYMBOL → valk_lenv_get(env, sym)
    ├─ If QEXPR → return unevaluated
    │
    └─ If SEXPR → valk_lval_eval_sexpr
         │
         ├─ Get function (first element)
         ├─ Evaluate arguments (rest of list)
         │
         └─ Call function:
            ├─ If builtin → Call C function
            ├─ If lambda → Create closure env, eval body
            └─ If special form → Handle specially (if, def, etc.)
```

## Type System

### Tagged Union Design

```c
struct valk_lval_t {
  uint64_t flags;              // 64-bit flag word
  void *origin_allocator;      // Allocator that created this
  valk_lval_t *gc_next;       // GC linked list
  
  union {
    struct { ... } fun;        // Function (lambda/builtin)
    struct { ... } cons;       // Cons cell (head/tail)
    struct { ... } ref;        // External reference
    long num;                  // Number
    char *str;                 // String/symbol
  };
}
```

### Flag Bit Layout

```
Bits  0-7:   Type (LVAL_NUM, LVAL_SYM, etc.)
Bits  8-9:   Allocation source (SCRATCH, GLOBAL, HEAP)
Bit  10:     GC mark (used during collection)
Bit  11:     Frozen (immutable)
Bit  12:     Escapes (outlives current scope)
Bit  13:     Forwarded (pointer forwarding for promotion)
Bits 14-63:  Reserved
```

### Type Coverage

```
Primitive Types:
  - NUM: Long integer
  - SYM: Symbol (interned string)
  - STR: String
  - ERR: Error value

Collection Types:
  - CONS: Cons cell (head/tail)
  - SEXPR: S-expression (cell list)
  - QEXPR: Quoted expression (unevaluated)
  - NIL: Empty list

Function Types:
  - FUN: Lambda or builtin function
  - ENV: Environment (symbol table)

Reference Types:
  - REF: Opaque external reference
```

## Concurrency Model

### Futures & Promises

```
┌─────────────────────────┐
│   Application Thread    │
└─────────────────────────┘
         │
         ├──→ valk_schedule(pool, arg, func)
         │    Creates future
         │
         └──→ valk_future_await(future)
              Blocks until result available
              │
              └──→ Returns valk_arc_box (result or error)

┌─────────────────────────────────────────┐
│         Worker Pool (4 default)         │
│  ┌──────────────┐   ┌──────────────┐   │
│  │   Worker 1   │   │   Worker 2   │   │
│  │   Process    │   │   Process    │   │
│  │   tasks      │   │   tasks      │   │
│  └──────────────┘   └──────────────┘   │
│  ┌──────────────┐   ┌──────────────┐   │
│  │   Worker 3   │   │   Worker 4   │   │
│  │   Process    │   │   Process    │   │
│  │   tasks      │   │   tasks      │   │
│  └──────────────┘   └──────────────┘   │
│         ↑                    ↑          │
│    Shared task queue (ring buffer)     │
└─────────────────────────────────────────┘
```

### Reference Counting for Concurrency

```
Single-threaded (stack values):
  valk_retain(ref)       // Increment refcount
  valk_release(ref)      // Decrement, free if 0

Concurrent (arc_box):
  valk_arc_retain(ref)   // Atomic increment
  valk_arc_release(ref)  // Atomic decrement, free if 0
  
  Uses: __atomic_fetch_add/sub for thread-safe ops
```

## HTTP/2 Architecture

### Request/Response Flow

```
Lisp Code:
  (http2/listen "localhost" 8080 cert.pem key.pem handler)
  (http2/connect "google.com" 443 ca-bundle.pem)
  (http2/request "GET" "https://google.com/")
  (http2/send request client)
  (await future-of-response)
  
    ↓
    
C Implementation:
  
valk_aio_system_t (manages event loop)
    ↓
    ├─ valk_aio_http_server (listening server)
    │  └─ Accepts connections → valk_aio_http_conn
    │
    └─ valk_aio_http2_client (client connections)
       └─ Sends requests → returns future
       
valk_http2_request_t (request structure)
  - method, scheme, authority, path
  - headers (array)
  - body (buffer)
  
valk_http2_response_t (response structure)
  - stream_id
  - status code
  - headers (array)
  - body (buffer)
  - promise (resolves when complete)
```

### TLS/SSL Integration

```
OpenSSL Context
    ↓
ALPN negotiation (HTTP/2)
    ↓
nghttp2 Session
    ↓
Stream management (multiplexing)
    ↓
Frames (headers, data, settings, etc.)
```

## Module Dependencies

```
repl.c (main entry)
  ├─ parser.h (evaluator)
  ├─ memory.h (allocators)
  ├─ gc.h (garbage collection)
  ├─ aio.h (networking)
  └─ concurrency.h (async primitives)

parser.c (evaluator)
  ├─ memory.h (allocation)
  ├─ gc.h (GC heap)
  ├─ concurrency.h (await builtin)
  ├─ aio.h (HTTP/2 builtins)
  └─ collections.h (internal utilities)

aio_uv.c (HTTP/2 implementation)
  ├─ libuv (event loop)
  ├─ nghttp2 (HTTP/2 protocol)
  ├─ OpenSSL (TLS)
  ├─ aio_ssl.c (certificate handling)
  └─ concurrency.h (futures/promises)

gc.c (garbage collector)
  ├─ memory.h (underlying allocators)
  └─ parser.h (value marking)
```

## Performance Characteristics

### Time Complexity

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Allocate (Scratch) | O(1) | Bump pointer |
| Allocate (Slab) | O(1) | Lock-free freelist |
| Allocate (GC Heap) | O(1) | Linked list prepend |
| GC Mark | O(n) | n = reachable objects |
| GC Sweep | O(m) | m = all objects |
| Symbol lookup | O(d) | d = scope depth |
| List access (cons) | O(n) | n = position |
| Function call | O(d) | d = scope depth + eval |

### Space Efficiency

```
Scratch Arena:
- No per-allocation overhead
- Just pointer and size
- Reset frees all at once

GC Heap:
- Header: 24 bytes (allocator ptr, next ptr, size)
- User data: variable
- Slab allocation for lval_t (fast path)

Slab Allocator:
- Header: 8 bytes per item (handle + next)
- User data: variable
- Lock-free freelist

Reference Counting:
- Overhead: 8 bytes per ref (refcount field)
```

## Escape Analysis in Practice

```
Example 1: Non-escaping (scratch)
  (+ 1 2)
  → Both 1 and 2 are scratch
  → Result (3) is scratch
  → All freed when iteration resets

Example 2: Escaping (GC heap)
  (def x 42)
  → Symbol 'x' escapes (stored in env)
  → Number 42 escapes (value in env)
  → Must be GC heap
  → Available for next iteration

Example 3: Lambda capturing (GC heap)
  (def add-x (\ {y} {+ x y}))
  → 'x' referenced in body
  → Body captures 'x'
  → Must be GC heap
  → Closure created with captured env
```

## Testing Strategy

### C Tests (Unit Level)

```
test_std.c
  - Parsing tests
  - Evaluation tests
  - Builtin tests

test_memory.c
  - Arena allocation
  - Slab allocation
  - Reference counting

test_concurrency.c
  - Task queue
  - Worker pool
  - Synchronization

test_freeze.c
  - Immutability enforcement
  - Recursive freezing

test_escape.c
  - Escape analysis correctness
  - Environment capture
  - Lambda closures

test_networking.c
  - Socket operations
  - TCP connectivity

test_networking_lisp.c
  - HTTP/2 integration
  - E2E server/client
```

### Lisp Tests (Integration Level)

```
test_prelude.valk
  - Standard library functions
  - List operations
  - Control flow

test_gc.valk
  - GC triggering
  - Collection metrics

google_http2.valk
  - Real-world API (Google)
  - TLS connectivity

http2_server_client.valk
  - E2E HTTP/2
  - Server and client
```

## Known Limitations & Future Work

### Current Limitations

1. **No Bytecode Compilation**
   - Tree-walking interpreter (slower than bytecode)
   - VM scaffolding exists for future implementation
   - Performance impact: ~2-5x slower than bytecode would be

2. **No Connection Pooling**
   - Creates new HTTP/2 connection per request
   - Could be optimized with connection reuse
   - Impact: Higher latency for sequential requests

3. **No String Manipulation**
   - Substring, contains, split functions missing
   - Workaround: Build in Lisp with existing ops

4. **Partial Application Buggy**
   - Function currying not fully working
   - Noted in prelude.valk comments

5. **Platform-Specific**
   - pthread hardcoded (no abstraction)
   - libuv for async (no pluggable backends)

### Future Improvements

1. **Bytecode VM** (High Priority)
   - Compile AST → bytecode
   - Stack-based or register-based VM
   - Major performance gain

2. **Connection Pooling**
   - Reuse HTTP/2 connections
   - Session management
   - Performance improvement

3. **Module System**
   - Framework exists, needs completion
   - Namespace isolation
   - Package management

4. **String Operations**
   - substring, contains, split
   - Pattern matching
   - Regular expressions

5. **Error Handling**
   - Try/catch mechanism
   - Better error messages
   - Stack traces

## Getting Started for Development

### Key Entry Points

1. **For Language Semantics**
   - src/prelude.valk: Standard library
   - src/parser.c:valk_lval_eval(): Core evaluator

2. **For Memory System**
   - src/memory.c: Allocators
   - src/gc.c: Garbage collection
   - src/parser.c: Escape analysis

3. **For Networking**
   - src/aio_uv.c: Main implementation
   - src/aio_ssl.c: TLS handling
   - src/parser.c: Lisp builtins

4. **For Testing**
   - test/testing.{c,h}: Test framework
   - test/test_std.c: Example C tests
   - test/test_prelude.valk: Example Lisp tests

### Build & Debug

```bash
# Initial setup
make configure       # Install dependencies

# Build
make build          # Debug build with symbols

# Test
make test          # Run all tests
make asan          # AddressSanitizer

# Debug
lldb build/valk   # Debug REPL
make lint          # Static analysis
```

---

This architecture design prioritizes:
- **Efficiency**: Multi-level allocators, escape analysis, safepoint GC
- **Simplicity**: Tree-walking interpreter (no bytecode complexity)
- **Concurrency**: Futures/promises, lock-free structures
- **Safety**: Comprehensive GC, immutability support, reference counting
