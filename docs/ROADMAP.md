# Valkyria Tech Tree

A dependency-based roadmap for the Valkyria language. Features are organized as a tech tree - unlocking one enables others.

## Legend

```
[###] = Unlocked (complete)     Cost: S = Small (1-3 days)
[## ] = Partial (in progress)   Cost: M = Medium (1-2 weeks)
[#  ] = Started (scaffolded)    Cost: L = Large (2-4 weeks)
[   ] = Locked (not started)    Cost: XL = Extra Large (1+ month)
```

---

## Tech Tree Visualization

```
                              ┌─────────────────────────────────────────────────────────────┐
                              │                      VALKYRIA TECH TREE                     │
                              └─────────────────────────────────────────────────────────────┘

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 0: FOUNDATIONS
═══════════════════════════════════════════════════════════════════════════════════════════════

  [###] Parser ──────┬──────> [###] S-Expressions ────> [###] Q-Expressions (quoting)
        (2.9k LOC)   │              (lists as code)           (lists as data)
                     │
                     ├──────> [###] Numbers ───────────> [   ] Rationals ──────> [   ] BigNums
                     │              (long/double)              (S)                    (M)
                     │
                     ├──────> [###] Strings ───────────> [   ] Unicode ────────> [   ] Regex
                     │              (C strings)                (M)                    (M)
                     │
                     └──────> [###] Symbols ───────────> [## ] Namespaces ─────> [   ] Modules
                                    (identifiers)              (S)                    (M)

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 1: EVALUATION
═══════════════════════════════════════════════════════════════════════════════════════════════

  [###] Tree-Walker ─┬──────> [###] Environments ─────> [###] Closures ────────> [###] Lexical Scope
        (eval loop)  │              (symbol tables)           (captured env)           (parent chain)
                     │
                     ├──────> [###] Builtins ─────────> [###] Varargs ─────────> [###] & rest params
                     │              (40+ C fns)               (variable args)          (collect rest)
                     │
                     └──────> [###] Lambda (\\) ───────> [###] fun macro ───────> [## ] Macros
                                    (anonymous fn)            (named fns)              (hygiene: M)

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 2: MEMORY
═══════════════════════════════════════════════════════════════════════════════════════════════

  [###] Allocators ──┬──────> [###] Arena ────────────> [###] Scratch Arena ───> [###] Reset per expr
        (636 LOC)    │              (bump alloc)              (REPL only)              (after each expr)
                     │
                     ├──────> [###] Slab ─────────────> [###] Lock-free Freelist
                     │              (fixed blocks)            (Treiber stack)
                     │
                     └──────> [###] GC Heap ──────────> [###] Mark & Sweep ────> [   ] Generational
                                    (643 LOC)                 (stop-world)             (L)
                                          │
                                          └─────────────> [## ] Escape Analysis ──> [## ] Intern to Heap
                                                                (marking works)            (partial: S)

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 3: CONTROL FLOW
═══════════════════════════════════════════════════════════════════════════════════════════════

  [###] if/do ───────┬──────> [###] Recursion ────────> [   ] TCO ─────────────────────────────┐
        (builtins)   │              (works)                   (BLOCKED - needs Stack Machine)  │
                     │                                                                          │
                     ├──────> [###] Continuations ────> [###] shift/reset ─────> [###] Async/Await
                     │              (LVAL_CONT)               (delimited)              (patterns)
                     │
                     └──────> [###] Error Handling ───> [   ] Conditions ──────> [   ] Restarts
                                    (LVAL_ERR)                (M)                      (L)

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 4: CONCURRENCY
═══════════════════════════════════════════════════════════════════════════════════════════════

  [###] Threads ─────┬──────> [###] Work Queue ───────> [###] Worker Pool ─────> [   ] Work Stealing
        (pthreads)   │              (job dispatch)            (4 workers)              (M)
                     │
                     ├──────> [###] Futures ──────────> [###] Promises ────────> [###] Await/Timeout
                     │              (async result)            (completion)             (valk_future_await_timeout)
                     │
                     ├──────> [###] ARC Boxes ────────> [###] Atomic Refcount
                     │              (thread-safe)             (arc_retain/release)
                     │
                     └──────> [   ] Channels ─────────> [   ] Actors ──────────> [   ] STM
                                    (M)                       (L)                      (XL)

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 5: I/O & NETWORKING
═══════════════════════════════════════════════════════════════════════════════════════════════

  [###] libuv ───────┬──────> [###] Event Loop ───────> [###] Async Callbacks
        (backend)    │              (uv_run)                  (non-blocking)
                     │
                     ├──────> [###] TLS/SSL ──────────> [###] Certificates
                     │              (OpenSSL)                 (test certs in build/)
                     │
                     ├──────> [###] HTTP/2 Client ────> [###] Request/Response ──> [###] High-Level API
                     │              (nghttp2)                 (objects)                  (40+ fns)
                     │
                     ├──────> [###] HTTP/2 Server ────> [#  ] Lisp Server API ───> [   ] Routing
                     │              (C API works)             (S)                       (M)
                     │
                     └──────> [   ] WebSocket ────────> [   ] Streaming
                                    (M)                       (M)

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 6: COMPILATION (VALK IR → LLVM PIPELINE)
═══════════════════════════════════════════════════════════════════════════════════════════════

                     ┌────────────────────────────────────────────────────────────────────────┐
                     │  UNLOCKS: TCO, 10-100x Performance, JIT, Native Binaries              │
                     │  STRATEGY: AST → Valk IR → LLVM IR (like Swift/Rust/Julia)            │
                     │  RATIONALE: Language-specific optimizations before LLVM lowering       │
                     └────────────────────────────────────────────────────────────────────────┘

  [   ] Phase 1: Valk IR Design ┬──────> [   ] IR Specification ─────> [   ] Instruction Set
        (M - 1-2 weeks)           │              (SSA form: S)                (30-40 opcodes: M)
                                  │
                                  ├──────> [   ] Value Types ─────────> [   ] Type System
                                  │              (vir_value_t: S)             (dynamic tags: S)
                                  │
                                  └──────> [   ] Control Flow ────────> [   ] Basic Blocks
                                                 (CFG repr: M)                 (branching: S)

  [   ] Phase 2: AST → Valk IR ──┬──────> [   ] IR Builder ──────────> [   ] Lowering Pass
        (L - 2-4 weeks)           │              (construction: M)            (AST walk: M)
                                  │
                                  ├──────> [   ] Tail Position ───────> [   ] TCO Analysis
                                  │              (marking: S)                 (identify tail: M)
                                  │
                                  ├──────> [   ] Closure Convert ─────> [   ] Env Flattening
                                  │              (lambda lift: M)             (heap alloc: M)
                                  │
                                  └──────> [   ] Continuation ────────> [   ] CPS Transform
                                                 (LVAL_CONT: L)               (state machine: L)

  [   ] Phase 3: Valk IR Opts ───┬──────> [   ] Escape Analysis ─────> [   ] Stack Promote
        (M - 1-2 weeks)           │              (complete: S)                (heap→stack: M)
                                  │
                                  ├──────> [   ] Inlining ────────────> [   ] Small Functions
                                  │              (heuristics: M)              (threshold: S)
                                  │
                                  └──────> [   ] Dead Code ───────────> [   ] DCE Pass
                                                 (eliminate: S)                (unreachable: S)

  [   ] Phase 4: Valk IR → LLVM ─┬──────> [   ] IR Lowering ─────────> [   ] Value Mapping
        (L - 2-4 weeks)           │              (translation: L)             (tagged union: M)
                                  │
                                  ├──────> [   ] Function Lower ──────> [   ] Call Conv
                                  │              (signatures: M)              (musttail: M)
                                  │
                                  └──────> [   ] GC Integration ──────> [   ] Stack Maps
                                                 (intrinsics: M)               (safepoints: L)

  [   ] Phase 5: Execution ──────┬──────> [   ] JIT (ORC) ───────────> [   ] REPL Mode
        (M - 1-2 weeks)           │              (lazy compile: M)            (interactive: M)
                                  │
                                  ├──────> [   ] AOT Compiler ────────> [   ] Native Binary
                                  │              (full optimize: M)           (linking: S)
                                  │
                                  └──────> [   ] Debug Info ──────────> [   ] Source Maps
                                                 (DILocation: M)               (vir→src: M)

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 7: TYPE SYSTEM (FUTURE)
═══════════════════════════════════════════════════════════════════════════════════════════════

  [   ] Type Annotations ───> [   ] Type Checker ─────> [   ] Type Inference ──> [   ] Gradual Types
        (syntax: S)                 (M)                       (L)                      (XL)
              │
              └───────────────> [   ] ADTs ───────────> [   ] Pattern Match ───> [   ] Exhaustive Check
                                      (M)                     (M)                      (M)

═══════════════════════════════════════════════════════════════════════════════════════════════
 TOOLING
═══════════════════════════════════════════════════════════════════════════════════════════════

  [###] REPL ────────┬──────> [###] History ──────────> [   ] Tab Completion ──> [   ] Syntax Highlight
        (editline)   │              (editline)                (M)                      (S)
                     │
                     ├──────> [###] Load Files ───────> [   ] Hot Reload
                     │              (load builtin)            (M)
                     │
                     └──────> [## ] Test Framework ───> [###] test/suite ───────> [###] test/skip
                                    (Lisp-based)              (define, run)            (skip reason)

  [###] C Tests ─────┬──────> [###] testing.{c,h} ────> [###] ASSERT macros
        (framework)  │              (framework)               (PASS/FAIL)
                     │
                     └──────> [   ] Test Runner ──────> [   ] Pattern Filter ──> [   ] Parallel Tests
                                    (M)                       (S)                      (M)

  [###] Logging ─────┬──────> [###] Log Levels ───────> [###] VALK_LOG env var
        (log.{c,h})  │              (ERROR→TRACE)             (runtime config)
                     │
                     └──────> [###] Stack Traces ─────> [###] libbacktrace ────> [   ] Source Locations
                                    (debug.{c,h})             (symbols)               (M)

  [   ] Debugger ────┬──────> [   ] Breakpoints ──────> [   ] Step/Continue ───> [   ] Inspect
        (L)          │              (M)                       (M)                      (S)
                     │
                     └──────> [   ] Profiler ─────────> [   ] Flame Graphs
                                    (L)                       (M)

  [   ] LSP Server ──┬──────> [   ] Diagnostics ──────> [   ] Completions ─────> [   ] Go to Def
        (L)          │              (M)                       (M)                      (M)

```

---

## Detailed Feature Status

### Unlocked (Complete)

| Area | Feature | LOC | Notes |
|------|---------|-----|-------|
| Parser | S-expressions, Q-expressions | 2,895 | Full Lisp syntax |
| Eval | Tree-walker, environments, closures | - | Lexical + dynamic fallback |
| Memory | Arena, Slab, GC heap | 1,279 | Mark & sweep, escape analysis |
| Control | Continuations (shift/reset) | 77 | Async/await patterns |
| Concurrency | Futures, promises, work queue | 455 | 4-worker pool |
| I/O | libuv, HTTP/2 client+server, TLS | 2,027 | nghttp2, OpenSSL |
| Stdlib | Prelude (40+ functions) | 200 | map, filter, fold, etc |
| HTTP API | High-level HTTP client | 379 | Middleware, batch ops |
| Tooling | REPL, logging, stack traces | 286 | editline, libbacktrace |
| Tests | C framework + Lisp framework | - | All passing |

### Partially Unlocked

| Feature | Status | Blocker | Cost |
|---------|--------|---------|------|
| Escape Analysis | Marking works (3/6 tests) | Return value promotion | S |
| Namespaces | Basic `namespace/symbol` parsing | Needs module system | S |
| Macros | Works but no hygiene | Hygiene system | M |
| Lisp Server API | C API works | Need Lisp bindings | S |
| Test Framework | Works | Need test runner tool | M |

### Locked (Dependencies Required)

| Feature | Requires | Cost | Unlocks |
|---------|----------|------|---------|
| **TCO** | Stack Machine | M | Deep recursion, FP idioms |
| Stack Machine | Bytecode design | L | TCO, performance, LLVM path |
| LLVM Backend | Stack Machine | XL | 10-100x perf, JIT, native |
| Type System | Stable syntax | L-XL | Safety, tooling, docs |
| Channels | Thread primitives | M | CSP concurrency |
| WebSocket | HTTP/2 infra | M | Real-time apps |
| Debugger | Source locations | L | Dev experience |
| LSP | Parser AST | L | Editor integration |

---

## Critical Paths

### Path A: LLVM Compilation (AST → Valk IR → LLVM)

```
[###] Tree-Walker (current)
      │
      ▼
[   ] Valk IR Design ───(M)───> SSA form, instruction set, basic blocks
      │
      ▼
[   ] AST → Valk IR ───(L)───> Lowering, closure conversion, tail analysis
      │
      ▼
[   ] Valk IR Optimizations ───(M)───> Escape analysis, inlining, DCE
      │
      ▼
[   ] Valk IR → LLVM ───(L)───> Translation, GC integration, TCO (musttail)
      │
      ▼
[   ] Execution Backends ───(M)───> JIT (ORC), AOT, debug info
```

**Total cost to Valk IR interpreter**: ~M+L = 3-6 weeks (can run without LLVM)
**Total cost to LLVM JIT**: ~M+L+M+L+M = 7-14 weeks (full pipeline)
**Total cost to TCO**: ~M+L+M+L = 6-12 weeks (enabled in Valk IR → LLVM)
**Total cost to production**: ~M+L+M+L+M+M+M = 9-18 weeks (includes FFI + embedding)

**Key advantage**: Valk IR can be interpreted/debugged independently before LLVM

**Timeline breakdown**:
- Phase 1 (Valk IR Design): 1-2 weeks
- Phase 2 (AST → Valk IR): 2-4 weeks
- Phase 3 (VIR Optimizations): 1-2 weeks
- Phase 4 (VIR → LLVM): 2-4 weeks
- Phase 5 (JIT/AOT): 1-2 weeks
- Phase 6 (FFI): 1-2 weeks
- Phase 7 (Embedding): 1-2 weeks
- **Total**: 9-18 weeks (2-4.5 months)

### Path B: Type Safety

```
[###] Parser
      │
      ▼
[   ] Type Annotations ───(S)───> [   ] Type Checker ───(M)───> [   ] Type Inference ───(L)
                                          │
                                          ▼
                                   [   ] ADTs ───(M)───> [   ] Pattern Match ───(M)
```

**Total cost to basic types**: ~M (annotations + checker)
**Total cost to full types**: ~XL (adds inference, ADTs, patterns)

### Path C: Production Tooling

```
[###] REPL + Logging
      │
      ├───> [   ] Hot Reload ───(M)
      │
      ├───> [   ] Debugger ───(L)───> [   ] Profiler ───(L)
      │
      └───> [   ] LSP Server ───(L)───> Editor Integration
```

**Total cost**: ~XL (debugger + profiler + LSP)

---

## Recommended Unlock Order (VALK IR APPROACH)

### Phase 1: Valk IR Design (1-2 weeks)

1. **IR Specification** [S] - Define SSA-based IR format (like Swift SIL, Rust MIR)
2. **Instruction Set** [M] - Design 30-40 opcodes for Valk semantics
3. **Value Types** [S] - vir_value_t structure with dynamic tags
4. **Control Flow** [M] - CFG representation with basic blocks

### Phase 2: AST → Valk IR Lowering (2-4 weeks)

5. **IR Builder API** [M] - Construction helpers for IR generation
6. **AST Lowering** [M] - Walk AST and emit Valk IR instructions
7. **Tail Position Analysis** [M] - Mark calls in tail position for TCO
8. **Closure Conversion** [M] - Lambda lifting and environment flattening
9. **Continuation Transform** [L] - CPS for LVAL_CONT (async/await support)

### Phase 3: Valk IR Optimizations (1-2 weeks)

10. **Complete Escape Analysis** [S] - Finish promotion (currently 3/6 tests pass)
11. **Stack Promotion** [M] - Move heap allocations to stack when safe
12. **Inlining** [M] - Small function inlining with heuristics
13. **Dead Code Elimination** [S] - Remove unreachable code

### Phase 4: Valk IR → LLVM Lowering (2-4 weeks)

14. **LLVM Setup** [S] - Link llvm-dev libraries, build system integration
15. **IR Translation** [L] - Map Valk IR instructions to LLVM IR
16. **Value Representation** [M] - Implement tagged union in LLVM (i64 + tags)
17. **Function Lowering** [M] - Generate LLVM functions with proper calling conv
18. **TCO Implementation** [M] - Emit musttail for tail-marked calls
19. **GC Integration** [L] - Stack maps, safepoints, gc.statepoint intrinsics

### Phase 5: Execution Backends (1-2 weeks)

20. **JIT with ORC** [M] - On-demand compilation for REPL
21. **AOT Compiler** [M] - Full optimization pipeline (-O2/-O3)
22. **Debug Info** [M] - DILocation mapping from Valk IR → source
23. **Native Linking** [S] - Generate standalone binaries

### Phase 6: FFI (Foreign Function Interface) (1-2 weeks)

24. **FFI Core** [M] - Call C functions from Valk using libffi
25. **Type Marshalling** [M] - Valk ↔ C value conversion
26. **Dynamic Loading** [S] - dlopen/dlsym support
27. **FFI in Valk IR** [S] - VIR_FFI_CALL opcode
28. **FFI in LLVM** [M] - Lower to LLVM with C calling convention

### Phase 7: Embedding API (1-2 weeks)

29. **Public API** [M] - valk_init, valk_eval_string, valk_call
30. **State Management** [S] - valk_state_t with isolated runtime
31. **Value Conversion** [S] - Helper functions for C ↔ Valk
32. **Shared Library** [S] - Build libvalk.so for embedding
33. **Documentation** [M] - Examples and API docs

### Optional: Valk IR Interpreter (parallel work)

- **VIR Interpreter** [M] - Execute Valk IR directly (useful for debugging)
- Can be developed in parallel with LLVM lowering
- Validates IR correctness before LLVM translation

---

## Cost Estimates

| Size | Time | Examples |
|------|------|----------|
| S | 1-3 days | Lisp server bindings, tab completion, namespace cleanup |
| M | 1-2 weeks | Bytecode design, TCO, channels, hot reload |
| L | 2-4 weeks | Stack machine, debugger, profiler, LSP |
| XL | 1+ month | LLVM backend, full type system, gradual types |

---

## Technical Debt

**54 TODO(networking)** comments in codebase:
- Memory lifetime edge cases
- Error handling improvements
- Connection pooling (scaffolded in io_uring)

Run `make todo` to see current TODOs for your branch.

---

## Validation Applications

Build these to prove features work:

1. **HTTP Service** - Validates server API, concurrency, error handling
2. **CLI Tool** - Validates file I/O, argument parsing, stdlib
3. **Game/Simulation** - Validates performance, GC pressure, real-time

---

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for development setup.

Use branch-specific TODOs: `TODO(networking):`, `TODO(llvm):`, `TODO(vir):`, `TODO(main):`

---

## LLVM Compilation Implementation Guide

### Architecture Overview

```
┌──────────────┐     ┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│              │     │              │     │              │     │              │
│  AST         │────>│  Valk IR     │────>│  LLVM IR     │────>│  Machine     │
│  (current)   │     │  (new)       │     │  (llvmlite)  │     │  Code        │
│              │     │              │     │              │     │              │
└──────────────┘     └──────────────┘     └──────────────┘     └──────────────┘
       │                     │                     │                     │
       │                     │                     │                     │
   2.9k LOC             ~1.5k LOC             ~2k LOC            native binary
  valk_lval_t          vir_value_t           LLVMValueRef
  Tree structure       SSA form              SSA form
   Closures (captured env)    Closures (flat env)    Function pointers      Call/ret
   Dynamic scope (fallback)   Closure conversion     Struct for closure     Indirect call
```

### Why Valk IR? (Knowledge Base Findings)

Research on compiler IRs shows that **languages with advanced features use intermediate IRs**:

- **Swift**: AST → SIL IR → LLVM IR (for ref counting, devirtualization)
- **Rust**: AST → MIR IR → LLVM IR (for borrow checking, closure conversion)
- **Julia**: AST → Julia IR → LLVM IR (for type specialization)
- **C/C++**: AST → LLVM IR directly (simpler semantics)

**Valkyria needs an IR because**:
1. **Continuations** (`LVAL_CONT`) - Transform to state machines before LLVM
2. **Dynamic scoping** (fallback chain) - Convert to explicit lookups
3. **Closure conversion** - Flatten environments to heap allocations
4. **Tail call optimization** - Easier to identify in high-level IR
5. **Escape analysis** - Complete before LLVM for stack promotion

### Phase 1: Valk IR Design (1-2 weeks)

#### File Structure

```
src/
├── vir/
│   ├── vir.h              # Core IR definitions
│   ├── vir.c              # IR construction/manipulation
│   ├── vir_builder.h      # Builder API (like LLVM IRBuilder)
│   ├── vir_builder.c      # Builder implementation
│   ├── vir_print.c        # Pretty printer for debugging
│   └── vir_validate.c     # IR validation pass
├── vir_lower/
│   ├── ast_to_vir.h       # AST → Valk IR lowering
│   ├── ast_to_vir.c       # Lowering implementation
│   ├── closure_conv.c     # Closure conversion pass
│   └── tail_analysis.c    # Tail call marking
├── vir_opt/
│   ├── vir_escape.c       # Escape analysis on VIR
│   ├── vir_inline.c       # Inlining pass
│   └── vir_dce.c          # Dead code elimination
└── llvm/
    ├── vir_to_llvm.h      # Valk IR → LLVM IR
    ├── vir_to_llvm.c      # LLVM lowering
    ├── llvm_gc.c          # GC integration (stack maps)
    └── llvm_jit.c         # ORC JIT driver
```

#### Valk IR Instruction Set (30-40 opcodes)

```c
// src/vir/vir.h

typedef enum {
  // Constants
  VIR_CONST_NUM,      // Immediate number
  VIR_CONST_STR,      // String literal
  VIR_CONST_NIL,      // Nil value
  
  // Memory
  VIR_ALLOC,          // Allocate value (heap or stack)
  VIR_LOAD,           // Load from memory
  VIR_STORE,          // Store to memory
  VIR_GC_ROOT,        // Mark as GC root
  
  // Arithmetic
  VIR_ADD, VIR_SUB, VIR_MUL, VIR_DIV, VIR_MOD,
  
  // Comparison
  VIR_EQ, VIR_NE, VIR_LT, VIR_LE, VIR_GT, VIR_GE,
  
  // Control flow
  VIR_BR,             // Unconditional branch
  VIR_BR_IF,          // Conditional branch
  VIR_SWITCH,         // Multi-way branch
  VIR_RET,            // Return from function
  
  // Functions
  VIR_CALL,           // Regular call
  VIR_TAIL_CALL,      // Tail call (TCO candidate)
  VIR_CLOSURE,        // Create closure
  VIR_CLOSURE_CALL,   // Call through closure
  
  // Environment access
  VIR_ENV_NEW,        // Create environment
  VIR_ENV_GET,        // Lookup symbol
  VIR_ENV_SET,        // Define/update symbol
  
  // Continuations
  VIR_CONT_NEW,       // Create continuation
  VIR_CONT_CALL,      // Resume continuation
  
  // Type operations
  VIR_TYPE_TAG,       // Get type tag
  VIR_TYPE_CHECK,     // Runtime type check
  VIR_CAST,           // Type cast (validated)
  
  // List operations (cons-based)
  VIR_CONS,           // Create cons cell
  VIR_CAR,            // Get head
  VIR_CDR,            // Get tail
  
  // Intrinsics
  VIR_INTRINSIC,      // Builtin operation
} vir_opcode_e;

typedef struct vir_value_t vir_value_t;
typedef struct vir_block_t vir_block_t;
typedef struct vir_function_t vir_function_t;

// SSA value (like LLVM Value)
struct vir_value_t {
  vir_opcode_e op;
  uint32_t id;              // SSA id (%0, %1, %2...)
  vir_type_e type;          // Dynamic type tag
  union {
    long num;               // Constant number
    char* str;              // Constant string
    vir_value_t* operands[4]; // Instruction operands
    vir_block_t* block;     // Branch target
  };
  vir_value_t* next;        // Linked list in block
};

// Basic block (CFG node)
struct vir_block_t {
  uint32_t id;
  char* label;
  vir_value_t* first_inst;  // First instruction
  vir_value_t* last_inst;   // Last instruction (terminator)
  vir_block_t** preds;      // Predecessor blocks
  size_t num_preds;
  vir_block_t** succs;      // Successor blocks
  size_t num_succs;
};

// Function
struct vir_function_t {
  char* name;
  vir_value_t** params;     // Parameters (SSA values)
  size_t num_params;
  vir_block_t* entry_block; // Entry basic block
  vir_block_t** blocks;     // All blocks
  size_t num_blocks;
  bool has_tail_calls;      // TCO opportunity
};
```

#### Example: AST → Valk IR

**Input AST** (for `(lambda (x) (+ x 1))`):
```
LVAL_FUN
  formals: LVAL_CONS(LVAL_SYM("x"), LVAL_NIL)
  body: LVAL_CONS(
    LVAL_SYM("+"),
    LVAL_CONS(LVAL_SYM("x"), LVAL_CONS(LVAL_NUM(1), LVAL_NIL))
  )
```

**Output Valk IR**:
```
function @lambda_0(ptr %x) {
entry:
  %0 = vir.load ptr %x              ; Load parameter
  %1 = vir.const.num 1              ; Constant 1
  %2 = vir.intrinsic.add %0, %1     ; Call + builtin
  vir.ret %2                         ; Return result
}
```

### Phase 2: AST → Valk IR (2-4 weeks)

#### Lowering Strategy

```c
// src/vir_lower/ast_to_vir.c

vir_function_t* valk_ast_to_vir(valk_lval_t* ast) {
  vir_builder_t* builder = vir_builder_new();
  
  // Create function
  vir_function_t* func = vir_function_new("main");
  vir_block_t* entry = vir_block_new(func, "entry");
  vir_builder_set_insert_point(builder, entry);
  
  // Lower AST to VIR
  vir_value_t* result = lower_sexpr(builder, ast);
  
  // Return result
  vir_builder_ret(builder, result);
  
  return func;
}

static vir_value_t* lower_sexpr(vir_builder_t* b, valk_lval_t* lval) {
  switch (LVAL_TYPE(lval)) {
    case LVAL_NUM:
      return vir_builder_const_num(b, lval->num);
    
    case LVAL_STR:
      return vir_builder_const_str(b, lval->str);
    
    case LVAL_SYM:
      // Environment lookup → VIR_ENV_GET
      return vir_builder_env_get(b, b->current_env, lval->str);
    
    case LVAL_CONS: {
      // Function call
      valk_lval_t* func = valk_lval_head(lval);
      valk_lval_t* args = valk_lval_tail(lval);
      
      // Check if tail position
      bool is_tail = check_tail_position(b);
      
      vir_value_t* func_val = lower_sexpr(b, func);
      vir_value_t** arg_vals = lower_args(b, args);
      
      if (is_tail) {
        return vir_builder_tail_call(b, func_val, arg_vals);
      } else {
        return vir_builder_call(b, func_val, arg_vals);
      }
    }
    
    case LVAL_FUN: {
      // Lambda → closure conversion
      return lower_lambda(b, lval);
    }
    
    // ... handle other types
  }
}
```

#### Tail Call Analysis

```c
// src/vir_lower/tail_analysis.c

// Mark tail calls for TCO
void vir_mark_tail_calls(vir_function_t* func) {
  for (size_t i = 0; i < func->num_blocks; i++) {
    vir_block_t* block = func->blocks[i];
    vir_value_t* last = block->last_inst;
    
    // If last instruction is RET, check if previous is CALL
    if (last->op == VIR_RET && last->operands[0]) {
      vir_value_t* ret_val = last->operands[0];
      if (ret_val->op == VIR_CALL) {
        // This is a tail call!
        ret_val->op = VIR_TAIL_CALL;
        func->has_tail_calls = true;
      }
    }
  }
}
```

#### Closure Conversion

```c
// src/vir_lower/closure_conv.c

// Convert closure to flat structure
vir_value_t* vir_closure_convert(vir_builder_t* b, valk_lval_t* lambda) {
  // 1. Analyze free variables
  char** free_vars = analyze_free_vars(lambda);
  size_t num_free = count_free_vars(free_vars);
  
  // 2. Create closure struct on heap
  //    struct { void* fn_ptr; void* env[num_free]; }
  vir_value_t* closure_size = vir_builder_const_num(b, 
    sizeof(void*) * (1 + num_free));
  vir_value_t* closure = vir_builder_alloc(b, closure_size);
  
  // 3. Store function pointer
  vir_value_t* fn_ptr = vir_builder_function_addr(b, lambda->fun.name);
  vir_builder_store(b, closure, 0, fn_ptr);
  
  // 4. Capture free variables
  for (size_t i = 0; i < num_free; i++) {
    vir_value_t* var = vir_builder_env_get(b, b->current_env, free_vars[i]);
    vir_builder_store(b, closure, i + 1, var);
  }
  
  return closure;
}
```

### Phase 3: Valk IR Optimizations (1-2 weeks)

#### Escape Analysis on VIR

```c
// src/vir_opt/vir_escape.c

void vir_escape_analysis(vir_function_t* func) {
  // Mark allocations that don't escape
  for (size_t i = 0; i < func->num_blocks; i++) {
    vir_block_t* block = func->blocks[i];
    for (vir_value_t* inst = block->first_inst; inst; inst = inst->next) {
      if (inst->op == VIR_ALLOC) {
        if (!value_escapes(func, inst)) {
          // Can promote to stack!
          inst->flags |= VIR_FLAG_STACK_ALLOC;
        }
      }
    }
  }
}

static bool value_escapes(vir_function_t* func, vir_value_t* val) {
  // Check all uses of this value
  for (use in uses(val)) {
    if (use->op == VIR_RET) return true;        // Returned
    if (use->op == VIR_STORE) {
      // Stored to heap location
      if (is_heap_location(use->operands[0])) return true;
    }
    if (use->op == VIR_CLOSURE) return true;    // Captured
  }
  return false;
}
```

### Phase 4: Valk IR → LLVM (2-4 weeks)

#### LLVM Lowering

```c
// src/llvm/vir_to_llvm.c

#include <llvm-c/Core.h>
#include <llvm-c/ExecutionEngine.h>

LLVMModuleRef vir_to_llvm_module(vir_function_t** funcs, size_t num_funcs) {
  LLVMContextRef ctx = LLVMContextCreate();
  LLVMModuleRef mod = LLVMModuleCreateWithNameInContext("valk", ctx);
  LLVMBuilderRef builder = LLVMCreateBuilderInContext(ctx);
  
  // Define value type: struct { i64 tag; i64 data; }
  LLVMTypeRef value_type = LLVMStructType(
    (LLVMTypeRef[]){LLVMInt64Type(), LLVMInt64Type()}, 2, false);
  
  // Lower each function
  for (size_t i = 0; i < num_funcs; i++) {
    lower_function(mod, builder, value_type, funcs[i]);
  }
  
  return mod;
}

static void lower_function(LLVMModuleRef mod, LLVMBuilderRef builder,
                          LLVMTypeRef value_type, vir_function_t* func) {
  // Create LLVM function
  LLVMTypeRef* param_types = malloc(func->num_params * sizeof(LLVMTypeRef));
  for (size_t i = 0; i < func->num_params; i++) {
    param_types[i] = LLVMPointerType(value_type, 0);
  }
  
  LLVMTypeRef func_type = LLVMFunctionType(
    LLVMPointerType(value_type, 0), param_types, func->num_params, false);
  
  LLVMValueRef llvm_func = LLVMAddFunction(mod, func->name, func_type);
  
  // Create basic blocks
  LLVMBasicBlockRef* llvm_blocks = malloc(func->num_blocks * sizeof(LLVMBasicBlockRef));
  for (size_t i = 0; i < func->num_blocks; i++) {
    llvm_blocks[i] = LLVMAppendBasicBlock(llvm_func, func->blocks[i]->label);
  }
  
  // Lower instructions block by block
  for (size_t i = 0; i < func->num_blocks; i++) {
    LLVMPositionBuilderAtEnd(builder, llvm_blocks[i]);
    lower_block(builder, value_type, func->blocks[i]);
  }
}

static void lower_block(LLVMBuilderRef builder, LLVMTypeRef value_type,
                       vir_block_t* block) {
  for (vir_value_t* inst = block->first_inst; inst; inst = inst->next) {
    switch (inst->op) {
      case VIR_CONST_NUM: {
        // Create tagged value: { TAG_NUM, num }
        LLVMValueRef val = LLVMConstStruct(
          (LLVMValueRef[]){
            LLVMConstInt(LLVMInt64Type(), TAG_NUM, false),
            LLVMConstInt(LLVMInt64Type(), inst->num, false)
          }, 2, false);
        inst->llvm_value = val;
        break;
      }
      
      case VIR_ADD: {
        // Extract numbers, add, retag
        LLVMValueRef left = lower_value(builder, inst->operands[0]);
        LLVMValueRef right = lower_value(builder, inst->operands[1]);
        // ... extract data field, add, create new tagged value
        break;
      }
      
      case VIR_TAIL_CALL: {
        // Emit musttail call
        LLVMValueRef func = lower_value(builder, inst->operands[0]);
        LLVMValueRef* args = lower_args(builder, inst->operands + 1);
        LLVMValueRef call = LLVMBuildCall2(builder, func_type, func, args, num_args, "");
        
        // Mark as musttail (requires LLVM 3.5+)
        LLVMSetTailCallKind(call, LLVMTailCallKindMustTail);
        inst->llvm_value = call;
        break;
      }
      
      case VIR_ALLOC: {
        if (inst->flags & VIR_FLAG_STACK_ALLOC) {
          // Stack allocation (escape analysis marked as safe)
          inst->llvm_value = LLVMBuildAlloca(builder, value_type, "stack");
        } else {
          // Heap allocation with GC
          inst->llvm_value = emit_gc_alloc(builder, inst->operands[0]);
        }
        break;
      }
      
      // ... handle other opcodes
    }
  }
}
```

#### GC Integration with Stack Maps

```c
// src/llvm/llvm_gc.c

// Use LLVM's gc.statepoint intrinsics
static LLVMValueRef emit_gc_alloc(LLVMBuilderRef builder, LLVMValueRef size) {
  // Call GC allocator
  LLVMValueRef gc_alloc_fn = LLVMGetNamedFunction(mod, "valk_gc_alloc");
  LLVMValueRef ptr = LLVMBuildCall2(builder, gc_alloc_type, gc_alloc_fn, 
                                    &size, 1, "gc_alloc");
  
  // Insert statepoint for GC
  // This allows LLVM to generate stack maps
  LLVMValueRef statepoint = emit_statepoint(builder, ptr);
  
  return statepoint;
}

// Stack map generation (LLVM handles this automatically)
// Just need to mark GC pointers with proper metadata
static void mark_gc_pointer(LLVMValueRef val) {
  LLVMSetMetadata(val, LLVMGetMDKindID("gc.root", 7), /* metadata */);
}
```

### Phase 5: Execution Backends (1-2 weeks)

#### JIT with LLVM ORC

```c
// src/llvm/llvm_jit.c

#include <llvm-c/LLJIT.h>
#include <llvm-c/OrcEE.h>

typedef struct {
  LLVMLLJITRef jit;
  LLVMContextRef ctx;
  LLVMTargetDataRef target_data;
} valk_jit_t;

valk_jit_t* valk_jit_init() {
  LLVMLLJITRef jit;
  LLVMErrorRef err;
  
  // Create ORC JIT
  if ((err = LLVMOrcCreateLLJIT(&jit, NULL))) {
    char* msg = LLVMGetErrorMessage(err);
    VALK_ERROR("Failed to create JIT: %s", msg);
    LLVMDisposeErrorMessage(msg);
    return NULL;
  }
  
  valk_jit_t* vjit = malloc(sizeof(valk_jit_t));
  vjit->jit = jit;
  vjit->ctx = LLVMContextCreate();
  vjit->target_data = LLVMOrcLLJITGetDataLayout(jit);
  
  return vjit;
}

// Compile and execute function
valk_lval_t* valk_jit_eval(valk_jit_t* jit, valk_lval_t* ast) {
  // AST → Valk IR
  vir_function_t* vir_func = valk_ast_to_vir(ast);
  
  // Valk IR optimizations
  vir_escape_analysis(vir_func);
  vir_inline_functions(vir_func);
  vir_mark_tail_calls(vir_func);
  
  // Valk IR → LLVM IR
  LLVMModuleRef mod = vir_to_llvm_module(&vir_func, 1);
  
  // Add to JIT
  LLVMOrcThreadSafeModuleRef tsm = 
    LLVMOrcCreateNewThreadSafeModule(mod, jit->ctx);
  LLVMErrorRef err = LLVMOrcLLJITAddLLVMIRModule(jit->jit, 
    LLVMOrcLLJITGetMainJITDylib(jit->jit), tsm);
  if (err) {
    VALK_ERROR("Failed to add module to JIT");
    return NULL;
  }
  
  // Look up function
  LLVMOrcJITTargetAddress addr;
  err = LLVMOrcLLJITLookup(jit->jit, &addr, vir_func->name);
  if (err) {
    VALK_ERROR("Failed to find function in JIT");
    return NULL;
  }
  
  // Call compiled function
  typedef valk_lval_t* (*jit_fn_t)();
  jit_fn_t fn = (jit_fn_t)addr;
  return fn();
}
```

#### AOT Compiler

```bash
# Generate object file
valkc compile program.valk -o program.o

# Link with runtime
gcc program.o -L./build -lvalk_runtime -o program

# Run
./program
```

```c
// AOT compilation path
void valk_compile_aot(const char* input_file, const char* output_file) {
  // Parse source
  valk_lval_t* ast = valk_parse_file(input_file);
  
  // AST → Valk IR
  vir_function_t* vir = valk_ast_to_vir(ast);
  
  // Optimize
  vir_escape_analysis(vir);
  vir_inline_functions(vir);
  vir_mark_tail_calls(vir);
  vir_dce(vir);
  
  // Valk IR → LLVM IR
  LLVMModuleRef mod = vir_to_llvm_module(&vir, 1);
  
  // LLVM optimizations
  LLVMPassManagerRef pm = LLVMCreatePassManager();
  LLVMAddInstructionCombiningPass(pm);
  LLVMAddReassociatePass(pm);
  LLVMAddGVNPass(pm);
  LLVMAddCFGSimplificationPass(pm);
  LLVMRunPassManager(pm, mod);
  
  // Emit object file
  LLVMTargetMachineRef target = create_target_machine();
  LLVMTargetMachineEmitToFile(target, mod, output_file, 
                              LLVMObjectFile, NULL);
}
```

### Testing Strategy

```c
// test/test_vir.c - Valk IR tests
void test_vir_lowering() {
  valk_lval_t* ast = valk_lval_num(42);
  vir_function_t* vir = valk_ast_to_vir(ast);
  
  ASSERT(vir->num_blocks == 1);
  ASSERT(vir->entry_block->first_inst->op == VIR_CONST_NUM);
  ASSERT(vir->entry_block->first_inst->num == 42);
}

void test_tail_call_analysis() {
  // (lambda (x) (f x)) in tail position
  valk_lval_t* ast = parse("(lambda (x) (f x))");
  vir_function_t* vir = valk_ast_to_vir(ast);
  vir_mark_tail_calls(vir);
  
  ASSERT(vir->has_tail_calls == true);
  // Find the call instruction
  vir_value_t* call = find_call_inst(vir);
  ASSERT(call->op == VIR_TAIL_CALL);
}

void test_escape_analysis() {
  // Local allocation that doesn't escape
  valk_lval_t* ast = parse("(let ((x 42)) x)");
  vir_function_t* vir = valk_ast_to_vir(ast);
  vir_escape_analysis(vir);
  
  vir_value_t* alloc = find_alloc_inst(vir);
  ASSERT(alloc->flags & VIR_FLAG_STACK_ALLOC);
}
```

### Migration Path

1. **Phase 1-2**: Develop Valk IR alongside tree-walker (no breaking changes)
2. **Phase 3**: Add VIR optimizations (still using tree-walker for execution)
3. **Phase 4**: Implement LLVM lowering (JIT mode optional flag: `--jit`)
4. **Phase 5**: Make JIT default, keep tree-walker as fallback
5. **Phase 6**: Remove tree-walker once LLVM is stable

### Performance Expectations

Based on knowledge base research and similar systems:

- **Tree-walker (current)**: Baseline (1x)
- **Valk IR interpreter**: 2-5x faster (if implemented)
- **LLVM JIT (-O0)**: 5-10x faster
- **LLVM AOT (-O2)**: 10-50x faster
- **LLVM AOT (-O3 + LTO)**: 50-100x faster

### Key Decisions from Knowledge Base

1. **SSA Form**: Valk IR uses SSA like LLVM (easier for optimization)
2. **Closure Conversion**: Done in Valk IR, not in LLVM (language-specific)
3. **Tail Calls**: Marked in Valk IR, enforced with `musttail` in LLVM
4. **GC Integration**: Use LLVM's `gc.statepoint` intrinsics for stack maps
5. **Continuations**: CPS transform in Valk IR → state machine → LLVM functions

### Resources

- **Swift SIL**: https://github.com/apple/swift/tree/main/docs/SIL.rst
- **Rust MIR**: https://rustc-dev-guide.rust-lang.org/mir/
- **LLVM C API**: https://llvm.org/doxygen/group__LLVMC.html
- **LLVM GC**: https://llvm.org/docs/GarbageCollection.html
- **LLVM ORC JIT**: https://llvm.org/docs/ORCv2.html

---

## C/C++ FFI and Embedding

### Overview

Valkyria needs bidirectional integration with C/C++:

1. **FFI (Foreign Function Interface)**: Call C/C++ from Valk
2. **Embedding API**: Embed Valk interpreter/JIT in C/C++ applications

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│  C/C++ Application                                              │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                                                           │   │
│  │  Valk Embedded Runtime                                    │   │
│  │  ┌──────────────┐       ┌──────────────┐                 │   │
│  │  │              │       │              │                 │   │
│  │  │  JIT Engine  │◄─────►│  C FFI Layer │◄──── C funcs   │   │
│  │  │  (LLVM ORC)  │       │  (libffi)    │                 │   │
│  │  │              │       │              │                 │   │
│  │  └──────────────┘       └──────────────┘                 │   │
│  │         │                       ▲                         │   │
│  │         │                       │                         │   │
│  │         ▼                       │                         │   │
│  │  ┌──────────────────────────────┴───────┐                │   │
│  │  │  Valk Code                           │                │   │
│  │  │  (lambda (x) (c-malloc 1024))        │                │   │
│  │  │  (c-call "printf" "Hello %d\n" x)    │                │   │
│  │  └──────────────────────────────────────┘                │   │
│  │                                                           │   │
│  └───────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Phase 6: FFI Implementation (M - 1-2 weeks)

#### File Structure

```
src/
├── ffi/
│   ├── ffi.h              # FFI public API
│   ├── ffi.c              # FFI implementation
│   ├── ffi_types.c        # Type marshalling (Valk ↔ C)
│   └── ffi_cache.c        # Cached function pointers
└── embed/
    ├── valk_embed.h       # Embedding API (public header)
    ├── valk_embed.c       # Embedding implementation
    └── valk_state.c       # Runtime state management
```

#### FFI Design: Calling C from Valk

```c
// src/ffi/ffi.h

typedef enum {
  FFI_TYPE_VOID,
  FFI_TYPE_INT,
  FFI_TYPE_LONG,
  FFI_TYPE_FLOAT,
  FFI_TYPE_DOUBLE,
  FFI_TYPE_PTR,
  FFI_TYPE_STRUCT,
} valk_ffi_type_e;

typedef struct {
  void* fn_ptr;                   // C function pointer
  valk_ffi_type_e ret_type;       // Return type
  valk_ffi_type_e* arg_types;     // Argument types
  size_t num_args;
  ffi_cif cif;                    // libffi call interface
} valk_ffi_fn_t;

// Register C function for calling from Valk
valk_ffi_fn_t* valk_ffi_register(const char* name, void* fn_ptr,
                                  valk_ffi_type_e ret_type,
                                  valk_ffi_type_e* arg_types,
                                  size_t num_args);

// Call C function from Valk (builtin)
valk_lval_t* valk_builtin_c_call(valk_lenv_t* env, valk_lval_t* args);
```

#### Example: Calling C from Valk

```lisp
; Register C function: int add(int a, int b)
(c-register "add" 
  :ret-type :int 
  :arg-types [:int :int])

; Call from Valk
(c-call "add" 10 20)  ; => 30

; Common C functions
(c-call "malloc" 1024)              ; Allocate memory
(c-call "printf" "Hello %s\n" name) ; Print to stdout
(c-call "fopen" "/tmp/file" "w")    ; Open file
```

#### FFI Implementation

```c
// src/ffi/ffi.c

#include <ffi.h>
#include <dlfcn.h>

// Global FFI function registry
static valk_ffi_fn_t** ffi_registry = NULL;
static size_t ffi_registry_size = 0;

valk_ffi_fn_t* valk_ffi_register(const char* name, void* fn_ptr,
                                  valk_ffi_type_e ret_type,
                                  valk_ffi_type_e* arg_types,
                                  size_t num_args) {
  valk_ffi_fn_t* fn = malloc(sizeof(valk_ffi_fn_t));
  fn->fn_ptr = fn_ptr;
  fn->ret_type = ret_type;
  fn->arg_types = malloc(num_args * sizeof(valk_ffi_type_e));
  memcpy(fn->arg_types, arg_types, num_args * sizeof(valk_ffi_type_e));
  fn->num_args = num_args;
  
  // Prepare libffi call interface
  ffi_type** ffi_arg_types = malloc(num_args * sizeof(ffi_type*));
  for (size_t i = 0; i < num_args; i++) {
    ffi_arg_types[i] = valk_ffi_to_libffi_type(arg_types[i]);
  }
  
  ffi_type* ffi_ret_type = valk_ffi_to_libffi_type(ret_type);
  
  if (ffi_prep_cif(&fn->cif, FFI_DEFAULT_ABI, num_args, 
                   ffi_ret_type, ffi_arg_types) != FFI_OK) {
    VALK_ERROR("Failed to prepare FFI call interface");
    free(fn);
    return NULL;
  }
  
  // Add to registry
  ffi_registry = realloc(ffi_registry, 
                         (ffi_registry_size + 1) * sizeof(valk_ffi_fn_t*));
  ffi_registry[ffi_registry_size++] = fn;
  
  return fn;
}

// Builtin: (c-call "function-name" arg1 arg2 ...)
valk_lval_t* valk_builtin_c_call(valk_lenv_t* env, valk_lval_t* args) {
  LVAL_ASSERT_COUNT_MIN(args, args, 1);
  
  valk_lval_t* fn_name_val = valk_lval_list_nth(args, 0);
  LVAL_ASSERT_TYPE(args, fn_name_val, LVAL_STR);
  const char* fn_name = fn_name_val->str;
  
  // Look up function in registry
  valk_ffi_fn_t* fn = find_ffi_function(fn_name);
  if (!fn) {
    return valk_lval_err("Unknown C function: %s", fn_name);
  }
  
  // Marshal arguments: Valk → C
  void** c_args = malloc(fn->num_args * sizeof(void*));
  for (size_t i = 0; i < fn->num_args; i++) {
    valk_lval_t* valk_arg = valk_lval_list_nth(args, i + 1);
    c_args[i] = valk_to_c_value(valk_arg, fn->arg_types[i]);
  }
  
  // Call C function via libffi
  void* ret_val = alloca(sizeof(long));  // Max return size
  ffi_call(&fn->cif, FFI_FN(fn->fn_ptr), ret_val, c_args);
  
  // Marshal return value: C → Valk
  valk_lval_t* result = c_to_valk_value(ret_val, fn->ret_type);
  
  // Cleanup
  free(c_args);
  
  return result;
}
```

#### Type Marshalling

```c
// src/ffi/ffi_types.c

// Convert Valk value to C value
void* valk_to_c_value(valk_lval_t* val, valk_ffi_type_e type) {
  void* c_val = malloc(type_size(type));
  
  switch (type) {
    case FFI_TYPE_INT:
      LVAL_ASSERT_TYPE(NULL, val, LVAL_NUM);
      *(int*)c_val = (int)val->num;
      break;
    
    case FFI_TYPE_LONG:
      LVAL_ASSERT_TYPE(NULL, val, LVAL_NUM);
      *(long*)c_val = val->num;
      break;
    
    case FFI_TYPE_DOUBLE:
      LVAL_ASSERT_TYPE(NULL, val, LVAL_NUM);
      *(double*)c_val = (double)val->num;
      break;
    
    case FFI_TYPE_PTR:
      // Valk string → C char*
      if (LVAL_TYPE(val) == LVAL_STR) {
        *(char**)c_val = val->str;
      }
      // Valk ref → C void*
      else if (LVAL_TYPE(val) == LVAL_REF) {
        *(void**)c_val = val->ref.ptr;
      }
      else {
        VALK_ERROR("Cannot convert to C pointer");
      }
      break;
    
    default:
      VALK_ERROR("Unsupported FFI type: %d", type);
  }
  
  return c_val;
}

// Convert C value to Valk value
valk_lval_t* c_to_valk_value(void* c_val, valk_ffi_type_e type) {
  switch (type) {
    case FFI_TYPE_VOID:
      return valk_lval_nil();
    
    case FFI_TYPE_INT:
      return valk_lval_num(*(int*)c_val);
    
    case FFI_TYPE_LONG:
      return valk_lval_num(*(long*)c_val);
    
    case FFI_TYPE_DOUBLE:
      return valk_lval_num((long)(*(double*)c_val));
    
    case FFI_TYPE_PTR:
      // Create Valk ref wrapping C pointer
      return valk_lval_ref("c-ptr", *(void**)c_val, NULL);
    
    default:
      return valk_lval_err("Unsupported FFI return type");
  }
}
```

#### Dynamic Library Loading

```c
// Load shared library and register all functions
valk_lval_t* valk_builtin_dlopen(valk_lenv_t* env, valk_lval_t* args) {
  LVAL_ASSERT_COUNT_EQ(args, args, 1);
  LVAL_ASSERT_TYPE(args, valk_lval_list_nth(args, 0), LVAL_STR);
  
  const char* lib_path = valk_lval_list_nth(args, 0)->str;
  
  // Load shared library
  void* handle = dlopen(lib_path, RTLD_LAZY);
  if (!handle) {
    return valk_lval_err("Failed to load library: %s", dlerror());
  }
  
  // Store handle as ref
  return valk_lval_ref("dl-handle", handle, (void(*)(void*))dlclose);
}

// Look up symbol from loaded library
valk_lval_t* valk_builtin_dlsym(valk_lenv_t* env, valk_lval_t* args) {
  LVAL_ASSERT_COUNT_EQ(args, args, 2);
  
  valk_lval_t* handle_val = valk_lval_list_nth(args, 0);
  LVAL_ASSERT_TYPE(args, handle_val, LVAL_REF);
  
  valk_lval_t* sym_name = valk_lval_list_nth(args, 1);
  LVAL_ASSERT_TYPE(args, sym_name, LVAL_STR);
  
  void* handle = handle_val->ref.ptr;
  void* sym = dlsym(handle, sym_name->str);
  
  if (!sym) {
    return valk_lval_err("Symbol not found: %s", sym_name->str);
  }
  
  return valk_lval_ref("fn-ptr", sym, NULL);
}
```

### Phase 7: Embedding API (M - 1-2 weeks)

#### Embedding API Design

```c
// src/embed/valk_embed.h - Public embedding API

typedef struct valk_state_t valk_state_t;

// Initialize Valk runtime
valk_state_t* valk_init();

// Shutdown runtime
void valk_shutdown(valk_state_t* state);

// Evaluate Valk code from C
int valk_eval_string(valk_state_t* state, const char* code, valk_lval_t** result);
int valk_eval_file(valk_state_t* state, const char* filename, valk_lval_t** result);

// Call Valk function from C
valk_lval_t* valk_call(valk_state_t* state, const char* fn_name, 
                       valk_lval_t** args, size_t num_args);

// Register C function callable from Valk
int valk_register_c_function(valk_state_t* state, const char* name,
                             valk_lval_builtin_t* fn);

// Value conversion helpers
long valk_to_long(valk_lval_t* val);
double valk_to_double(valk_lval_t* val);
const char* valk_to_string(valk_lval_t* val);

valk_lval_t* valk_from_long(valk_state_t* state, long val);
valk_lval_t* valk_from_double(valk_state_t* state, double val);
valk_lval_t* valk_from_string(valk_state_t* state, const char* str);
```

#### Example: Embedding Valk in C

```c
// example/embed_demo.c

#include "valk_embed.h"
#include <stdio.h>

// C function callable from Valk
valk_lval_t* c_add(valk_lenv_t* env, valk_lval_t* args) {
  long a = valk_to_long(valk_lval_list_nth(args, 0));
  long b = valk_to_long(valk_lval_list_nth(args, 1));
  return valk_from_long(env, a + b);
}

int main() {
  // Initialize Valk runtime
  valk_state_t* valk = valk_init();
  
  // Register C function
  valk_register_c_function(valk, "c-add", c_add);
  
  // Evaluate Valk code
  valk_lval_t* result;
  int ret = valk_eval_string(valk, 
    "(fun double (x) (* x 2))"
    "(double 21)", 
    &result);
  
  if (ret == 0) {
    printf("Result: %ld\n", valk_to_long(result));  // 42
  }
  
  // Call Valk function from C
  valk_lval_t* args[] = {valk_from_long(valk, 10)};
  valk_lval_t* doubled = valk_call(valk, "double", args, 1);
  printf("Doubled: %ld\n", valk_to_long(doubled));  // 20
  
  // Shutdown
  valk_shutdown(valk);
  return 0;
}
```

#### Implementation

```c
// src/embed/valk_embed.c

struct valk_state_t {
  valk_lenv_t* global_env;     // Global environment
  valk_gc_malloc_heap_t* heap; // GC heap
  valk_mem_arena_t* scratch;   // Scratch arena
  valk_jit_t* jit;             // JIT compiler (optional)
  bool jit_enabled;
};

valk_state_t* valk_init() {
  valk_state_t* state = malloc(sizeof(valk_state_t));
  
  // Initialize memory
  state->heap = valk_gc_malloc_heap_init(
    16 * 1024 * 1024,  // 16MB threshold
    64 * 1024 * 1024   // 64MB hard limit
  );
  
  state->scratch = valk_mem_arena_new(1 * 1024 * 1024);  // 1MB scratch
  
  // Create global environment with builtins
  VALK_WITH_ALLOC(state->heap) {
    state->global_env = valk_lenv_builtins();
  }
  
  valk_gc_malloc_set_root(state->heap, state->global_env);
  
  // Initialize JIT (optional, based on VALK_JIT env var)
  const char* jit_enabled = getenv("VALK_JIT");
  if (jit_enabled && strcmp(jit_enabled, "1") == 0) {
    state->jit = valk_jit_init();
    state->jit_enabled = true;
  } else {
    state->jit = NULL;
    state->jit_enabled = false;
  }
  
  return state;
}

void valk_shutdown(valk_state_t* state) {
  if (state->jit) {
    valk_jit_shutdown(state->jit);
  }
  valk_gc_malloc_heap_destroy(state->heap);
  valk_mem_arena_free(state->scratch);
  free(state);
}

int valk_eval_string(valk_state_t* state, const char* code, valk_lval_t** result) {
  // Parse
  valk_lval_t* ast = valk_parse_string(code);
  if (LVAL_TYPE(ast) == LVAL_ERR) {
    *result = ast;
    return -1;
  }
  
  // Evaluate (tree-walker or JIT)
  if (state->jit_enabled) {
    *result = valk_jit_eval(state->jit, ast);
  } else {
    *result = valk_lval_eval(state->global_env, ast);
  }
  
  return LVAL_TYPE(*result) == LVAL_ERR ? -1 : 0;
}

valk_lval_t* valk_call(valk_state_t* state, const char* fn_name,
                       valk_lval_t** args, size_t num_args) {
  // Look up function in environment
  valk_lval_t* fn = valk_lenv_get(state->global_env, fn_name);
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("Not a function: %s", fn_name);
  }
  
  // Build argument list
  valk_lval_t* arg_list = valk_lval_nil();
  for (int i = num_args - 1; i >= 0; i--) {
    arg_list = valk_lval_cons(args[i], arg_list);
  }
  
  // Call
  return valk_lval_eval_call(state->global_env, fn, arg_list);
}

int valk_register_c_function(valk_state_t* state, const char* name,
                             valk_lval_builtin_t* fn) {
  valk_lval_t* fn_val = valk_lval_builtin(fn, name);
  valk_lenv_def(state->global_env, name, fn_val);
  return 0;
}
```

### Integration with Valk IR and LLVM

#### FFI in Valk IR

```c
// Valk IR opcodes for FFI
typedef enum {
  // ... existing opcodes
  
  VIR_FFI_CALL,       // Call C function via FFI
  VIR_FFI_DLOPEN,     // Load dynamic library
  VIR_FFI_DLSYM,      // Look up symbol
} vir_opcode_e;
```

#### FFI in LLVM

```c
// Lower VIR_FFI_CALL to LLVM
case VIR_FFI_CALL: {
  // Generate LLVM call with proper ABI
  valk_ffi_fn_t* ffi_fn = inst->ffi_fn;
  
  // Marshal arguments
  LLVMValueRef* llvm_args = marshal_args_to_llvm(builder, inst->operands);
  
  // Create function type matching C ABI
  LLVMTypeRef fn_type = create_ffi_function_type(ffi_fn);
  
  // Create function pointer
  LLVMValueRef fn_ptr = LLVMConstIntToPtr(
    LLVMConstInt(LLVMInt64Type(), (uint64_t)ffi_fn->fn_ptr, false),
    LLVMPointerType(fn_type, 0)
  );
  
  // Call with C calling convention
  LLVMValueRef call = LLVMBuildCall2(builder, fn_type, fn_ptr, 
                                     llvm_args, ffi_fn->num_args, "ffi_call");
  LLVMSetInstructionCallConv(call, LLVMCCallConv);
  
  // Marshal return value back to Valk value
  inst->llvm_value = marshal_return_to_valk(builder, call, ffi_fn->ret_type);
  break;
}
```

### Build System Integration

```makefile
# Makefile additions for FFI and embedding

# FFI requires libffi
CFLAGS += $(shell pkg-config --cflags libffi)
LDFLAGS += $(shell pkg-config --libs libffi) -ldl

# Embedding library
libvalk.so: $(VALK_OBJS)
	$(CC) -shared -o $@ $^ $(LDFLAGS)

# Install embedding header
install:
	mkdir -p $(PREFIX)/include
	cp src/embed/valk_embed.h $(PREFIX)/include/
	mkdir -p $(PREFIX)/lib
	cp libvalk.so $(PREFIX)/lib/
```

### Testing Strategy

```c
// test/test_ffi.c

void test_ffi_basic_call() {
  valk_state_t* valk = valk_init();
  
  // Register libc printf
  valk_ffi_register("printf", printf, FFI_TYPE_INT,
    (valk_ffi_type_e[]){FFI_TYPE_PTR}, 1);
  
  // Call from Valk
  valk_lval_t* result;
  valk_eval_string(valk, "(c-call \"printf\" \"Test\\n\")", &result);
  
  ASSERT(LVAL_TYPE(result) == LVAL_NUM);
  valk_shutdown(valk);
}

void test_embedding() {
  valk_state_t* valk = valk_init();
  
  // Define function in Valk
  valk_eval_string(valk, "(fun square (x) (* x x))", NULL);
  
  // Call from C
  valk_lval_t* args[] = {valk_from_long(valk, 5)};
  valk_lval_t* result = valk_call(valk, "square", args, 1);
  
  ASSERT(valk_to_long(result) == 25);
  valk_shutdown(valk);
}
```

### Common Use Cases

#### Use Case 1: Game Scripting

```c
// Game engine with Valk scripting
typedef struct {
  float x, y;
} Vec2;

// Register game API
valk_lval_t* set_player_pos(valk_lenv_t* env, valk_lval_t* args) {
  float x = valk_to_double(valk_lval_list_nth(args, 0));
  float y = valk_to_double(valk_lval_list_nth(args, 1));
  player.pos = (Vec2){x, y};
  return valk_lval_nil();
}

void game_init() {
  valk = valk_init();
  valk_register_c_function(valk, "set-player-pos", set_player_pos);
  valk_eval_file(valk, "scripts/game_logic.valk", NULL);
}

void game_update() {
  // Call Valk update function
  valk_lval_t* delta_time = valk_from_double(valk, dt);
  valk_call(valk, "on-update", &delta_time, 1);
}
```

#### Use Case 2: Plugin System

```c
// Application with Valk plugins
typedef struct {
  char* name;
  valk_state_t* valk;
} Plugin;

Plugin* load_plugin(const char* path) {
  Plugin* plugin = malloc(sizeof(Plugin));
  plugin->valk = valk_init();
  
  // Load plugin code
  valk_eval_file(plugin->valk, path, NULL);
  
  // Get plugin name
  valk_lval_t* name_val;
  valk_eval_string(plugin->valk, "plugin-name", &name_val);
  plugin->name = strdup(valk_to_string(name_val));
  
  return plugin;
}
```

### Documentation Examples

```lisp
; examples/ffi_example.valk

; Load C math library
(def libm (dlopen "libm.so.6"))

; Register sqrt function
(c-register "sqrt" 
  :lib libm
  :ret-type :double
  :arg-types [:double])

; Use C function
(print (c-call "sqrt" 2.0))  ; => 1.414...

; Call C malloc/free
(c-register "malloc" :ret-type :ptr :arg-types [:long])
(c-register "free" :ret-type :void :arg-types [:ptr])

(def buffer (c-call "malloc" 1024))
; ... use buffer ...
(c-call "free" buffer)
```

### Future Enhancements

1. **Struct marshalling** - Pass/return C structs
2. **Callback support** - C calls Valk functions
3. **Async FFI** - Non-blocking C calls with futures
4. **JIT FFI inlining** - Inline C calls in JIT code
5. **SWIG integration** - Auto-generate bindings
