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
 LAYER 6: COMPILATION (FUTURE)
═══════════════════════════════════════════════════════════════════════════════════════════════

                     ┌────────────────────────────────────────────────────────────────────────┐
                     │  UNLOCKS: TCO, 10-100x Performance, JIT, Native Binaries              │
                     └────────────────────────────────────────────────────────────────────────┘

  [   ] Bytecode ────┬──────> [   ] Instruction Set ──> [   ] Compiler ────────> [   ] Optimizer
        Design (M)   │              (opcodes: M)              (AST->BC: L)             (L)
                     │
                     ├──────> [   ] Stack Machine ────> [   ] Eval Stack ──────> [   ] TCO
                     │              (L)                       (frames: M)              (M) ←── UNBLOCKED!
                     │
                     └──────> [   ] LLVM Backend ─────> [   ] IR Generation ───> [   ] JIT
                                    (XL)                      (L)                      (L)

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

### Path A: Performance (TCO → JIT)

```
[###] Tree-Walker
      │
      ▼
[   ] Bytecode Design ───(M)───> [   ] Instruction Set ───(M)───> [   ] Stack Machine ───(L)
                                                                          │
                                                                          ▼
                                                                   [   ] TCO ───(M)
                                                                          │
                                                                          ▼
                                                        [   ] LLVM IR Gen ───(L)───> [   ] JIT ───(L)
```

**Total cost to TCO**: ~L (bytecode + stack machine + TCO impl)
**Total cost to JIT**: ~XL (adds LLVM integration)

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

## Recommended Unlock Order

### Near Term (Next Sprint)

1. **Lisp Server API** [S] - Expose existing C server to Lisp
2. **Test Runner** [M] - Pattern filtering, better output
3. **Namespace cleanup** [S] - Proper module imports

### Medium Term

4. **Bytecode Design** [M] - Design instruction set
5. **Stack Machine** [L] - Explicit eval stack
6. **TCO** [M] - Finally possible!

### Long Term

7. **Type Annotations** [S] - Optional syntax
8. **LLVM Backend** [XL] - Performance
9. **Debugger** [L] - Dev experience

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

Use branch-specific TODOs: `TODO(networking):`, `TODO(llvm):`, `TODO(main):`
