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
                     │              (75+ C fns)               (variable args)          (collect rest)
                     │
                     └──────> [###] Lambda (\\) ───────> [###] fun macro ───────> [## ] Macros
                                    (anonymous fn)            (named fns)              (hygiene: M)

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 2: MEMORY
═══════════════════════════════════════════════════════════════════════════════════════════════

  [###] Allocators ──┬──────> [###] Arena ────────────> [###] Scratch Arena ───> [###] Checkpoint
        (636 LOC)    │              (bump alloc)              (REPL only)              (evacuation)
                     │
                     ├──────> [###] Slab ─────────────> [###] Lock-free Freelist
                     │              (fixed blocks)            (Treiber stack)
                     │
                     └──────> [###] GC Heap ──────────> [###] Mark & Sweep ────> [   ] Generational
                                    (643 LOC)                 (stop-world)             (L)

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
                     ├──────> [###] HTTP/2 Server ────> [###] Load Shedding ────> [   ] Routing
                     │              (C API works)             (backpressure)            (M)
                     │
                     └──────> [   ] WebSocket ────────> [   ] Streaming
                                    (M)                       (M)

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 6: COMPILATION (FUTURE)
═══════════════════════════════════════════════════════════════════════════════════════════════

                     ┌────────────────────────────────────────────────────────────────────────┐
                     │  UNLOCKS: TCO, 10-100x Performance, JIT, Native Binaries              │
                     │  STRATEGY: AST → Valk IR → LLVM IR (like Swift/Rust/Julia)            │
                     └────────────────────────────────────────────────────────────────────────┘

  [   ] Valk IR Design ───> [   ] AST → Valk IR ───> [   ] VIR Optimizations ───> [   ] LLVM Backend
        (M)                       (L)                      (M)                          (L)

  See: implementation_board/layer_6_compilation.md for detailed breakdown

═══════════════════════════════════════════════════════════════════════════════════════════════
 LAYER 7: TYPE SYSTEM (FUTURE)
═══════════════════════════════════════════════════════════════════════════════════════════════

  [   ] Type Annotations ───> [   ] Type Checker ─────> [   ] Type Inference ──> [   ] Gradual Types
        (syntax: S)                 (M)                       (L)                      (XL)

═══════════════════════════════════════════════════════════════════════════════════════════════
 TOOLING
═══════════════════════════════════════════════════════════════════════════════════════════════

  [###] REPL ────────┬──────> [###] History ──────────> [   ] Tab Completion ──> [   ] Syntax Highlight
        (editline)   │              (editline)                (M)                      (S)
                     │
                     ├──────> [###] Load Files ───────> [   ] Hot Reload
                     │              (load builtin)            (M)
                     │
                     └──────> [###] Test Framework ───> [###] test/suite ───────> [###] test/skip
                                    (Lisp-based)              (define, run)            (skip reason)

  [###] C Tests ─────┬──────> [###] testing.{c,h} ────> [###] ASSERT macros
        (framework)  │              (framework)               (PASS/FAIL)

  [###] Logging ─────┬──────> [###] Log Levels ───────> [###] VALK_LOG env var
        (log.{c,h})  │              (ERROR→TRACE)             (runtime config)
                     │
                     └──────> [###] Stack Traces ─────> [###] libbacktrace
                                    (debug.{c,h})             (symbols)

  [###] Metrics ─────┬──────> [###] JSON Export ──────> [###] Prometheus Export
        (observability)             (vm/metrics-json)         (vm/metrics-prometheus)

```

---

## Feature Status Summary

### Complete

| Layer | Features |
|-------|----------|
| 0: Foundations | Parser, S/Q-expressions, numbers, strings, symbols |
| 1: Evaluation | Tree-walker, environments, closures, 75+ builtins |
| 2: Memory | Scratch arena with checkpoint, slab allocator, mark & sweep GC |
| 3: Control Flow | Continuations (shift/reset), async patterns, error handling |
| 4: Concurrency | Thread pool, futures, promises, ARC boxes |
| 5: I/O | libuv backend, HTTP/2 client+server, TLS, load shedding |
| Tooling | REPL, test frameworks, logging, metrics |

### In Progress

| Feature | Status | Next Step |
|---------|--------|-----------|
| Namespaces | Basic parsing works | Module system |
| Macros | Works, no hygiene | Hygiene system |
| HTTP Server Lisp API | C API complete | Lisp bindings |

### Blocked

| Feature | Blocker | Unlocks |
|---------|---------|---------|
| TCO | Needs compilation | Deep recursion, FP idioms |
| LLVM Backend | Design work needed | 10-100x performance |

---

## Critical Paths

### Path A: Performance (LLVM)

```
[###] Tree-Walker → [   ] Valk IR → [   ] LLVM Backend → TCO + JIT + AOT
```

### Path B: Type Safety

```
[###] Parser → [   ] Type Annotations → [   ] Type Checker → [   ] Inference
```

### Path C: Production Tooling

```
[###] REPL → [   ] Hot Reload → [   ] Debugger → [   ] LSP
```

---

## Technical Debt

Run `make todo` to see current TODOs for your branch.

---

## Documentation

- **[features/](features/)** - Implemented feature documentation
- **[LANGUAGE.md](LANGUAGE.md)** - Language reference
- **[CONTRIBUTING.md](CONTRIBUTING.md)** - Development guide
- **[implementation_board/](implementation_board/)** - Detailed task breakdown by layer
