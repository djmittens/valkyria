# Valkyria Vision

## Purpose

Valkyria is a statically-typed Lisp designed for **rapid prototyping of systems**. It enables fast iteration on high-level features like CI pipelines, API composition, and interactive system development while maintaining memory safety and type safety.

## Core Principles

1. **REPL-Centric Development**: The REPL is the primary development environment and must never crash
2. **Memory Safe**: Arena-first allocation with GC safety net
3. **Type Safe**: Static types with inference for compile-time guarantees
4. **Protocol Native**: First-class support for protobufs, gRPC, and Thrift
5. **Embeddable**: Minimal dependencies, portable to any platform
6. **Self-Bootstrapped**: Compiler, tools, and stdlib eventually written in Valkyria

## Target Use Cases

- **Systems Scripting**: CI/CD pipelines, deployment automation, infrastructure management
- **API Development**: Rapid prototyping of microservices and distributed systems
- **Game Prototyping**: Embedded scripting for game engines
- **Interactive Development**: Live coding with hot reload and self-modifying code

## Target Platforms

- Linux, macOS, Windows (in priority order)
- Web browsers (WebAssembly)
- Web servers
- Mobile (iOS, Android)
- Embedded in game engines and other applications

## Technical Architecture

### The Unkillable REPL

**Critical Constraint**: The REPL must never crash. All user code runs in a sandboxed environment where errors are recoverable.

**Architecture**:
```
┌─────────────────────────────────────┐
│   REPL TUI (Supervisor Process)     │
│   - Always running                   │
│   - Profiler/debugger UI             │
│   - Test runner UI                   │
│   - Type inspector                   │
│   - Network inspector                │
└─────────────┬───────────────────────┘
              │ IPC (Unix socket/pipe)
┌─────────────▼───────────────────────┐
│   Evaluator Worker Process           │
│   - Executes user code               │
│   - Sandboxed with resource limits   │
│   - Can crash and restart            │
│   - Preserves environment state      │
└──────────────────────────────────────┘
```

**Safety Mechanisms**:
- Signal handlers catch crashes (SIGSEGV, SIGABRT)
- Resource limits (memory, CPU, stack depth)
- Watchdog timers for hung evaluations
- State preservation across crashes
- Versioned definitions for hot reload

### Memory Management

**Strategy**: Arena-first with GC for heap

- **Arenas**: Explicit allocation for structured lifetimes (request handlers, script execution)
- **GC Heap**: Automatic collection for unbounded data (closures, long-lived structures)
- **Reference Counting**: Deterministic cleanup where needed
- **Compiler Hints**: Allocation site analysis (arena vs heap)

**Implementation**:
- Generational GC (young/old generation)
- Incremental collection (no long pauses)
- Write barriers for cross-allocator references
- Arena size limits with graceful failure

### Type System

**Model**: Static types with Hindley-Milner inference

- **Type Syntax**: `(: name Type)` or `(define (foo [x: Int] [y: String]) -> Bool ...)`
- **Type Inference**: Unification-based, minimal annotations required
- **Type Features**:
  - Sum types (variants/tagged unions)
  - Product types (records/structs)
  - Type aliases
  - Generic types (parametric polymorphism)
  - Effect types (for I/O, mutation tracking)

**Gradual Migration**:
- `:Any` escape hatch for untyped code
- Type-check at compile time, not runtime
- Strict mode eventually required

### Protocol-Native Support

**Schema Integration**: Protobufs and Thrift schemas are first-class language constructs

```lisp
; Import generates types + serialization
(import-proto "api/user.proto")

; Native message construction
(def user (User :name "alice" :id 123))

; Type-safe RPC calls
(grpc/call service-client "GetUser" {:id 123})
```

**Features**:
- Schema parser (`.proto`, `.thrift`)
- Automatic type generation
- Zero-copy serialization where possible
- gRPC client/server
- Thrift RPC support
- Schema validation at compile-time

### Async I/O & Concurrency

**Model**: Futures and promises with structured concurrency

- **Futures**: Represent pending computations
- **Async/Await**: Syntax sugar for future composition
- **Work Queue**: Thread pool for concurrent execution
- **Channels**: CSP-style message passing
- **Actors**: Lightweight processes (future)

**Current Implementation**:
- libuv-based I/O event loop
- HTTP/2 with nghttp2
- TLS with OpenSSL
- Pluggable backends (epoll, kqueue, io_uring planned)

### Language Features

**Current (Dynamic Lisp)**:
- S-expressions
- First-class functions, closures
- Lexical scoping
- Macros
- Reference types

**Planned (Static + Modern)**:
- Type annotations and inference
- Pattern matching
- Module system
- Better literals (maps, sets, vectors)
- Syntax sugar for common patterns
- Conditions (restartable errors)

## Development Roadmap

### Phase 1: Networking Foundation (Current)

**Goal**: Stable HTTP server/client API in Lisp

**Deliverables**:
- HTTP server with request handlers
- HTTP client returning futures
- Test framework in Lisp
- Error handling (no crashes)
- Basic REPL safety mechanisms
- Network inspector in REPL

**Foundations Established**:
- Async I/O patterns
- Concurrency primitives
- Testing infrastructure
- Error recovery

### Phase 2: Type System

**Goal**: Add static types with inference

**Deliverables**:
- Type syntax for Lisp
- Type inference engine
- Type checker integrated with compiler
- Typed prelude/stdlib
- Type-aware REPL

**Benefits**:
- Catch errors at compile-time
- Enable protocol integration
- Better tooling (IDE support)
- Foundation for optimization

### Phase 3: Protocol Support

**Goal**: Native protobufs/gRPC/Thrift

**Deliverables**:
- Schema parsers
- Type generation from schemas
- gRPC client/server
- Thrift RPC support
- Schema validation

**Use Cases Enabled**:
- API development and composition
- Microservices prototyping
- Cross-language interop

### Phase 4: Real Garbage Collection

**Goal**: Production-ready GC

**Deliverables**:
- Generational GC implementation
- Incremental collection
- Allocator integration (arenas + GC)
- Performance benchmarks
- Tuning parameters

**Benefits**:
- Memory safety without manual management
- Easier programming model
- Long-running processes

### Phase 5: Rich REPL/TUI

**Goal**: Feature-complete interactive development environment

**Deliverables**:
- TUI with multiple panes
- Integrated debugger (step, inspect, breakpoints)
- Profiler (CPU, memory, allocations)
- Test runner with coverage
- Network inspector
- Hot reload system
- Definition browser
- Documentation viewer

**Experience**:
- Never leave the REPL
- Interactive development workflow
- Self-modifying code with safety
- Visual feedback on system state

### Phase 6: Embeddability & Portability

**Goal**: Run everywhere

**Deliverables**:
- Optional dependencies (pure C implementations)
- WebAssembly target
- Mobile builds (iOS/Android)
- Clean C embedding API
- Sandboxing/resource limits for embedded use
- Reduced runtime for constrained platforms

**Platforms Unlocked**:
- Browsers
- Mobile apps
- Game engines
- Embedded systems

### Phase 7: Self-Hosting

**Goal**: Compiler and tools in Valkyria

**Deliverables**:
- Parser in Valkyria
- Type checker in Valkyria
- Compiler in Valkyria
- Build system
- Package manager
- LSP server
- Standard library expansion

**Benefits**:
- Dogfooding
- Easier language evolution
- Better tooling
- Community contributions

## Design Decisions

### Error Handling: Conditions

Valkyria uses a condition system (Common Lisp style) for error handling:

```lisp
; Signal a condition
(error 'http-error :status 404 :message "Not found")

; Handle with restarts
(handler-case
  (http/get "http://example.com")
  (http-error (e)
    (use-restart 'retry)     ; Or: (use-restart 'use-cached)
    ))

; Define restarts
(with-restarts
  [(retry [] (http/get url))
   (use-cached [] (cache/get url))]
  (risky-operation))
```

**Why**: Enables REPL recovery - when error occurs, user can inspect state and choose how to continue without unwinding stack.

### Syntax Evolution

Evolve S-expressions with modern conveniences:

```lisp
; Better literals
{:key "value" :count 42}           ; Maps
#{1 2 3}                           ; Sets
[1 2 3]                           ; Vectors

; Type annotations
(: name String)
(define (handler [req: Request]) -> Response
  {:status 200 :body "ok"})

; Pattern matching
(match response
  [{:ok value} (process value)]
  [{:error reason} (log reason)])

; Syntax sugar
(-> value
    (transform)
    (process)
    (finalize))                    ; Threading macro

(async
  (let [user (await (db/get-user id))
        posts (await (db/get-posts user))]
    (render posts)))              ; Async/await
```

### Dependencies

**Current**: Focus on features first
- nghttp2 (HTTP/2)
- libuv (async I/O)
- OpenSSL (TLS)
- libedit (readline)
- libbacktrace (debugging)

**Future**: Make optional
- Pure C HTTP/2 implementation
- Pluggable I/O backends (epoll, kqueue, IOCP)
- Optional TLS (mbedtls, bearssl)
- Compile-time feature flags

## Success Metrics

### Developer Experience
- Time from idea to working prototype (minutes, not hours)
- REPL uptime (days of continuous development)
- Hot reload success rate (>99%)
- Error recovery rate (100% - never lose work)

### Performance
- Startup time (<100ms)
- Request latency (comparable to Go/Node.js)
- Memory efficiency (arena allocation, low GC overhead)
- Compilation speed (fast feedback loop)

### Portability
- Supported platforms (8+)
- Binary size (minimal runtime)
- Dependency count (optional only)
- Build time (fast, minimal toolchain)

## Community & Ecosystem

**Future Goals**:
- Package manager and repository
- Standard library modules
- Documentation generator
- Tutorial and examples
- Editor plugins (VS Code, Emacs, Vim)
- Online playground (REPL in browser)

---

**Status**: Phase 1 (Networking Foundation) in progress
**License**: MIT (or to be determined)
**Repository**: https://github.com/[user]/valkyria
