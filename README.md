# Valkyria

A statically-typed Lisp designed for rapid prototyping of systems, featuring built-in concurrency primitives, asynchronous I/O, and HTTP/2 networking support.

## 🚀 Quick Start

```bash
# Build the project
make build

# Run the REPL
./build/valk

# Run tests
make test

# Run a script
./build/valk script.valk
```

## 📊 Project Status

**Overall Completion: 75-80% (Experimental - No Production Validation)**

| Component | Status | Notes |
|-----------|--------|-------|
| Core Language | 🟡 90% | Parser, evaluator, REPL working - unvalidated |
| Memory/GC | 🟡 95% | Mark & sweep GC implemented - untested at scale |
| Networking | 🟡 75% | HTTP/2 works, needs Lisp integration |
| Type System | 🔴 0% | Planned for Phase 2 |
| Standard Library | 🟡 70% | Core functions implemented - needs battle testing |

**⚠️ Important**: No components are production-ready. The language needs validation through building substantial applications (game engine, CI system, or web service) before any features can be considered stable.

## 🎯 Features

- **REPL-Centric Development** - Interactive development with hot reload
- **Memory Safe** - Sophisticated 3-tier memory management with GC
- **Async I/O** - Futures and promises for concurrent operations
- **HTTP/2 Native** - Built-in networking with TLS support
- **Lisp Syntax** - S-expressions with planned type annotations

## 📚 Documentation

**Start Here**:
- [Master Plan](docs/MASTER_PLAN.md) - What to build next
- [Implementation Checklist](docs/IMPLEMENTATION_CHECKLIST.md) - Detailed task list

**Reference**:
- [Technical Roadmap](docs/TECHNICAL_ROADMAP_WIKI.md) - Complete vision
- [Architecture Overview](docs/ARCHITECTURE_OVERVIEW.md) - System design
- [Quick Reference](docs/QUICK_REFERENCE.md) - Commands and status

## 🔧 Development

**Current Branch**: `networking` (Phase 1 - 75% complete)

### Building from Source

```bash
# Install dependencies
make configure

# Build with tests
make build

# Debug build
make debug

# Run linters
make lint
```

### Example Code

```lisp
; Define a function
(fun {factorial n}
  {if (<= n 1)
    {1}
    {* n (factorial (- n 1))}})

(factorial 5)  ; Returns 120

; Future HTTP server (when networking complete)
(def {server}
  (http2/listen aio "127.0.0.1" 8080
    "server.key" "server.crt"
    (fn {req}
      {http2/response :status 200
                     :body "Hello, World!"})))
```

## 🗺️ Roadmap

1. **Phase 1: Networking** (Current - 75%)
2. **Phase 2: Type System** (Next)
3. **Phase 3: Protocol Support** (Protobuf/gRPC)
4. **Phase 4: Garbage Collection** (95% Complete!)
5. **Phase 5: Rich REPL/TUI**
6. **Phase 6: Embeddability**
7. **Phase 7: Self-Hosting**

## 🤝 Contributing

**How to contribute**:
1. Read [SESSION_GUIDE.md](SESSION_GUIDE.md) - How to pick up work
2. Check [docs/IMPLEMENTATION_CHECKLIST.md](docs/IMPLEMENTATION_CHECKLIST.md) - Find next task
3. Follow [CLAUDE.md](CLAUDE.md) - For AI assistant usage

**Quick start**: Next task is Phase 0.1 Tail Call Optimization (BLOCKING)

## 📄 License

MIT (pending confirmation)

## 🔗 Links

- [Documentation Index](docs/)
- [Current Sprint Tasks](docs/NETWORKING_BRANCH_TASKS.md)
- [Game Engine Path](docs/GAME_ENGINE_PATH.md)
- [CI System Path](docs/CI_SYSTEM_PATH.md)