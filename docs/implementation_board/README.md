# Valkyria Implementation Board

Discrete, actionable tasks organized by roadmap layer. Each file contains detailed tasks for one area of the language implementation.

**Updated**: 2025-12-01

---

## Structure

Each layer file contains:
- **Milestone description** - What unlocks when complete
- **Discrete tasks** - Markdown checkboxes with time estimates
- **Implementation details** - File paths, code snippets, research notes
- **Test requirements** - Validation criteria
- **Dependencies** - What must be complete first

---

## Layers

### [Layer 0: Foundations](layer_0_foundations.md)
**Status**: Partially complete (parser, basic types done)

Remaining work:
- [ ] Rationals (S - 1-3 days)
- [ ] BigNums (M - 1-2 weeks)
- [ ] Unicode support (M - 1-2 weeks)
- [ ] Regex (M - 1-2 weeks)
- [ ] Module system (M - 1-2 weeks)

**Total**: ~2-3 months for full completion

---

### [Layer 1: Evaluation](layer_1_evaluation.md)
**Status**: Complete except macro hygiene

Remaining work:
- [ ] Macro hygiene system (M - 1-2 weeks)

**Total**: ~1-2 weeks

---

### [Layer 2: Memory](layer_2_memory.md)
**Status**: GC and allocators complete, escape analysis partial

Remaining work:
- [ ] Complete escape analysis (S - 1-3 days)
- [ ] Generational GC (L - 2-4 weeks)

**Total**: ~2-5 weeks

---

### [Layer 3: Control Flow](layer_3_control_flow.md)
**Status**: Continuations complete, TCO blocked on compilation

Remaining work:
- [ ] TCO via Valk IR (included in Layer 6)
- [ ] Common Lisp Conditions (M - 1-2 weeks)
- [ ] Restarts (L - 2-4 weeks)

**Total**: ~3-6 weeks

---

### [Layer 4: Concurrency](layer_4_concurrency.md)
**Status**: Futures, promises, work queue complete

Remaining work:
- [ ] Work stealing scheduler (M - 1-2 weeks)
- [ ] Channels (M - 1-2 weeks)
- [ ] Actor model (L - 2-4 weeks)
- [ ] Software Transactional Memory (XL - 4-8 weeks)

**Total**: ~2-4 months

---

### [Layer 5: I/O & Networking](layer_5_io_networking.md)
**Status**: HTTP/2 client complete, server partial

Remaining work:
- [ ] Lisp server API (S - 1-3 days)
- [ ] HTTP routing (M - 1-2 weeks)
- [ ] WebSocket support (M - 1-2 weeks)
- [ ] Streaming (M - 1-2 weeks)

**Total**: ~1-2 months

---

### [Layer 6: Compilation](layer_6_compilation.md)
**Status**: Not started - NEW PRIORITY

Complete pipeline:
- [ ] Valk IR Design (1-2 weeks)
- [ ] AST → Valk IR (2-4 weeks)
- [ ] VIR Optimizations (1-2 weeks)
- [ ] VIR → LLVM (2-4 weeks)
- [ ] JIT/AOT Execution (1-2 weeks)
- [ ] FFI (1-2 weeks)
- [ ] Embedding API (1-2 weeks)

**Total**: ~9-18 weeks (2-4.5 months)
**Tasks**: 113 discrete tasks

---

### [Layer 7: Type System](layer_7_type_system.md)
**Status**: Not started - FUTURE

Complete type system:
- [ ] Type annotations (S - 1-3 days)
- [ ] Type checker (M - 1-2 weeks)
- [ ] Type inference (L - 2-4 weeks)
- [ ] Gradual types (XL - 4-8 weeks)
- [ ] ADTs (M - 1-2 weeks)
- [ ] Pattern matching (M - 1-2 weeks)
- [ ] Exhaustiveness checking (M - 1-2 weeks)

**Total**: ~3-5 months

---

### [Tooling](tooling.md)
**Status**: REPL, logging, tests complete

Remaining work:
- [ ] Tab completion (M - 1-2 weeks)
- [ ] Syntax highlighting (S - 1-3 days)
- [ ] Hot reload (M - 1-2 weeks)
- [ ] Debugger (L - 2-4 weeks)
- [ ] Profiler (L - 2-4 weeks)
- [ ] LSP Server (L - 2-4 weeks)

**Total**: ~2-4 months

---

## Quick Start

### Currently In Progress: **Layer 6 - Compilation**

See [layer_6_compilation.md](layer_6_compilation.md) for 113 discrete tasks.

**Next steps**:
1. Phase 1, Task 1.1: Define IR data structures in `src/vir/vir.h`
2. Read through all Phase 1 tasks (IR Design)
3. Estimate 1-2 weeks for Phase 1 completion

---

## Recommended Work Order

Based on dependencies and value:

1. **Layer 6: Compilation** (HIGH PRIORITY)
   - Unlocks: 10-100x performance, TCO, native binaries
   - Timeline: 2-4.5 months
   - Start here if you want major performance gains

2. **Layer 2: Memory** (MEDIUM PRIORITY)
   - Complete escape analysis (needed for Layer 6)
   - Generational GC (optional optimization)
   - Timeline: 2-5 weeks

3. **Layer 5: I/O & Networking** (MEDIUM PRIORITY)
   - Complete server API for web apps
   - Timeline: 1-2 months

4. **Layer 4: Concurrency** (MEDIUM PRIORITY)
   - Channels for CSP concurrency
   - Actors for Erlang-style concurrency
   - Timeline: 2-4 months

5. **Layer 3: Control Flow** (LOW PRIORITY)
   - Conditions/Restarts for CL-style error handling
   - Timeline: 3-6 weeks

6. **Layer 0: Foundations** (LOW PRIORITY)
   - Nice-to-have features
   - Timeline: 2-3 months

7. **Layer 7: Type System** (FUTURE)
   - Wait until language is stable
   - Timeline: 3-5 months

8. **Tooling** (ONGOING)
   - Can be done in parallel with other work
   - Timeline: 2-4 months

---

## Progress Tracking

### Status Legend
- `[ ]` Not started
- `[~]` In progress
- `[x]` Complete
- `[!]` Blocked
- `[?]` Needs discussion

### Current Sprint
- **Layer**: ___
- **Phase**: ___
- **Tasks this week**: ___

### Velocity
- **Week 1**: ___ tasks completed
- **Week 2**: ___ tasks completed
- ...

### Blockers
- None currently

---

## Resources

### Core Documentation
- [ROADMAP.md](../ROADMAP.md) - High-level tech tree
- [LANGUAGE.md](../LANGUAGE.md) - Language reference
- [CONTRIBUTING.md](../CONTRIBUTING.md) - Development guide

### External References
- Swift SIL: https://github.com/apple/swift/tree/main/docs/SIL.rst
- Rust MIR: https://rustc-dev-guide.rust-lang.org/mir/
- LLVM C API: https://llvm.org/doxygen/group__LLVMC.html
- LLVM GC: https://llvm.org/docs/GarbageCollection.html
- LLVM ORC JIT: https://llvm.org/docs/ORCv2.html
- libffi: https://sourceware.org/libffi/

---

## Contributing

When completing tasks:
1. Check off the task: `- [x]`
2. Add session notes with commit SHA
3. Update velocity tracking
4. Note any blockers discovered

Example:
```markdown
- [x] **1.1: Define IR Data Structures** (2-3 days)
  - **Completed**: 2025-12-05 (commit: abc1234)
  - **Notes**: Added vir_value_t, vir_block_t, vir_function_t
  - **Issues**: None
```
