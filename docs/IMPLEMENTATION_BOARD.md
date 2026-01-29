# Valkyria Implementation Board

**This file has been reorganized into a folder structure for better organization.**

## 📁 New Location

See **[docs/implementation_board/](implementation_board/)** for all implementation tasks.

### Quick Links

- **[README.md](implementation_board/README.md)** - Overview and navigation
- **[Layer 0: Foundations](implementation_board/layer_0_foundations.md)** - Rationals, BigNums, Unicode, Regex, Modules
- **[Layer 1: Evaluation](implementation_board/layer_1_evaluation.md)** - Macro hygiene
- **[Layer 2: Memory](implementation_board/layer_2_memory.md)** - Complete escape analysis, Generational GC
- **[Layer 3: Control Flow](implementation_board/layer_3_control_flow.md)** - Conditions, Restarts
- **[Layer 4: Concurrency](implementation_board/layer_4_concurrency.md)** - Work stealing, Channels, Actors, STM
- **[Layer 5: I/O & Networking](implementation_board/layer_5_io_networking.md)** - Server API, Routing, WebSocket, Streaming
- **[Layer 6: Compilation](implementation_board/layer_6_compilation.md)** - **113 tasks** for Valk IR → LLVM pipeline
- **[Layer 7: Type System](implementation_board/layer_7_type_system.md)** - Type annotations, checking, inference, ADTs
- **[Tooling](implementation_board/tooling.md)** - Tab completion, Debugger, Profiler, LSP

---

## Why the Change?

The original single-file board was 800+ lines and only covered compilation (Layer 6).

With all roadmap layers included, the board would be **3000+ lines**, making it difficult to navigate.

The folder structure allows:
- ✅ Separate concerns by layer
- ✅ Easier navigation
- ✅ Better version control diffs
- ✅ Parallel work on different layers
- ✅ Clear progress tracking per layer

---

## Current Priority: Layer 6 - Compilation

See **[layer_6_compilation.md](implementation_board/layer_6_compilation.md)** for 113 discrete tasks.

**Next steps**:
1. Phase 1, Task 1.1: Define IR data structures
2. Estimated timeline: 9-18 weeks (2-4.5 months)
3. Unlocks: 10-100x performance, TCO, JIT, native binaries

---

**Last Updated**: 2025-12-01
