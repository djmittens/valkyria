# LLVM Compilation Implementation Guide

This document contains detailed implementation notes for the LLVM compilation pipeline (Layer 6).

*Moved from ROADMAP.md to keep the roadmap focused on status tracking.*

## Architecture Overview

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

## Why Valk IR?

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

## File Structure

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

## Valk IR Instruction Set (30-40 opcodes)

See `implementation_board/layer_6_compilation.md` for the complete instruction set specification.

## Performance Expectations

Based on research and similar systems:

- **Tree-walker (current)**: Baseline (1x)
- **Valk IR interpreter**: 2-5x faster (if implemented)
- **LLVM JIT (-O0)**: 5-10x faster
- **LLVM AOT (-O2)**: 10-50x faster
- **LLVM AOT (-O3 + LTO)**: 50-100x faster

## Key Design Decisions

1. **SSA Form**: Valk IR uses SSA like LLVM (easier for optimization)
2. **Closure Conversion**: Done in Valk IR, not in LLVM (language-specific)
3. **Tail Calls**: Marked in Valk IR, enforced with `musttail` in LLVM
4. **GC Integration**: Use LLVM's `gc.statepoint` intrinsics for stack maps
5. **Continuations**: CPS transform in Valk IR → state machine → LLVM functions

## Resources

- **Swift SIL**: https://github.com/apple/swift/tree/main/docs/SIL.rst
- **Rust MIR**: https://rustc-dev-guide.rust-lang.org/mir/
- **LLVM C API**: https://llvm.org/doxygen/group__LLVMC.html
- **LLVM GC**: https://llvm.org/docs/GarbageCollection.html
- **LLVM ORC JIT**: https://llvm.org/docs/ORCv2.html

---

*For detailed code examples, see the archived implementation notes.*
