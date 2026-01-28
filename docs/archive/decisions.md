# Technical Decisions

## Why Shift/Reset Instead of Futures/ARCs?

### Problems with ARCs
- Atomic operations on every retain/release (overhead)
- Callbacks can't capture Lisp closures properly
- Reference cycles never collected
- Complex lifetime management

### Benefits of Continuations
- Just GC'd values (no reference counting)
- Natural lexical scope capture
- Compose like regular functions
- Simple "pause and resume" mental model

## Why Bytecode Compiler?

### Current Performance
- Interpreter is slow for compute-heavy tasks
- Tree-walking evaluation has overhead
- No optimization opportunities

### Bytecode Benefits
- 10-100x performance improvement
- Enables future JIT compilation
- Better cache locality
- Optimization passes possible

## Why These Phases?

### Phase 0 First (Continuations)
- Blocks all async development
- Simplifies entire codebase
- Foundation for everything else

### Phase 1 Next (Networking)
- Validates continuation design
- Enables real applications
- Most user-visible feature

### Phase 2 Then (Bytecode)
- Performance needed for production
- Builds on stable foundation
- Can optimize continuation ops

### Phase 3 Last (Ecosystem)
- Needs stable core first
- Can iterate based on usage
- Community can contribute

## Architecture Principles

1. **Simplicity over cleverness**
   - Continuations are simpler than ARCs
   - GC handles all memory

2. **Composability**
   - Everything is a value
   - Functions compose naturally

3. **Performance when needed**
   - Interpreter for development
   - Bytecode for production

4. **Gradual enhancement**
   - Each phase stands alone
   - Can ship after any phase