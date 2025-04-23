# This is title
- [ ] Dictionaries
- [x] Testing
- [ ] Runtime Asserts
- [ ] Remove Readline from repl
- [ ] Memory
    - [ ] Arenas
    - [ ] GC
- [ ] LLVM IR compiler
    - [ ] JIT
- [ ] Regular Expressions
- [ ] Boostrap
- [ ] VM
- [ ] Telemetry
- [ ] Optimization
- [ ] LSP
- [ ] Parser Combinators
- [ ] Strict Types
- [ ] Monads
- [ ] Valgrind
     So for this thing ... since im using clang, combination of asan and lsan could be enough
     ON linux and mac, valgrind doesnt work.  Unless I run everything through docker since manjaro dont support it
- [ ] gRPC
- [ ] Thrift
- [ ] Centralize memory management in `memory.h`
    i have a bunch of  `//NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)`
    all over the place, but thats because memory handling is not centralized and
    considered unsafe, i need a containment zone for this code

## Subtitle or something
Doing something
### more stuff
