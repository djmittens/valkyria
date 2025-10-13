# This is title
- [ ] VM
    - [ ] Memory
        - [ ] Mark / Sweep GC
            - Ok so the heap for lisp should be considered dynamic, meaning i
            cant predict how it can shrink / grow 
                - How can i expose memory management for the lisp? can i do
                some sort of a thing where i let it execute, and not have to
                garbage collect? bump alloc or something
                - I could just use dynamic (eg malloc) for the heap, and not
                think about it.
                - Its not going to be performant but itll work.
                - For anything lisp based thats how we can operate by default,
                and then optimize specific things into pools like lets say
                LVALs and such
        - [ ] LVAL Arenas
            - Only make sense if i introduce something to lvals that will make
            their initialization or destruction heavy.
            - This can be supported by my threadsafe slab allocator [ ] GC? (do
            i need this part ?)
        - [ ] Stack alloc
    - [ ] Eval
    - [ ] Stats
    - [ ] Debugger
    - [ ] Optimizer (JIT?)
    - [ ] JIT
- [ ] Dictionaries
- [x] Testing
    - [x] C Runtime testing
    - [ ] Native Valk Language testing
- [x] Symbolizer support for stack traces
- [ ] Runtime Asserts
- [ ] Remove Readline from repl
- [ ] Windows support
- [ ] LLVM IR compiler
    - [ ] JIT
- [ ] Single place for build time configuration
    - [ ] Turning ASAN on / off
    - [ ] Controlling module specific config, such as max number of concurrent
    requests
        - [ ] AIO / HTTP config
        - [ ] Test config (eg. Fork or not to fork)
    - [ ] Toolchain config, eg target windows + clang vs linux + clang
- [ ] Regular Expressions
- [ ] Boostrap
- [ ] Telemetry
- [ ] Optimization
- [ ] LSP
- [ ] Parser Combinators
- [ ] Strict Types
- [ ] Monads
- [ ] Valgrind So for this thing ... since im using clang, combination of asan
and lsan could be enough ON linux and mac, valgrind doesnt work.  Unless I run
everything through docker since manjaro dont support it
- [ ] gRPC
- [ ] Thrift
- [ ] Centralize memory management in `memory.h` i have a bunch of
`//NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)`
all over the place, but thats because memory handling is not centralized and
considered unsafe, i need a containment zone for this code

## Subtitle or something Doing something ### more stuff


## Mark / Sweep
create lval
>> marked

do some calculations

sweep
>> unmarked



