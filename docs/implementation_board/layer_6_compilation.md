# Valkyria Compilation Implementation Board

**Strategy**: AST → Valk IR → LLVM IR (inspired by Swift SIL, Rust MIR, Julia IR)

**Timeline**: 9-18 weeks (2-4.5 months) | **Updated**: 2025-12-01

---

## Phase 1: Valk IR Design (1-2 weeks)

### Milestone: IR Specification Complete

**Goal**: Design SSA-based intermediate representation for Valk semantics

#### Tasks

- [ ] **1.1: Define IR Data Structures** (2-3 days)
  - File: `src/vir/vir.h`
  - Define `vir_value_t` (SSA values with opcodes, operands, type tags)
  - Define `vir_block_t` (CFG nodes with predecessor/successor links)
  - Define `vir_function_t` (entry block, parameter list, block array)
  - Add `vir_module_t` (collection of functions, global table)
  - **Research note**: Follow LLVM Value/BasicBlock/Function hierarchy
  - **Implementation**: Use linked lists for instructions within blocks
  - **Memory**: Allocate VIR structures on GC heap for persistence

- [ ] **1.2: Design Instruction Set** (3-4 days)
  - File: `src/vir/vir.h`
  - Define 30-40 opcodes via `vir_opcode_e` enum
  - Constants: `VIR_CONST_NUM`, `VIR_CONST_STR`, `VIR_CONST_NIL`
  - Memory: `VIR_ALLOC`, `VIR_LOAD`, `VIR_STORE`, `VIR_GC_ROOT`
  - Arithmetic: `VIR_ADD`, `VIR_SUB`, `VIR_MUL`, `VIR_DIV`, `VIR_MOD`
  - Comparison: `VIR_EQ`, `VIR_NE`, `VIR_LT`, `VIR_LE`, `VIR_GT`, `VIR_GE`
  - Control: `VIR_BR`, `VIR_BR_IF`, `VIR_SWITCH`, `VIR_RET`
  - Functions: `VIR_CALL`, `VIR_TAIL_CALL`, `VIR_CLOSURE`, `VIR_CLOSURE_CALL`
  - Environment: `VIR_ENV_NEW`, `VIR_ENV_GET`, `VIR_ENV_SET`
  - Continuations: `VIR_CONT_NEW`, `VIR_CONT_CALL`
  - Type ops: `VIR_TYPE_TAG`, `VIR_TYPE_CHECK`, `VIR_CAST`
  - List ops: `VIR_CONS`, `VIR_CAR`, `VIR_CDR`
  - **Research note**: Keep instruction set minimal but complete for Valk semantics
  - **Test**: Write opcode → string conversion for debugging

- [ ] **1.3: Implement IR Builder API** (2-3 days)
  - File: `src/vir/vir_builder.h`, `src/vir/vir_builder.c`
  - Create `vir_builder_t` context (tracks current block, insertion point, SSA counter)
  - Implement `vir_builder_new()`, `vir_builder_free()`
  - Add `vir_builder_set_insert_point(builder, block)`
  - Implement instruction builders: `vir_builder_const_num()`, `vir_builder_add()`, etc.
  - Add CFG builders: `vir_builder_create_block()`, `vir_builder_br()`, `vir_builder_br_if()`
  - Implement SSA value numbering (auto-increment `%0`, `%1`, `%2`, ...)
  - **Research note**: Follow LLVM IRBuilder pattern for consistency
  - **Memory**: Use scratch arena for builder state, GC heap for IR itself

- [ ] **1.4: IR Validation Pass** (1-2 days)
  - File: `src/vir/vir_validate.c`
  - Check all values defined before use (SSA property)
  - Check all blocks have terminator (BR, BR_IF, RET, SWITCH)
  - Check CFG edges consistent (pred/succ match)
  - Check operand counts match opcode requirements
  - Check type consistency (dynamic but track tags)
  - **Test**: Create invalid IR and verify validator catches errors
  - **Output**: Return validation errors with source location

- [ ] **1.5: IR Pretty Printer** (1 day)
  - File: `src/vir/vir_print.c`
  - Implement `vir_print_function(func, FILE*)`
  - Format: `function @name(ptr %x, ptr %y) { ... }`
  - Print basic blocks with labels: `entry:`, `loop:`, `exit:`
  - Print instructions: `%0 = vir.add %x, %y`
  - Print CFG edges: `; predecessors: entry, loop`
  - **Purpose**: Essential for debugging IR generation
  - **Format**: Follow LLVM IR text format conventions

- [ ] **1.6: Build System Integration** (1 day)
  - Update `Makefile`
  - Add `VIR_OBJS = src/vir/vir.o src/vir/vir_builder.o src/vir/vir_print.o src/vir/vir_validate.o`
  - Add target: `build/test_vir` for IR tests
  - Create `test/test_vir.c` skeleton
  - **Test**: Ensure `make clean && make build/test_vir` works

- [ ] **1.7: Basic IR Tests** (1 day)
  - File: `test/test_vir.c`
  - Test: Create function with single const return
  - Test: Create function with arithmetic (add two params)
  - Test: Create function with conditional branch
  - Test: Validate SSA numbering is correct
  - Test: Validate CFG pred/succ links
  - **Run**: `make test` should include VIR tests

---

## Phase 2: AST → Valk IR Lowering (2-4 weeks)

### Milestone: AST Successfully Lowers to VIR

**Goal**: Transform tree-structured AST into SSA-form Valk IR

#### Tasks

- [ ] **2.1: Lowering Infrastructure** (2-3 days)
  - File: `src/vir_lower/ast_to_vir.h`, `src/vir_lower/ast_to_vir.c`
  - Define `ast_lower_context_t` (builder, env stack, break/continue targets)
  - Implement `valk_ast_to_vir(ast) -> vir_function_t*`
  - Add environment stack for scoping (track lexical bindings)
  - Track loop context for break/continue (target blocks)
  - **Research note**: Maintain mapping from AST nodes to VIR instructions for debug info
  - **Memory**: Allocate lowering context on stack, IR on GC heap

- [ ] **2.2: Lower Primitives** (1-2 days)
  - File: `src/vir_lower/ast_to_vir.c`
  - Implement `lower_sexpr(builder, lval)` main dispatcher
  - Case `LVAL_NUM`: emit `VIR_CONST_NUM`
  - Case `LVAL_STR`: emit `VIR_CONST_STR`
  - Case `LVAL_NIL`: emit `VIR_CONST_NIL`
  - Case `LVAL_SYM`: emit `VIR_ENV_GET` (lookup in environment)
  - **Test**: `(+ 1 2)` lowers to const loads + VIR_ADD

- [ ] **2.3: Lower Function Calls** (2-3 days)
  - Handle `LVAL_CONS` for S-expressions
  - Extract function (head) and arguments (tail)
  - Lower function expression to VIR value
  - Lower arguments recursively to VIR values
  - Emit `VIR_CALL` with function + args
  - Handle builtin detection (add, sub, etc.) → intrinsics
  - **Test**: `(foo x y)` lowers to VIR_CALL
  - **Edge case**: Varargs (collect rest params)

- [ ] **2.4: Lower Control Flow** (3-4 days)
  - Implement `lower_if(builder, condition, then_expr, else_expr)`
  - Create three blocks: `then`, `else`, `merge`
  - Emit `VIR_BR_IF` based on condition
  - Lower then/else branches into respective blocks
  - Use phi nodes for merging results (or explicit env passing)
  - Implement `lower_do(builder, exprs)` for sequencing
  - **Research note**: SSA requires phi nodes or explicit variable passing
  - **Test**: `(if (> x 0) 1 -1)` creates proper CFG

- [ ] **2.5: Lower Lambda** (3-4 days)
  - File: `src/vir_lower/ast_to_vir.c`
  - Create new `vir_function_t` for lambda body
  - Add parameters from formals list
  - Lower body into function
  - Emit `VIR_CLOSURE` to create closure object (handled in 2.7)
  - **Test**: `(lambda (x) (+ x 1))` creates function + closure
  - **Note**: Closure conversion happens in separate pass (2.7)

- [ ] **2.6: Lower Let Bindings** (2-3 days)
  - Handle `(let ((x 1) (y 2)) (+ x y))`
  - Lower each binding value
  - Create new environment scope (or use SSA directly)
  - Update environment stack
  - Lower body with new bindings in scope
  - **Decision**: Use SSA values directly or explicit env operations?
  - **Test**: Nested lets with shadowing

- [ ] **2.7: Closure Conversion Pass** (4-5 days)
  - File: `src/vir_lower/closure_conv.h`, `src/vir_lower/closure_conv.c`
  - Implement free variable analysis: `analyze_free_vars(lambda) -> char**`
  - Walk lambda body, find all symbol references
  - Remove symbols defined in formals or local lets
  - Remaining symbols = free variables
  - Implement `vir_closure_convert(builder, lambda, free_vars)`
  - Allocate closure struct: `{ fn_ptr, env[num_free] }`
  - Store function pointer at offset 0
  - Capture each free variable into env array
  - Replace lambda references with closure struct
  - **Research note**: This is lambda lifting - moves free vars to explicit captures
  - **Test**: `(let ((x 1)) (lambda (y) (+ x y)))` captures `x`

- [ ] **2.8: Tail Position Analysis** (2-3 days)
  - File: `src/vir_lower/tail_analysis.h`, `src/vir_lower/tail_analysis.c`
  - Implement `vir_mark_tail_calls(func)`
  - Walk CFG, find all `VIR_RET` instructions
  - Check if return value is a `VIR_CALL`
  - If yes, change to `VIR_TAIL_CALL`
  - Set `func->has_tail_calls = true`
  - **Edge case**: Tail position in if-then-else (both branches)
  - **Test**: `(fun fact (n acc) (if (= n 0) acc (fact (- n 1) (* n acc))))` marks recursive call as tail
  - **Validation**: Run test suite, ensure tail calls identified correctly

- [ ] **2.9: Lower Continuations** (5-6 days) **[OPTIONAL - Can defer]**
  - File: `src/vir_lower/cps_transform.h`, `src/vir_lower/cps_transform.c`
  - Implement CPS transformation for `LVAL_CONT`
  - Convert continuation to state machine
  - Each continuation point = new basic block
  - Store continuation state in heap-allocated struct
  - Emit `VIR_CONT_NEW` to create continuation
  - Emit `VIR_CONT_CALL` to resume
  - **Research note**: This is complex - can be deferred to Phase 3
  - **Alternative**: Keep tree-walker for continuations initially

- [ ] **2.10: Integration Tests** (2-3 days)
  - File: `test/test_ast_to_vir.c`
  - Test: Lower arithmetic: `(+ (* 2 3) 4)` → VIR
  - Test: Lower function: `(fun add (x y) (+ x y))` → VIR
  - Test: Lower recursion: `(fun fib (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))`
  - Test: Lower closure: `(let ((x 10)) (lambda (y) (+ x y)))`
  - Test: Print VIR for each, manually verify correctness
  - **Run**: `make test` includes AST→VIR tests

---

## Phase 3: Valk IR Optimizations (1-2 weeks)

### Milestone: VIR Optimized Before LLVM

**Goal**: Apply language-specific optimizations at VIR level

#### Tasks

- [ ] **3.1: Escape Analysis Infrastructure** (2-3 days)
  - File: `src/vir_opt/vir_escape.h`, `src/vir_opt/vir_escape.c`
  - Complete existing escape analysis (currently 3/6 tests pass)
  - Implement `vir_escape_analysis(func)`
  - Build use-def chains for all values
  - Track uses: returned, stored to heap, captured in closure
  - **Algorithm**: Mark `VIR_ALLOC` as `VIR_FLAG_STACK_ALLOC` if doesn't escape
  - **Test**: Fix failing escape analysis tests in `test/test_escape.valk`

- [ ] **3.2: Stack Promotion** (1-2 days)
  - File: `src/vir_opt/vir_escape.c`
  - For allocations marked `VIR_FLAG_STACK_ALLOC`:
  - Change allocation from heap → stack representation
  - Add metadata for stack slot size
  - **Benefit**: Eliminates GC pressure for temporary allocations
  - **Test**: Verify promoted allocations don't trigger GC

- [ ] **3.3: Inlining Pass** (3-4 days)
  - File: `src/vir_opt/vir_inline.h`, `src/vir_opt/vir_inline.c`
  - Implement `vir_inline_functions(func, threshold)`
  - Find all `VIR_CALL` sites
  - Check callee size (instruction count)
  - If < threshold (e.g., 10 instructions), inline
  - Clone callee blocks into caller
  - Update CFG edges (rewire branches)
  - Replace call with inlined code
  - **Research note**: Be careful with recursive functions (don't inline)
  - **Test**: Small helper functions get inlined

- [ ] **3.4: Dead Code Elimination** (2-3 days)
  - File: `src/vir_opt/vir_dce.h`, `src/vir_opt/vir_dce.c`
  - Implement `vir_dce(func)` - dead code elimination
  - Mark phase: Start from function return, mark all used values
  - Sweep phase: Remove unmarked instructions
  - Remove unreachable blocks (no predecessors)
  - **Test**: Unused variables eliminated
  - **Test**: Unreachable if-branches removed

- [ ] **3.5: Constant Folding** (1-2 days)
  - File: `src/vir_opt/vir_fold.c`
  - Implement `vir_constant_fold(func)`
  - Find arithmetic ops with constant operands
  - Evaluate at compile time: `VIR_ADD(1, 2)` → `VIR_CONST_NUM(3)`
  - Replace instruction with constant
  - **Test**: `(+ 1 2)` becomes `3` at VIR level

- [ ] **3.6: Optimization Pipeline** (1-2 days)
  - File: `src/vir_opt/vir_optimize.h`, `src/vir_opt/vir_optimize.c`
  - Create `vir_optimize(func, level)` with optimization levels
  - Level 0: No optimization
  - Level 1: Constant folding, DCE
  - Level 2: + Inlining, escape analysis
  - Level 3: + Aggressive inlining
  - Run optimizations in order (some enable others)
  - **Test**: Verify optimization level flags work

- [ ] **3.7: Optimization Tests** (1-2 days)
  - File: `test/test_vir_opt.c`
  - Test: Constant folding reduces arithmetic
  - Test: Dead code removed
  - Test: Small functions inlined
  - Test: Stack promotion for local allocations
  - **Validation**: Print VIR before/after optimization

---

## Phase 4: Valk IR → LLVM Lowering (2-4 weeks)

### Milestone: VIR Successfully Lowers to LLVM IR

**Goal**: Translate Valk IR to LLVM IR with proper calling conventions

#### Tasks

- [ ] **4.1: LLVM Setup** (1-2 days)
  - Install: `sudo apt install llvm-dev libllvm15 llvm-15-dev` (or latest)
  - Update `Makefile`:
    - Add `LLVM_CFLAGS = $(shell llvm-config --cflags)`
    - Add `LLVM_LDFLAGS = $(shell llvm-config --ldflags --libs core orcjit native)`
  - Test: Compile simple LLVM C API program
  - **Files**: Create `src/llvm/` directory

- [ ] **4.2: Value Representation Design** (2-3 days)
  - File: `src/llvm/vir_to_llvm.h`
  - Design tagged union for dynamic values
  - Option A: `struct { i64 tag; i64 data; }` (simple, 16 bytes)
  - Option B: `struct { i8 tag; union { i64 num; ptr str; ... } }` (complex, varies)
  - **Decision**: Use Option A for simplicity (tag + data as i64)
  - Define type tags: `TAG_NUM=0, TAG_STR=1, TAG_FUN=2, TAG_NIL=3, ...`
  - **Research note**: Julia uses tagged unions, NumPy uses tagged pointers
  - **Test**: Create LLVM struct type for valk value

- [ ] **4.3: LLVM Lowering Infrastructure** (2-3 days)
  - File: `src/llvm/vir_to_llvm.h`, `src/llvm/vir_to_llvm.c`
  - Implement `vir_to_llvm_module(vir_funcs, num_funcs) -> LLVMModuleRef`
  - Create LLVM context and module
  - Define value type globally (struct type)
  - Map VIR functions to LLVM functions
  - Create `vir_to_llvm_context_t` to track mappings
  - **Test**: Create empty LLVM module

- [ ] **4.4: Lower VIR Values** (2-3 days)
  - Implement `lower_value(ctx, vir_value) -> LLVMValueRef`
  - Case `VIR_CONST_NUM`: create `{ TAG_NUM, num_value }` constant struct
  - Case `VIR_CONST_STR`: create global string, return `{ TAG_STR, ptr }`
  - Case `VIR_CONST_NIL`: return `{ TAG_NIL, 0 }`
  - **Test**: Lower constants to LLVM

- [ ] **4.5: Lower Functions** (3-4 days)
  - Implement `lower_function(ctx, vir_func) -> LLVMValueRef`
  - Create LLVM function with proper signature
  - Signature: `valk_value* func(valk_value* arg0, valk_value* arg1, ...)`
  - Create basic blocks for each VIR block
  - Map VIR block → LLVM basic block
  - **Test**: Create LLVM function skeleton

- [ ] **4.6: Lower Arithmetic** (2-3 days)
  - Implement lowering for `VIR_ADD`, `VIR_SUB`, `VIR_MUL`, `VIR_DIV`
  - Extract tag from operands (check type)
  - Extract data field (i64)
  - Perform operation (LLVMBuildAdd, etc.)
  - Create result value (tagged union)
  - **Edge case**: Type errors (non-numbers) → runtime error
  - **Test**: `(+ 1 2)` compiles and executes correctly

- [ ] **4.7: Lower Control Flow** (2-3 days)
  - Case `VIR_BR`: emit `LLVMBuildBr`
  - Case `VIR_BR_IF`: extract condition, emit `LLVMBuildCondBr`
  - Case `VIR_RET`: emit `LLVMBuildRet`
  - Case `VIR_SWITCH`: emit `LLVMBuildSwitch` with cases
  - **Test**: Conditional code compiles correctly

- [ ] **4.8: Lower Function Calls** (3-4 days)
  - Case `VIR_CALL`: emit `LLVMBuildCall2`
  - Extract function pointer from closure struct
  - Pass arguments (already lowered to LLVM values)
  - Set calling convention: `LLVMSetInstructionCallConv(call, LLVMCCallConv)`
  - **Test**: Function calls work

- [ ] **4.9: Implement TCO with musttail** (2-3 days)
  - Case `VIR_TAIL_CALL`: emit `LLVMBuildCall2` + mark as tail
  - Call `LLVMSetTailCallKind(call, LLVMTailCallKindMustTail)`
  - Verify calling conventions match (required for musttail)
  - **Research note**: musttail guarantees TCO, unlike plain tail call hint
  - **Test**: Recursive function doesn't overflow stack
  - **Validation**: Run factorial with large N (e.g., 100000)

- [ ] **4.10: GC Integration - Stack Maps** (4-5 days)
  - File: `src/llvm/llvm_gc.h`, `src/llvm/llvm_gc.c`
  - Case `VIR_ALLOC`: emit call to `valk_gc_alloc`
  - Insert gc.statepoint for GC safepoint
  - Use `gc.relocate` for live pointers after potential GC
  - Mark function with GC strategy: `LLVMSetGC(func, "statepoint-example")`
  - **Research note**: LLVM's statepoint system generates stack maps automatically
  - **Alternative**: Use shadow stack (simpler but slower)
  - **Test**: Allocation triggers GC, stack pointers updated correctly
  - **Documentation**: Read https://llvm.org/docs/GarbageCollection.html

- [ ] **4.11: Lower Closures** (3-4 days)
  - Case `VIR_CLOSURE`: allocate struct, store fn_ptr + captures
  - Case `VIR_CLOSURE_CALL`: load fn_ptr, call with closure as context
  - Use LLVM struct types for closure representation
  - **Test**: Closure captures free variables correctly

- [ ] **4.12: LLVM Lowering Tests** (2-3 days)
  - File: `test/test_vir_to_llvm.c`
  - Test: Lower arithmetic to LLVM, verify IR
  - Test: Lower function, compile with LLVM, execute
  - Test: Lower tail call, verify musttail in IR
  - Test: Lower closure, verify struct layout
  - **Tool**: Use `llvm-dis` to inspect generated LLVM IR

---

## Phase 5: Execution Backends (1-2 weeks)

### Milestone: JIT and AOT Compilation Working

**Goal**: Execute compiled code via JIT and AOT

#### Tasks

- [ ] **5.1: LLVM JIT (ORC) Infrastructure** (3-4 days)
  - File: `src/llvm/llvm_jit.h`, `src/llvm/llvm_jit.c`
  - Include `<llvm-c/LLJIT.h>`, `<llvm-c/OrcEE.h>`
  - Implement `valk_jit_init() -> valk_jit_t*`
  - Create `LLVMLLJITRef` via `LLVMOrcCreateLLJIT`
  - Store in `valk_jit_t` struct with context and target data
  - **Research note**: ORC JIT is newer, simpler than legacy MCJIT
  - **Test**: Initialize JIT, verify no errors

- [ ] **5.2: JIT Compilation** (2-3 days)
  - Implement `valk_jit_eval(jit, ast) -> valk_lval_t*`
  - Pipeline: AST → VIR → Optimize → LLVM IR
  - Add LLVM module to JIT via `LLVMOrcLLJITAddLLVMIRModule`
  - Look up function via `LLVMOrcLLJITLookup`
  - Cast address to function pointer, call
  - **Test**: Evaluate `(+ 1 2)` via JIT, get 3

- [ ] **5.3: REPL JIT Integration** (2-3 days)
  - File: `src/repl.c`
  - Add `--jit` flag to enable JIT mode
  - Initialize JIT in REPL startup
  - Route evaluation through JIT when enabled
  - Keep tree-walker as fallback (graceful degradation)
  - **Test**: `./build/valk --jit` runs REPL with JIT

- [ ] **5.4: AOT Compiler Infrastructure** (2-3 days)
  - File: `src/compiler/valk_aot.h`, `src/compiler/valk_aot.c`
  - Implement `valk_compile_aot(input_file, output_file, opt_level)`
  - Pipeline: Parse → AST → VIR → Optimize → LLVM
  - Create LLVM target machine for host architecture
  - **Test**: Compile hello world program to object file

- [ ] **5.5: LLVM Optimization Passes** (1-2 days)
  - Create pass manager: `LLVMPassManagerRef pm = LLVMCreatePassManager()`
  - Add standard passes:
    - `LLVMAddInstructionCombiningPass(pm)` - Simplify instructions
    - `LLVMAddReassociatePass(pm)` - Reassociate expressions
    - `LLVMAddGVNPass(pm)` - Global value numbering
    - `LLVMAddCFGSimplificationPass(pm)` - Simplify CFG
  - Run: `LLVMRunPassManager(pm, module)`
  - **Test**: Compare IR before/after optimization

- [ ] **5.6: Object File Emission** (1-2 days)
  - Implement `emit_object_file(module, output_path)`
  - Use `LLVMTargetMachineEmitToFile(target, module, path, LLVMObjectFile, &error)`
  - **Test**: Generate `.o` file, inspect with `objdump`

- [ ] **5.7: Native Linking** (1-2 days)
  - Create runtime library: `libvalk_runtime.a`
  - Include GC, builtins, prelude
  - Link object file with runtime: `gcc program.o -L./build -lvalk_runtime -o program`
  - **Test**: Compile and run standalone binary

- [ ] **5.8: Debug Info (DILocation)** (2-3 days)
  - File: `src/llvm/llvm_debug.c`
  - Create debug info builder: `LLVMDIBuilderRef di = LLVMCreateDIBuilder(module)`
  - Create compile unit: `LLVMDIBuilderCreateCompileUnit(...)`
  - For each function: `LLVMDIBuilderCreateFunction(...)`
  - For each instruction: `LLVMSetCurrentDebugLocation2(builder, line, col, scope)`
  - Finalize: `LLVMDIBuilderFinalize(di)`
  - **Test**: Compile with `-g`, use `gdb` to inspect source lines

- [ ] **5.9: Compiler Driver** (2 days)
  - File: `src/compiler/valk_compiler.c`
  - Create `valkc` executable (compiler driver)
  - Commands:
    - `valkc compile file.valk -o program` - AOT compile
    - `valkc run file.valk` - JIT execute
    - `valkc emit-llvm file.valk -o file.ll` - Output LLVM IR
  - **Test**: All commands work

- [ ] **5.10: Performance Benchmarks** (1-2 days)
  - File: `bench/bench_compilation.valk`
  - Benchmark: Tree-walker vs JIT vs AOT
  - Test programs: Fibonacci, prime sieve, map/filter
  - Measure: Execution time, memory usage
  - **Expected**: JIT 5-10x faster, AOT 10-50x faster
  - **Document**: Results in `docs/BENCHMARKS.md`

---

## Phase 6: FFI (Foreign Function Interface) (1-2 weeks)

### Milestone: C Interop Working

**Goal**: Call C functions from Valk, bidirectional interop

#### Tasks

- [ ] **6.1: FFI Infrastructure** (2-3 days)
  - Install: `sudo apt install libffi-dev`
  - File: `src/ffi/ffi.h`, `src/ffi/ffi.c`
  - Include `<ffi.h>`, `<dlfcn.h>`
  - Define `valk_ffi_type_e` enum (INT, LONG, DOUBLE, PTR, VOID, STRUCT)
  - Define `valk_ffi_fn_t` struct (fn_ptr, ret_type, arg_types, ffi_cif)
  - Create global FFI registry (hash table: name → valk_ffi_fn_t)
  - **Test**: Registry add/lookup works

- [ ] **6.2: Function Registration** (2-3 days)
  - Implement `valk_ffi_register(name, fn_ptr, ret_type, arg_types, num_args)`
  - Convert valk_ffi_type_e → ffi_type* (libffi types)
  - Call `ffi_prep_cif(&cif, FFI_DEFAULT_ABI, num_args, ret_type, arg_types)`
  - Store in registry
  - **Test**: Register `printf`, verify CIF prepared correctly

- [ ] **6.3: Type Marshalling** (3-4 days)
  - File: `src/ffi/ffi_types.h`, `src/ffi/ffi_types.c`
  - Implement `valk_to_c_value(valk_lval_t*, ffi_type) -> void*`
  - Case LVAL_NUM → int/long/double
  - Case LVAL_STR → char*
  - Case LVAL_REF → void*
  - Implement `c_to_valk_value(void*, ffi_type) -> valk_lval_t*`
  - **Test**: Round-trip conversion works

- [ ] **6.4: C Call Builtin** (2-3 days)
  - Implement `valk_builtin_c_call(env, args)`
  - Parse: `(c-call "function-name" arg1 arg2 ...)`
  - Look up function in registry
  - Marshal arguments: Valk → C
  - Call via libffi: `ffi_call(&cif, fn_ptr, ret_val, c_args)`
  - Marshal return: C → Valk
  - **Test**: `(c-call "printf" "Hello %d\n" 42)` prints correctly

- [ ] **6.5: Dynamic Library Loading** (1-2 days)
  - Implement `valk_builtin_dlopen(env, args)` → `(dlopen "libc.so.6")`
  - Call `dlopen(path, RTLD_LAZY)`, return handle as LVAL_REF
  - Implement `valk_builtin_dlsym(env, args)` → `(dlsym handle "symbol")`
  - Call `dlsym(handle, name)`, return ptr as LVAL_REF
  - **Test**: Load libc, look up malloc/free, call them

- [ ] **6.6: FFI in Valk IR** (2 days)
  - Add `VIR_FFI_CALL` opcode to `vir_opcode_e`
  - Lower `(c-call ...)` to `VIR_FFI_CALL` in AST→VIR pass
  - Store function pointer and type info in instruction
  - **Test**: C calls lower to VIR correctly

- [ ] **6.7: FFI in LLVM** (2-3 days)
  - Case `VIR_FFI_CALL` in LLVM lowering
  - Create LLVM function type matching C ABI
  - Create function pointer constant
  - Emit `LLVMBuildCall2` with `LLVMCCallConv`
  - Marshal arguments before call
  - Marshal return after call
  - **Test**: C call compiles to LLVM correctly

- [ ] **6.8: FFI Cache** (1-2 days)
  - File: `src/ffi/ffi_cache.c`
  - Cache function pointers after first lookup (avoid dlsym overhead)
  - Use hash table: (lib_handle, symbol_name) → fn_ptr
  - **Performance**: First call slow (dlsym), subsequent fast (cached)

- [ ] **6.9: Common C Functions** (1 day)
  - File: `src/modules/c_ffi.valk`
  - Pre-register common C functions:
    - Memory: malloc, free, calloc, realloc
    - I/O: printf, fprintf, fopen, fclose, fread, fwrite
    - String: strlen, strcmp, strcpy, strcat
    - Math: sqrt, sin, cos, pow, exp, log
  - **Test**: Import `c-ffi` module, call pre-registered functions

- [ ] **6.10: FFI Tests** (1-2 days)
  - File: `test/test_ffi.c`, `test/test_ffi.valk`
  - Test: Call printf from Valk
  - Test: Call malloc/free
  - Test: Call math functions (sqrt, pow)
  - Test: Load custom shared library
  - **Validation**: All FFI tests pass

---

## Phase 7: Embedding API (1-2 weeks)

### Milestone: Valk Embeddable in C/C++

**Goal**: Public C API for embedding Valk in applications

#### Tasks

- [ ] **7.1: Public API Design** (1-2 days)
  - File: `src/embed/valk_embed.h` (public header)
  - Define `valk_state_t` (opaque pointer)
  - Declare functions:
    - `valk_state_t* valk_init()`
    - `void valk_shutdown(valk_state_t*)`
    - `int valk_eval_string(valk_state_t*, const char* code, valk_lval_t** result)`
    - `int valk_eval_file(valk_state_t*, const char* filename, valk_lval_t** result)`
    - `valk_lval_t* valk_call(valk_state_t*, const char* fn_name, valk_lval_t** args, size_t num_args)`
    - `int valk_register_c_function(valk_state_t*, const char* name, valk_lval_builtin_t* fn)`
  - **Note**: Keep API minimal and stable

- [ ] **7.2: State Management** (2-3 days)
  - File: `src/embed/valk_state.c`
  - Define `struct valk_state_t`:
    - `valk_lenv_t* global_env`
    - `valk_gc_malloc_heap_t* heap`
    - `valk_mem_arena_t* scratch`
    - `valk_jit_t* jit` (optional)
    - `bool jit_enabled`
  - Implement `valk_init()`:
    - Initialize heap (16MB threshold, 64MB limit)
    - Initialize scratch (1MB)
    - Create global environment with builtins
    - Optionally initialize JIT (check VALK_JIT env var)
  - Implement `valk_shutdown()`:
    - Destroy JIT
    - Destroy heap
    - Free scratch
  - **Test**: Init/shutdown without leaks

- [ ] **7.3: Eval from C** (2-3 days)
  - Implement `valk_eval_string(state, code, result)`
  - Parse code to AST
  - Evaluate via tree-walker or JIT (based on state->jit_enabled)
  - Store result in `*result`
  - Return 0 on success, -1 on error
  - Implement `valk_eval_file(state, filename, result)` similarly
  - **Test**: Evaluate `(+ 1 2)` from C, get 3

- [ ] **7.4: Call Valk from C** (2-3 days)
  - Implement `valk_call(state, fn_name, args, num_args)`
  - Look up function in global environment
  - Build argument list (array → cons list)
  - Call via `valk_lval_eval_call`
  - Return result
  - **Test**: Define function in Valk, call from C

- [ ] **7.5: Register C Functions** (1-2 days)
  - Implement `valk_register_c_function(state, name, fn)`
  - Wrap builtin function in LVAL_FUN
  - Add to global environment
  - **Test**: Register C function, call from Valk

- [ ] **7.6: Value Conversion Helpers** (2 days)
  - File: `src/embed/valk_values.c`
  - Implement extractors:
    - `long valk_to_long(valk_lval_t*)`
    - `double valk_to_double(valk_lval_t*)`
    - `const char* valk_to_string(valk_lval_t*)`
    - `void* valk_to_ptr(valk_lval_t*)`
  - Implement constructors:
    - `valk_lval_t* valk_from_long(valk_state_t*, long)`
    - `valk_lval_t* valk_from_double(valk_state_t*, double)`
    - `valk_lval_t* valk_from_string(valk_state_t*, const char*)`
    - `valk_lval_t* valk_from_ptr(valk_state_t*, void*)`
  - **Test**: Round-trip conversions work

- [ ] **7.7: Build Shared Library** (1-2 days)
  - Update `Makefile`:
    - `libvalk.so: $(VALK_OBJS)`
    - `$(CC) -shared -o $@ $^ $(LDFLAGS)`
  - Create pkg-config file: `valk.pc`
  - **Test**: Link example program against libvalk.so

- [ ] **7.8: Installation** (1 day)
  - Add `make install` target:
    - Install `libvalk.so` to `$(PREFIX)/lib`
    - Install `valk_embed.h` to `$(PREFIX)/include`
    - Install `valk.pc` to `$(PREFIX)/lib/pkgconfig`
  - **Default prefix**: `/usr/local`
  - **Test**: Install, build external program using installed lib

- [ ] **7.9: Example Programs** (2-3 days)
  - File: `examples/embed_demo.c`
  - Example 1: Evaluate expression from C
  - Example 2: Call Valk function from C
  - Example 3: Register C function, call from Valk
  - Example 4: Game scripting (player movement)
  - Example 5: Plugin system (load Valk plugins)
  - **Documentation**: Comment examples thoroughly

- [ ] **7.10: Embedding Documentation** (2 days)
  - File: `docs/EMBEDDING.md`
  - Write tutorial:
    - Getting started (init/shutdown)
    - Evaluating code
    - Calling functions
    - Type conversion
    - Error handling
    - Thread safety (note: currently single-threaded)
  - Include all examples
  - API reference (all functions)
  - **Test**: Follow tutorial step-by-step, verify works

---

## Integration & Testing

### Cross-Phase Tasks

- [ ] **INT-1: End-to-End Test Suite** (3-4 days)
  - File: `test/test_compilation_e2e.c`
  - Test 1: Fibonacci (tree-walker vs JIT vs AOT)
  - Test 2: Prime sieve
  - Test 3: Map/filter/reduce
  - Test 4: Tail-recursive factorial (large N)
  - Test 5: Closure capturing
  - Test 6: FFI calling C
  - Test 7: Embedding (C calls Valk)
  - **Validation**: All execution paths produce same result

- [ ] **INT-2: Memory Leak Testing** (2 days)
  - Run all tests under Valgrind
  - Check: No leaks from GC heap
  - Check: No leaks from LLVM JIT
  - Check: No leaks from FFI
  - Fix any leaks found
  - **Command**: `valgrind --leak-check=full ./build/valk`

- [ ] **INT-3: Performance Profiling** (2-3 days)
  - Use `perf` to profile JIT compilation
  - Use `gprof` to profile AOT execution
  - Identify hotspots
  - Optimize critical paths
  - **Target**: JIT compile time < 100ms for small programs

- [ ] **INT-4: Documentation Completion** (3-4 days)
  - Update `README.md` with compilation features
  - Complete `docs/LANGUAGE.md` with examples
  - Write `docs/COMPILER.md` (architecture overview)
  - Write `docs/FFI.md` (FFI guide)
  - Update `docs/CONTRIBUTING.md` (VIR development)
  - **Test**: Have someone unfamiliar follow docs

- [ ] **INT-5: CI/CD Setup** (2 days)
  - Create `.github/workflows/test.yml`
  - Run tests on: Ubuntu, macOS
  - Test matrix: gcc, clang
  - Check: Build succeeds, all tests pass
  - **Bonus**: Cache LLVM installation for faster CI

---

## Migration Path

### Gradual Transition

- [ ] **MIG-1: Feature Flag for JIT** (1 day)
  - Add `--jit` flag to REPL and compiler
  - Default: tree-walker (stable)
  - Optional: `--jit` (experimental)
  - **Test**: Both modes work side-by-side

- [ ] **MIG-2: Performance Comparison** (2 days)
  - Run benchmark suite with both modes
  - Document performance gains
  - Identify any JIT correctness issues
  - Fix JIT bugs before making default

- [ ] **MIG-3: Make JIT Default** (1 day)
  - Change default to JIT
  - Add `--no-jit` flag for tree-walker fallback
  - Update documentation
  - **Timeline**: After Phase 5 complete and tested

- [ ] **MIG-4: Deprecate Tree-Walker** (1 day)
  - Mark tree-walker as deprecated
  - Document: "Use for debugging only"
  - Keep code for now (useful for comparison)
  - **Timeline**: After 1-2 months of stable JIT

- [ ] **MIG-5: Remove Tree-Walker** (1 day) **[OPTIONAL - Far future]**
  - Remove `valk_lval_eval` tree-walker code
  - Clean up AST evaluation
  - **Benefit**: Simpler codebase
  - **Risk**: Lose reference implementation
  - **Decision**: Maybe keep tree-walker forever as fallback

---

## Progress Tracking

### Status Legend
- `[ ]` Not started
- `[~]` In progress
- `[x]` Complete
- `[!]` Blocked
- `[?]` Needs discussion

### Current Phase: **Phase 0 - Preparation**

### Velocity Tracking
- **Week 1**: __ tasks completed
- **Week 2**: __ tasks completed
- **Week 3**: __ tasks completed
- ...

### Blockers
- None currently

### Notes
- Add session notes here
- Link to commits
- Track issues discovered

---

## Resources

### Knowledge Base References
- Swift SIL: https://github.com/apple/swift/tree/main/docs/SIL.rst
- Rust MIR: https://rustc-dev-guide.rust-lang.org/mir/
- LLVM C API: https://llvm.org/doxygen/group__LLVMC.html
- LLVM GC: https://llvm.org/docs/GarbageCollection.html
- LLVM ORC JIT: https://llvm.org/docs/ORCv2.html
- libffi: https://sourceware.org/libffi/

### Implementation Sessions
- **Session 1**: [Date] - [Tasks completed] - [Notes/commits]
- **Session 2**: [Date] - [Tasks completed] - [Notes/commits]
- ...

---

**Last Updated**: 2025-12-01
**Total Tasks**: 113 compilation tasks + additional layers below
**Estimated Completion**: Varies by layer (see timeline for each)
