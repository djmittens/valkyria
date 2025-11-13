# Bytecode VM Design for Valkyria

## Goal
Replace tree-walking interpreter with bytecode VM that provides:
- **True O(1) TCO** - constant memory for tail calls
- **Better performance** - 10-100x faster than tree walking
- **Simpler async** - natural suspend/resume for async/await

## Architecture Overview

### High-Level Flow
```
Source Code → Parser → AST → Compiler → Bytecode → VM → Result
```

### Current vs New
**Current**: `AST → valk_lval_eval(ast)` (tree-walking interpreter)
**New**: `AST → compile(ast) → bytecode → vm_run(bytecode)` (bytecode VM)

## Bytecode Instructions

### Stack-Based VM
Use a value stack + call stack architecture (like Python, Lua, JVM).

```c
typedef enum {
  // Literals
  OP_CONST,      // Push constant from constant pool
  OP_NIL,        // Push nil
  OP_TRUE,       // Push 1 (true)
  OP_FALSE,      // Push 0 (false)
  
  // Variables
  OP_GET_LOCAL,  // Push local variable (by index)
  OP_SET_LOCAL,  // Pop and store to local
  OP_GET_GLOBAL, // Push global variable (by name)
  OP_SET_GLOBAL, // Pop and store to global
  OP_GET_UPVAL,  // Push upvalue (closure capture)
  
  // Arithmetic
  OP_ADD,        // Pop b, pop a, push a+b
  OP_SUB,        // Pop b, pop a, push a-b
  OP_MUL,        // Pop b, pop a, push a*b
  OP_DIV,        // Pop b, pop a, push a/b
  OP_EQ,         // Pop b, pop a, push a==b
  OP_LT,         // Pop b, pop a, push a<b
  OP_GT,         // Pop b, pop a, push a>b
  
  // Control flow
  OP_JUMP,       // Unconditional jump (offset)
  OP_JUMP_IF_FALSE, // Pop value, jump if false
  OP_JUMP_IF_TRUE,  // Pop value, jump if true
  
  // Functions
  OP_CALL,       // Call function (arg count)
  OP_TAIL_CALL,  // Tail call (arg count) - TCO!
  OP_RETURN,     // Return from function
  OP_CLOSURE,    // Create closure (function index)
  
  // Lists
  OP_LIST,       // Create list (element count on stack)
  OP_HEAD,       // Pop list, push head
  OP_TAIL,       // Pop list, push tail
  OP_CONS,       // Pop tail, pop head, push cons
  
  // Other
  OP_POP,        // Discard top of stack
  OP_PRINT,      // Pop and print value
} valk_opcode_e;
```

### Key Insight for TCO: OP_TAIL_CALL

```c
case OP_TAIL_CALL: {
  uint8_t arg_count = READ_BYTE();
  
  // Instead of pushing new call frame, REUSE current frame:
  // 1. Copy arguments to frame's local slots
  // 2. Reset IP to function start
  // 3. DON'T push new frame
  
  valk_lval_t* func = vm->stack[vm->sp - arg_count - 1];
  
  // Reuse current frame
  vm->ip = func->bytecode.code;  // Reset instruction pointer
  // Arguments are already on stack
  // No new call frame = O(1) memory!
  
  break;
}
```

## Data Structures

### VM State
```c
typedef struct {
  uint8_t* ip;              // Instruction pointer
  valk_lval_t** stack;      // Value stack
  size_t sp;                // Stack pointer
  valk_call_frame_t* frames; // Call stack
  size_t frame_count;       // Current frame depth
  valk_lval_t** constants;  // Constant pool
  valk_lenv_t* globals;     // Global environment
} valk_vm_t;
```

### Call Frame
```c
typedef struct {
  uint8_t* return_ip;       // Where to return to
  valk_lval_t** locals;     // Local variables
  size_t stack_offset;      // Where our stack starts
} valk_call_frame_t;
```

### Compiled Function
```c
typedef struct {
  uint8_t* code;            // Bytecode
  size_t code_length;       // Length
  size_t arity;             // Number of parameters
  valk_lval_t** constants;  // Constant pool for this function
  char** local_names;       // Debug info
} valk_bytecode_t;
```

## Compiler

### Compilation Strategy

```lisp
(def {countdown} (\ {n}
  {if (== n 0)
    {0}
    {countdown (- n 1)}}))
```

Compiles to:
```
Function countdown(n):
  Constants: [0, 1]
  
  0000: GET_LOCAL 0        ; n
  0001: CONST 0            ; 0
  0002: EQ                 ; n == 0
  0003: JUMP_IF_FALSE 6    ; if false, skip to else
  0004: CONST 0            ; 0 (true branch)
  0005: RETURN
  
  0006: GET_GLOBAL "countdown"  ; else branch
  0007: GET_LOCAL 0        ; n
  0008: CONST 1            ; 1
  0009: SUB                ; n - 1
  0010: TAIL_CALL 1        ; countdown(n-1) with TCO!
```

Key: Line 0010 uses `TAIL_CALL` instead of `CALL` because it's in tail position!

### Tail Position Detection

During compilation, track whether we're in tail position:
```c
void compile_expr(compiler_t* c, valk_lval_t* expr, bool is_tail) {
  if (is_sexpr(expr)) {
    if (is_if_expr(expr)) {
      compile_if(c, expr, is_tail);  // Pass tail flag to branches
    } else if (is_call(expr)) {
      compile_call(c, expr, is_tail);  // Emit TAIL_CALL if is_tail
    }
  }
}
```

## Implementation Plan

### Phase 1: Core VM (2-3 days)
1. Define bytecode instruction set
2. Implement VM interpreter loop
3. Basic operations: literals, arithmetic, locals
4. Test: `(+ 1 2)` works in bytecode

### Phase 2: Compiler (2-3 days)
1. AST → bytecode compiler
2. Compile functions, calls
3. Tail position detection
4. Test: simple functions compile and run

### Phase 3: TCO (1 day)
1. Implement OP_TAIL_CALL
2. Test: countdown(100000) works with O(1) memory
3. Verify no stack growth, no heap growth

### Phase 4: Full Language (2-3 days)
1. Closures and upvalues
2. Lists and cons operations
3. All builtins
4. Test: full test suite passes

### Phase 5: Integration (1 day)
1. Switch REPL to use bytecode backend
2. Keep AST for now (hybrid mode)
3. Performance benchmarks

**Total Estimate: 1-2 weeks**

## Benefits

1. **True O(1) TCO** - No stack growth, no heap growth for tail calls
2. **10-100x performance** - Direct dispatch vs tree walking
3. **Easier async** - VM can pause/resume between instructions
4. **Better debugging** - Can inspect bytecode, set breakpoints
5. **JIT potential** - Can optimize hot bytecode later

## Compatibility

Keep existing `valk_lval_t` types and APIs:
- Parser still produces AST
- Compiler consumes AST
- VM operates on `valk_lval_t` values
- Builtins remain the same

This is an **implementation change**, not a language change.

## Example: O(1) Memory Proof

```lisp
(countdown 1000000)
```

**Tree-walker** (current):
- Stack: O(1) with our thunk TCO ✓
- Heap: O(n) - creates 1M thunks and 1M numbers ✗
- Time: O(n) overhead from thunk unwrapping

**Bytecode VM**:
- Stack: O(1) - reuses same call frame ✓
- Heap: O(1) - reuses same stack slots ✓  
- Time: O(n) but 10-100x faster than tree-walking

The VM **reuses the same memory** for each iteration!

## Next Steps

1. Create `src/bytecode.h` and `src/vm.h`
2. Implement basic VM loop
3. Write compiler from AST → bytecode
4. Test with countdown
5. Expand to full language

Ready to start?
