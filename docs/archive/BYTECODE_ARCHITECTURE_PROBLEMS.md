# Bytecode VM Architecture Problems

## Current Mess

### Problem 1: Builtins Get Wrong Environment
**Location:** bc_vm.c:439
```c
valk_lval_t* result = func->fun.builtin(vm->globals, args);
```

**Issue:** Builtins always receive `vm->globals`, never the local frame environment. This means:
- `async-reset` inside a lambda can't access lambda locals
- `eval` can't see local variables
- Any builtin that needs lexical scope is broken

### Problem 2: Upvalue Capture is Hacky
**Location:** bc_vm.c:242-306 (OP_CLOSURE)

**Issue:** Upvalues are captured through a complex bytecode dance:
- Compiler tracks upvalues separately from locals
- OP_CLOSURE has special encoding with is_local flags
- Each closure has its own upvalue array
- This is overly complex for what should be simple lexical scope

**Why This Exists:** Because we don't have proper environment chaining.

### Problem 3: Special Cases Everywhere in Compiler
**Locations:**
- compiler.c:500-623: Separate `def` vs `=` handling
- compiler.c:284-310: Lambda body multi-statement detection
- parser.c:1867-1905: `eval` multi-statement detection
- parser.c:2386-2429: `async-reset` multi-statement detection

**Issue:** Same logic duplicated in multiple places because there's no clean separation between:
- What should be a compiler special form
- What should be a builtin function
- What should be VM-level primitives

### Problem 4: No Proper Environment Chaining
**What We Have:**
- Stack slots for locals (in call frames)
- Upvalue arrays for captures
- Global environment (lenv)

**What's Missing:**
- Each frame should have its own lexical environment (lenv)
- Environments should chain to parent (like standard Lisp)
- No need for separate upvalue mechanism

## Clean Architecture

### Solution 1: Frame-Local Environments

Each call frame should have its own environment that chains to the caller's environment:

```c
typedef struct {
  uint8_t* ip;                    // Return address
  valk_lval_t** slots;            // Stack slots (for args)
  int slot_count;
  valk_chunk_t* chunk;            // Calling chunk
  valk_lenv_t* env;               // LOCAL ENVIRONMENT <-- ADD THIS
} valk_bc_call_frame_t;
```

### Solution 2: Environment Creation on Function Call

When calling a function:
1. Create new environment with parent = caller's env (or globals for top-level)
2. Bind parameters in the new environment
3. Pass THIS environment to builtins, not vm->globals

```c
// On function call:
valk_lenv_t* call_env = valk_lenv_new();
call_env->parent = vm->frame_count > 0 ?
  vm->frames[vm->frame_count - 1].env : vm->globals;

// Bind parameters
for (int i = 0; i < arity; i++) {
  valk_lenv_put(call_env, param_name[i], arg_values[i]);
}

frame->env = call_env;
```

### Solution 3: Pass Frame Environment to Builtins

```c
// OLD (BROKEN):
valk_lval_t* result = func->fun.builtin(vm->globals, args);

// NEW (CORRECT):
valk_lenv_t* call_env = vm->frame_count > 0 ?
  vm->frames[vm->frame_count - 1].env : vm->globals;
valk_lval_t* result = func->fun.builtin(call_env, args);
```

### Solution 4: Remove Upvalue Mechanism

Once we have environment chaining:
- Closures automatically capture their defining environment
- No need for OP_CLOSURE complexity
- No need for upvalue tracking in compiler
- Lambda compilation becomes simpler

### Solution 5: Unify def and =

With proper environments:
- `def` creates binding in root/global env: `valk_lenv_def(env, sym, val)`
- `=` creates binding in current env: `valk_lenv_put(env, sym, val)`
- No need for OP_SET_LOCAL vs OP_SET_GLOBAL distinction
- Compiler doesn't need to track locals separately

## Implementation Plan

1. **Add env to call frames** - Modify valk_bc_call_frame_t
2. **Create env on call** - In OP_CALL, create chained environment
3. **Pass env to builtins** - Fix builtin calls to use frame env
4. **Remove upvalue mechanism** - Delete OP_CLOSURE complexity, use env capture
5. **Simplify compiler** - Remove local tracking, just emit SET/GET with symbol names
6. **Unify def/=** - Single code path, different builtin functions

## Benefits

- ✅ Builtins can access local variables (fixes async-reset bug)
- ✅ No special case logic for multi-statement bodies
- ✅ Simpler compiler (no local/upvalue tracking)
- ✅ Standard Lisp semantics
- ✅ Easier to understand and maintain
- ✅ No weird capture groups

## Trade-offs

- **Performance:** Environment lookup is slower than stack slot indexing
- **Memory:** Each frame needs an environment (more allocations)

**Counter-argument:**
- We already have lenv implementation
- We can optimize hot paths later
- Correctness > premature optimization
- Current "optimization" is broken anyway
