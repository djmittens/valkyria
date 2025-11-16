#include "bc_vm.h"
#include "bytecode.h"
#include "compiler.h"
#include "parser.h"
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Macros for bytecode reading
#define READ_BYTE() (*vm->ip++)
#define READ_SHORT() \
  (vm->ip += 2, (uint16_t)((vm->ip[-2] << 8) | vm->ip[-1]))
#define READ_CONSTANT() (vm->chunk->constants[READ_SHORT()])

// Binary operation macro
#define BINARY_OP(op) \
  do { \
    if (LVAL_TYPE(valk_bc_vm_peek(vm, 0)) != LVAL_NUM || \
        LVAL_TYPE(valk_bc_vm_peek(vm, 1)) != LVAL_NUM) { \
      valk_bc_vm_runtime_error(vm, "Operands must be numbers"); \
      return BC_VM_RUNTIME_ERROR; \
    } \
    long b = valk_bc_vm_pop(vm)->num; \
    long a = valk_bc_vm_pop(vm)->num; \
    valk_bc_vm_push(vm, valk_lval_num(a op b)); \
  } while (0)

void valk_bc_vm_init(valk_bc_vm_t* vm) {
  vm->chunk = NULL;
  vm->ip = NULL;
  vm->stack_top = vm->stack;
  vm->frame_count = 0;
  vm->globals = valk_lenv_empty();
  valk_lenv_builtins(vm->globals);
}

void valk_bc_vm_free(valk_bc_vm_t* vm) {
  // Note: We don't free lval values on the stack because they're managed by GC
  vm->stack_top = vm->stack;
  vm->frame_count = 0;
}

void valk_bc_vm_push(valk_bc_vm_t* vm, valk_lval_t* value) {
  *vm->stack_top = value;
  vm->stack_top++;
}

valk_lval_t* valk_bc_vm_pop(valk_bc_vm_t* vm) {
  vm->stack_top--;
  return *vm->stack_top;
}

valk_lval_t* valk_bc_vm_peek(valk_bc_vm_t* vm, int distance) {
  return vm->stack_top[-1 - distance];
}

void valk_bc_vm_runtime_error(valk_bc_vm_t* vm, const char* format, ...) {
  va_list args;
  va_start(args, format);
  vfprintf(stderr, format, args);
  va_end(args);
  fputs("\n", stderr);

  // TODO: Print stack trace properly
  // The issue is each frame might be from a different chunk
  // For now just show frame count
  if (vm->frame_count > 0) {
    fprintf(stderr, "[%d call frames on stack]\n", vm->frame_count);
  }

  vm->stack_top = vm->stack;
}

valk_bc_vm_result_e valk_bc_vm_run(valk_bc_vm_t* vm, valk_chunk_t* chunk, valk_lenv_t* env) {
  vm->chunk = chunk;
  vm->ip = chunk->code;

  // Create an initial frame with the given environment if not already in a call
  if (vm->frame_count == 0 && env) {
    valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count++];
    frame->chunk = NULL;  // No return point for top-level
    frame->ip = NULL;
    frame->slots = vm->stack;  // Empty stack
    frame->slot_count = 0;
    frame->env = env;
  }

  for (;;) {
#ifdef VALK_DEBUG_TRACE_EXECUTION
    // Print stack contents
    printf("          ");
    for (valk_lval_t** slot = vm->stack; slot < vm->stack_top; slot++) {
      printf("[ ");
      valk_lval_print(*slot);
      printf(" ]");
    }
    printf("\n");
    valk_disassemble_instruction(vm->chunk, (size_t)(vm->ip - vm->chunk->code));
#endif

    uint8_t instruction = READ_BYTE();

    switch (instruction) {
      case OP_CONST: {
        uint16_t const_idx = READ_SHORT();
        if (const_idx >= vm->chunk->const_count) {
          fprintf(stderr, "[ERROR] Constant index %d out of bounds (count=%zu)\n", const_idx, vm->chunk->const_count);
          return BC_VM_RUNTIME_ERROR;
        }
        valk_lval_t* constant = vm->chunk->constants[const_idx];
        if (!constant) {
          fprintf(stderr, "[ERROR] Constant at index %d is NULL\n", const_idx);
          return BC_VM_RUNTIME_ERROR;
        }
        valk_bc_vm_push(vm, constant);
        break;
      }

      case OP_NIL:
        valk_bc_vm_push(vm, valk_lval_nil());
        break;

      case OP_TRUE:
        valk_bc_vm_push(vm, valk_lval_num(1));
        break;

      case OP_FALSE:
        valk_bc_vm_push(vm, valk_lval_num(0));
        break;

      case OP_GET: {
        valk_lval_t* name = READ_CONSTANT();
        if (LVAL_TYPE(name) != LVAL_SYM) {
          valk_bc_vm_runtime_error(vm, "Variable name must be a symbol");
          return BC_VM_RUNTIME_ERROR;
        }
        // Get environment from current frame, fall back to globals
        valk_lenv_t* env = vm->globals;
        if (vm->frame_count > 0) {
          env = vm->frames[vm->frame_count - 1].env;
        }

        valk_lval_t* value = valk_lenv_get(env, name);
        // Check if variable lookup returned an error
        if (LVAL_TYPE(value) == LVAL_ERR) {
          valk_bc_vm_push(vm, value);
          return BC_VM_RUNTIME_ERROR;
        }
        valk_bc_vm_push(vm, value);
        break;
      }

      case OP_LET: {
        valk_lval_t* name = READ_CONSTANT();
        if (LVAL_TYPE(name) != LVAL_SYM) {
          valk_bc_vm_runtime_error(vm, "Variable name must be a symbol");
          return BC_VM_RUNTIME_ERROR;
        }
        valk_lval_t* value = valk_bc_vm_peek(vm, 0);  // Don't pop

        // Put in current frame's environment, fall back to globals
        valk_lenv_t* env = vm->globals;
        if (vm->frame_count > 0) {
          env = vm->frames[vm->frame_count - 1].env;
        }

        valk_lenv_put(env, name, value);
        break;
      }

      case OP_DEF: {
        valk_lval_t* name = READ_CONSTANT();
        if (LVAL_TYPE(name) != LVAL_SYM) {
          valk_bc_vm_runtime_error(vm, "Variable name must be a symbol");
          return BC_VM_RUNTIME_ERROR;
        }
        valk_lval_t* value = valk_bc_vm_peek(vm, 0);  // Don't pop

        // Def in global environment (walk up to root)
        valk_lenv_t* env = vm->globals;
        if (vm->frame_count > 0) {
          env = vm->frames[vm->frame_count - 1].env;
        }

        valk_lenv_def(env, name, value);
        break;
      }

      case OP_ADD:
        BINARY_OP(+);
        break;

      case OP_SUB:
        BINARY_OP(-);
        break;

      case OP_MUL:
        BINARY_OP(*);
        break;

      case OP_DIV: {
        if (LVAL_TYPE(valk_bc_vm_peek(vm, 0)) != LVAL_NUM ||
            LVAL_TYPE(valk_bc_vm_peek(vm, 1)) != LVAL_NUM) {
          valk_bc_vm_runtime_error(vm, "Operands must be numbers");
          return BC_VM_RUNTIME_ERROR;
        }
        long b = valk_bc_vm_pop(vm)->num;
        if (b == 0) {
          valk_bc_vm_runtime_error(vm, "Division by zero");
          return BC_VM_RUNTIME_ERROR;
        }
        long a = valk_bc_vm_pop(vm)->num;
        valk_bc_vm_push(vm, valk_lval_num(a / b));
        break;
      }

      case OP_MOD:
        BINARY_OP(%);
        break;

      case OP_EQ: {
        valk_lval_t* b = valk_bc_vm_pop(vm);
        valk_lval_t* a = valk_bc_vm_pop(vm);
        valk_bc_vm_push(vm, valk_lval_num(valk_lval_eq(a, b) ? 1 : 0));
        break;
      }

      case OP_NE: {
        valk_lval_t* b = valk_bc_vm_pop(vm);
        valk_lval_t* a = valk_bc_vm_pop(vm);
        valk_bc_vm_push(vm, valk_lval_num(valk_lval_eq(a, b) ? 0 : 1));
        break;
      }

      case OP_LT:
        BINARY_OP(<);
        break;

      case OP_LE:
        BINARY_OP(<=);
        break;

      case OP_GT:
        BINARY_OP(>);
        break;

      case OP_GE:
        BINARY_OP(>=);
        break;

      case OP_JUMP_IF_FALSE: {
        uint16_t offset = READ_SHORT();
        valk_lval_t* cond = valk_bc_vm_peek(vm, 0);
        // In Valkyria, 0 is false, everything else is true
        int is_false = (LVAL_TYPE(cond) == LVAL_NUM && cond->num == 0) ||
                       (LVAL_TYPE(cond) == LVAL_NIL);
        if (is_false) {
          vm->ip += offset;
        }
        break;
      }

      case OP_JUMP: {
        uint16_t offset = READ_SHORT();
        vm->ip += offset;
        break;
      }

      case OP_POP:
        valk_bc_vm_pop(vm);
        break;

      case OP_DUP:
        valk_bc_vm_push(vm, valk_bc_vm_peek(vm, 0));
        break;

      case OP_PRINT: {
        valk_lval_println(valk_bc_vm_pop(vm));
        break;
      }

      case OP_CALL: {
        uint8_t arg_count = READ_BYTE();

        // Stack layout: [func, arg1, arg2, ..., argN]
        // func is at position -(arg_count + 1) from top
        valk_lval_t* func = valk_bc_vm_peek(vm, arg_count);

        // Check if it's a builtin function
        if (LVAL_TYPE(func) == LVAL_FUN && func->fun.builtin != NULL) {
          // Call builtin directly
          // Build args list from stack
          valk_lval_t* args = valk_lval_sexpr_empty();
          for (int i = 0; i < arg_count; i++) {
            valk_lval_add(args, valk_bc_vm_peek(vm, arg_count - 1 - i));
          }

          // Pop arguments and function from stack
          for (int i = 0; i <= arg_count; i++) {
            valk_bc_vm_pop(vm);
          }

          // Save VM state before calling builtin (in case it nests valk_bc_vm_run)
          // This is necessary because builtins can call user functions, which may
          // trigger nested bytecode execution that would corrupt vm->chunk and vm->ip
          valk_chunk_t* saved_chunk = vm->chunk;
          uint8_t* saved_ip = vm->ip;

          // Call builtin with closure environment (if available) or global environment
          valk_lenv_t* env = func->fun.env ? func->fun.env : vm->globals;
          valk_lval_t* result = func->fun.builtin(env, args);

          // Restore VM state after builtin call
          vm->chunk = saved_chunk;
          vm->ip = saved_ip;

          // Check if builtin returned an error - if so, propagate it
          if (LVAL_TYPE(result) == LVAL_ERR) {
            valk_bc_vm_push(vm, result);
            return BC_VM_RUNTIME_ERROR;
          }

          // Push result (builtins use the thread-local VM, no thunks needed)
          valk_bc_vm_push(vm, result);
          break;
        }

        // Check if it's a function
        if (LVAL_TYPE(func) != LVAL_FUN) {
          if (LVAL_TYPE(func) == LVAL_ERR) {
            valk_bc_vm_runtime_error(vm, "Can only call functions, got Error: %s", func->str);
          } else {
            valk_bc_vm_runtime_error(vm, "Can only call functions, got: %s", valk_ltype_name(LVAL_TYPE(func)));
          }
          return BC_VM_RUNTIME_ERROR;
        }

        // Check if it has bytecode
        if (func->fun.chunk == nullptr) {
          const char* name = func->fun.name ? func->fun.name : "<unnamed>";
          valk_bc_vm_runtime_error(vm, "Function '%s' has no bytecode chunk in OP_CALL", name);
          return BC_VM_RUNTIME_ERROR;
        }

        // Check arity (negative means variadic)
        if (func->fun.arity >= 0) {
          // Non-variadic: exact match required
          if (func->fun.arity != arg_count) {
            valk_bc_vm_runtime_error(vm, "Expected %d arguments but got %d",
                                     func->fun.arity, arg_count);
            return BC_VM_RUNTIME_ERROR;
          }
        } else {
          // Variadic: arity = -(min_args + 1)
          int min_args = -(func->fun.arity + 1);
          if (arg_count < min_args) {
            valk_bc_vm_runtime_error(vm, "Expected at least %d arguments but got %d",
                                     min_args, arg_count);
            return BC_VM_RUNTIME_ERROR;
          }
        }

        // Check if we have space for a new frame
        if (vm->frame_count >= VALK_FRAMES_MAX) {
          valk_bc_vm_runtime_error(vm, "Stack overflow");
          return BC_VM_RUNTIME_ERROR;
        }

        // Handle variadic arguments
        if (func->fun.arity < 0) {
          // Variadic function: arity = -(min_args + 1)
          int min_args = -(func->fun.arity + 1);
          int extra_args = arg_count - min_args;

          // Create qexpr containing extra args
          valk_lval_t* variadic_list = valk_lval_qexpr_empty();
          for (int i = 0; i < extra_args; i++) {
            // Args are at: stack_top - extra_args + i
            valk_lval_t* arg = *(vm->stack_top - extra_args + i);
            valk_lval_add(variadic_list, arg);
          }

          // Remove extra args from stack
          vm->stack_top -= extra_args;

          // Push the variadic list
          valk_bc_vm_push(vm, variadic_list);

          // Update arg_count to reflect min_args + 1 (for variadic list)
          arg_count = min_args + 1;
        }

        // Push new call frame
        valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count++];
        frame->chunk = vm->chunk;  // Save current chunk
        frame->ip = vm->ip;  // Save return address
        frame->slots = vm->stack_top - arg_count - 1;  // Point to func slot
        frame->slot_count = arg_count + 1;  // func + args

        // Create local environment for parameters
        valk_lenv_t* local_env = valk_lenv_empty();
        local_env->parent = func->fun.env;  // Parent is the closure environment

        // Bind parameters to local environment
        if (func->fun.formals) {
          valk_lval_t* formals = func->fun.formals;
          size_t param_idx = 0;

          for (size_t i = 0; i < valk_lval_list_count(formals); i++) {
            valk_lval_t* formal = valk_lval_list_nth(formals, i);

            // Skip variadic marker
            if (LVAL_TYPE(formal) == LVAL_SYM && strcmp(formal->str, "&") == 0) {
              continue;
            }

            // Bind parameter
            if (LVAL_TYPE(formal) == LVAL_SYM && param_idx < arg_count) {
              valk_lval_t* arg_value = frame->slots[param_idx + 1];  // +1 to skip function
              valk_lenv_put(local_env, formal, arg_value);
              param_idx++;
            }
          }
        }

        frame->env = local_env;  // Set local environment for this call

        // Jump to function code
        vm->chunk = func->fun.chunk;
        vm->ip = func->fun.chunk->code;

        break;
      }

      case OP_TAIL_CALL: {
        uint8_t arg_count = READ_BYTE();

        // Stack layout: [func, arg1, arg2, ..., argN]
        valk_lval_t* func = valk_bc_vm_peek(vm, arg_count);

        // Check if it's a builtin function - tail calls to builtins are just regular calls
        if (LVAL_TYPE(func) == LVAL_FUN && func->fun.builtin != NULL) {
          // Call builtin directly (same as OP_CALL)
          valk_lval_t* args = valk_lval_sexpr_empty();
          for (int i = 0; i < arg_count; i++) {
            valk_lval_add(args, valk_bc_vm_peek(vm, arg_count - 1 - i));
          }

          // Pop arguments and function from stack
          for (int i = 0; i <= arg_count; i++) {
            valk_bc_vm_pop(vm);
          }

          // Save VM state before calling builtin (in case it nests valk_bc_vm_run)
          // This is necessary because builtins can call user functions, which may
          // trigger nested bytecode execution that would corrupt vm->chunk and vm->ip
          valk_chunk_t* saved_chunk = vm->chunk;
          uint8_t* saved_ip = vm->ip;

          // Call builtin with closure environment (if available) or global environment
          valk_lenv_t* env = func->fun.env ? func->fun.env : vm->globals;
          valk_lval_t* result = func->fun.builtin(env, args);

          // Restore VM state after builtin call
          vm->chunk = saved_chunk;
          vm->ip = saved_ip;

          // Check if builtin returned an error - if so, propagate it
          if (LVAL_TYPE(result) == LVAL_ERR) {
            valk_bc_vm_push(vm, result);
            return BC_VM_RUNTIME_ERROR;
          }

          // Push result (builtins use the thread-local VM, no thunks needed)
          valk_bc_vm_push(vm, result);
          break;
        }

        if (LVAL_TYPE(func) != LVAL_FUN) {
          if (LVAL_TYPE(func) == LVAL_ERR) {
            valk_bc_vm_runtime_error(vm, "Can only call functions in tail position, got Error: %s", func->str);
          } else {
            valk_bc_vm_runtime_error(vm, "Can only call functions in tail position, got: %s", valk_ltype_name(LVAL_TYPE(func)));
          }
          return BC_VM_RUNTIME_ERROR;
        }

        // Check if it has bytecode or is a builtin
        if (func->fun.chunk == nullptr && func->fun.builtin == nullptr) {
          const char* name = func->fun.name ? func->fun.name : "<unnamed>";
          valk_bc_vm_runtime_error(vm, "Function '%s' has no bytecode or builtin implementation", name);
          return BC_VM_RUNTIME_ERROR;
        }

        // Check arity (negative means variadic)
        if (func->fun.arity >= 0) {
          // Non-variadic: exact match required
          if (func->fun.arity != arg_count) {
            valk_bc_vm_runtime_error(vm, "Expected %d arguments but got %d",
                                     func->fun.arity, arg_count);
            return BC_VM_RUNTIME_ERROR;
          }
        } else {
          // Variadic: arity = -(min_args + 1)
          int min_args = -(func->fun.arity + 1);
          if (arg_count < min_args) {
            valk_bc_vm_runtime_error(vm, "Expected at least %d arguments but got %d",
                                     min_args, arg_count);
            return BC_VM_RUNTIME_ERROR;
          }
        }

        // Handle variadic arguments
        if (func->fun.arity < 0) {
          // Variadic function: arity = -(min_args + 1)
          int min_args = -(func->fun.arity + 1);
          int extra_args = arg_count - min_args;

          // Create qexpr containing extra args
          valk_lval_t* variadic_list = valk_lval_qexpr_empty();
          for (int i = 0; i < extra_args; i++) {
            // Args are at: stack_top - extra_args + i
            valk_lval_t* arg = *(vm->stack_top - extra_args + i);
            valk_lval_add(variadic_list, arg);
          }

          // Remove extra args from stack
          vm->stack_top -= extra_args;

          // Push the variadic list
          valk_bc_vm_push(vm, variadic_list);

          // Update arg_count to reflect min_args + 1 (for variadic list)
          arg_count = min_args + 1;
        }

        // TAIL CALL OPTIMIZATION: Loop within the same frame
        // Instead of creating a new frame, we:
        // 1. Keep the same frame and environment (preserves access to all vars)
        // 2. The new function and args are already on the stack
        // 3. Update frame->slots to point to the new function
        // 4. Loop by jumping to the new function's code
        // This achieves O(1) space while preserving environment accessibility

        if (vm->frame_count == 0) {
          // Top-level tail call - create initial frame
          valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count++];
          frame->chunk = vm->chunk;  // Save current chunk
          frame->ip = vm->ip;
          frame->slots = vm->stack_top - arg_count - 1;
          frame->slot_count = arg_count + 1;
          frame->env = func->fun.env;

          // Jump to function code
          vm->chunk = func->fun.chunk;
          vm->ip = func->fun.chunk->code;
        } else {
          // TCO: Keep the same frame, just loop with new function
          valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count - 1];

          // Stack layout before TCO:
          // [... old_func old_arg1 old_arg2 ... new_func new_arg1 new_arg2]
          //      ^frame->slots                 ^stack_top - arg_count - 1
          //
          // We need to move the new function and args to where the old function was

          valk_lval_t** new_func_pos = vm->stack_top - arg_count - 1;

          // Move new function and args to the frame's base position
          for (int i = 0; i <= arg_count; i++) {
            frame->slots[i] = new_func_pos[i];
          }

          // Reset stack top to just after the new arguments
          vm->stack_top = frame->slots + arg_count + 1;

          // Update slot count
          frame->slot_count = arg_count + 1;

          // Create NEW local environment for the new function's parameters
          // Keep the SAME parent (closure env) to preserve environment chain
          valk_lenv_t* local_env = valk_lenv_empty();
          local_env->parent = func->fun.env;  // Parent is new function's closure environment

          // Bind new function's parameters to local environment
          if (func->fun.formals) {
            valk_lval_t* formals = func->fun.formals;
            size_t param_idx = 0;

            for (size_t i = 0; i < valk_lval_list_count(formals); i++) {
              valk_lval_t* formal = valk_lval_list_nth(formals, i);

              // Skip variadic marker
              if (LVAL_TYPE(formal) == LVAL_SYM && strcmp(formal->str, "&") == 0) {
                continue;
              }

              // Bind parameter
              if (LVAL_TYPE(formal) == LVAL_SYM && param_idx < arg_count) {
                valk_lval_t* arg_value = frame->slots[param_idx + 1];  // +1 to skip function
                valk_lenv_put(local_env, formal, arg_value);
                param_idx++;
              }
            }
          }

          frame->env = local_env;  // Update to new local environment

          // Loop: Jump to new function's bytecode
          vm->chunk = func->fun.chunk;
          vm->ip = func->fun.chunk->code;
        }

        break;
      }

      case OP_HALT:
        return BC_VM_OK;

      case OP_EVAL: {
        // Pop qexpr from stack, convert to sexpr
        valk_lval_t* qexpr = valk_bc_vm_pop(vm);
        valk_lval_t* sexpr = valk_lval_copy(qexpr);
        sexpr->flags = ((sexpr->flags & LVAL_FLAGS_MASK) | LVAL_SEXPR);

        // Compile the sexpr to bytecode
        // Use is_tail=true since OP_EVAL creates its own call frame
        // The expression will return via OP_RETURN to the caller
        valk_compiler_t eval_compiler;
        valk_compiler_init(&eval_compiler, vm->globals);
        valk_chunk_t* eval_chunk = malloc(sizeof(valk_chunk_t));
        valk_chunk_init(eval_chunk);
        eval_compiler.chunk = eval_chunk;
        valk_compile_expr(&eval_compiler, sexpr, true);  // is_tail = true
        valk_emit_return(&eval_compiler);

        // Create a function that wraps this chunk (no parameters)
        valk_lval_t* eval_fn = valk_lval_lambda(vm->globals,
                                                 valk_lval_qexpr_empty(),
                                                 valk_lval_qexpr_empty());
        eval_fn->fun.chunk = eval_chunk;
        eval_fn->fun.arity = 0;

        // Push the function on the stack (needed for call frame setup)
        valk_bc_vm_push(vm, eval_fn);

        // Create a new call frame for this evaluation
        if (vm->frame_count >= VALK_FRAMES_MAX) {
          fprintf(stderr, "Stack overflow in OP_EVAL\n");
          return BC_VM_RUNTIME_ERROR;
        }

        valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count++];
        frame->chunk = vm->chunk;  // Save current chunk
        frame->ip = vm->ip;  // Save return address
        frame->slots = vm->stack_top - 1;  // Point to function slot
        frame->slot_count = 1;  // Just the function, no args

        // Jump to the compiled bytecode
        vm->chunk = eval_chunk;
        vm->ip = eval_chunk->code;

        break;
      }

      case OP_RETURN: {
        // Pop return value
        valk_lval_t* result = valk_bc_vm_pop(vm);

        // Mark return value as escaping (critical for memory safety)
        result->flags |= LVAL_FLAG_ESCAPES;

        // If no frames or returning from initial frame, we're done
        if (vm->frame_count == 0 || (vm->frame_count == 1 && vm->frames[0].chunk == NULL)) {
          valk_bc_vm_push(vm, result);
          // Clean up the initial frame if it exists
          if (vm->frame_count > 0) {
            vm->frame_count--;
          }
          return BC_VM_OK;
        }

        // Pop call frame
        vm->frame_count--;
        valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count];

        // Restore stack to just before the call
        vm->stack_top = frame->slots;

        // Check if return value is an error - if so, propagate it
        if (LVAL_TYPE(result) == LVAL_ERR) {
          valk_bc_vm_push(vm, result);
          // Restore IP and chunk before returning error
          vm->chunk = frame->chunk;
          vm->ip = frame->ip;
          return BC_VM_RUNTIME_ERROR;
        }

        // Push return value
        valk_bc_vm_push(vm, result);

        // Restore IP and chunk from saved frame
        vm->chunk = frame->chunk;
        vm->ip = frame->ip;

        break;
      }

      default:
        valk_bc_vm_runtime_error(vm, "Unknown opcode %d at offset %ld",
                                 instruction, (long)(vm->ip - vm->chunk->code - 1));
        return BC_VM_RUNTIME_ERROR;
    }
  }

  return BC_VM_OK;
}

// Execute a chunk and return the result value
// This is used for nested execution (e.g., compiling and running thunks)
valk_lval_t* valk_bc_vm_execute_chunk(valk_bc_vm_t* vm, valk_chunk_t* chunk, valk_lenv_t* env) {
  // Save current VM state
  valk_chunk_t* saved_chunk = vm->chunk;
  uint8_t* saved_ip = vm->ip;
  valk_lval_t** saved_stack_top = vm->stack_top;

  // Execute the new chunk
  valk_bc_vm_result_e result = valk_bc_vm_run(vm, chunk, env);

  // Get the result from the stack (should be top value)
  valk_lval_t* return_value = NULL;
  if (result == BC_VM_OK && vm->stack_top > vm->stack) {
    return_value = valk_bc_vm_pop(vm);
  } else if (result != BC_VM_OK) {
    return_value = valk_lval_err("Thunk execution failed");
  } else {
    return_value = valk_lval_nil();
  }

  // Restore VM state
  vm->chunk = saved_chunk;
  vm->ip = saved_ip;
  vm->stack_top = saved_stack_top;

  return return_value;
}
