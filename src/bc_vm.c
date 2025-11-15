#include "bc_vm.h"
#include "bytecode.h"
#include "parser.h"
#include <stdarg.h>
#include <stdio.h>
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

valk_bc_vm_result_e valk_bc_vm_run(valk_bc_vm_t* vm, valk_chunk_t* chunk) {
  vm->chunk = chunk;
  vm->ip = chunk->code;

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
        valk_lval_t* constant = READ_CONSTANT();
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

      case OP_GET_LOCAL: {
        uint8_t slot = READ_BYTE();
        fprintf(stderr, "[DEBUG OP_GET_LOCAL] slot=%d\n", slot);
        // Get from current frame's slots
        if (vm->frame_count > 0) {
          valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count - 1];
          // slot 0 is the function itself, slot 1+ are arguments
          valk_lval_t* value = frame->slots[slot + 1];
          fprintf(stderr, "[DEBUG OP_GET_LOCAL] Retrieved value type=%s\n", valk_ltype_name(LVAL_TYPE(value)));
          valk_bc_vm_push(vm, value);
        } else {
          valk_bc_vm_runtime_error(vm, "No call frame for local access");
          return BC_VM_RUNTIME_ERROR;
        }
        break;
      }

      case OP_SET_LOCAL: {
        uint8_t slot = READ_BYTE();
        valk_lval_t* value = valk_bc_vm_peek(vm, 0);  // Don't pop yet
        if (vm->frame_count > 0) {
          valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count - 1];
          frame->slots[slot + 1] = value;
        } else {
          valk_bc_vm_runtime_error(vm, "No call frame for local access");
          return BC_VM_RUNTIME_ERROR;
        }
        break;
      }

      case OP_GET_GLOBAL: {
        valk_lval_t* name = READ_CONSTANT();
        if (LVAL_TYPE(name) != LVAL_SYM) {
          valk_bc_vm_runtime_error(vm, "Global name must be a symbol");
          return BC_VM_RUNTIME_ERROR;
        }
        valk_lval_t* value = valk_lenv_get(vm->globals, name);
        valk_bc_vm_push(vm, value);
        break;
      }

      case OP_SET_GLOBAL: {
        valk_lval_t* name = READ_CONSTANT();
        if (LVAL_TYPE(name) != LVAL_SYM) {
          valk_bc_vm_runtime_error(vm, "Global name must be a symbol");
          return BC_VM_RUNTIME_ERROR;
        }
        valk_lval_t* value = valk_bc_vm_peek(vm, 0);  // Don't pop
        valk_lenv_def(vm->globals, name, value);
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

        // Debug: what type is func?
        fprintf(stderr, "[DEBUG] OP_CALL: func type=%s, is_builtin=%d\n",
                valk_ltype_name(LVAL_TYPE(func)),
                (LVAL_TYPE(func) == LVAL_FUN) ? (func->fun.builtin != NULL) : 0);

        // Check if it's a builtin function
        if (LVAL_TYPE(func) == LVAL_FUN && func->fun.builtin != NULL) {
          fprintf(stderr, "[DEBUG OP_CALL builtin] Calling builtin (name=%s)\n",
                  func->fun.name ? func->fun.name : "unnamed");
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

          // Call builtin with closure environment (if available) or global environment
          valk_lenv_t* env = func->fun.env ? func->fun.env : vm->globals;
          valk_lval_t* result = func->fun.builtin(env, args);

          // Push result
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

        fprintf(stderr, "[DEBUG OP_CALL] Calling bytecode function with %d args (arity=%d)\n", arg_count, func->fun.arity);

        // Handle variadic arguments
        if (func->fun.arity < 0) {
          // Variadic function: arity = -(min_args + 1)
          int min_args = -(func->fun.arity + 1);
          int extra_args = arg_count - min_args;

          fprintf(stderr, "[DEBUG OP_CALL variadic] min_args=%d, extra_args=%d\n", min_args, extra_args);

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

          fprintf(stderr, "[DEBUG OP_CALL variadic] Packed %d args into variadic list, new arg_count=%d\n", extra_args, arg_count);
        }

        // Push new call frame
        valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count++];
        frame->ip = vm->ip;  // Save return address
        frame->slots = vm->stack_top - arg_count - 1;  // Point to func slot
        frame->slot_count = arg_count + 1;  // func + args

        // Jump to function code
        vm->chunk = func->fun.chunk;
        vm->ip = func->fun.chunk->code;

        fprintf(stderr, "[DEBUG OP_CALL] Jumped to bytecode, first opcode: %d\n", *vm->ip);

        break;
      }

      case OP_TAIL_CALL: {
        uint8_t arg_count = READ_BYTE();

        // Stack layout: [func, arg1, arg2, ..., argN]
        valk_lval_t* func = valk_bc_vm_peek(vm, arg_count);

        fprintf(stderr, "[DEBUG OP_TAIL_CALL] Stack before tail call (arg_count=%d):\n", arg_count);
        for (int i = arg_count; i >= 0; i--) {
          valk_lval_t* item = valk_bc_vm_peek(vm, i);
          fprintf(stderr, "  [%d]: type=%s\n", i, valk_ltype_name(LVAL_TYPE(item)));
          if (LVAL_TYPE(item) == LVAL_ERR) {
            fprintf(stderr, "       error=%s\n", item->str);
          }
        }

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

          // Call builtin with closure environment (if available) or global environment
          valk_lenv_t* env = func->fun.env ? func->fun.env : vm->globals;
          valk_lval_t* result = func->fun.builtin(env, args);

          // Push result
          valk_bc_vm_push(vm, result);
          break;
        }

        if (LVAL_TYPE(func) != LVAL_FUN) {
          if (LVAL_TYPE(func) == LVAL_ERR) {
            fprintf(stderr, "[DEBUG OP_TAIL_CALL] Got error instead of function: %s\n", func->str);
            valk_bc_vm_runtime_error(vm, "Can only call functions in tail position, got Error: %s", func->str);
          } else {
            valk_bc_vm_runtime_error(vm, "Can only call functions in tail position, got: %s", valk_ltype_name(LVAL_TYPE(func)));
          }
          return BC_VM_RUNTIME_ERROR;
        }

        // Check if it has bytecode or is a builtin
        if (func->fun.chunk == nullptr && func->fun.builtin == nullptr) {
          valk_bc_vm_runtime_error(vm, "Function has no bytecode or builtin implementation");
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

        fprintf(stderr, "[DEBUG OP_TAIL_CALL] Tail-calling bytecode function with %d args (arity=%d)\n", arg_count, func->fun.arity);

        // Handle variadic arguments
        if (func->fun.arity < 0) {
          // Variadic function: arity = -(min_args + 1)
          int min_args = -(func->fun.arity + 1);
          int extra_args = arg_count - min_args;

          fprintf(stderr, "[DEBUG OP_TAIL_CALL variadic] min_args=%d, extra_args=%d\n", min_args, extra_args);

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

          fprintf(stderr, "[DEBUG OP_TAIL_CALL variadic] Packed %d args into variadic list, new arg_count=%d\n", extra_args, arg_count);

          // Debug: show stack after packing
          fprintf(stderr, "[DEBUG OP_TAIL_CALL variadic] Stack after packing (arg_count=%d):\n", arg_count);
          for (int i = arg_count; i >= 0; i--) {
            valk_lval_t* item = valk_bc_vm_peek(vm, i);
            fprintf(stderr, "  [%d]: type=%s", i, valk_ltype_name(LVAL_TYPE(item)));
            if (LVAL_TYPE(item) == LVAL_QEXPR) {
              fprintf(stderr, " (qexpr with %zu elements)", valk_lval_list_count(item));
            }
            fprintf(stderr, "\n");
          }
        }

        // TAIL CALL OPTIMIZATION: Reuse the current frame!
        // Instead of pushing a new frame, we:
        // 1. Copy arguments to the current frame's base
        // 2. Reset IP to function start
        // 3. Keep frame_count the same (O(1) space!)

        if (vm->frame_count == 0) {
          // Top-level tail call - treat as regular call
          valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count++];
          frame->ip = vm->ip;
          frame->slots = vm->stack_top - arg_count - 1;
          frame->slot_count = arg_count + 1;
        } else {
          // Reuse current frame
          valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count - 1];

          // Copy func and args to current frame's slots
          valk_lval_t** src = vm->stack_top - arg_count - 1;
          for (int i = 0; i <= arg_count; i++) {
            frame->slots[i] = src[i];
          }

          // Reset stack top to just after the arguments
          vm->stack_top = frame->slots + arg_count + 1;

          // Note: We DON'T save return address - we'll return to the
          // same place the current function would have returned to.
          // This is the key to O(1) space!
        }

        // Jump to function code
        vm->chunk = func->fun.chunk;
        vm->ip = func->fun.chunk->code;

        fprintf(stderr, "[DEBUG OP_TAIL_CALL] Jumped to bytecode, first opcode: %d\n", *vm->ip);

        break;
      }

      case OP_HALT:
        return BC_VM_OK;

      case OP_RETURN: {
        // Pop return value
        valk_lval_t* result = valk_bc_vm_pop(vm);

        // If no frames, we're done (top-level return)
        if (vm->frame_count == 0) {
          valk_bc_vm_push(vm, result);
          return BC_VM_OK;
        }

        // Pop call frame
        vm->frame_count--;
        valk_bc_call_frame_t* frame = &vm->frames[vm->frame_count];

        // Restore stack to just before the call
        vm->stack_top = frame->slots;

        // Push return value
        valk_bc_vm_push(vm, result);

        // Restore IP and chunk
        vm->ip = frame->ip;
        if (vm->frame_count > 0) {
          // Get chunk from previous frame's function
          valk_bc_call_frame_t* prev_frame = &vm->frames[vm->frame_count - 1];
          // Need to reconstruct chunk from frame... for now assume we're in same chunk
          // This will need refinement when we have multiple chunks
        }

        break;
      }

      default:
        valk_bc_vm_runtime_error(vm, "Unknown opcode %d", instruction);
        return BC_VM_RUNTIME_ERROR;
    }
  }

  return BC_VM_OK;
}
