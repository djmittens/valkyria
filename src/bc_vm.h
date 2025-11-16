#ifndef VALK_BC_VM_H
#define VALK_BC_VM_H

#include "bytecode.h"
#include "parser.h"
#include <stddef.h>

#define VALK_STACK_MAX 256
#define VALK_FRAMES_MAX 64

// Call frame for function calls
typedef struct {
  valk_chunk_t* chunk;     // Chunk to return to (for restoring after call)
  uint8_t* ip;             // Instruction pointer (return address)
  valk_lval_t** slots;     // Pointer to this frame's locals on the stack
  size_t slot_count;       // Number of local slots in this frame
  valk_lenv_t* env;        // Environment for this frame (function's closure env)
} valk_bc_call_frame_t;

// Virtual machine state
typedef struct {
  valk_chunk_t* chunk;                  // Current executing chunk
  uint8_t* ip;                          // Instruction pointer

  valk_lval_t* stack[VALK_STACK_MAX];   // Value stack
  valk_lval_t** stack_top;              // Points to next free slot

  valk_bc_call_frame_t frames[VALK_FRAMES_MAX]; // Call stack
  int frame_count;                      // Current frame depth

  valk_lenv_t* globals;                 // Global environment
} valk_bc_vm_t;

// VM result codes
typedef enum {
  BC_VM_OK,
  BC_VM_COMPILE_ERROR,
  BC_VM_RUNTIME_ERROR,
} valk_bc_vm_result_e;

// Initialize the VM
void valk_bc_vm_init(valk_bc_vm_t* vm);

// Free VM resources
void valk_bc_vm_free(valk_bc_vm_t* vm);

// Execute a chunk of bytecode with given environment
valk_bc_vm_result_e valk_bc_vm_run(valk_bc_vm_t* vm, valk_chunk_t* chunk, valk_lenv_t* env);

// Execute a chunk and return the top stack value (for nested execution)
valk_lval_t* valk_bc_vm_execute_chunk(valk_bc_vm_t* vm, valk_chunk_t* chunk, valk_lenv_t* env);

// Push/pop stack operations
void valk_bc_vm_push(valk_bc_vm_t* vm, valk_lval_t* value);
valk_lval_t* valk_bc_vm_pop(valk_bc_vm_t* vm);
valk_lval_t* valk_bc_vm_peek(valk_bc_vm_t* vm, int distance);

// Runtime error reporting
void valk_bc_vm_runtime_error(valk_bc_vm_t* vm, const char* format, ...);

#endif // VALK_BC_VM_H
