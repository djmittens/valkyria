#ifndef VALK_BYTECODE_H
#define VALK_BYTECODE_H

#include <stddef.h>
#include <stdint.h>

// Forward declarations
typedef struct valk_lval_t valk_lval_t;

// Bytecode opcodes for Valkyria VM
typedef enum {
  // Literals - push values onto stack
  OP_CONST,         // Push constant from pool [index:u16]
  OP_NIL,           // Push nil
  OP_TRUE,          // Push true (1)
  OP_FALSE,         // Push false (0)

  // Variables
  OP_GET_LOCAL,     // Push local variable [slot:u8]
  OP_SET_LOCAL,     // Pop and store to local [slot:u8]
  OP_GET_GLOBAL,    // Push global variable [name_index:u16]
  OP_SET_GLOBAL,    // Pop and store to global [name_index:u16]

  // Arithmetic - pop b, pop a, push result
  OP_ADD,           // a + b
  OP_SUB,           // a - b
  OP_MUL,           // a * b
  OP_DIV,           // a / b
  OP_MOD,           // a % b

  // Comparison - pop b, pop a, push 1 or 0
  OP_EQ,            // a == b
  OP_NE,            // a != b
  OP_LT,            // a < b
  OP_LE,            // a <= b
  OP_GT,            // a > b
  OP_GE,            // a >= b

  // Control flow
  OP_JUMP,          // Unconditional jump [offset:i16]
  OP_JUMP_IF_FALSE, // Pop value, jump if false [offset:i16]
  OP_JUMP_IF_TRUE,  // Pop value, jump if true [offset:i16]
  OP_LOOP,          // Jump backward [offset:u16]

  // Functions
  OP_CALL,          // Call function [arg_count:u8]
  OP_TAIL_CALL,     // Tail call (TCO) [arg_count:u8]
  OP_RETURN,        // Return from function
  OP_EVAL,          // Evaluate qexpr as sexpr (converts qexpr to sexpr and evaluates)

  // Lists (cons-based)
  OP_LIST,          // Create list from stack [count:u8]
  OP_CONS,          // Pop tail, pop head, push cons
  OP_HEAD,          // Pop list, push head
  OP_TAIL,          // Pop list, push tail

  // Stack manipulation
  OP_POP,           // Discard top of stack
  OP_DUP,           // Duplicate top of stack

  // Debugging
  OP_PRINT,         // Pop and print value
  OP_HALT,          // Stop execution
} valk_opcode_e;

// Chunk of bytecode with constant pool
typedef struct {
  uint8_t* code;           // Bytecode array
  size_t code_capacity;    // Allocated size
  size_t code_count;       // Used size

  valk_lval_t** constants; // Constant pool
  size_t const_capacity;   // Allocated size
  size_t const_count;      // Used size

  // Line number information for debugging
  int* lines;              // Line number for each bytecode
  size_t line_capacity;
  size_t line_count;
} valk_chunk_t;

// Initialize a bytecode chunk
void valk_chunk_init(valk_chunk_t* chunk);

// Free a bytecode chunk
void valk_chunk_free(valk_chunk_t* chunk);

// Write a byte to the chunk
void valk_chunk_write(valk_chunk_t* chunk, uint8_t byte, int line);

// Add a constant to the pool, return its index
size_t valk_chunk_add_constant(valk_chunk_t* chunk, valk_lval_t* value);

// Disassemble a chunk for debugging
void valk_chunk_disassemble(valk_chunk_t* chunk, const char* name);

// Disassemble a single instruction, return next offset
size_t valk_disassemble_instruction(valk_chunk_t* chunk, size_t offset);

#endif // VALK_BYTECODE_H
