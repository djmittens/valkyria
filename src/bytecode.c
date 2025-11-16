#include "bytecode.h"
#include "parser.h"
#include <stdio.h>
#include <stdlib.h>

void valk_chunk_init(valk_chunk_t* chunk) {
  chunk->code = NULL;
  chunk->code_capacity = 0;
  chunk->code_count = 0;

  chunk->constants = NULL;
  chunk->const_capacity = 0;
  chunk->const_count = 0;

  chunk->lines = NULL;
  chunk->line_capacity = 0;
  chunk->line_count = 0;
}

void valk_chunk_free(valk_chunk_t* chunk) {
  free(chunk->code);
  free(chunk->constants);
  free(chunk->lines);
  valk_chunk_init(chunk);
}

void valk_chunk_write(valk_chunk_t* chunk, uint8_t byte, int line) {
  // Grow code array if needed
  if (chunk->code_capacity < chunk->code_count + 1) {
    size_t old_capacity = chunk->code_capacity;
    chunk->code_capacity = old_capacity < 8 ? 8 : old_capacity * 2;
    chunk->code = realloc(chunk->code, chunk->code_capacity);
  }

  // Grow line array if needed
  if (chunk->line_capacity < chunk->line_count + 1) {
    size_t old_capacity = chunk->line_capacity;
    chunk->line_capacity = old_capacity < 8 ? 8 : old_capacity * 2;
    chunk->lines = realloc(chunk->lines, chunk->line_capacity * sizeof(int));
  }

  chunk->code[chunk->code_count] = byte;
  chunk->lines[chunk->line_count] = line;
  chunk->code_count++;
  chunk->line_count++;
}

size_t valk_chunk_add_constant(valk_chunk_t* chunk, valk_lval_t* value) {
  // Grow constants array if needed
  if (chunk->const_capacity < chunk->const_count + 1) {
    size_t old_capacity = chunk->const_capacity;
    chunk->const_capacity = old_capacity < 8 ? 8 : old_capacity * 2;
    chunk->constants = realloc(chunk->constants,
                               chunk->const_capacity * sizeof(valk_lval_t*));
  }

  chunk->constants[chunk->const_count] = value;
  return chunk->const_count++;
}

// Disassembly helpers
static size_t simple_instruction(const char* name, size_t offset) {
  printf("%s\n", name);
  return offset + 1;
}

static size_t byte_instruction(const char* name, valk_chunk_t* chunk, size_t offset) {
  uint8_t slot = chunk->code[offset + 1];
  printf("%-16s %4d\n", name, slot);
  return offset + 2;
}

static size_t constant_instruction(const char* name, valk_chunk_t* chunk, size_t offset) {
  uint16_t constant = (chunk->code[offset + 1] << 8) | chunk->code[offset + 2];
  printf("%-16s %4d '", name, constant);
  if (constant < chunk->const_count) {
    valk_lval_print(chunk->constants[constant]);
  } else {
    printf("<invalid>");
  }
  printf("'\n");
  return offset + 3;
}

static size_t jump_instruction(const char* name, int sign, valk_chunk_t* chunk, size_t offset) {
  uint16_t jump = (chunk->code[offset + 1] << 8) | chunk->code[offset + 2];
  printf("%-16s %4zu -> %zu\n", name, offset, offset + 3 + sign * jump);
  return offset + 3;
}

void valk_chunk_disassemble(valk_chunk_t* chunk, const char* name) {
  printf("== %s ==\n", name);

  for (size_t offset = 0; offset < chunk->code_count;) {
    offset = valk_disassemble_instruction(chunk, offset);
  }
}

size_t valk_disassemble_instruction(valk_chunk_t* chunk, size_t offset) {
  printf("%04zu ", offset);

  // Print line number
  if (offset > 0 && chunk->lines[offset] == chunk->lines[offset - 1]) {
    printf("   | ");
  } else {
    printf("%4d ", chunk->lines[offset]);
  }

  uint8_t instruction = chunk->code[offset];
  switch (instruction) {
    case OP_CONST:
      return constant_instruction("OP_CONST", chunk, offset);
    case OP_NIL:
      return simple_instruction("OP_NIL", offset);
    case OP_TRUE:
      return simple_instruction("OP_TRUE", offset);
    case OP_FALSE:
      return simple_instruction("OP_FALSE", offset);

    case OP_GET:
      return constant_instruction("OP_GET", chunk, offset);
    case OP_LET:
      return constant_instruction("OP_LET", chunk, offset);
    case OP_DEF:
      return constant_instruction("OP_DEF", chunk, offset);

    case OP_ADD:
      return simple_instruction("OP_ADD", offset);
    case OP_SUB:
      return simple_instruction("OP_SUB", offset);
    case OP_MUL:
      return simple_instruction("OP_MUL", offset);
    case OP_DIV:
      return simple_instruction("OP_DIV", offset);
    case OP_MOD:
      return simple_instruction("OP_MOD", offset);

    case OP_EQ:
      return simple_instruction("OP_EQ", offset);
    case OP_NE:
      return simple_instruction("OP_NE", offset);
    case OP_LT:
      return simple_instruction("OP_LT", offset);
    case OP_LE:
      return simple_instruction("OP_LE", offset);
    case OP_GT:
      return simple_instruction("OP_GT", offset);
    case OP_GE:
      return simple_instruction("OP_GE", offset);

    case OP_JUMP:
      return jump_instruction("OP_JUMP", 1, chunk, offset);
    case OP_JUMP_IF_FALSE:
      return jump_instruction("OP_JUMP_IF_FALSE", 1, chunk, offset);
    case OP_JUMP_IF_TRUE:
      return jump_instruction("OP_JUMP_IF_TRUE", 1, chunk, offset);
    case OP_LOOP:
      return jump_instruction("OP_LOOP", -1, chunk, offset);

    case OP_CALL:
      return byte_instruction("OP_CALL", chunk, offset);
    case OP_TAIL_CALL:
      return byte_instruction("OP_TAIL_CALL", chunk, offset);
    case OP_RETURN:
      return simple_instruction("OP_RETURN", offset);

    case OP_LIST:
      return byte_instruction("OP_LIST", chunk, offset);
    case OP_CONS:
      return simple_instruction("OP_CONS", offset);
    case OP_HEAD:
      return simple_instruction("OP_HEAD", offset);
    case OP_TAIL:
      return simple_instruction("OP_TAIL", offset);

    case OP_POP:
      return simple_instruction("OP_POP", offset);
    case OP_DUP:
      return simple_instruction("OP_DUP", offset);

    case OP_PRINT:
      return simple_instruction("OP_PRINT", offset);
    case OP_HALT:
      return simple_instruction("OP_HALT", offset);

    default:
      printf("Unknown opcode %d\n", instruction);
      return offset + 1;
  }
}
