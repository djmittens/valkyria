#ifndef VALK_COMPILER_H
#define VALK_COMPILER_H

#include "bytecode.h"
#include "parser.h"

// Compiler state
typedef struct {
  valk_chunk_t* chunk;           // Current chunk being compiled to

  // Local variables tracking
  struct {
    char* name;                  // Variable name
    int depth;                   // Scope depth (-1 = uninitialized)
  } locals[256];
  int local_count;               // Number of locals
  int scope_depth;               // Current scope depth (0 = global)

  // Control flow
  int loop_start;                // Start of current loop (for OP_LOOP)
  int loop_depth;                // Depth of loop nesting

  valk_lenv_t* globals;          // Global environment for name lookups
} valk_compiler_t;

// Initialize compiler
void valk_compiler_init(valk_compiler_t* compiler, valk_lenv_t* globals);

// Compile an lval expression to bytecode
// is_tail: true if this expression is in tail position (for TCO)
void valk_compile_expr(valk_compiler_t* c, valk_lval_t* expr, bool is_tail);

// Compile a top-level expression (convenience wrapper)
valk_chunk_t* valk_compile(valk_lval_t* expr, valk_lenv_t* globals);

// Compile lambda body directly (for runtime lambda creation)
valk_chunk_t* valk_compile_lambda_body(valk_lenv_t* globals, valk_lval_t* formals, valk_lval_t* body);

// Emit bytecode instructions
void valk_emit_byte(valk_compiler_t* c, uint8_t byte);
void valk_emit_bytes(valk_compiler_t* c, uint8_t byte1, uint8_t byte2);
void valk_emit_return(valk_compiler_t* c);

// Emit a constant
void valk_emit_constant(valk_compiler_t* c, valk_lval_t* value);

// Control flow helpers
int valk_emit_jump(valk_compiler_t* c, uint8_t instruction);
void valk_patch_jump(valk_compiler_t* c, int offset);

// Local variable management
void valk_begin_scope(valk_compiler_t* c);
void valk_end_scope(valk_compiler_t* c);
int valk_add_local(valk_compiler_t* c, const char* name);
int valk_resolve_local(valk_compiler_t* c, const char* name);

#endif // VALK_COMPILER_H
