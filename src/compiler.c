#include "compiler.h"
#include "bytecode.h"
#include "parser.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void valk_compiler_init(valk_compiler_t* c, valk_lenv_t* globals) {
  c->chunk = NULL;
  c->local_count = 0;
  c->scope_depth = 0;
  c->loop_start = -1;
  c->loop_depth = 0;
  c->globals = globals;
}

// Emit a single byte
void valk_emit_byte(valk_compiler_t* c, uint8_t byte) {
  valk_chunk_write(c->chunk, byte, 0);  // TODO: track line numbers
}

// Emit two bytes
void valk_emit_bytes(valk_compiler_t* c, uint8_t byte1, uint8_t byte2) {
  valk_emit_byte(c, byte1);
  valk_emit_byte(c, byte2);
}

// Emit a return instruction
void valk_emit_return(valk_compiler_t* c) {
  valk_emit_byte(c, OP_RETURN);
}

// Emit a constant
void valk_emit_constant(valk_compiler_t* c, valk_lval_t* value) {
  size_t constant = valk_chunk_add_constant(c->chunk, value);
  valk_emit_byte(c, OP_CONST);
  valk_emit_byte(c, (constant >> 8) & 0xFF);
  valk_emit_byte(c, constant & 0xFF);
}

// Emit a jump instruction, return the offset for patching
int valk_emit_jump(valk_compiler_t* c, uint8_t instruction) {
  valk_emit_byte(c, instruction);
  valk_emit_byte(c, 0xFF);  // Placeholder
  valk_emit_byte(c, 0xFF);  // Placeholder
  return c->chunk->code_count - 2;
}

// Patch a jump instruction with the actual offset
void valk_patch_jump(valk_compiler_t* c, int offset) {
  // -2 to adjust for the jump offset itself
  int jump = c->chunk->code_count - offset - 2;

  if (jump > UINT16_MAX) {
    fprintf(stderr, "Too much code to jump over\n");
    return;
  }

  c->chunk->code[offset] = (jump >> 8) & 0xFF;
  c->chunk->code[offset + 1] = jump & 0xFF;
}

// Local variable management
void valk_begin_scope(valk_compiler_t* c) {
  c->scope_depth++;
}

void valk_end_scope(valk_compiler_t* c) {
  c->scope_depth--;

  // Pop locals that go out of scope
  while (c->local_count > 0 &&
         c->locals[c->local_count - 1].depth > c->scope_depth) {
    valk_emit_byte(c, OP_POP);
    c->local_count--;
  }
}

int valk_add_local(valk_compiler_t* c, const char* name) {
  if (c->local_count >= 256) {
    fprintf(stderr, "Too many local variables\n");
    return -1;
  }

  c->locals[c->local_count].name = (char*)name;
  c->locals[c->local_count].depth = c->scope_depth;
  return c->local_count++;
}

int valk_resolve_local(valk_compiler_t* c, const char* name) {
  // Search backwards to find most recent variable with this name
  for (int i = c->local_count - 1; i >= 0; i--) {
    if (strcmp(c->locals[i].name, name) == 0) {
      return i;
    }
  }
  return -1;  // Not found - it's a global
}

// Forward declarations for mutual recursion
static void compile_sexpr(valk_compiler_t* c, valk_lval_t* expr, bool is_tail);
static void compile_call(valk_compiler_t* c, valk_lval_t* func, valk_lval_t* args, bool is_tail);
static void compile_lambda(valk_compiler_t* c, valk_lval_t* expr);

// Compile a number literal
static void compile_number(valk_compiler_t* c, valk_lval_t* expr) {
  valk_emit_constant(c, expr);
}

// Compile a string literal
static void compile_string(valk_compiler_t* c, valk_lval_t* expr) {
  valk_emit_constant(c, expr);
}

// Compile a symbol (variable lookup)
static void compile_symbol(valk_compiler_t* c, valk_lval_t* expr) {
  const char* name = expr->str;

  // Use unified OP_GET for all variable lookups
  size_t name_idx = valk_chunk_add_constant(c->chunk, valk_lval_sym(name));
  valk_emit_byte(c, OP_GET);
  valk_emit_byte(c, (name_idx >> 8) & 0xFF);
  valk_emit_byte(c, name_idx & 0xFF);
}

// Compile a lambda: (\ {args} body)
static void compile_lambda(valk_compiler_t* c, valk_lval_t* expr) {
  // expr is the full sexpr: (\ {args} body)
  size_t count = valk_lval_list_count(expr);
  if (count != 3) {
    fprintf(stderr, "lambda requires 2 arguments\n");
    return;
  }

  valk_lval_t* formals = valk_lval_list_nth(expr, 1);
  valk_lval_t* body = valk_lval_list_nth(expr, 2);

  // Count the number of parameters
  // Formals can be QEXPR or SEXPR (when evaluated from fun macro)
  int param_count = 0;
  if (LVAL_TYPE(formals) == LVAL_QEXPR || LVAL_TYPE(formals) == LVAL_SEXPR) {
    param_count = valk_lval_list_count(formals);
  } else {
    fprintf(stderr, "lambda formals must be a list, got: %s\n", valk_ltype_name(LVAL_TYPE(formals)));
    return;
  }

  // Create a new compiler context for the function
  valk_compiler_t func_compiler;
  valk_compiler_init(&func_compiler, c->globals);

  // Create new chunk for function
  valk_chunk_t* func_chunk = malloc(sizeof(valk_chunk_t));
  valk_chunk_init(func_chunk);
  func_compiler.chunk = func_chunk;

  // Detect variadic parameters and add all parameters as local variables
  // Arity encoding:
  // - Non-variadic: arity = number of parameters
  // - Variadic: arity = -(min_required_args + 1)
  int arity = 0;
  bool is_variadic = false;
  int min_required_args = 0;

  for (int i = 0; i < param_count; i++) {
    valk_lval_t* param = valk_lval_list_nth(formals, i);
    if (LVAL_TYPE(param) == LVAL_SYM) {
      // Check for variadic marker '&'
      if (strcmp(param->str, "&") == 0) {
        // Next parameter is the variadic args name
        if (i + 1 < param_count) {
          is_variadic = true;
          min_required_args = i;  // Number of params before '&'
          i++;  // Skip to variadic parameter name
          param = valk_lval_list_nth(formals, i);
          if (LVAL_TYPE(param) == LVAL_SYM) {
            valk_add_local(&func_compiler, param->str);
          } else {
            fprintf(stderr, "variadic parameter name must be a symbol\n");
            return;
          }
        } else {
          fprintf(stderr, "variadic marker '&' must be followed by parameter name\n");
          return;
        }
        // No more parameters allowed after variadic
        if (i + 1 < param_count) {
          fprintf(stderr, "no parameters allowed after variadic parameter\n");
          return;
        }
        break;
      }
      valk_add_local(&func_compiler, param->str);
    } else {
      fprintf(stderr, "lambda parameter must be a symbol\n");
      return;
    }
  }

  // Calculate final arity
  if (is_variadic) {
    arity = -(min_required_args + 1);
  } else {
    arity = param_count;
  }

  // Compile body (in tail position)
  // Body is a qexpr that should be evaluated as code
  // {+ x 1} is treated as an implicit sexpr: (+ x 1)
  if (LVAL_TYPE(body) == LVAL_QEXPR) {
    size_t body_count = valk_lval_list_count(body);
    if (body_count == 0) {
      // Empty body - return nil
      valk_emit_byte(&func_compiler, OP_NIL);
    } else if (body_count == 1) {
      // Single expression - compile it in tail position
      valk_compile_expr(&func_compiler, valk_lval_list_nth(body, 0), true);
    } else {
      // Multiple elements: {+ x 1}
      // Convert to sexpr and compile: (+ x 1)
      valk_lval_t* as_sexpr = valk_qexpr_to_sexpr(body);
      valk_compile_expr(&func_compiler, as_sexpr, true);
    }
  } else {
    // Body is not a qexpr - compile it directly in tail position
    valk_compile_expr(&func_compiler, body, true);
  }

  // Emit return
  valk_emit_return(&func_compiler);

  // Create bytecode function value
  valk_lval_t* bc_fun = valk_lval_bc_fun(func_chunk, arity, "<lambda>");

  // Set closure environment so the function can access variables from its creation context
  bc_fun->fun.env = c->globals;

  // Emit it as a constant
  valk_emit_constant(c, bc_fun);
}

// Compile an if expression: (if cond then else)
static void compile_if(valk_compiler_t* c, valk_lval_t* expr, bool is_tail) {
  // expr is the full sexpr: (if cond then else)
  size_t count = valk_lval_list_count(expr);
  if (count != 4) {
    fprintf(stderr, "if requires 3 arguments\n");
    return;
  }

  valk_lval_t* cond = valk_lval_list_nth(expr, 1);
  valk_lval_t* then_branch = valk_lval_list_nth(expr, 2);
  valk_lval_t* else_branch = valk_lval_list_nth(expr, 3);

  // Compile condition
  valk_compile_expr(c, cond, false);

  // Jump to else if false
  int else_jump = valk_emit_jump(c, OP_JUMP_IF_FALSE);
  valk_emit_byte(c, OP_POP);  // Pop condition

  // Compile then branch
  // If it's a qexpr, we need to evaluate it
  if (LVAL_TYPE(then_branch) == LVAL_QEXPR) {
    size_t count = valk_lval_list_count(then_branch);
    if (count == 0) {
      // Empty qexpr {} evaluates to empty sexpr ()
      valk_compile_expr(c, then_branch, false);
      valk_emit_byte(c, OP_EVAL);
    } else if (count == 1) {
      // Single element qexpr {x} just evaluates to x
      valk_compile_expr(c, valk_lval_list_nth(then_branch, 0), is_tail);
    } else {
      // Multi-element qexpr {a b c} converts to sexpr (a b c) and compiles it
      valk_lval_t* as_sexpr = valk_qexpr_to_sexpr(then_branch);
      valk_compile_expr(c, as_sexpr, is_tail);
    }
  } else {
    valk_compile_expr(c, then_branch, is_tail);
  }

  // Jump over else
  int end_jump = valk_emit_jump(c, OP_JUMP);

  // Else branch
  valk_patch_jump(c, else_jump);
  valk_emit_byte(c, OP_POP);  // Pop condition

  if (LVAL_TYPE(else_branch) == LVAL_QEXPR) {
    size_t count = valk_lval_list_count(else_branch);
    if (count == 0) {
      // Empty qexpr {} evaluates to empty sexpr ()
      valk_compile_expr(c, else_branch, false);
      valk_emit_byte(c, OP_EVAL);
    } else if (count == 1) {
      // Single element qexpr {x} just evaluates to x
      valk_compile_expr(c, valk_lval_list_nth(else_branch, 0), is_tail);
    } else {
      // Multi-element qexpr {a b c} converts to sexpr (a b c) and compiles it
      valk_lval_t* as_sexpr = valk_qexpr_to_sexpr(else_branch);
      valk_compile_expr(c, as_sexpr, is_tail);
    }
  } else {
    valk_compile_expr(c, else_branch, is_tail);
  }

  valk_patch_jump(c, end_jump);
}

// Compile a builtin operation
static void compile_builtin_op(valk_compiler_t* c, const char* op, valk_lval_t* args) {
  // Compile arguments
  size_t arg_count = valk_lval_list_count(args);

  // Binary operators
  if (strcmp(op, "+") == 0 || strcmp(op, "-") == 0 ||
      strcmp(op, "*") == 0 || strcmp(op, "/") == 0 ||
      strcmp(op, "%") == 0 || strcmp(op, "==") == 0 ||
      strcmp(op, "!=") == 0 || strcmp(op, "<") == 0 ||
      strcmp(op, "<=") == 0 || strcmp(op, ">") == 0 ||
      strcmp(op, ">=") == 0) {

    if (arg_count != 2) {
      fprintf(stderr, "Binary operator requires 2 arguments\n");
      return;
    }

    // Compile both arguments
    valk_compile_expr(c, valk_lval_list_nth(args, 0), false);
    valk_compile_expr(c, valk_lval_list_nth(args, 1), false);

    // Emit the operation
    if (strcmp(op, "+") == 0) valk_emit_byte(c, OP_ADD);
    else if (strcmp(op, "-") == 0) valk_emit_byte(c, OP_SUB);
    else if (strcmp(op, "*") == 0) valk_emit_byte(c, OP_MUL);
    else if (strcmp(op, "/") == 0) valk_emit_byte(c, OP_DIV);
    else if (strcmp(op, "%") == 0) valk_emit_byte(c, OP_MOD);
    else if (strcmp(op, "==") == 0) valk_emit_byte(c, OP_EQ);
    else if (strcmp(op, "!=") == 0) valk_emit_byte(c, OP_NE);
    else if (strcmp(op, "<") == 0) valk_emit_byte(c, OP_LT);
    else if (strcmp(op, "<=") == 0) valk_emit_byte(c, OP_LE);
    else if (strcmp(op, ">") == 0) valk_emit_byte(c, OP_GT);
    else if (strcmp(op, ">=") == 0) valk_emit_byte(c, OP_GE);
  } else {
    fprintf(stderr, "Unknown builtin: %s\n", op);
  }
}

// Compile an S-expression (function call or special form)
static void compile_sexpr(valk_compiler_t* c, valk_lval_t* expr, bool is_tail) {
  size_t count = valk_lval_list_count(expr);
  if (count == 0) {
    valk_emit_byte(c, OP_NIL);
    return;
  }

  valk_lval_t* first = valk_lval_list_nth(expr, 0);

  // Single-element sexpr with a non-callable value - just return that value
  // Example: ({}) should return the qexpr, not try to call it
  if (count == 1 && LVAL_TYPE(first) != LVAL_SYM && LVAL_TYPE(first) != LVAL_FUN) {
    valk_compile_expr(c, first, is_tail);
    return;
  }

  // Check for special forms
  if (LVAL_TYPE(first) == LVAL_SYM) {
    const char* name = first->str;

    // if is special
    if (strcmp(name, "if") == 0) {
      compile_if(c, expr, is_tail);
      return;
    }

    // do is special - evaluates expressions in sequence, returns last
    if (strcmp(name, "do") == 0) {
      if (count == 1) {
        // (do) with no args returns nil
        valk_emit_byte(c, OP_NIL);
        return;
      }
      // Compile all expressions except the last, popping their results
      for (size_t i = 1; i < count - 1; i++) {
        valk_compile_expr(c, valk_lval_list_nth(expr, i), false);
        valk_emit_byte(c, OP_POP);  // Discard result
      }
      // Compile last expression (tail position inherited)
      valk_compile_expr(c, valk_lval_list_nth(expr, count - 1), is_tail);
      return;
    }

    // eval is special - compile to OP_EVAL instruction
    if (strcmp(name, "eval") == 0) {
      if (count != 2) {
        fprintf(stderr, "eval requires exactly 1 argument\n");
        return;
      }
      // Compile the argument (should be a qexpr)
      valk_compile_expr(c, valk_lval_list_nth(expr, 1), false);
      // Emit OP_EVAL to evaluate it
      valk_emit_byte(c, OP_EVAL);
      return;
    }

    // lambda is special - but only if formals and body are literal qexprs
    // If they're variables/expressions, compile as regular function call
    if (strcmp(name, "\\") == 0) {
      if (count == 3) {
        valk_lval_t* formals = valk_lval_list_nth(expr, 1);
        valk_lval_t* body = valk_lval_list_nth(expr, 2);
        // Only use special compilation if both are literal qexprs
        if (LVAL_TYPE(formals) == LVAL_QEXPR && LVAL_TYPE(body) == LVAL_QEXPR) {
          compile_lambda(c, expr);
          return;
        }
      }
      // Fall through to compile as regular function call
    }

    // def is special - (def {x y} val1 val2)
    // DISABLED: This optimization breaks the fun macro which uses (def (head f) ...)
    // Let def be called as a regular builtin instead
    /*
    if (strcmp(name, "def") == 0) {
      if (count < 3) {
        fprintf(stderr, "def requires at least 2 arguments\n");
        return;
      }

      valk_lval_t* syms = valk_lval_list_nth(expr, 1);
      if (LVAL_TYPE(syms) != LVAL_QEXPR) {
        fprintf(stderr, "def first argument must be a qexpr\n");
        return;
      }

      size_t sym_count = valk_lval_list_count(syms);
      if (sym_count != count - 2) {
        fprintf(stderr, "def symbol count must match value count\n");
        return;
      }

      // Compile each value and set it to the corresponding symbol
      for (size_t i = 0; i < sym_count; i++) {
        valk_lval_t* sym = valk_lval_list_nth(syms, i);
        valk_lval_t* val = valk_lval_list_nth(expr, i + 2);

        if (LVAL_TYPE(sym) != LVAL_SYM) {
          fprintf(stderr, "def symbols must be symbols\n");
          return;
        }

        // Compile the value
        valk_compile_expr(c, val, false);

        // Emit OP_DEF with symbol name
        size_t name_idx = valk_chunk_add_constant(c->chunk, sym);
        valk_emit_byte(c, OP_DEF);
        valk_emit_byte(c, (name_idx >> 8) & 0xFF);
        valk_emit_byte(c, name_idx & 0xFF);

        // Pop the value (OP_DEF leaves it on stack)
        valk_emit_byte(c, OP_POP);
      }

      // Return nil
      valk_emit_byte(c, OP_NIL);
      return;
    }
    */

    // Check if it's a builtin operator
    if (strcmp(name, "+") == 0 || strcmp(name, "-") == 0 ||
        strcmp(name, "*") == 0 || strcmp(name, "/") == 0 ||
        strcmp(name, "%") == 0 || strcmp(name, "==") == 0 ||
        strcmp(name, "!=") == 0 || strcmp(name, "<") == 0 ||
        strcmp(name, "<=") == 0 || strcmp(name, ">") == 0 ||
        strcmp(name, ">=") == 0) {

      // Build args list (skip the operator itself)
      valk_lval_t* args = valk_lval_sexpr_empty();
      for (size_t i = 1; i < count; i++) {
        valk_lval_add(args, valk_lval_list_nth(expr, i));
      }
      compile_builtin_op(c, name, args);
      return;
    }
  }

  // General function call
  // Compile function
  valk_compile_expr(c, first, false);

  // Compile arguments
  for (size_t i = 1; i < count; i++) {
    valk_compile_expr(c, valk_lval_list_nth(expr, i), false);
  }

  // Emit call instruction (tail or regular)
  if (is_tail) {
    valk_emit_bytes(c, OP_TAIL_CALL, (uint8_t)(count - 1));
  } else {
    valk_emit_bytes(c, OP_CALL, (uint8_t)(count - 1));
  }
}

// Main compile expression entry point
void valk_compile_expr(valk_compiler_t* c, valk_lval_t* expr, bool is_tail) {
  switch (LVAL_TYPE(expr)) {
    case LVAL_NUM:
      compile_number(c, expr);
      break;

    case LVAL_STR:
      compile_string(c, expr);
      break;

    case LVAL_SYM:
      compile_symbol(c, expr);
      break;

    case LVAL_SEXPR:
      compile_sexpr(c, expr, is_tail);
      break;

    case LVAL_QEXPR:
      // Q-expressions evaluate to themselves (like quotes)
      valk_emit_constant(c, expr);
      break;

    case LVAL_NIL:
      valk_emit_byte(c, OP_NIL);
      break;

    case LVAL_FUN:
      // Functions as values - emit as constant
      valk_emit_constant(c, expr);
      break;

    case LVAL_ERR:
    case LVAL_REF:
    case LVAL_ENV:
    case LVAL_CONS:
    case LVAL_THUNK:
    case LVAL_CONT:
      // These types can be emitted as constants
      valk_emit_constant(c, expr);
      break;

    default:
      fprintf(stderr, "Cannot compile type: %s\n", valk_ltype_name(LVAL_TYPE(expr)));
      valk_emit_byte(c, OP_NIL);
      break;
  }
}

// Compile a top-level expression
valk_chunk_t* valk_compile(valk_lval_t* expr, valk_lenv_t* globals) {
  valk_compiler_t compiler;
  valk_compiler_init(&compiler, globals);

  valk_chunk_t* chunk = malloc(sizeof(valk_chunk_t));
  valk_chunk_init(chunk);
  compiler.chunk = chunk;

  // Compile the expression (tail position for top-level)
  valk_compile_expr(&compiler, expr, true);

  // Emit return
  valk_emit_return(&compiler);

  return chunk;
}

// Compile lambda body directly (for runtime lambda creation)
valk_chunk_t* valk_compile_lambda_body(valk_lenv_t* globals, valk_lval_t* formals, valk_lval_t* body) {
  valk_compiler_t compiler;
  valk_compiler_init(&compiler, globals);

  valk_chunk_t* chunk = malloc(sizeof(valk_chunk_t));
  valk_chunk_init(chunk);
  compiler.chunk = chunk;

  // Add parameters as local variables
  int arity = 0;
  for (size_t i = 0; i < valk_lval_list_count(formals); i++) {
    valk_lval_t* param = valk_lval_list_nth(formals, i);
    if (LVAL_TYPE(param) == LVAL_SYM) {
      // Check for variadic marker '&'
      if (strcmp(param->str, "&") == 0) {
        // Next parameter is the variadic args name
        if (i + 1 < valk_lval_list_count(formals)) {
          i++;  // Skip to variadic parameter name
          param = valk_lval_list_nth(formals, i);
          if (LVAL_TYPE(param) == LVAL_SYM) {
            valk_add_local(&compiler, param->str);
          }
        }
        continue;
      }
      valk_add_local(&compiler, param->str);
    }
  }

  // Compile body (in tail position)
  // Body is a qexpr that should be evaluated as code
  // {def {x} {+ a b}} is treated as an implicit sexpr: (def {x} {+ a b})
  if (LVAL_TYPE(body) == LVAL_QEXPR) {
    size_t body_count = valk_lval_list_count(body);
    if (body_count == 0) {
      // Empty body - return nil
      valk_emit_byte(&compiler, OP_NIL);
    } else if (body_count == 1) {
      // Single element body - compile it directly
      valk_lval_t* elem = valk_lval_list_nth(body, 0);
      valk_compile_expr(&compiler, elem, true);
    } else {
      // Multiple elements: {def {x} {+ a b}}
      // Convert to sexpr and compile: (def {x} {+ a b})
      valk_lval_t* as_sexpr = valk_qexpr_to_sexpr(body);
      valk_compile_expr(&compiler, as_sexpr, true);
    }
  } else {
    // Body is not a qexpr - compile it directly in tail position
    valk_compile_expr(&compiler, body, true);
  }

  // Emit return
  valk_emit_return(&compiler);

  return chunk;
}
