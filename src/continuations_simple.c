// Simple continuation implementation for async/await
// This avoids the complexity of full delimited continuations
// and focuses on what we need for async I/O

#include "parser.h"
#include "memory.h"

// Simple continuation structure - just stores a callback function
typedef struct {
  valk_lval_t* (*resume)(valk_lenv_t* env, valk_lval_t* value);
  valk_lenv_t* env;
  void* user_data;
} valk_continuation_t;

// Global to track current continuation (simplified for now)
static __thread valk_continuation_t* current_continuation = NULL;

// Create a continuation
valk_lval_t* valk_continuation_new(valk_lenv_t* env) {
  valk_continuation_t* cont = valk_mem_alloc(sizeof(valk_continuation_t));
  cont->env = env;
  cont->resume = NULL;
  cont->user_data = NULL;

  return valk_lval_ref("continuation", cont, valk_mem_free);
}

// Apply a continuation with a value
valk_lval_t* valk_continuation_resume(valk_lval_t* cont_ref, valk_lval_t* value) {
  if (strcmp(cont_ref->ref.type, "continuation") != 0) {
    return valk_lval_err("Expected continuation, got %s", cont_ref->ref.type);
  }

  valk_continuation_t* cont = cont_ref->ref.ptr;
  if (cont->resume) {
    return cont->resume(cont->env, value);
  }

  return value;  // No continuation, just return value
}

// Builtin: async-shift - captures continuation for async operation
// (async-shift k async-op) where async-op gets passed k
valk_lval_t* valk_builtin_async_shift(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  // First arg should be a symbol for continuation variable
  valk_lval_t* k_sym = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, k_sym, LVAL_SYM);

  // Create a continuation
  valk_lval_t* cont = valk_continuation_new(e);

  // Bind continuation to the symbol
  valk_lenv_put(e, k_sym, cont);

  // Evaluate the async operation with continuation available
  valk_lval_t* async_expr = valk_lval_list_nth(a, 1);
  return valk_lval_eval(e, async_expr);
}

// Builtin: async-reset - establishes async context
// (async-reset expr) evaluates expr in async context
valk_lval_t* valk_builtin_async_reset(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  // For now, just evaluate the expression
  // In a full implementation, this would set up prompt/delimiter
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  return valk_lval_eval(e, expr);
}

// Register async builtins
void valk_register_async_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "async-shift", valk_builtin_async_shift);
  valk_lenv_put_builtin(env, "async-reset", valk_builtin_async_reset);
}