#include "eval_trampoline.h"

#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "coverage.h"
#include "gc.h"
#include "memory.h"

// ============================================================================
// Feature Flag
// ============================================================================

static bool g_trampoline_eval_enabled = false;

// ============================================================================
// Thread-Local Current Stack (for perform/resume)
// ============================================================================

// Thread-local pointer to the current eval stack.
// This allows `perform` (called as a builtin) to capture the stack.
static __thread valk_eval_stack_t *g_current_eval_stack = NULL;

// Get the current eval stack (for perform to capture)
valk_eval_stack_t *valk_eval_get_current_stack(void) {
  return g_current_eval_stack;
}

// Set the current eval stack (called by trampoline)
static void set_current_eval_stack(valk_eval_stack_t *stack) {
  g_current_eval_stack = stack;
}

bool valk_trampoline_eval_enabled(void) {
  return g_trampoline_eval_enabled;
}

void valk_trampoline_eval_set_enabled(bool enabled) {
  g_trampoline_eval_enabled = enabled;
}

// ============================================================================
// Stack Operations
// ============================================================================

#define INITIAL_STACK_CAPACITY 64

void valk_eval_stack_init(valk_eval_stack_t *stack) {
  stack->frames = NULL;
  stack->count = 0;
  stack->capacity = 0;
  stack->version = 0;
}

void valk_eval_stack_free(valk_eval_stack_t *stack) {
  if (stack->frames) {
    // Free any dynamically allocated frame data
    for (size_t i = 0; i < stack->count; i++) {
      valk_eval_frame_t *frame = &stack->frames[i];
      if (frame->type == FRAME_CALL_EVAL_FN ||
          frame->type == FRAME_CALL_EVAL_ARGS ||
          frame->type == FRAME_CALL_APPLY) {
        if (frame->call.args) {
          free(frame->call.args);
          frame->call.args = NULL;
        }
      }
    }
    free(stack->frames);
    stack->frames = NULL;
  }
  stack->count = 0;
  stack->capacity = 0;
}

void valk_eval_stack_push(valk_eval_stack_t *stack, valk_eval_frame_t frame) {
  if (stack->count >= stack->capacity) {
    size_t new_capacity = stack->capacity == 0 ? INITIAL_STACK_CAPACITY
                                               : stack->capacity * 2;
    valk_eval_frame_t *new_frames =
        realloc(stack->frames, new_capacity * sizeof(valk_eval_frame_t));
    if (!new_frames) {
      // Fatal error - cannot grow stack
      abort();
    }
    stack->frames = new_frames;
    stack->capacity = new_capacity;
  }
  stack->frames[stack->count++] = frame;
  stack->version++;
}

valk_eval_frame_t *valk_eval_stack_top(valk_eval_stack_t *stack) {
  if (stack->count == 0) return NULL;
  return &stack->frames[stack->count - 1];
}

void valk_eval_stack_pop(valk_eval_stack_t *stack) {
  if (stack->count > 0) {
    valk_eval_frame_t *frame = &stack->frames[stack->count - 1];
    // Free call frame args array if present
    if (frame->type == FRAME_CALL_EVAL_FN ||
        frame->type == FRAME_CALL_EVAL_ARGS ||
        frame->type == FRAME_CALL_APPLY) {
      if (frame->call.args) {
        free(frame->call.args);
        frame->call.args = NULL;
      }
    }
    stack->count--;
    stack->version++;
  }
}

bool valk_eval_stack_empty(valk_eval_stack_t *stack) {
  return stack->count == 0;
}

valk_eval_stack_t *valk_eval_stack_copy(valk_eval_stack_t *stack) {
  valk_eval_stack_t *copy = malloc(sizeof(valk_eval_stack_t));
  if (!copy) return NULL;

  copy->count = stack->count;
  copy->capacity = stack->count;  // Tight fit
  copy->version = stack->version;

  if (stack->count == 0) {
    copy->frames = NULL;
    return copy;
  }

  copy->frames = malloc(stack->count * sizeof(valk_eval_frame_t));
  if (!copy->frames) {
    free(copy);
    return NULL;
  }

  // Shallow copy frames - they reference heap-allocated data
  memcpy(copy->frames, stack->frames, stack->count * sizeof(valk_eval_frame_t));

  // Deep copy the args arrays for call frames
  for (size_t i = 0; i < copy->count; i++) {
    valk_eval_frame_t *frame = &copy->frames[i];
    if ((frame->type == FRAME_CALL_EVAL_FN ||
         frame->type == FRAME_CALL_EVAL_ARGS ||
         frame->type == FRAME_CALL_APPLY) &&
        frame->call.args != NULL && frame->call.args_capacity > 0) {
      valk_lval_t **new_args =
          malloc(frame->call.args_capacity * sizeof(valk_lval_t *));
      if (new_args) {
        memcpy(new_args, frame->call.args,
               frame->call.args_count * sizeof(valk_lval_t *));
        frame->call.args = new_args;
      } else {
        frame->call.args = NULL;
      }
    }
  }

  return copy;
}

// ============================================================================
// Forward Declarations for Step Functions
// ============================================================================

static valk_lval_t *eval_step_expr(valk_eval_stack_t *stack,
                                    valk_eval_frame_t *frame,
                                    valk_lval_t *prev_value);
static valk_lval_t *eval_step_call_fn(valk_eval_stack_t *stack,
                                       valk_eval_frame_t *frame,
                                       valk_lval_t *prev_value);
static valk_lval_t *eval_step_call_args(valk_eval_stack_t *stack,
                                         valk_eval_frame_t *frame,
                                         valk_lval_t *prev_value);
static valk_lval_t *eval_step_call_apply(valk_eval_stack_t *stack,
                                          valk_eval_frame_t *frame,
                                          valk_lval_t *prev_value);
static valk_lval_t *eval_step_if(valk_eval_stack_t *stack,
                                  valk_eval_frame_t *frame,
                                  valk_lval_t *prev_value);
static valk_lval_t *eval_step_sequence(valk_eval_stack_t *stack,
                                        valk_eval_frame_t *frame,
                                        valk_lval_t *prev_value);

// ============================================================================
// Helper Functions
// ============================================================================

// Convert QEXPR to CONS for evaluation
// Only converts the spine (tail) of the list, keeping head elements as-is
// This is important: nested QEXPRs in head position should NOT be converted
// e.g., {\\ {y} {x}} becomes (\\ {y} {x}) where {y} and {x} remain QEXPRs
static valk_lval_t *valk_qexpr_to_cons_trampoline(valk_lval_t *qexpr) {
  if (qexpr == NULL || LVAL_TYPE(qexpr) == LVAL_NIL) {
    return valk_lval_nil();
  }
  if (LVAL_TYPE(qexpr) != LVAL_QEXPR) {
    return qexpr;
  }

  // Keep head as-is, only convert tail (the spine of the list)
  valk_lval_t *new_tail = valk_qexpr_to_cons_trampoline(qexpr->cons.tail);
  return valk_lval_cons(qexpr->cons.head, new_tail);
}

// Check if a type is a list type (CONS, QEXPR, or NIL)
static inline bool is_list_type(valk_ltype_e type) {
  return type == LVAL_CONS || type == LVAL_QEXPR || type == LVAL_NIL;
}

// ============================================================================
// Step Functions - Each handles one frame type
// ============================================================================

static valk_lval_t *eval_step_expr(valk_eval_stack_t *stack,
                                    valk_eval_frame_t *frame,
                                    valk_lval_t *prev_value) {
  UNUSED(prev_value);
  valk_lval_t *expr = frame->eval.expr;
  valk_lenv_t *env = frame->env;

  // Pop this frame - we're handling it now
  valk_eval_stack_pop(stack);

  // Handle NULL gracefully
  if (expr == NULL) {
    return valk_lval_nil();
  }

  valk_ltype_e type = LVAL_TYPE(expr);

  // Self-evaluating forms
  switch (type) {
    case LVAL_NUM:
    case LVAL_STR:
    case LVAL_FUN:
    case LVAL_ERR:
    case LVAL_NIL:
    case LVAL_REF:
    case LVAL_QEXPR:
    case LVAL_HANDLE:
      return expr;

    case LVAL_SYM: {
      // Symbol lookup
      VALK_COVERAGE_RECORD_LVAL(expr);
      // Keyword symbols (starting with :) are self-evaluating
      if (expr->str[0] == ':') {
        return expr;
      }
      return valk_lenv_get(env, expr);
    }

    case LVAL_CONS: {
      // Record coverage for cons cells
      VALK_COVERAGE_RECORD_LVAL(expr);

      size_t count = valk_lval_list_count(expr);

      // Empty list evaluates to nil
      if (count == 0) {
        return valk_lval_nil();
      }

      valk_lval_t *first = expr->cons.head;

      // Check for special forms BEFORE evaluating first element
      if (LVAL_TYPE(first) == LVAL_SYM) {
        // quote: return argument unevaluated
        if (strcmp(first->str, "quote") == 0) {
          if (count != 2) {
            return valk_lval_err("quote expects exactly 1 argument, got %zu",
                                 count - 1);
          }
          return valk_lval_list_nth(expr, 1);
        }

        // quasiquote: template with selective evaluation via unquote/unquote-splicing
        if (strcmp(first->str, "quasiquote") == 0) {
          if (count != 2) {
            return valk_lval_err("quasiquote expects exactly 1 argument, got %zu",
                                 count - 1);
          }
          valk_lval_t *arg = valk_lval_list_nth(expr, 1);
          return valk_quasiquote_expand(env, arg);
        }

        // if: push IF_COND frame, then eval condition
        if (strcmp(first->str, "if") == 0) {
          if (count != 4) {
            return valk_lval_err("if expects exactly 3 arguments, got %zu",
                                 count - 1);
          }
          valk_eval_stack_push(stack, (valk_eval_frame_t){
            .type = FRAME_IF_COND,
            .env = env,
            .if_cond = {
              .then_branch = valk_lval_list_nth(expr, 2),
              .else_branch = valk_lval_list_nth(expr, 3)
            }
          });
          // Push eval frame for condition
          valk_eval_stack_push(stack, (valk_eval_frame_t){
            .type = FRAME_EVAL,
            .env = env,
            .eval = { .expr = valk_lval_list_nth(expr, 1) }
          });
          return NULL;  // Continue loop
        }

        // do: push sequence frame
        if (strcmp(first->str, "do") == 0) {
          valk_lval_t *body = expr->cons.tail;
          if (valk_lval_list_is_empty(body)) {
            return valk_lval_nil();
          }
          // If multiple expressions, set up sequence
          if (valk_lval_list_count(body) > 1) {
            valk_eval_stack_push(stack, (valk_eval_frame_t){
              .type = FRAME_DO_SEQUENCE,
              .env = env,
              .seq = { .remaining = body->cons.tail }
            });
          }
          // Evaluate first expression
          valk_eval_stack_push(stack, (valk_eval_frame_t){
            .type = FRAME_EVAL,
            .env = env,
            .eval = { .expr = body->cons.head }
          });
          return NULL;
        }
      }

      // Single element list - evaluate and return (or call if function)
      if (count == 1) {
        // Push a frame that will handle the "maybe call" logic
        valk_eval_stack_push(stack, (valk_eval_frame_t){
          .type = FRAME_CALL_EVAL_FN,
          .env = env,
          .call = {
            .fn = NULL,
            .args = NULL,
            .args_capacity = 0,
            .args_count = 0,
            .remaining = valk_lval_nil(),
            .original_expr = expr
          }
        });
        valk_eval_stack_push(stack, (valk_eval_frame_t){
          .type = FRAME_EVAL,
          .env = env,
          .eval = { .expr = first }
        });
        return NULL;
      }

      // Regular function call with arguments
      // Push CALL_EVAL_FN frame, then eval function position
      valk_lval_t *args_list = expr->cons.tail;
      size_t arg_count = valk_lval_list_count(args_list);

      valk_eval_stack_push(stack, (valk_eval_frame_t){
        .type = FRAME_CALL_EVAL_FN,
        .env = env,
        .call = {
          .fn = NULL,
          .args = arg_count > 0 ? malloc(sizeof(valk_lval_t*) * arg_count) : NULL,
          .args_capacity = arg_count,
          .args_count = 0,
          .remaining = args_list,
          .original_expr = expr
        }
      });
      valk_eval_stack_push(stack, (valk_eval_frame_t){
        .type = FRAME_EVAL,
        .env = env,
        .eval = { .expr = first }
      });
      return NULL;
    }

    default:
      return valk_lval_err("Unknown value type in evaluation: %s",
                           valk_ltype_name(type));
  }
}

static valk_lval_t *eval_step_call_fn(valk_eval_stack_t *stack,
                                       valk_eval_frame_t *frame,
                                       valk_lval_t *prev_value) {
  // prev_value is the evaluated function position
  if (LVAL_TYPE(prev_value) == LVAL_ERR) {
    valk_eval_stack_pop(stack);
    return prev_value;
  }

  // Special case: single-element list with non-function result
  // Just return the value directly
  if (LVAL_TYPE(prev_value) != LVAL_FUN &&
      valk_lval_list_is_empty(frame->call.remaining)) {
    valk_eval_stack_pop(stack);
    return prev_value;
  }

  frame->call.fn = prev_value;

  // If no args, go directly to apply
  if (valk_lval_list_is_empty(frame->call.remaining)) {
    frame->type = FRAME_CALL_APPLY;
    return NULL;  // Continue with apply
  }

  // Start evaluating args
  frame->type = FRAME_CALL_EVAL_ARGS;
  valk_lval_t *first_arg = frame->call.remaining->cons.head;
  frame->call.remaining = frame->call.remaining->cons.tail;

  valk_eval_stack_push(stack, (valk_eval_frame_t){
    .type = FRAME_EVAL,
    .env = frame->env,
    .eval = { .expr = first_arg }
  });
  return NULL;
}

static valk_lval_t *eval_step_call_args(valk_eval_stack_t *stack,
                                         valk_eval_frame_t *frame,
                                         valk_lval_t *prev_value) {
  // prev_value is an evaluated argument - store it
  // Note: Don't propagate errors - allow functions like error? to receive them
  if (frame->call.args && frame->call.args_count < frame->call.args_capacity) {
    frame->call.args[frame->call.args_count++] = prev_value;
  }

  // More args to evaluate?
  if (!valk_lval_list_is_empty(frame->call.remaining)) {
    valk_lval_t *next_arg = frame->call.remaining->cons.head;
    frame->call.remaining = frame->call.remaining->cons.tail;

    valk_eval_stack_push(stack, (valk_eval_frame_t){
      .type = FRAME_EVAL,
      .env = frame->env,
      .eval = { .expr = next_arg }
    });
    return NULL;
  }

  // All args evaluated - transition to apply
  frame->type = FRAME_CALL_APPLY;
  return NULL;
}

static valk_lval_t *eval_step_call_apply(valk_eval_stack_t *stack,
                                          valk_eval_frame_t *frame,
                                          valk_lval_t *prev_value) {
  UNUSED(prev_value);

  valk_lval_t *func = frame->call.fn;
  valk_lenv_t *env = frame->env;

  if (LVAL_TYPE(func) != LVAL_FUN) {
    valk_eval_stack_pop(stack);
    return valk_lval_err("Attempted to call non-function: %s",
                         valk_ltype_name(LVAL_TYPE(func)));
  }

  // Build args list from array
  valk_lval_t *args = valk_lval_nil();
  for (size_t i = frame->call.args_count; i > 0; i--) {
    args = valk_lval_cons(frame->call.args[i - 1], args);
  }

  // Pop call frame before applying
  valk_eval_stack_pop(stack);

  // Builtin function - call directly
  if (func->fun.builtin) {
    return func->fun.builtin(env, args);
  }

  // User-defined function - set up environment and evaluate body
  size_t given = valk_lval_list_count(args);
  size_t num_formals = valk_lval_list_count(func->fun.formals);

  // Create new environment for bindings
  valk_lenv_t *call_env = valk_lenv_empty();
  if (func->fun.env) {
    call_env->parent = func->fun.env;
  } else {
    call_env->parent = env;
  }
  call_env->fallback = env;

  // Bind formals to args
  valk_lval_t *formal_iter = func->fun.formals;
  valk_lval_t *arg_iter = args;
  bool saw_varargs = false;

  while (!valk_lval_list_is_empty(formal_iter) &&
         !valk_lval_list_is_empty(arg_iter)) {
    valk_lval_t *formal_sym = formal_iter->cons.head;

    // Handle varargs
    if (LVAL_TYPE(formal_sym) == LVAL_SYM &&
        strcmp(formal_sym->str, "&") == 0) {
      formal_iter = formal_iter->cons.tail;
      if (valk_lval_list_is_empty(formal_iter)) {
        return valk_lval_err(
            "Invalid function format: & not followed by varargs name");
      }
      valk_lval_t *varargs_sym = formal_iter->cons.head;
      // Convert remaining args to list
      valk_lval_t *varargs_list = valk_lval_nil();
      valk_lval_t *arg_curr = arg_iter;
      size_t vcount = valk_lval_list_count(arg_curr);
      valk_lval_t *varr[vcount];
      for (size_t i = 0; i < vcount; i++) {
        varr[i] = arg_curr->cons.head;
        arg_curr = arg_curr->cons.tail;
      }
      varargs_list = valk_lval_qlist(varr, vcount);
      valk_lenv_put(call_env, varargs_sym, varargs_list);
      saw_varargs = true;
      arg_iter = valk_lval_nil();
      formal_iter = formal_iter->cons.tail;
      break;
    }

    // Regular formal - bind it
    valk_lval_t *val = arg_iter->cons.head;
    valk_lenv_put(call_env, formal_sym, val);

    formal_iter = formal_iter->cons.tail;
    arg_iter = arg_iter->cons.tail;
  }

  // Check if more args than formals
  if (!valk_lval_list_is_empty(arg_iter) && !saw_varargs) {
    return valk_lval_err(
        "More arguments were given than required. Actual: %zu, Expected: %zu",
        given, num_formals);
  }

  // Handle remaining formals (partial application or varargs default)
  if (!valk_lval_list_is_empty(formal_iter)) {
    // Check for varargs with no args provided
    if (LVAL_TYPE(formal_iter->cons.head) == LVAL_SYM &&
        strcmp(formal_iter->cons.head->str, "&") == 0) {
      formal_iter = formal_iter->cons.tail;
      if (valk_lval_list_is_empty(formal_iter)) {
        return valk_lval_err(
            "Invalid function format: & not followed by varargs name");
      }
      valk_lval_t *varargs_sym = formal_iter->cons.head;
      valk_lenv_put(call_env, varargs_sym, valk_lval_nil());
      formal_iter = formal_iter->cons.tail;
    }

    // If still have unbound formals, return partially applied function
    if (!valk_lval_list_is_empty(formal_iter)) {
      valk_lval_t *partial = valk_mem_alloc(sizeof(valk_lval_t));
      partial->flags =
          LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
      partial->origin_allocator = valk_thread_ctx.allocator;
      partial->fun.builtin = NULL;
      partial->fun.arity = func->fun.arity;
      partial->fun.name = func->fun.name;
      partial->fun.env = call_env;
      partial->fun.formals = formal_iter;
      partial->fun.body = func->fun.body;
      return partial;
    }
  }

  // Prepare body for evaluation
  valk_lval_t *body = func->fun.body;
  if (LVAL_TYPE(body) == LVAL_QEXPR) {
    body = valk_qexpr_to_cons_trampoline(body);
  }

  // If body is a list of expressions (implicit do), set up sequence
  if (is_list_type(LVAL_TYPE(body)) && valk_lval_list_count(body) > 0) {
    valk_lval_t *first_elem = body->cons.head;
    if (is_list_type(LVAL_TYPE(first_elem))) {
      // Multiple expressions - set up sequence
      if (valk_lval_list_count(body) > 1) {
        valk_eval_stack_push(stack, (valk_eval_frame_t){
          .type = FRAME_DO_SEQUENCE,
          .env = call_env,
          .seq = { .remaining = body->cons.tail }
        });
      }
      valk_eval_stack_push(stack, (valk_eval_frame_t){
        .type = FRAME_EVAL,
        .env = call_env,
        .eval = { .expr = body->cons.head }
      });
      return NULL;
    }
  }

  // Single expression body
  valk_eval_stack_push(stack, (valk_eval_frame_t){
    .type = FRAME_EVAL,
    .env = call_env,
    .eval = { .expr = body }
  });
  return NULL;
}

static valk_lval_t *eval_step_if(valk_eval_stack_t *stack,
                                  valk_eval_frame_t *frame,
                                  valk_lval_t *prev_value) {
  // prev_value is the evaluated condition
  if (LVAL_TYPE(prev_value) == LVAL_ERR) {
    valk_eval_stack_pop(stack);
    return prev_value;
  }

  if (LVAL_TYPE(prev_value) != LVAL_NUM) {
    valk_eval_stack_pop(stack);
    return valk_lval_err("if condition must be a number, got %s",
                         valk_ltype_name(LVAL_TYPE(prev_value)));
  }

  bool condition = prev_value->num != 0;
  valk_lval_t *branch = condition ? frame->if_cond.then_branch
                                   : frame->if_cond.else_branch;

#ifdef VALK_COVERAGE
  // Record branch coverage
  uint16_t file_id = frame->if_cond.then_branch->cov_file_id;
  uint16_t line = frame->if_cond.then_branch->cov_line;
  if (file_id == 0 || line == 0) {
    file_id = frame->if_cond.else_branch->cov_file_id;
    line = frame->if_cond.else_branch->cov_line;
  }
  VALK_COVERAGE_RECORD_BRANCH(file_id, line, condition);
#endif

  // Convert QEXPR to CONS if needed
  if (LVAL_TYPE(branch) == LVAL_QEXPR) {
    VALK_COVERAGE_RECORD_LVAL(branch);
    branch = valk_qexpr_to_cons_trampoline(branch);
  }

  // Pop if frame and push eval for branch
  valk_lenv_t *env = frame->env;
  valk_eval_stack_pop(stack);

  valk_eval_stack_push(stack, (valk_eval_frame_t){
    .type = FRAME_EVAL,
    .env = env,
    .eval = { .expr = branch }
  });
  return NULL;
}

static valk_lval_t *eval_step_sequence(valk_eval_stack_t *stack,
                                        valk_eval_frame_t *frame,
                                        valk_lval_t *prev_value) {
  // prev_value is the result of the last expression (ignored unless last)
  if (LVAL_TYPE(prev_value) == LVAL_ERR) {
    valk_eval_stack_pop(stack);
    return prev_value;
  }

  // More expressions to evaluate?
  if (!valk_lval_list_is_empty(frame->seq.remaining)) {
    valk_lval_t *next_expr = frame->seq.remaining->cons.head;
    frame->seq.remaining = frame->seq.remaining->cons.tail;

    valk_eval_stack_push(stack, (valk_eval_frame_t){
      .type = FRAME_EVAL,
      .env = frame->env,
      .eval = { .expr = next_expr }
    });
    return NULL;
  }

  // All expressions evaluated - return last result
  valk_eval_stack_pop(stack);
  return prev_value;
}

// ============================================================================
// Main Trampoline Loop
// ============================================================================

valk_lval_t *valk_eval_trampoline(valk_lenv_t *env, valk_lval_t *expr) {
  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);

  // Save and set current stack for perform/resume access
  valk_eval_stack_t *prev_stack = g_current_eval_stack;
  set_current_eval_stack(&stack);

  // Initial frame: evaluate the expression
  valk_eval_stack_push(&stack, (valk_eval_frame_t){
    .type = FRAME_EVAL,
    .env = env,
    .eval = { .expr = expr }
  });

  valk_lval_t *value = NULL;

  while (!valk_eval_stack_empty(&stack)) {
    valk_eval_frame_t *frame = valk_eval_stack_top(&stack);

    switch (frame->type) {
      case FRAME_EVAL:
        value = eval_step_expr(&stack, frame, value);
        break;

      case FRAME_CALL_EVAL_FN:
        value = eval_step_call_fn(&stack, frame, value);
        break;

      case FRAME_CALL_EVAL_ARGS:
        value = eval_step_call_args(&stack, frame, value);
        break;

      case FRAME_CALL_APPLY:
        value = eval_step_call_apply(&stack, frame, value);
        break;

      case FRAME_IF_COND:
        value = eval_step_if(&stack, frame, value);
        break;

      case FRAME_DO_SEQUENCE:
        value = eval_step_sequence(&stack, frame, value);
        break;

      case FRAME_DEF_VALUE:
      case FRAME_LET_BINDINGS:
      case FRAME_HANDLER_BODY:
      case FRAME_PERFORM:
        // Not yet implemented - will be added in later phases
        valk_eval_stack_pop(&stack);
        value = valk_lval_err("Frame type %d not yet implemented", frame->type);
        break;
    }

    // Check for errors - propagate immediately
    if (value && LVAL_TYPE(value) == LVAL_ERR) {
      set_current_eval_stack(prev_stack);
      valk_eval_stack_free(&stack);
      return value;
    }
  }

  set_current_eval_stack(prev_stack);
  valk_eval_stack_free(&stack);
  return value ? value : valk_lval_nil();
}

valk_lval_t *valk_eval_trampoline_with_stack(valk_eval_stack_t *stack,
                                              valk_lval_t *initial_value) {
  // Save and set current stack for nested perform/resume access
  valk_eval_stack_t *prev_stack = g_current_eval_stack;
  set_current_eval_stack(stack);

  valk_lval_t *value = initial_value;

  while (!valk_eval_stack_empty(stack)) {
    valk_eval_frame_t *frame = valk_eval_stack_top(stack);

    switch (frame->type) {
      case FRAME_EVAL:
        value = eval_step_expr(stack, frame, value);
        break;

      case FRAME_CALL_EVAL_FN:
        value = eval_step_call_fn(stack, frame, value);
        break;

      case FRAME_CALL_EVAL_ARGS:
        value = eval_step_call_args(stack, frame, value);
        break;

      case FRAME_CALL_APPLY:
        value = eval_step_call_apply(stack, frame, value);
        break;

      case FRAME_IF_COND:
        value = eval_step_if(stack, frame, value);
        break;

      case FRAME_DO_SEQUENCE:
        value = eval_step_sequence(stack, frame, value);
        break;

      case FRAME_DEF_VALUE:
      case FRAME_LET_BINDINGS:
      case FRAME_HANDLER_BODY:
      case FRAME_PERFORM:
        valk_eval_stack_pop(stack);
        value = valk_lval_err("Frame type %d not yet implemented", frame->type);
        break;
    }

    if (value && LVAL_TYPE(value) == LVAL_ERR) {
      set_current_eval_stack(prev_stack);
      return value;
    }
  }

  set_current_eval_stack(prev_stack);
  return value ? value : valk_lval_nil();
}

// ============================================================================
// GC Integration
// ============================================================================

void valk_gc_mark_eval_stack(valk_eval_stack_t *stack) {
  if (stack == NULL || stack->frames == NULL) return;

  // We need to forward declare the GC marking functions
  // For now, mark all lval pointers in frames
  extern void valk_gc_mark_lval_external(valk_lval_t *v);
  extern void valk_gc_mark_env_external(valk_lenv_t *env);

  for (size_t i = 0; i < stack->count; i++) {
    valk_eval_frame_t *frame = &stack->frames[i];

    // Mark environment
    if (frame->env) {
      valk_gc_mark_env_external(frame->env);
    }

    // Mark frame-specific data
    switch (frame->type) {
      case FRAME_EVAL:
        if (frame->eval.expr) {
          valk_gc_mark_lval_external(frame->eval.expr);
        }
        break;

      case FRAME_CALL_EVAL_FN:
      case FRAME_CALL_EVAL_ARGS:
      case FRAME_CALL_APPLY:
        if (frame->call.fn) {
          valk_gc_mark_lval_external(frame->call.fn);
        }
        for (size_t j = 0; j < frame->call.args_count; j++) {
          if (frame->call.args[j]) {
            valk_gc_mark_lval_external(frame->call.args[j]);
          }
        }
        if (frame->call.remaining) {
          valk_gc_mark_lval_external(frame->call.remaining);
        }
        if (frame->call.original_expr) {
          valk_gc_mark_lval_external(frame->call.original_expr);
        }
        break;

      case FRAME_IF_COND:
        if (frame->if_cond.then_branch) {
          valk_gc_mark_lval_external(frame->if_cond.then_branch);
        }
        if (frame->if_cond.else_branch) {
          valk_gc_mark_lval_external(frame->if_cond.else_branch);
        }
        break;

      case FRAME_DO_SEQUENCE:
        if (frame->seq.remaining) {
          valk_gc_mark_lval_external(frame->seq.remaining);
        }
        break;

      case FRAME_DEF_VALUE:
        if (frame->def.symbol) {
          valk_gc_mark_lval_external(frame->def.symbol);
        }
        break;

      case FRAME_LET_BINDINGS:
        if (frame->let.remaining_bindings) {
          valk_gc_mark_lval_external(frame->let.remaining_bindings);
        }
        if (frame->let.body) {
          valk_gc_mark_lval_external(frame->let.body);
        }
        if (frame->let.let_env) {
          valk_gc_mark_env_external(frame->let.let_env);
        }
        break;

      case FRAME_HANDLER_BODY:
        if (frame->handler.handlers) {
          valk_gc_mark_lval_external(frame->handler.handlers);
        }
        if (frame->handler.prev_handlers) {
          valk_gc_mark_lval_external(frame->handler.prev_handlers);
        }
        break;

      case FRAME_PERFORM:
        if (frame->perform.effect_op) {
          valk_gc_mark_lval_external(frame->perform.effect_op);
        }
        if (frame->perform.value) {
          valk_gc_mark_lval_external(frame->perform.value);
        }
        break;
    }
  }
}
