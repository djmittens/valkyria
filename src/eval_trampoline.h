#pragma once
#include "parser.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// ============================================================================
// Trampoline-Based Evaluator for Algebraic Effects
// ============================================================================
//
// This module implements a trampoline-based evaluator that replaces the
// recursive C-stack eval with an explicit frame stack. This is the foundation
// for proper continuation capture and algebraic effects.
//
// Key insight: Instead of using the C call stack to track "what to do next",
// we use an explicit eval stack that can be captured and restored.
//
// ============================================================================

// Forward declarations
typedef struct valk_eval_stack_t valk_eval_stack_t;
typedef struct valk_eval_frame_t valk_eval_frame_t;

// ============================================================================
// Frame Types
// ============================================================================

typedef enum {
  // Expression evaluation
  FRAME_EVAL,              // Evaluate an expression, return result

  // Function call frames
  FRAME_CALL_EVAL_FN,      // Evaluating function position of a call
  FRAME_CALL_EVAL_ARGS,    // Evaluating arguments
  FRAME_CALL_APPLY,        // All args ready, apply function

  // Special form frames
  FRAME_IF_COND,           // Evaluated condition, pick branch
  FRAME_DO_SEQUENCE,       // Sequence of expressions
  FRAME_DEF_VALUE,         // Binding a value
  FRAME_LET_BINDINGS,      // Processing let bindings

  // Effect frames (for future algebraic effects)
  FRAME_HANDLER_BODY,      // Inside with-handler body
  FRAME_PERFORM,           // Performing an effect
} valk_frame_type_t;

// ============================================================================
// Frame Structure
// ============================================================================

struct valk_eval_frame_t {
  valk_frame_type_t type;
  valk_lenv_t *env;              // Environment for this frame

  union {
    // FRAME_EVAL
    struct {
      valk_lval_t *expr;
    } eval;

    // FRAME_CALL_EVAL_FN, FRAME_CALL_EVAL_ARGS, FRAME_CALL_APPLY
    struct {
      valk_lval_t *fn;           // Evaluated function (NULL until ready)
      valk_lval_t **args;        // Array of evaluated args
      size_t args_capacity;
      size_t args_count;         // How many args evaluated so far
      valk_lval_t *remaining;    // Unevaluated args list
      valk_lval_t *original_expr; // For error messages
    } call;

    // FRAME_IF_COND
    struct {
      valk_lval_t *then_branch;
      valk_lval_t *else_branch;
    } if_cond;

    // FRAME_DO_SEQUENCE
    struct {
      valk_lval_t *remaining;    // Remaining expressions to evaluate
    } seq;

    // FRAME_DEF_VALUE
    struct {
      valk_lval_t *symbol;
    } def;

    // FRAME_LET_BINDINGS
    struct {
      valk_lval_t *remaining_bindings;
      valk_lval_t *body;
      valk_lenv_t *let_env;
    } let;

    // FRAME_HANDLER_BODY
    struct {
      valk_lval_t *handlers;     // Handler definitions
      valk_lval_t *prev_handlers; // Previous handler stack (for restore)
    } handler;

    // FRAME_PERFORM
    struct {
      valk_lval_t *effect_op;
      valk_lval_t *value;
    } perform;
  };
};

// ============================================================================
// Eval Stack Structure
// ============================================================================

struct valk_eval_stack_t {
  valk_eval_frame_t *frames;
  size_t count;
  size_t capacity;

  // For continuation capture
  uint64_t version;              // Incremented on push/pop for cache invalidation
};

// ============================================================================
// Stack Operations
// ============================================================================

// Initialize an eval stack (does not allocate)
void valk_eval_stack_init(valk_eval_stack_t *stack);

// Free eval stack resources
void valk_eval_stack_free(valk_eval_stack_t *stack);

// Push a frame onto the stack
void valk_eval_stack_push(valk_eval_stack_t *stack, valk_eval_frame_t frame);

// Get top frame (returns NULL if empty)
valk_eval_frame_t *valk_eval_stack_top(valk_eval_stack_t *stack);

// Pop top frame
void valk_eval_stack_pop(valk_eval_stack_t *stack);

// Check if stack is empty
bool valk_eval_stack_empty(valk_eval_stack_t *stack);

// Copy stack for continuation capture (shallow copy - frames reference heap data)
valk_eval_stack_t *valk_eval_stack_copy(valk_eval_stack_t *stack);

// ============================================================================
// Trampoline Entry Points
// ============================================================================

// Main trampoline entry point - evaluates expression using frame stack
valk_lval_t *valk_eval_trampoline(valk_lenv_t *env, valk_lval_t *expr);

// Trampoline with existing stack and initial value (for resume)
valk_lval_t *valk_eval_trampoline_with_stack(valk_eval_stack_t *stack,
                                              valk_lval_t *initial_value);

// ============================================================================
// GC Integration
// ============================================================================

// Mark all objects referenced by eval stack for GC
void valk_gc_mark_eval_stack(valk_eval_stack_t *stack);

// ============================================================================
// Feature Flag
// ============================================================================

// When defined, use trampoline eval instead of recursive eval
// #define VALK_TRAMPOLINE_EVAL 1

// Helper to check if trampoline eval is enabled at runtime
bool valk_trampoline_eval_enabled(void);

// Enable/disable trampoline eval at runtime (for testing)
void valk_trampoline_eval_set_enabled(bool enabled);
