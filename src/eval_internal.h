#pragma once
#include <stdbool.h>
#include "types.h"

typedef struct valk_lval_t valk_lval_t;
typedef struct valk_lenv_t valk_lenv_t;

// ============================================================================
// Iterative Evaluator (Stack-based, no C recursion)
// ============================================================================

typedef enum {
  CONT_DONE,           // Return final value
  CONT_EVAL_ARGS,      // Function evaluated, now evaluate arguments
  CONT_COLLECT_ARG,    // Collecting evaluated arguments one by one
  CONT_APPLY_FUNC,     // All args collected, apply function
  CONT_IF_BRANCH,      // Condition evaluated, pick and eval branch
  CONT_DO_NEXT,        // Evaluated one expr in do-sequence
  CONT_SELECT_CHECK,   // Evaluated condition in select clause
  CONT_BODY_NEXT,      // Evaluated one expr in function body
  CONT_SINGLE_ELEM,    // Single-element list: if result is function, call it
  CONT_LAMBDA_DONE,    // Lambda body evaluated, decrement call depth
  CONT_CTX_DEADLINE,   // ctx/with-deadline: timeout evaluated, now eval body
  CONT_CTX_WITH,       // ctx/with: key/value evaluated, now eval body
} valk_cont_kind_e;

typedef struct valk_cont_frame {
  valk_cont_kind_e kind;
  valk_lenv_t *env;
  
  union {
    struct {
      valk_lval_t *func;
      valk_lval_t *remaining;
    } eval_args;
    
    struct {
      valk_lval_t *func;
      valk_lval_t **args;
      u64 count;
      u64 capacity;
      valk_lval_t *remaining;
    } collect_arg;
    
    struct {
      valk_lval_t *true_branch;
      valk_lval_t *false_branch;
    } if_branch;
    
    struct {
      valk_lval_t *remaining;
    } do_next;
    
    struct {
      valk_lval_t *result_expr;
      valk_lval_t *remaining;
      valk_lval_t *original_args;
    } select_check;
    
    struct {
      valk_lval_t *remaining;
      valk_lenv_t *call_env;
    } body_next;

    struct {
      valk_lval_t *body;
      struct valk_request_ctx *old_ctx;
    } ctx_deadline;

    struct {
      valk_lval_t *value_expr;
      valk_lval_t *body;
      struct valk_request_ctx *old_ctx;
    } ctx_with;
  };
} valk_cont_frame_t;

#define VALK_EVAL_STACK_INIT_CAP 64

typedef struct {
  valk_cont_frame_t *frames;
  u64 count;
  u64 capacity;
} valk_eval_stack_t;

void valk_eval_stack_init(valk_eval_stack_t *stack);
void valk_eval_stack_push(valk_eval_stack_t *stack, valk_cont_frame_t frame);
valk_cont_frame_t valk_eval_stack_pop(valk_eval_stack_t *stack);
void valk_eval_stack_destroy(valk_eval_stack_t *stack);

typedef struct {
  bool is_thunk;
  union {
    valk_lval_t *value;
    struct {
      valk_lval_t *expr;
      valk_lenv_t *env;
      valk_lval_t *remaining_body;
      valk_lenv_t *call_env;
    } thunk;
  };
} valk_eval_result_t;

static inline valk_eval_result_t valk_eval_value(valk_lval_t *val) {
  return (valk_eval_result_t){.is_thunk = false, .value = val};
}

static inline valk_eval_result_t valk_eval_thunk(valk_lval_t *expr, valk_lenv_t *env) {
  return (valk_eval_result_t){
    .is_thunk = true,
    .thunk = {.expr = expr, .env = env, .remaining_body = nullptr, .call_env = nullptr}
  };
}

static inline valk_eval_result_t valk_eval_thunk_body(valk_lval_t *expr, valk_lenv_t *env,
                                                       valk_lval_t *remaining, valk_lenv_t *call_env) {
  return (valk_eval_result_t){
    .is_thunk = true,
    .thunk = {.expr = expr, .env = env, .remaining_body = remaining, .call_env = call_env}
  };
}

void valk_eval_metrics_get(u64* evals, u64* func_calls,
                            u64* builtin_calls, u32* stack_max,
                            u64* closures, u64* lookups);
