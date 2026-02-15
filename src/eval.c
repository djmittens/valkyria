#include "parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "builtins_internal.h"
#include "common.h"
#include "coverage.h"
#include "gc.h"
#include "memory.h"
#include "aio/aio_request_ctx.h"

extern valk_eval_metrics_t g_eval_metrics;

void valk_eval_stack_init(valk_eval_stack_t *stack) {
  stack->frames = malloc(sizeof(valk_cont_frame_t) * VALK_EVAL_STACK_INIT_CAP);
  stack->count = 0;
  stack->capacity = VALK_EVAL_STACK_INIT_CAP;
}

void valk_eval_stack_push(valk_eval_stack_t *stack, valk_cont_frame_t frame) {
  if (stack->count >= stack->capacity) {
    stack->capacity *= 2;
    stack->frames = realloc(stack->frames, sizeof(valk_cont_frame_t) * stack->capacity);
  }
  stack->frames[stack->count++] = frame;
}

valk_cont_frame_t valk_eval_stack_pop(valk_eval_stack_t *stack) {
  VALK_ASSERT(stack->count > 0, "Cannot pop from empty eval stack");
  return stack->frames[--stack->count];
}

void valk_eval_stack_destroy(valk_eval_stack_t *stack) {
  if (stack->frames) {
    for (u64 i = 0; i < stack->count; i++) {
      if (stack->frames[i].kind == CONT_COLLECT_ARG && stack->frames[i].collect_arg.args) {
        free(stack->frames[i].collect_arg.args);
      }
    }
    free(stack->frames);
    stack->frames = NULL;
  }
  stack->count = 0;
  stack->capacity = 0;
}

#define LVAL_RAISE(args, fmt, ...)                                       \
  do {                                                                   \
    char* _fmt =                                                         \
        valk_c_err_format((fmt), __FILE_NAME__, __LINE__, __FUNCTION__); \
    valk_lval_t* err = valk_lval_err(_fmt, ##__VA_ARGS__);               \
    valk_mem_free(_fmt);                                                 \
    return err;                                                          \
  } while (0)

#define VALK_SET_ORIGIN_ALLOCATOR(obj)                   \
  do {                                                   \
    (obj)->origin_allocator = valk_thread_ctx.allocator; \
    (obj)->gc_next = nullptr;                            \
  } while (0)

#define LVAL_ASSERT(args, cond, fmt, ...) \
  if ((cond)) {                           \
  } else {                                \
    LVAL_RAISE(args, fmt, ##__VA_ARGS__); \
  }

#define LVAL_ASSERT_TYPE(args, lval, _type, ...)                             \
  do {                                                                       \
    char _found = 0;                                                         \
    valk_ltype_e _expected[] = {(_type), ##__VA_ARGS__};                     \
    u64 _n_expected = sizeof(_expected) / sizeof(valk_ltype_e);           \
                                                                             \
    for (u64 i = 0; i < _n_expected; i++) {                               \
      if (LVAL_TYPE(lval) == _expected[i]) {                                 \
        _found = 1;                                                          \
        break;                                                               \
      }                                                                      \
    }                                                                        \
    if (!_found) {                                                           \
      char const* _expect_str[_n_expected];                                  \
      for (u64 i = 0; i < _n_expected; i++) {                             \
        _expect_str[i] = valk_ltype_name(_expected[i]);                      \
      }                                                                      \
      char* _estr = valk_str_join(_n_expected, _expect_str, ", ");           \
                                                                             \
      char* _fmt = valk_c_err_format("Actual: %s, Expected(One-Of): [%s]",   \
                                     __FILE_NAME__, __LINE__, __FUNCTION__); \
      valk_lval_t* err =                                                     \
          valk_lval_err(_fmt, valk_ltype_name(LVAL_TYPE(lval)), _estr);      \
      valk_mem_free(_estr);                                                  \
      valk_mem_free(_fmt);                                                   \
      return err;                                                            \
    }                                                                        \
  } while (0)

static inline int valk_is_list_type(valk_ltype_e type) {
  return type == LVAL_CONS || type == LVAL_QEXPR || type == LVAL_NIL;
}

static bool valk_is_tagged_list(valk_lval_t* lval, const char* tag) {
  if (LVAL_TYPE(lval) != LVAL_CONS && LVAL_TYPE(lval) != LVAL_QEXPR) {
    return false;
  }
  valk_lval_t* first = lval->cons.head;
  return LVAL_TYPE(first) == LVAL_SYM && strcmp(first->str, tag) == 0;
}

// LCOV_EXCL_BR_START - quasiquote has complex type dispatch logic
static valk_lval_t* valk_quasiquote_expand(valk_lenv_t* env, valk_lval_t* form) {
  if (LVAL_TYPE(form) != LVAL_CONS && LVAL_TYPE(form) != LVAL_QEXPR) {
    return form;
  }

  if (LVAL_TYPE(form) == LVAL_NIL) {
    return form;
  }

  if (valk_is_tagged_list(form, "unquote")) {
    if (valk_lval_list_count(form) != 2) {
      return valk_lval_err("unquote expects exactly 1 argument");
    }
    valk_lval_t* arg = valk_lval_list_nth(form, 1);
    return valk_lval_eval(env, arg);
  }

  if (valk_is_tagged_list(form, "unquote-splicing")) {
    return valk_lval_err("unquote-splicing (,@) not valid at top level of quasiquote");
  }

  bool is_qexpr = (form->flags & LVAL_FLAG_QUOTED) != 0;

  u64 capacity = 16;
  u64 count = 0;
  valk_lval_t** elements = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);

  valk_lval_t* curr = form;
  while (LVAL_TYPE(curr) != LVAL_NIL) {
    valk_lval_t* elem = curr->cons.head;

    if (valk_is_tagged_list(elem, "unquote-splicing")) {
      if (valk_lval_list_count(elem) != 2) {
        return valk_lval_err("unquote-splicing expects exactly 1 argument");
      }
      valk_lval_t* splice_arg = valk_lval_list_nth(elem, 1);
      valk_lval_t* splice_result = valk_lval_eval(env, splice_arg);
      if (LVAL_TYPE(splice_result) == LVAL_ERR) {
        return splice_result;
      }

      if (LVAL_TYPE(splice_result) != LVAL_NIL &&
          LVAL_TYPE(splice_result) != LVAL_CONS &&
          LVAL_TYPE(splice_result) != LVAL_QEXPR) {
        return valk_lval_err("unquote-splicing requires a list, got %s",
                             valk_ltype_name(LVAL_TYPE(splice_result)));
      }

      valk_lval_t* splice_curr = splice_result;
      while (LVAL_TYPE(splice_curr) != LVAL_NIL) {
        if (count >= capacity) {
          capacity *= 2;
          valk_lval_t** new_elements = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);
          memcpy(new_elements, elements, sizeof(valk_lval_t*) * count);
          elements = new_elements;
        }
        elements[count++] = splice_curr->cons.head;
        splice_curr = splice_curr->cons.tail;
      }
    } else {
      valk_lval_t* expanded = valk_quasiquote_expand(env, elem);
      if (LVAL_TYPE(expanded) == LVAL_ERR) {
        return expanded;
      }

      if (count >= capacity) {
        capacity *= 2;
        valk_lval_t** new_elements = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);
        memcpy(new_elements, elements, sizeof(valk_lval_t*) * count);
        elements = new_elements;
      }
      elements[count++] = expanded;
    }

    curr = curr->cons.tail;
  }

  valk_lval_t* result = valk_lval_nil();
  for (u64 j = count; j > 0; j--) {
    if (is_qexpr) {
      result = valk_lval_qcons(elements[j - 1], result);
    } else {
      result = valk_lval_cons(elements[j - 1], result);
    }
  }

  return result;
}
// LCOV_EXCL_BR_STOP

static valk_eval_result_t valk_eval_apply_func_iter(valk_lenv_t* env, valk_lval_t* func, valk_lval_t* args);

static valk_eval_result_t valk_eval_apply_func_iter(valk_lenv_t* env, valk_lval_t* func, valk_lval_t* args) {
  if (LVAL_TYPE(func) != LVAL_FUN) {
    return valk_eval_value(valk_lval_err("Cannot call non-function: %s", valk_ltype_name(LVAL_TYPE(func))));
  }

  u32 depth = atomic_fetch_add(&g_eval_metrics.stack_depth, 1) + 1;
  if (depth > g_eval_metrics.stack_depth_max) {
    g_eval_metrics.stack_depth_max = depth;
  }

  if (func->fun.builtin) {
    atomic_fetch_add(&g_eval_metrics.builtin_calls, 1);
    valk_lval_t* result = func->fun.builtin(env, args);
    atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
    // LCOV_EXCL_START - defensive check: builtins should never return NULL
    if (result == NULL) {
      return valk_eval_value(valk_lval_err("Internal error: builtin returned NULL"));
    }
    // LCOV_EXCL_STOP
    return valk_eval_value(result);
  }

  atomic_fetch_add(&g_eval_metrics.function_calls, 1);
  valk_thread_ctx.call_depth++;

  u64 given = valk_lval_list_count(args);
  u64 num_formals = valk_lval_list_count(func->fun.formals);

  valk_lenv_t* call_env = valk_lenv_empty();
  // LCOV_EXCL_BR_START - closures always have env, else branch rarely exercised
  if (func->fun.env) {
    call_env->parent = func->fun.env;
  } else {
    call_env->parent = env;
  }
  // LCOV_EXCL_BR_STOP

  // LCOV_EXCL_BR_START - lambda argument binding has many internal branches for variadics/partial application
  valk_lval_t* formal_iter = func->fun.formals;
  valk_lval_t* arg_iter = args;
  bool saw_varargs = false;

  while (!valk_lval_list_is_empty(formal_iter) && !valk_lval_list_is_empty(arg_iter)) {
    valk_lval_t* formal_sym = formal_iter->cons.head;

    if (LVAL_TYPE(formal_sym) == LVAL_SYM && strcmp(formal_sym->str, "&") == 0) {
      formal_iter = formal_iter->cons.tail;
      if (valk_lval_list_is_empty(formal_iter)) {
        valk_thread_ctx.call_depth--;
        atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
        return valk_eval_value(valk_lval_err("Invalid function format: & not followed by varargs name"));
      }
      valk_lval_t* varargs_sym = formal_iter->cons.head;
      valk_lval_t* varargs_list = valk_builtin_list(nullptr, arg_iter);
      valk_lenv_put(call_env, varargs_sym, varargs_list);
      saw_varargs = true;
      arg_iter = valk_lval_nil();
      formal_iter = formal_iter->cons.tail;
      break;
    }

    valk_lval_t* val = arg_iter->cons.head;
    valk_lenv_put(call_env, formal_sym, val);
    formal_iter = formal_iter->cons.tail;
    arg_iter = arg_iter->cons.tail;
  }

  if (!valk_lval_list_is_empty(arg_iter) && !saw_varargs) {
    valk_thread_ctx.call_depth--;
    atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
    return valk_eval_value(valk_lval_err("More arguments were given than required. Actual: %zu, Expected: %zu", given, num_formals));
  }

  if (!valk_lval_list_is_empty(formal_iter)) {
    if (!valk_lval_list_is_empty(formal_iter) &&
        LVAL_TYPE(formal_iter->cons.head) == LVAL_SYM &&
        strcmp(formal_iter->cons.head->str, "&") == 0) {
      formal_iter = formal_iter->cons.tail;
      if (valk_lval_list_is_empty(formal_iter)) {
        valk_thread_ctx.call_depth--;
        atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
        return valk_eval_value(valk_lval_err("Invalid function format: & not followed by varargs name"));
      }
      valk_lval_t* varargs_sym = formal_iter->cons.head;
      valk_lenv_put(call_env, varargs_sym, valk_lval_nil());
      formal_iter = formal_iter->cons.tail;
    }

    if (!valk_lval_list_is_empty(formal_iter)) {
      valk_lval_t* partial = valk_mem_alloc(sizeof(valk_lval_t));
      partial->flags = LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
      VALK_SET_ORIGIN_ALLOCATOR(partial);
      partial->fun.builtin = nullptr;
      partial->fun.arity = func->fun.arity;
      partial->fun.name = func->fun.name;
      partial->fun.env = call_env;
      partial->fun.formals = formal_iter;
      partial->fun.body = func->fun.body;
      valk_thread_ctx.call_depth--;
      atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
      return valk_eval_value(partial);
    }
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t* body = func->fun.body;
  if (LVAL_TYPE(body) == LVAL_CONS && (body->flags & LVAL_FLAG_QUOTED)) {
    body = valk_qexpr_to_cons(body);
  }

  if (valk_is_list_type(LVAL_TYPE(body)) && valk_lval_list_count(body) > 0) {
    valk_lval_t* first_elem = body->cons.head;
    if (valk_is_list_type(LVAL_TYPE(first_elem))) {
      valk_lval_t* first_expr = body->cons.head;
      valk_lval_t* remaining = body->cons.tail;
      return valk_eval_thunk_body(first_expr, call_env, remaining, call_env);
    }
  }

  return valk_eval_thunk_body(body, call_env, NULL, call_env);
}

#define SETUP_THUNK_CONTINUATION(res, stack_ptr, frame_env, expr_var, cur_env_var) do { \
  valk_eval_stack_push((stack_ptr), (valk_cont_frame_t){.kind = CONT_LAMBDA_DONE, .env = (frame_env)}); \
  if ((res).thunk.remaining_body != NULL && !valk_lval_list_is_empty((res).thunk.remaining_body)) { \
    valk_eval_stack_push((stack_ptr), (valk_cont_frame_t){ \
      .kind = CONT_BODY_NEXT, \
      .env = (res).thunk.env, \
      .body_next = {.remaining = (res).thunk.remaining_body, .call_env = (res).thunk.call_env} \
    }); \
  } \
  (expr_var) = (res).thunk.expr; \
  (cur_env_var) = (res).thunk.env; \
} while(0)

static valk_lval_t* valk_lval_eval_iterative(valk_lenv_t* env, valk_lval_t* lval) {
  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);
  
  valk_lval_t* expr = lval;
  valk_lenv_t* cur_env = env;
  valk_lval_t* value = NULL;
  
  void *saved_stack = valk_thread_ctx.eval_stack;
  valk_lval_t *saved_expr = valk_thread_ctx.eval_expr;
  valk_lval_t *saved_value = valk_thread_ctx.eval_value;
  valk_thread_ctx.eval_stack = &stack;
  
  valk_eval_stack_push(&stack, (valk_cont_frame_t){.kind = CONT_DONE, .env = env});

  while (1) {
    valk_thread_ctx.eval_expr = expr;
    valk_thread_ctx.eval_value = value;

    VALK_GC_SAFE_POINT();
    
    expr = valk_thread_ctx.eval_expr;
    value = valk_thread_ctx.eval_value;
    
    atomic_fetch_add(&g_eval_metrics.evals_total, 1);
    
    if (expr != NULL) {  // LCOV_EXCL_BR_LINE - evaluator dispatch
      // LCOV_EXCL_BR_START - type dispatch has many short-circuit branches
      if (LVAL_TYPE(expr) == LVAL_NUM || LVAL_TYPE(expr) == LVAL_STR ||
          LVAL_TYPE(expr) == LVAL_FUN || LVAL_TYPE(expr) == LVAL_ERR ||
          LVAL_TYPE(expr) == LVAL_NIL || LVAL_TYPE(expr) == LVAL_REF ||
          LVAL_TYPE(expr) == LVAL_HANDLE ||
          (LVAL_TYPE(expr) == LVAL_CONS && (expr->flags & LVAL_FLAG_QUOTED))) {
        // LCOV_EXCL_BR_STOP
        value = expr;
        expr = NULL;
        goto apply_cont;
      }
      
      if (LVAL_TYPE(expr) == LVAL_SYM) {
        VALK_COVERAGE_RECORD_LVAL(expr);
        if (expr->str[0] == ':') {
          value = expr;
        } else {
          value = valk_lenv_get(cur_env, expr);
        }
        expr = NULL;
        goto apply_cont;
      }
      
      VALK_COVERAGE_RECORD_LVAL(expr);

      if (LVAL_TYPE(expr) == LVAL_CONS) {  // LCOV_EXCL_BR_LINE - evaluator dispatch
        u64 count = valk_lval_list_count(expr);

        if (count == 0) {  // LCOV_EXCL_BR_LINE - empty list is rare
          value = valk_lval_nil();
          expr = NULL;
          goto apply_cont;
        }
        
        if (count == 1) {
          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_SINGLE_ELEM,
            .env = cur_env
          });
          expr = valk_lval_list_nth(expr, 0);
          continue;
        }
        
        valk_lval_t* first = expr->cons.head;
        if (LVAL_TYPE(first) == LVAL_SYM) {
          if (strcmp(first->str, "quasiquote") == 0) {
            if (count != 2) {
              value = valk_lval_err("quasiquote expects exactly 1 argument, got %zu", count - 1);
            } else {
              value = valk_quasiquote_expand(cur_env, valk_lval_list_nth(expr, 1));
            }
            expr = NULL;
            goto apply_cont;
          }
          
          if (strcmp(first->str, "if") == 0) {
            if (count < 3 || count > 4) {
              value = valk_lval_err("if requires 2-3 arguments, got %zu", count - 1);
              expr = NULL;
              goto apply_cont;
            }
            valk_lval_t* cond = valk_lval_list_nth(expr, 1);
            valk_lval_t* true_branch = valk_lval_list_nth(expr, 2);
            valk_lval_t* false_branch = (count == 4) ? valk_lval_list_nth(expr, 3) : valk_lval_nil();
            
            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_IF_BRANCH,
              .env = cur_env,
              .if_branch = {.true_branch = true_branch, .false_branch = false_branch}
            });
            expr = cond;
            continue;
          }

          if (strcmp(first->str, "ctx/with-deadline") == 0) {
            if (count < 3) {
              value = valk_lval_err("ctx/with-deadline requires timeout-ms and body, got %zu args", count - 1);
              expr = NULL;
              goto apply_cont;
            }
            valk_lval_t* timeout_expr = valk_lval_list_nth(expr, 1);
            valk_lval_t* body = expr->cons.tail->cons.tail;

            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_CTX_DEADLINE,
              .env = cur_env,
              .ctx_deadline = {.body = body, .old_ctx = valk_thread_ctx.request_ctx}
            });
            expr = timeout_expr;
            continue;
          }

          if (strcmp(first->str, "ctx/with") == 0) {
            if (count < 4) {
              value = valk_lval_err("ctx/with requires key, value, and body, got %zu args", count - 1);
              expr = NULL;
              goto apply_cont;
            }
            valk_lval_t* key_expr = valk_lval_list_nth(expr, 1);
            valk_lval_t* value_expr = valk_lval_list_nth(expr, 2);
            valk_lval_t* body = expr->cons.tail->cons.tail->cons.tail;

            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_CTX_WITH,
              .env = cur_env,
              .ctx_with = {.value_expr = value_expr, .body = body, .old_ctx = valk_thread_ctx.request_ctx}
            });
            expr = key_expr;
            continue;
          }
        }
        
        valk_eval_stack_push(&stack, (valk_cont_frame_t){
          .kind = CONT_EVAL_ARGS,
          .env = cur_env,
          .eval_args = {.func = NULL, .remaining = expr->cons.tail}
        });
        expr = first;
        continue;
      }
      
      value = valk_lval_err("Unknown value type in evaluation: %s", valk_ltype_name(LVAL_TYPE(expr)));
      expr = NULL;
    }
    
apply_cont:
    {
      VALK_ASSERT(value != nullptr, "value must not be null at apply_cont");
      valk_cont_frame_t frame = valk_eval_stack_pop(&stack);

      switch (frame.kind) {  // LCOV_EXCL_BR_LINE - continuation dispatch (not all types exercised)
        case CONT_DONE:
          valk_eval_stack_destroy(&stack);
          valk_thread_ctx.eval_stack = saved_stack;
          valk_thread_ctx.eval_expr = saved_expr;
          valk_thread_ctx.eval_value = saved_value;
          return value;
          
        case CONT_SINGLE_ELEM:
          if (LVAL_TYPE(value) == LVAL_FUN) {
            valk_eval_result_t res = valk_eval_apply_func_iter(frame.env, value, valk_lval_nil());
            if (!res.is_thunk) {
              value = res.value;
              if (LVAL_TYPE(value) == LVAL_ERR) goto apply_cont;
            } else {
              SETUP_THUNK_CONTINUATION(res, &stack, frame.env, expr, cur_env);
              continue;
            }
          }
          goto apply_cont;
          
        case CONT_EVAL_ARGS: {
          if (LVAL_TYPE(value) == LVAL_ERR) goto apply_cont;
          
          valk_lval_t* func = value;
          valk_lval_t* remaining = frame.eval_args.remaining;
          
          u64 arg_count = valk_lval_list_count(remaining);
          valk_lval_t** args = malloc(sizeof(valk_lval_t*) * arg_count);
          
          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_COLLECT_ARG,
            .env = frame.env,
            .collect_arg = {
              .func = func,
              .args = args,
              .count = 0,
              .capacity = arg_count,
              .remaining = remaining->cons.tail
            }
          });
          expr = remaining->cons.head;
          cur_env = frame.env;
          continue;
        }
        
        case CONT_COLLECT_ARG: {
          frame.collect_arg.args[frame.collect_arg.count++] = value;
          
          if (valk_lval_list_is_empty(frame.collect_arg.remaining)) {
            valk_lval_t* args_list = valk_lval_list(frame.collect_arg.args, frame.collect_arg.count);
            free(frame.collect_arg.args);
            valk_eval_result_t res = valk_eval_apply_func_iter(frame.env, frame.collect_arg.func, args_list);
            if (!res.is_thunk) {
              value = res.value;
              goto apply_cont;
            } else {
              SETUP_THUNK_CONTINUATION(res, &stack, frame.env, expr, cur_env);
              continue;
            }
          }
          
          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_COLLECT_ARG,
            .env = frame.env,
            .collect_arg = {
              .func = frame.collect_arg.func,
              .args = frame.collect_arg.args,
              .count = frame.collect_arg.count,
              .capacity = frame.collect_arg.capacity,
              .remaining = frame.collect_arg.remaining->cons.tail
            }
          });
          expr = frame.collect_arg.remaining->cons.head;
          cur_env = frame.env;
          continue;
        }
        
        case CONT_IF_BRANCH: {
          if (LVAL_TYPE(value) == LVAL_ERR) goto apply_cont;
          
          bool condition = false;
          if (LVAL_TYPE(value) == LVAL_NUM) {
            condition = (value->num != 0);
          } else if (LVAL_TYPE(value) != LVAL_NIL) {
            condition = true;
          }
          
          valk_lval_t* branch = condition ? frame.if_branch.true_branch : frame.if_branch.false_branch;
          if (LVAL_TYPE(branch) == LVAL_CONS && (branch->flags & LVAL_FLAG_QUOTED)) {
            branch = valk_qexpr_to_cons(branch);
          }
          expr = branch;
          cur_env = frame.env;
          continue;
        }
        
        case CONT_BODY_NEXT: {
          if (LVAL_TYPE(value) == LVAL_ERR) {
            goto apply_cont;
          }
          
          if (valk_lval_list_is_empty(frame.body_next.remaining)) {
            goto apply_cont;
          }
          
          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_BODY_NEXT,
            .env = frame.env,
            .body_next = {
              .remaining = frame.body_next.remaining->cons.tail,
              .call_env = frame.body_next.call_env
            }
          });
          expr = frame.body_next.remaining->cons.head;
          cur_env = frame.body_next.call_env;
          continue;
        }
        
        case CONT_LAMBDA_DONE:
          valk_thread_ctx.call_depth--;
          atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
          goto apply_cont;

        case CONT_CTX_DEADLINE: {
          if (LVAL_TYPE(value) == LVAL_ERR) {
            valk_thread_ctx.request_ctx = frame.ctx_deadline.old_ctx;
            goto apply_cont;
          }
          if (LVAL_TYPE(value) != LVAL_NUM) {
            valk_thread_ctx.request_ctx = frame.ctx_deadline.old_ctx;
            value = valk_lval_err("ctx/with-deadline timeout must be a number, got %s", valk_ltype_name(LVAL_TYPE(value)));
            goto apply_cont;
          }

          u64 timeout_ms = (u64)value->num;
          valk_request_ctx_t *new_ctx = valk_request_ctx_with_timeout(
            valk_thread_ctx.request_ctx, timeout_ms, valk_thread_ctx.allocator);
          valk_thread_ctx.request_ctx = new_ctx;

          valk_lval_t *body = frame.ctx_deadline.body;

          if (valk_lval_list_is_empty(body)) {
            valk_thread_ctx.request_ctx = frame.ctx_deadline.old_ctx;
            value = valk_lval_nil();
            goto apply_cont;
          }

          if (valk_lval_list_is_empty(body->cons.tail)) {
            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_CTX_DEADLINE,
              .env = frame.env,
              .ctx_deadline = {.body = valk_lval_nil(), .old_ctx = frame.ctx_deadline.old_ctx}
            });
            expr = body->cons.head;
            cur_env = frame.env;
            continue;
          }

          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_CTX_DEADLINE,
            .env = frame.env,
            .ctx_deadline = {.body = body->cons.tail, .old_ctx = frame.ctx_deadline.old_ctx}
          });
          expr = body->cons.head;
          cur_env = frame.env;
          continue;
        }

        case CONT_CTX_WITH: {
          if (LVAL_TYPE(value) == LVAL_ERR) {
            valk_thread_ctx.request_ctx = frame.ctx_with.old_ctx;
            goto apply_cont;
          }

          valk_lval_t *key = value;
          valk_lval_t *value_expr = frame.ctx_with.value_expr;
          valk_lval_t *val = valk_lval_eval(frame.env, value_expr);
          if (LVAL_TYPE(val) == LVAL_ERR) {
            valk_thread_ctx.request_ctx = frame.ctx_with.old_ctx;
            value = val;
            goto apply_cont;
          }

          valk_request_ctx_t *new_ctx = valk_request_ctx_with_local(
            valk_thread_ctx.request_ctx, key, val, valk_thread_ctx.allocator);
          valk_thread_ctx.request_ctx = new_ctx;

          valk_lval_t *body = frame.ctx_with.body;
          if (valk_lval_list_is_empty(body)) {
            valk_thread_ctx.request_ctx = frame.ctx_with.old_ctx;
            value = valk_lval_nil();
            goto apply_cont;
          }

          if (valk_lval_list_is_empty(body->cons.tail)) {
            valk_eval_stack_push(&stack, (valk_cont_frame_t){
              .kind = CONT_CTX_DEADLINE,
              .env = frame.env,
              .ctx_deadline = {.body = valk_lval_nil(), .old_ctx = frame.ctx_with.old_ctx}
            });
            expr = body->cons.head;
            cur_env = frame.env;
            continue;
          }

          valk_eval_stack_push(&stack, (valk_cont_frame_t){
            .kind = CONT_CTX_DEADLINE,
            .env = frame.env,
            .ctx_deadline = {.body = body->cons.tail, .old_ctx = frame.ctx_with.old_ctx}
          });
          expr = body->cons.head;
          cur_env = frame.env;
          continue;
        }

        default:
          value = valk_lval_err("Unknown continuation type: %d", frame.kind);
          goto apply_cont;
      }
    }
  }
#undef SETUP_THUNK_CONTINUATION
}

valk_lval_t* valk_lval_eval(valk_lenv_t* env, valk_lval_t* lval) {
  return valk_lval_eval_iterative(env, lval);
}

valk_lval_t* valk_lval_eval_call(valk_lenv_t* env, valk_lval_t* func,
                                 valk_lval_t* args) {
  LVAL_ASSERT_TYPE(args, func, LVAL_FUN);

  valk_eval_result_t res = valk_eval_apply_func_iter(env, func, args);
  
  if (!res.is_thunk) {
    return res.value;
  }
  
  if (res.thunk.remaining_body != NULL && !valk_lval_list_is_empty(res.thunk.remaining_body)) {
    valk_lval_t* result = valk_lval_eval(res.thunk.env, res.thunk.expr);
    if (LVAL_TYPE(result) == LVAL_ERR) {
      valk_thread_ctx.call_depth--;
      atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
      return result;
    }
    
    valk_lval_t* curr = res.thunk.remaining_body;
    while (!valk_lval_list_is_empty(curr)) {
      result = valk_lval_eval(res.thunk.call_env, curr->cons.head);
      if (LVAL_TYPE(result) == LVAL_ERR) {
        valk_thread_ctx.call_depth--;
        atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
        return result;
      }
      curr = curr->cons.tail;
    }
    
    valk_thread_ctx.call_depth--;
    atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
    return result;
  }
  
  valk_lval_t* result = valk_lval_eval(res.thunk.env, res.thunk.expr);
  valk_thread_ctx.call_depth--;
  atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
  return result;
}
