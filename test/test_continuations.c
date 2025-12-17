#include "common.h"
#include "eval_trampoline.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

#include <string.h>

// ============================================================================
// Test Fixtures
// ============================================================================

static valk_gc_malloc_heap_t *g_heap = NULL;
static valk_lenv_t *g_env = NULL;

static void setup_test_env(void) {
  g_heap = valk_gc_malloc_heap_init(64 * 1024 * 1024, 128 * 1024 * 1024);
  valk_thread_ctx.allocator = (valk_mem_allocator_t *)g_heap;

  g_env = valk_lenv_empty();
  valk_lenv_builtins(g_env);
  valk_gc_malloc_set_root(g_heap, g_env);
}

static void teardown_test_env(void) {
  if (g_heap) {
    valk_gc_malloc_heap_destroy(g_heap);
    g_heap = NULL;
  }
  g_env = NULL;
  valk_thread_ctx.allocator = NULL;
}

// ============================================================================
// Phase 1 Tests: lenv cont and handler_stack fields
// ============================================================================

void test_lenv_cont_field_initialized_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Create a new environment
  valk_lenv_t *env = valk_lenv_empty();

  // Verify cont is initialized to NULL
  VALK_TEST_ASSERT(env->cont == NULL,
                   "New environment should have cont initialized to NULL");

  // Verify handler_stack is initialized to NULL
  VALK_TEST_ASSERT(env->handler_stack == NULL,
                   "New environment should have handler_stack initialized to NULL");

  teardown_test_env();
  VALK_PASS();
}

void test_lenv_handler_stack_field_initialized_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lenv_t *env = valk_lenv_empty();

  VALK_TEST_ASSERT(env->handler_stack == NULL,
                   "New environment should have handler_stack initialized to NULL");

  teardown_test_env();
  VALK_PASS();
}

void test_lenv_cont_field_preserved_on_copy(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Create environment and set cont to a value
  valk_lenv_t *env = valk_lenv_empty();

  // Create a continuation lval to set as cont
  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);
  valk_lval_t *cont = valk_lval_cont(&stack, env, true);

  env->cont = cont;

  // Copy the environment
  valk_lenv_t *copy = valk_lenv_copy(env);

  // Verify cont is preserved
  VALK_TEST_ASSERT(copy->cont == env->cont,
                   "Copied environment should preserve cont field");

  valk_eval_stack_free(&stack);
  teardown_test_env();
  VALK_PASS();
}

void test_lenv_handler_stack_preserved_on_copy(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lenv_t *env = valk_lenv_empty();

  // Create a handler stack (list of handlers)
  valk_lval_t *handler = valk_lval_num(42);  // Placeholder for handler
  valk_lval_t *handler_stack = valk_lval_cons(handler, valk_lval_nil());
  env->handler_stack = handler_stack;

  // Copy the environment
  valk_lenv_t *copy = valk_lenv_copy(env);

  // Verify handler_stack is preserved
  VALK_TEST_ASSERT(copy->handler_stack == env->handler_stack,
                   "Copied environment should preserve handler_stack field");

  teardown_test_env();
  VALK_PASS();
}

void test_gc_marks_lenv_cont(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Create environment with a continuation
  valk_lenv_t *env = valk_lenv_empty();

  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);
  valk_lval_t *cont = valk_lval_cont(&stack, g_env, true);

  env->cont = cont;

  // Set this env as root so it's reachable
  valk_gc_malloc_set_root(g_heap, env);

  // Run GC - the cont should be marked and not collected
  valk_gc_malloc_collect(g_heap, NULL);

  // Verify cont is still valid (not collected)
  VALK_TEST_ASSERT(env->cont != NULL,
                   "cont should not be collected by GC when reachable");
  VALK_TEST_ASSERT(LVAL_TYPE(env->cont) == LVAL_CONT,
                   "cont should still be LVAL_CONT type after GC");

  valk_eval_stack_free(&stack);
  teardown_test_env();
  VALK_PASS();
}

void test_gc_marks_handler_stack(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lenv_t *env = valk_lenv_empty();

  // Create a handler stack with some values
  valk_lval_t *handler1 = valk_lval_num(100);
  valk_lval_t *handler2 = valk_lval_num(200);
  valk_lval_t *handler_stack = valk_lval_cons(handler1,
                                 valk_lval_cons(handler2, valk_lval_nil()));
  env->handler_stack = handler_stack;

  // Set this env as root
  valk_gc_malloc_set_root(g_heap, env);

  // Run GC
  valk_gc_malloc_collect(g_heap, NULL);

  // Verify handler_stack is still valid
  VALK_TEST_ASSERT(env->handler_stack != NULL,
                   "handler_stack should not be collected by GC when reachable");
  VALK_TEST_ASSERT(LVAL_TYPE(env->handler_stack) == LVAL_CONS,
                   "handler_stack should still be LVAL_CONS type after GC");

  // Verify the values in handler_stack are preserved
  VALK_TEST_ASSERT(env->handler_stack->cons.head != NULL,
                   "handler_stack head should be preserved");
  VALK_TEST_ASSERT(LVAL_TYPE(env->handler_stack->cons.head) == LVAL_NUM,
                   "handler_stack head should still be LVAL_NUM");
  VALK_TEST_ASSERT(env->handler_stack->cons.head->num == 100,
                   "handler_stack head value should be 100");

  teardown_test_env();
  VALK_PASS();
}

// ============================================================================
// Phase 1 Tests: LVAL_CONT creation and operations
// ============================================================================

void test_lval_cont_creation(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Create an eval stack
  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);

  // Push some frames
  valk_eval_stack_push(&stack, (valk_eval_frame_t){
    .type = FRAME_EVAL,
    .env = g_env
  });

  // Create continuation
  valk_lval_t *cont = valk_lval_cont(&stack, g_env, true);

  // Verify creation
  VALK_TEST_ASSERT(cont != NULL, "Continuation should be created");
  VALK_TEST_ASSERT(LVAL_TYPE(cont) == LVAL_CONT,
                   "Continuation should have LVAL_CONT type");
  VALK_TEST_ASSERT(cont->cont.stack == &stack,
                   "Continuation should reference the stack");
  VALK_TEST_ASSERT(cont->cont.env == g_env,
                   "Continuation should reference the environment");
  VALK_TEST_ASSERT(cont->cont.one_shot == true,
                   "Continuation should have one_shot flag set");

  valk_eval_stack_free(&stack);
  teardown_test_env();
  VALK_PASS();
}

void test_lval_cont_creation_not_one_shot(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);

  // Create continuation with one_shot = false
  valk_lval_t *cont = valk_lval_cont(&stack, g_env, false);

  VALK_TEST_ASSERT(cont != NULL, "Continuation should be created");
  VALK_TEST_ASSERT(cont->cont.one_shot == false,
                   "Continuation should have one_shot flag unset");

  valk_eval_stack_free(&stack);
  teardown_test_env();
  VALK_PASS();
}

void test_lval_cont_with_null_stack(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Create continuation with NULL stack
  valk_lval_t *cont = valk_lval_cont(NULL, g_env, true);

  VALK_TEST_ASSERT(cont != NULL, "Continuation should be created even with NULL stack");
  VALK_TEST_ASSERT(LVAL_TYPE(cont) == LVAL_CONT,
                   "Continuation should have LVAL_CONT type");
  VALK_TEST_ASSERT(cont->cont.stack == NULL,
                   "Continuation should have NULL stack");

  teardown_test_env();
  VALK_PASS();
}

void test_lval_cont_with_null_env(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);

  // Create continuation with NULL env
  valk_lval_t *cont = valk_lval_cont(&stack, NULL, true);

  VALK_TEST_ASSERT(cont != NULL, "Continuation should be created even with NULL env");
  VALK_TEST_ASSERT(cont->cont.env == NULL,
                   "Continuation should have NULL env");

  valk_eval_stack_free(&stack);
  teardown_test_env();
  VALK_PASS();
}

// ============================================================================
// Phase 1 Tests: Environment chain with effects fields
// ============================================================================

void test_lenv_parent_chain_effects_fields(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Create parent env with handler_stack
  valk_lenv_t *parent = valk_lenv_empty();
  valk_lval_t *parent_handlers = valk_lval_cons(valk_lval_num(1), valk_lval_nil());
  parent->handler_stack = parent_handlers;

  // Create child env
  valk_lenv_t *child = valk_lenv_empty();
  child->parent = parent;
  valk_lval_t *child_handlers = valk_lval_cons(valk_lval_num(2), valk_lval_nil());
  child->handler_stack = child_handlers;

  // Verify each env has its own handler_stack
  VALK_TEST_ASSERT(parent->handler_stack != child->handler_stack,
                   "Parent and child should have separate handler_stacks");
  VALK_TEST_ASSERT(parent->handler_stack->cons.head->num == 1,
                   "Parent handler_stack should have value 1");
  VALK_TEST_ASSERT(child->handler_stack->cons.head->num == 2,
                   "Child handler_stack should have value 2");

  teardown_test_env();
  VALK_PASS();
}

void test_gc_marks_nested_env_effects_fields(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Create nested environments with effects fields
  valk_lenv_t *outer = valk_lenv_empty();
  outer->handler_stack = valk_lval_cons(valk_lval_num(10), valk_lval_nil());

  valk_lenv_t *inner = valk_lenv_empty();
  inner->parent = outer;
  inner->handler_stack = valk_lval_cons(valk_lval_num(20), valk_lval_nil());

  // Set inner as root (outer is reachable via parent)
  valk_gc_malloc_set_root(g_heap, inner);

  // Run GC
  valk_gc_malloc_collect(g_heap, NULL);

  // Verify both handler_stacks are preserved
  VALK_TEST_ASSERT(outer->handler_stack != NULL,
                   "Outer handler_stack should be preserved after GC");
  VALK_TEST_ASSERT(outer->handler_stack->cons.head->num == 10,
                   "Outer handler_stack value should be 10");
  VALK_TEST_ASSERT(inner->handler_stack != NULL,
                   "Inner handler_stack should be preserved after GC");
  VALK_TEST_ASSERT(inner->handler_stack->cons.head->num == 20,
                   "Inner handler_stack value should be 20");

  teardown_test_env();
  VALK_PASS();
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  // lenv effects field initialization
  valk_testsuite_add_test(suite, "test_lenv_cont_field_initialized_null",
                          test_lenv_cont_field_initialized_null);
  valk_testsuite_add_test(suite, "test_lenv_handler_stack_field_initialized_null",
                          test_lenv_handler_stack_field_initialized_null);

  // lenv effects field copying
  valk_testsuite_add_test(suite, "test_lenv_cont_field_preserved_on_copy",
                          test_lenv_cont_field_preserved_on_copy);
  valk_testsuite_add_test(suite, "test_lenv_handler_stack_preserved_on_copy",
                          test_lenv_handler_stack_preserved_on_copy);

  // GC marking of effects fields
  valk_testsuite_add_test(suite, "test_gc_marks_lenv_cont",
                          test_gc_marks_lenv_cont);
  valk_testsuite_add_test(suite, "test_gc_marks_handler_stack",
                          test_gc_marks_handler_stack);

  // LVAL_CONT creation
  valk_testsuite_add_test(suite, "test_lval_cont_creation",
                          test_lval_cont_creation);
  valk_testsuite_add_test(suite, "test_lval_cont_creation_not_one_shot",
                          test_lval_cont_creation_not_one_shot);
  valk_testsuite_add_test(suite, "test_lval_cont_with_null_stack",
                          test_lval_cont_with_null_stack);
  valk_testsuite_add_test(suite, "test_lval_cont_with_null_env",
                          test_lval_cont_with_null_env);

  // Environment chains with effects
  valk_testsuite_add_test(suite, "test_lenv_parent_chain_effects_fields",
                          test_lenv_parent_chain_effects_fields);
  valk_testsuite_add_test(suite, "test_gc_marks_nested_env_effects_fields",
                          test_gc_marks_nested_env_effects_fields);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);

  valk_mem_init_malloc();
  valk_testsuite_free(suite);

  return res;
}
