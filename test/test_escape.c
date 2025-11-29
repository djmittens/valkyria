#include <stdio.h>
#include <stdlib.h>

#include "../src/gc.h"
#include "../src/memory.h"
#include "../src/parser.h"
#include "testing.h"

// Test 1: Values stored in environment are marked as escaping
void test_env_put_marks_escaping(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t* env = valk_lenv_empty();
  valk_lval_t* val = valk_lval_num(42);
  valk_lval_t* key = valk_lval_sym("x");

  // Initially not marked as escaping
  VALK_TEST_ASSERT(!LVAL_ESCAPES(val), "Value should not escape initially");

  // Store in environment
  valk_lenv_put(env, key, val);

  // Should be marked as escaping after put
  VALK_TEST_ASSERT(LVAL_ESCAPES(val),
                   "Value should be marked as escaping after env put");
  VALK_PASS();
}

// Test 2: Lambda captures are marked as escaping
void test_lambda_captures_escape(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t* formals =
      valk_lval_cons(valk_lval_sym("x"), valk_lval_nil());

  valk_lval_t* body =
      valk_lval_cons(valk_lval_sym("x"), valk_lval_nil());

  // Initially not marked as escaping
  VALK_TEST_ASSERT(!LVAL_ESCAPES(formals),
                   "Formals should not escape initially");
  VALK_TEST_ASSERT(!LVAL_ESCAPES(body), "Body should not escape initially");

  // Create lambda (captures formals and body)
  valk_lval_t* lambda = valk_lval_lambda(nullptr, formals, body);

  // Should be marked as escaping after lambda creation
  VALK_TEST_ASSERT(LVAL_ESCAPES(formals),
                   "Formals should escape after lambda creation");
  VALK_TEST_ASSERT(LVAL_ESCAPES(body),
                   "Body should escape after lambda creation");

  (void)lambda;  // Suppress unused warning
  VALK_PASS();
}

// Test 3: Zero-copy for frozen heap values in valk_intern
void test_zero_copy_frozen_heap_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a GC heap
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024);
  valk_lenv_t* env = valk_lenv_empty();
  env->allocator = (void*)heap;

  // Allocate a value on the heap and freeze it
  valk_lval_t* original;
  VALK_WITH_ALLOC((void*)heap) {
    original = valk_lval_num(42);
    valk_lval_freeze(original);
  }

  // Verify it's on the heap and frozen
  VALK_TEST_ASSERT(LVAL_ALLOC(original) == LVAL_ALLOC_HEAP,
                   "Value should be on heap");
  VALK_TEST_ASSERT(LVAL_IS_FROZEN(original), "Value should be frozen");

  // Intern should return the same pointer (zero copy)
  valk_lval_t* interned = valk_intern(env, original);
  VALK_TEST_ASSERT(
      interned == original,
      "Interning frozen heap value should return same pointer (zero copy)");

  // Clean up GC heap to avoid memory leaks
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test 4: Shallow copy for frozen children in valk_lval_copy
void test_shallow_copy_frozen_children(VALK_TEST_ARGS()) {
  VALK_TEST();
  //
  // // Create a list with frozen elements on heap
  // valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024);
  //
  // valk_lval_t* list;
  // valk_lval_t* elem1;
  // valk_lval_t* elem2;
  //
  // VALK_WITH_ALLOC((void*)heap) {
  //   elem1 = valk_lval_num(1);
  //   elem2 = valk_lval_num(2);
  //   valk_lval_freeze(elem1);
  //   valk_lval_freeze(elem2);
  //
  //   list = valk_lval_qexpr_empty();
  // }
  //
  // // Add frozen heap elements to list
  // VALK_WITH_ALLOC((void*)heap) {
  //   valk_lval_add(list, elem1);
  //   valk_lval_add(list, elem2);
  // }
  //
  // // Copy the list
  // valk_lval_t* list_copy;
  // VALK_WITH_ALLOC((void*)heap) { list_copy = valk_lval_copy(list); }
  //
  // // The frozen heap children should be aliased (same pointers)
  // VALK_TEST_ASSERT(valk_lval_list_nth(list_copy, 0) == elem1,
  //                  "Frozen heap child should be aliased, not deep copied");
  // VALK_TEST_ASSERT(valk_lval_list_nth(list_copy, 1) == elem2,
  //                  "Frozen heap child should be aliased, not deep copied");
  //
  // // Clean up GC heap to avoid memory leaks
  // valk_gc_malloc_heap_destroy(heap);
  // VALK_PASS();
  VALK_SKIP("Not implemented");
}

// Test 5: Scratch values are copied even if frozen
void test_scratch_frozen_values_copied(VALK_TEST_ARGS()) {
  VALK_TEST();

  // size_t const SCRATCH_SIZE = 4 * 1024 * 1024;
  // size_t const GLOBAL_SIZE = 16 * 1024 * 1024;
  //
  // valk_mem_arena_t* scratch = malloc(SCRATCH_SIZE);
  // valk_mem_arena_init(scratch, SCRATCH_SIZE - sizeof(*scratch));
  //
  // valk_mem_arena_t* global = malloc(GLOBAL_SIZE);
  // valk_mem_arena_init(global, GLOBAL_SIZE - sizeof(*global));
  //
  // valk_lenv_t* env = valk_lenv_empty();
  // env->allocator = (void*)global;
  //
  // // Create a frozen value in scratch
  // valk_lval_t* scratch_val;
  // VALK_WITH_ALLOC((void*)scratch) {
  //   scratch_val = valk_lval_num(42);
  //   valk_lval_freeze(scratch_val);
  // }
  //
  // VALK_TEST_ASSERT(LVAL_ALLOC(scratch_val) == LVAL_ALLOC_SCRATCH,
  //                  "Value should be in scratch");
  // VALK_TEST_ASSERT(LVAL_IS_FROZEN(scratch_val), "Value should be frozen");
  //
  // // Intern into global - should make a copy (not alias)
  // valk_lval_t* interned = valk_intern(env, scratch_val);
  //
  // VALK_TEST_ASSERT(
  //     interned != scratch_val,
  //     "Scratch values should be copied, not aliased (even if frozen)");
  // // Note: Both arenas have type VALK_ALLOC_ARENA, so both will be marked
  // // LVAL_ALLOC_SCRATCH The distinction between "global" and "scratch" arena is
  // // semantic, not in the allocator type
  // VALK_TEST_ASSERT(
  //     LVAL_ALLOC(interned) == LVAL_ALLOC_SCRATCH,
  //     "Interned value from arena should be marked as scratch (arena type)");
  //
  // free(scratch);
  // free(global);
  // VALK_PASS();
  VALK_SKIP("Not implemented");
}

// Test 6: Function return values are marked as escaping
void test_function_return_escapes(VALK_TEST_ARGS()) {
  VALK_TEST();
  // valk_lenv_t* env = valk_lenv_empty();
  // valk_lenv_builtins(env);
  //
  // // Create and evaluate a lambda that returns a value
  // // (\ {x} {x})
  // valk_lval_t* formals = valk_lval_qexpr_empty();
  // valk_lval_add(formals, valk_lval_sym("x"));
  //
  // valk_lval_t* body = valk_lval_qexpr_empty();
  // valk_lval_add(body, valk_lval_sym("x"));
  //
  // valk_lval_t* lambda = valk_lval_lambda(env, formals, body);
  //
  // // Call the lambda with an argument: ((\ {x} {x}) 42)
  // // Build S-expr: (lambda 42)
  // valk_lval_t* call_sexpr = valk_lval_sexpr_empty();
  // valk_lval_add(call_sexpr, lambda);
  // valk_lval_add(call_sexpr, valk_lval_num(42));
  //
  // // Evaluate through valk_lval_eval to properly handle thunks
  // valk_lval_t* result = valk_lval_eval(env, call_sexpr);
  //
  // // The return value should be marked as escaping
  // VALK_TEST_ASSERT(LVAL_ESCAPES(result),
  //                  "Function return value should be marked as escaping");
  // VALK_PASS();
  VALK_SKIP("Not implemented");
}

int main(int argc, const char** argv) {
  (void)argc;
  (void)argv;

  // Use GC heap for everything, including test suite
  size_t const GC_THRESHOLD_BYTES = 16 * 1024 * 1024;  // 16 MiB
  valk_gc_malloc_heap_t* gc_heap = valk_gc_malloc_heap_init(GC_THRESHOLD_BYTES);
  valk_thread_ctx.allocator = (void*)gc_heap;

  valk_test_suite_t* suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_env_put_marks_escaping",
                          test_env_put_marks_escaping);
  valk_testsuite_add_test(suite, "test_lambda_captures_escape",
                          test_lambda_captures_escape);
  valk_testsuite_add_test(suite, "test_zero_copy_frozen_heap_values",
                          test_zero_copy_frozen_heap_values);
  valk_testsuite_add_test(suite, "test_shallow_copy_frozen_children",
                          test_shallow_copy_frozen_children);
  valk_testsuite_add_test(suite, "test_scratch_frozen_values_copied",
                          test_scratch_frozen_values_copied);
  valk_testsuite_add_test(suite, "test_function_return_escapes",
                          test_function_return_escapes);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);

  valk_testsuite_free(suite);

  // Clean up GC heap to avoid memory leaks
  valk_gc_malloc_heap_destroy(gc_heap);

  return res;
}
