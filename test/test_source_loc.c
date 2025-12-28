#define _GNU_SOURCE
#include <stdlib.h>
#include "testing.h"
#include "parser.h"
#include "memory.h"
#include "gc.h"

#ifdef VALK_COVERAGE
#include "coverage.h"
#include "source_loc.h"
#endif

void test_copy_preserves_source_loc(VALK_TEST_ARGS()) {
  VALK_TEST();
#ifdef VALK_COVERAGE
  valk_lval_t* original = valk_lval_num(42);
  original->cov_file_id = 1;
  original->cov_line = 10;
  original->cov_column = 5;

  valk_lval_t* copy = valk_lval_copy(original);

  VALK_TEST_ASSERT(copy->cov_file_id == 1, "file_id should be 1, got %d", copy->cov_file_id);
  VALK_TEST_ASSERT(copy->cov_line == 10, "line should be 10, got %d", copy->cov_line);
  VALK_TEST_ASSERT(copy->cov_column == 5, "column should be 5, got %d", copy->cov_column);
#else
  VALK_SKIP("VALK_COVERAGE not enabled");
#endif
  VALK_PASS();
}

void test_cons_inherits_head_loc(VALK_TEST_ARGS()) {
  VALK_TEST();
#ifdef VALK_COVERAGE
  valk_lval_t* head = valk_lval_num(1);
  head->cov_file_id = 3;
  head->cov_line = 30;
  head->cov_column = 7;

  valk_lval_t* tail = valk_lval_nil();
  valk_lval_t* cons = valk_lval_cons(head, tail);

  VALK_TEST_ASSERT(cons->cov_file_id == 3, "file_id should be 3, got %d", cons->cov_file_id);
  VALK_TEST_ASSERT(cons->cov_line == 30, "line should be 30, got %d", cons->cov_line);
  VALK_TEST_ASSERT(cons->cov_column == 7, "column should be 7, got %d", cons->cov_column);
#else
  VALK_SKIP("VALK_COVERAGE not enabled");
#endif
  VALK_PASS();
}

void test_qcons_inherits_head_loc(VALK_TEST_ARGS()) {
  VALK_TEST();
#ifdef VALK_COVERAGE
  valk_lval_t* head = valk_lval_num(1);
  head->cov_file_id = 4;
  head->cov_line = 40;
  head->cov_column = 8;

  valk_lval_t* tail = valk_lval_nil();
  valk_lval_t* qcons = valk_lval_qcons(head, tail);

  VALK_TEST_ASSERT(qcons->cov_file_id == 4, "file_id should be 4, got %d", qcons->cov_file_id);
  VALK_TEST_ASSERT(qcons->cov_line == 40, "line should be 40, got %d", qcons->cov_line);
  VALK_TEST_ASSERT(qcons->cov_column == 8, "column should be 8, got %d", qcons->cov_column);
#else
  VALK_SKIP("VALK_COVERAGE not enabled");
#endif
  VALK_PASS();
}

void test_list_inherits_first_elem_loc(VALK_TEST_ARGS()) {
  VALK_TEST();
#ifdef VALK_COVERAGE
  valk_lval_t* elems[3];
  elems[0] = valk_lval_num(1);
  elems[0]->cov_file_id = 5;
  elems[0]->cov_line = 50;
  elems[0]->cov_column = 9;
  elems[1] = valk_lval_num(2);
  elems[2] = valk_lval_num(3);

  valk_lval_t* list = valk_lval_list(elems, 3);

  VALK_TEST_ASSERT(list->cov_file_id == 5, "file_id should be 5, got %d", list->cov_file_id);
  VALK_TEST_ASSERT(list->cov_line == 50, "line should be 50, got %d", list->cov_line);
#else
  VALK_SKIP("VALK_COVERAGE not enabled");
#endif
  VALK_PASS();
}

void test_join_inherits_left_loc(VALK_TEST_ARGS()) {
  VALK_TEST();
#ifdef VALK_COVERAGE
  valk_lval_t* a_elems[2];
  a_elems[0] = valk_lval_num(1);
  a_elems[0]->cov_file_id = 6;
  a_elems[0]->cov_line = 60;
  a_elems[0]->cov_column = 10;
  a_elems[1] = valk_lval_num(2);

  valk_lval_t* b_elems[2];
  b_elems[0] = valk_lval_num(3);
  b_elems[1] = valk_lval_num(4);

  valk_lval_t* a = valk_lval_list(a_elems, 2);
  valk_lval_t* b = valk_lval_list(b_elems, 2);

  valk_lval_t* joined = valk_lval_join(a, b);

  VALK_TEST_ASSERT(joined->cov_file_id == 6, "file_id should be 6, got %d", joined->cov_file_id);
  VALK_TEST_ASSERT(joined->cov_line == 60, "line should be 60, got %d", joined->cov_line);
#else
  VALK_SKIP("VALK_COVERAGE not enabled");
#endif
  VALK_PASS();
}

void test_lambda_inherits_body_loc(VALK_TEST_ARGS()) {
  VALK_TEST();
#ifdef VALK_COVERAGE
  valk_lval_t* formals = valk_lval_qcons(valk_lval_sym("x"), valk_lval_nil());
  valk_lval_t* body = valk_lval_qcons(valk_lval_sym("+"), valk_lval_nil());
  body->cov_file_id = 7;
  body->cov_line = 70;
  body->cov_column = 11;

  valk_lenv_t* env = valk_lenv_empty();
  valk_lval_t* lambda = valk_lval_lambda(env, formals, body);

  VALK_TEST_ASSERT(lambda->cov_file_id == 7, "file_id should be 7, got %d", lambda->cov_file_id);
  VALK_TEST_ASSERT(lambda->cov_line == 70, "line should be 70, got %d", lambda->cov_line);
#else
  VALK_SKIP("VALK_COVERAGE not enabled");
#endif
  VALK_PASS();
}

void test_ref_has_zero_source_loc(VALK_TEST_ARGS()) {
  VALK_TEST();
#ifdef VALK_COVERAGE
  valk_lval_t* ref = valk_lval_ref("test", NULL, NULL);

  VALK_TEST_ASSERT(ref->cov_file_id == 0, "file_id should be 0, got %d", ref->cov_file_id);
  VALK_TEST_ASSERT(ref->cov_line == 0, "line should be 0, got %d", ref->cov_line);
  VALK_TEST_ASSERT(ref->cov_column == 0, "column should be 0, got %d", ref->cov_column);
#else
  VALK_SKIP("VALK_COVERAGE not enabled");
#endif
  VALK_PASS();
}

#ifdef VALK_COVERAGE
void test_branch_coverage_records_line(VALK_TEST_ARGS()) {
  VALK_TEST();

  putenv("VALK_COVERAGE=1");
  valk_coverage_init();
  valk_line_coverage_init();

  u16 file_id = valk_source_register_file("test_branch.valk");

  valk_coverage_record_branch(file_id, 15, true);
  valk_coverage_record_branch(file_id, 15, false);

  valk_line_coverage_file_t* fc = valk_coverage_get_file(file_id);
  VALK_TEST_ASSERT(fc != NULL, "file coverage should exist");

  valk_branch_t* br = fc->branches;
  while (br != NULL && br->line != 15) br = br->next;

  VALK_TEST_ASSERT(br != NULL, "branch at line 15 should exist");
  VALK_TEST_ASSERT(br->true_count == 1, "true_count should be 1, got %d", br->true_count);
  VALK_TEST_ASSERT(br->false_count == 1, "false_count should be 1, got %d", br->false_count);

  valk_line_coverage_reset();
  valk_source_registry_reset();

  VALK_PASS();
}
#endif

int main(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);
  valk_thread_ctx.allocator = (valk_mem_allocator_t*)heap;

  valk_test_suite_t* suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_copy_preserves_source_loc", test_copy_preserves_source_loc);
  valk_testsuite_add_test(suite, "test_cons_inherits_head_loc", test_cons_inherits_head_loc);
  valk_testsuite_add_test(suite, "test_qcons_inherits_head_loc", test_qcons_inherits_head_loc);
  valk_testsuite_add_test(suite, "test_list_inherits_first_elem_loc", test_list_inherits_first_elem_loc);
  valk_testsuite_add_test(suite, "test_join_inherits_left_loc", test_join_inherits_left_loc);
  valk_testsuite_add_test(suite, "test_lambda_inherits_body_loc", test_lambda_inherits_body_loc);
  valk_testsuite_add_test(suite, "test_ref_has_zero_source_loc", test_ref_has_zero_source_loc);
#ifdef VALK_COVERAGE
  valk_testsuite_add_test(suite, "test_branch_coverage_records_line", test_branch_coverage_records_line);
#endif

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
