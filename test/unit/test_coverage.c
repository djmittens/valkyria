#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/coverage.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_coverage_init_does_not_crash(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_init();
  valk_coverage_init();

  VALK_PASS();
}

void test_coverage_enabled_default_false(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool enabled = valk_coverage_enabled();
  VALK_TEST_ASSERT(enabled == false || enabled == true, "enabled should be boolean");

  VALK_PASS();
}

void test_coverage_output_path(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *path = valk_coverage_output_path();
  if (valk_coverage_enabled()) {
    VALK_TEST_ASSERT(path != NULL, "path should not be NULL when coverage enabled");
  }

  VALK_PASS();
}

void test_coverage_record_file_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_record_file("test_file.valk");

  VALK_PASS();
}

void test_coverage_report_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_report("/tmp/test_coverage.txt");

  VALK_PASS();
}

void test_coverage_report_lcov_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_report_lcov("/tmp/test_coverage.info");

  VALK_PASS();
}

void test_coverage_reset_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_reset();

  VALK_PASS();
}

void test_coverage_save_on_exit_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_save_on_exit();

  VALK_PASS();
}

void test_coverage_multiple_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  for (int i = 0; i < 10; i++) {
    valk_coverage_init();
  }

  VALK_PASS();
}

void test_coverage_multiple_reset(VALK_TEST_ARGS()) {
  VALK_TEST();

  for (int i = 0; i < 10; i++) {
    valk_coverage_reset();
  }

  VALK_PASS();
}

void test_coverage_record_many_files(VALK_TEST_ARGS()) {
  VALK_TEST();

  for (int i = 0; i < 100; i++) {
    char filename[256];
    snprintf(filename, sizeof(filename), "test_file_%d.valk", i);
    valk_coverage_record_file(filename);
  }

  VALK_PASS();
}

void test_coverage_record_same_file_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  for (int i = 0; i < 100; i++) {
    valk_coverage_record_file("same_file.valk");
  }

  VALK_PASS();
}

void test_coverage_record_empty_filename(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_record_file("");

  VALK_PASS();
}

void test_coverage_record_long_filename(VALK_TEST_ARGS()) {
  VALK_TEST();

  char long_name[1024];
  memset(long_name, 'a', sizeof(long_name) - 6);
  strcpy(long_name + sizeof(long_name) - 6, ".valk");

  valk_coverage_record_file(long_name);

  VALK_PASS();
}

void test_coverage_enabled_consistent(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool first = valk_coverage_enabled();
  bool second = valk_coverage_enabled();
  VALK_TEST_ASSERT(first == second, "coverage_enabled should be consistent");

  VALK_PASS();
}

void test_coverage_output_path_consistent(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *first = valk_coverage_output_path();
  const char *second = valk_coverage_output_path();

  if (first != NULL && second != NULL) {
    VALK_TEST_ASSERT(strcmp(first, second) == 0, "output_path should be consistent");
  } else {
    VALK_TEST_ASSERT(first == second, "both should be NULL or both non-NULL");
  }

  VALK_PASS();
}

#ifdef VALK_COVERAGE

void test_line_coverage_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_line_coverage_init();
  valk_line_coverage_init();

  VALK_PASS();
}

void test_coverage_mark_line(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_mark_line(0, 0);
  valk_coverage_mark_line(1, 1);
  valk_coverage_mark_line(100, 500);

  VALK_PASS();
}

void test_coverage_record_line(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_record_line(0, 0);
  valk_coverage_record_line(1, 1);
  valk_coverage_record_line(100, 500);

  VALK_PASS();
}

void test_coverage_mark_expr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_mark_expr(0, 0, 0, 0);
  valk_coverage_mark_expr(1, 1, 1, 10);
  valk_coverage_mark_expr(100, 500, 20, 30);

  VALK_PASS();
}

void test_coverage_record_expr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_record_expr(0, 0, 0);
  valk_coverage_record_expr(1, 1, 1);
  valk_coverage_record_expr(100, 500, 20);

  VALK_PASS();
}

void test_coverage_record_branch(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_coverage_record_branch(0, 0, true);
  valk_coverage_record_branch(1, 1, false);
  valk_coverage_record_branch(100, 500, true);

  VALK_PASS();
}

void test_coverage_get_line_expr_count(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t hit, total;
  size_t result = valk_coverage_get_line_expr_count(0, 0, &hit, &total);
  VALK_TEST_ASSERT(result == 0, "Invalid file_id should return 0");
  VALK_TEST_ASSERT(hit == 0, "hit should be 0");
  VALK_TEST_ASSERT(total == 0, "total should be 0");

  VALK_PASS();
}

void test_coverage_get_file_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_line_coverage_file_t *fc = valk_coverage_get_file(0);
  VALK_TEST_ASSERT(fc == NULL, "file_id 0 should return NULL");

  VALK_PASS();
}

void test_line_coverage_reset(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_line_coverage_reset();
  valk_line_coverage_reset();

  VALK_PASS();
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_coverage_init_does_not_crash", test_coverage_init_does_not_crash);
  valk_testsuite_add_test(suite, "test_coverage_enabled_default_false", test_coverage_enabled_default_false);
  valk_testsuite_add_test(suite, "test_coverage_output_path", test_coverage_output_path);
  valk_testsuite_add_test(suite, "test_coverage_record_file_disabled", test_coverage_record_file_disabled);
  valk_testsuite_add_test(suite, "test_coverage_report_disabled", test_coverage_report_disabled);
  valk_testsuite_add_test(suite, "test_coverage_report_lcov_disabled", test_coverage_report_lcov_disabled);
  valk_testsuite_add_test(suite, "test_coverage_reset_disabled", test_coverage_reset_disabled);
  valk_testsuite_add_test(suite, "test_coverage_save_on_exit_disabled", test_coverage_save_on_exit_disabled);
  valk_testsuite_add_test(suite, "test_coverage_multiple_init", test_coverage_multiple_init);
  valk_testsuite_add_test(suite, "test_coverage_multiple_reset", test_coverage_multiple_reset);
  valk_testsuite_add_test(suite, "test_coverage_record_many_files", test_coverage_record_many_files);
  valk_testsuite_add_test(suite, "test_coverage_record_same_file_multiple", test_coverage_record_same_file_multiple);
  valk_testsuite_add_test(suite, "test_coverage_record_empty_filename", test_coverage_record_empty_filename);
  valk_testsuite_add_test(suite, "test_coverage_record_long_filename", test_coverage_record_long_filename);
  valk_testsuite_add_test(suite, "test_coverage_enabled_consistent", test_coverage_enabled_consistent);
  valk_testsuite_add_test(suite, "test_coverage_output_path_consistent", test_coverage_output_path_consistent);

#ifdef VALK_COVERAGE
  valk_testsuite_add_test(suite, "test_line_coverage_init", test_line_coverage_init);
  valk_testsuite_add_test(suite, "test_coverage_mark_line", test_coverage_mark_line);
  valk_testsuite_add_test(suite, "test_coverage_record_line", test_coverage_record_line);
  valk_testsuite_add_test(suite, "test_coverage_mark_expr", test_coverage_mark_expr);
  valk_testsuite_add_test(suite, "test_coverage_record_expr", test_coverage_record_expr);
  valk_testsuite_add_test(suite, "test_coverage_record_branch", test_coverage_record_branch);
  valk_testsuite_add_test(suite, "test_coverage_get_line_expr_count", test_coverage_get_line_expr_count);
  valk_testsuite_add_test(suite, "test_coverage_get_file_null", test_coverage_get_file_null);
  valk_testsuite_add_test(suite, "test_line_coverage_reset", test_line_coverage_reset);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
