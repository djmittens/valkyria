#include "testing.h"
#include <stdlib.h>
#include <string.h>

valk_test_suite_t *valk_testsuite_empty(const char *filename) {
  valk_test_suite_t *res = malloc(sizeof(valk_test_suite_t));
  res->filename = strdup(filename);
  da_init(&res->tests);

  da_init(&res->fixtures);

  return res;
}

void valk_testsuite_free(valk_test_suite_t *suite) {
  for (size_t i = 0; i < suite->tests.count; i++) {
    free(suite->tests.items[i].name);
  }
  free(suite->tests.items);

  for (size_t i = 0; i < suite->fixtures.count; i++) {
    free(suite->fixtures.items[i].name);
    suite->fixtures.items[i].free(suite->fixtures.items[i].value);
  }

  free(suite->fixtures.items);

  for (size_t i = 0; i < suite->results.count; i++) {
    if (suite->results.items[i].type == VALK_TEST_FAIL) {
      free(suite->results.items[i].error);
    }
  }
  free(suite->results.items);

  free(suite->filename);

  for (size_t i = 0; i < suite->results.count; i++) {
    free(suite->results.items[i].error);
  }
  free(suite->results.items);

  free(suite);
}

size_t valk_testsuite_add_test(valk_test_suite_t *suite, const char *name,
                               valk_test_f *func) {

  valk_test_t test = {.name = strdup(name), .func = func};
  da_add(&suite->tests, test);

  return suite->tests.count;
}

valk_test_result_t *valk_testsuite_new_result(valk_test_suite_t *suite,
                                              const char *testName) {
  valk_test_result_t res;

  for (int i = 0; i < suite->tests.count; ++i) {
    if (strcmp(suite->tests.items[i].name, testName) == 0) {
      res.testOffset = i;
      res.type = VALK_TEST_UNDEFINED;
      da_add(&suite->results, res);
      return &suite->results.items[suite->results.count - 1];
    }
  }

  return NULL;
}

int valk_testsuite_run(valk_test_suite_t *suite) {
  for (size_t i = 0; i < suite->tests.count; i++) {
    valk_test_t *test = &suite->tests.items[i];
    test->func(suite);
  }
  for (size_t i = 0; i < suite->results.count; i++) {
    valk_test_result_t *result = &suite->results.items[i];
    if (result->type != VALK_TEST_PASS) {
      return 1;
    }
  }
  return 0;
}

void valk_testsuite_print(valk_test_suite_t *suite) {
  printf("[%ld/%ld] %s Suite Results: \n", suite->results.count,
         suite->tests.count, suite->filename);
  for (size_t i = 0; i < suite->results.count; i++) {
    valk_test_result_t *result = &suite->results.items[i];
    valk_test_t *test = &suite->tests.items[result->testOffset];
    if (result->type == VALK_TEST_PASS) {
      printf("Test: %s .......... PASS : in %llu (ms)\n", test->name,
             (result->stopTime - result->startTime));
    } else if (result->type == VALK_TEST_UNDEFINED) {
      printf("Test: %s .......... UNDEFINED\n", test->name);
    } else if (result->type == VALK_TEST_FAIL) {
      printf("Test: %s .......... ERROR : in %llu (ms)\n", test->name,
             (result->stopTime - result->startTime));
      printf("%s\n", result->error);
    }
  }
}
