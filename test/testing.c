#include "testing.h"
#include "collections.h"

#include <stdlib.h>
#include <string.h>
#include <time.h>

#define SEC_TO_MS(sec) ((sec) * 1000)
#define SEC_TO_US(sec) ((sec) * 1000000)
#define SEC_TO_NS(sec) ((sec) * 1000000000)

#define NS_TO_SEC(ns) ((ns) / 1000000000)
#define NS_TO_MS(ns) ((ns) / 1000000)
#define NS_TO_US(ns) ((ns) / 1000)

#ifndef VALK_REPORT_WIDTH
#define VALK_REPORT_WIDTH 100
#endif
const char *DOT_FILL =
    ".........................................................................."
    ".........................................................................."
    ".........................................................................."
    ".........................................................................."
    "....";

valk_test_suite_t *valk_testsuite_empty(const char *filename) {
  valk_test_suite_t *res = malloc(sizeof(valk_test_suite_t));
  res->filename = strdup(filename);
  da_init(&res->tests);
  da_init(&res->fixtures);
  da_init(&res->results);

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
    printf("🏃 Running: %s\n", test->name);
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
    char *precision;
    switch (result->timePrecision) {
    case VALK_MILLIS:
      precision = "ms";
      break;
    case VALK_MICROS:
      precision = "µs";
      break;
    case VALK_NANOS:
      precision = "ns";
      break;
    }

    int len = VALK_REPORT_WIDTH - strlen(test->name);

    switch (result->type) {
    case VALK_TEST_UNDEFINED: {
      printf("%s%.*s  UNDEFINED\n", test->name, len, DOT_FILL);
      break;
    }
    case VALK_TEST_PASS:
      printf("✅ %s%.*s  PASS : in %lu(%s)\n", test->name, len, DOT_FILL,
             (result->stopTime - result->startTime), precision);
      break;
    case VALK_TEST_FAIL:
      printf("🐞 %s%.*s  FAIL : in %lu(%s)\n", test->name, len, DOT_FILL,
             (result->stopTime - result->startTime), precision);
      printf("ERROR: %s\n", result->error);
      break;
    }
  }
}

void valk_testsuite_fixture_add(valk_test_suite_t *suite, const char *name,
                                void *value, _fixture_copy_f *copyFunc,
                                _fixture_free_f *freeFunc) {
  valk_test_fixture_t res = {
      .value = value, .copy = copyFunc, .free = freeFunc, .name = strdup(name)};
  da_add(&suite->fixtures, res);
}

void *valk_testsuite_fixture_get(valk_test_suite_t *suite, const char *name) {
  for (size_t i = 0; i < suite->fixtures.count; i++) {
    if (strcmp(suite->fixtures.items[i].name, name) == 0) {
      return suite->fixtures.items[i].copy(suite->fixtures.items[i].value);
    }
  }
  return NULL;
}

long valk_get_nanos(void) {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  return SEC_TO_NS(ts.tv_sec) + ts.tv_nsec;
}

long valk_get_millis(void) {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  return SEC_TO_MS(ts.tv_sec) + NS_TO_MS(ts.tv_nsec);
}

long valk_get_micros(void) {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  return SEC_TO_US(ts.tv_sec) + NS_TO_US(ts.tv_nsec);
}

long valk_get_time(valk_time_precision_e p) {
  switch (p) {
  case VALK_MILLIS:
    return valk_get_millis();
  case VALK_MICROS:
    return valk_get_micros();
  case VALK_NANOS:
    return valk_get_nanos();
  }
}
