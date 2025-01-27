#include "testing.h"
#include <stdlib.h>
#include <string.h>

valk_test_suite_t *valk_testsuite_empty(const char *filename) {
  valk_test_suite_t *res = malloc(sizeof(valk_test_suite_t));
  res->filename = strdup(filename);
  res->tests.count = 0;
  res->tests.names = NULL;
  res->tests.values = NULL;

  res->fixtures.count = 0;
  res->fixtures.names = NULL;
  res->fixtures.values = NULL;
  res->fixtures.frees = NULL;

  return res;
}

void valk_testsuite_free(valk_test_suite_t *suite) {
  for (size_t i = 0; i < suite->tests.count; i++) {
    free(suite->tests.names[i]);
  }
  free(suite->tests.names);
  free(suite->tests.values);

  for (size_t i = 0; i < suite->fixtures.count; i++) {
    free(suite->fixtures.names[i]);
    suite->fixtures.frees[i](suite->fixtures.values[i]);
  }
  free(suite->fixtures.names);
  free(suite->fixtures.values);
  free(suite->fixtures.frees);

  free(suite->filename);

  free(suite);
}

void valk_testsuite_add_test(valk_test_suite_t *suite, const char *name,
                             valk_test_f *func) {
  suite->tests.names =
      realloc(suite->tests.names,
              sizeof(valk_test_suite_t *) * (suite->tests.count + 1));
  suite->tests.names[suite->tests.count] = strdup(name);

  suite->tests.values = realloc(
      suite->tests.values, sizeof(valk_test_f *) * (suite->tests.count + 1));
  suite->tests.values[suite->tests.count] = func;

  suite->tests.count++;
}
