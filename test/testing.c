#include "testing.h"
#include <_string.h>
#include <stdlib.h>

valk_test_suite_t *valk_test_suite_empty(const char *filename) {
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

void valk_test_suite_free(valk_test_suite_t *suite) {
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

valk_test_suite_t *valk_test_new() {
}
