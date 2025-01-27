#pragma once

#include <stddef.h>
#include <stdint.h>

#define TEST_SUITE()

typedef struct valk_test_result_t valk_test_result_t;
typedef struct valk_test_t valk_test_t;

typedef valk_test_result_t *(valk_test_f)(valk_test_t *);
typedef void(_fixture_free_f)(void *);

typedef enum { VALK_TEST_PASS, VALK_TEST_FAIL } valk_test_result_type;

typedef struct valk_test_fixtures_t {
  void **values;
  char **names;
  _fixture_free_f **frees;
  size_t count;
} valk_test_fixtures_t;

typedef struct valk_test_result_t {
  valk_test_result_type type;
  uint64_t runtimeNano;
} valk_test_result_t;

typedef struct valk_tests_t {
  valk_test_f **values;
  char **names;
  size_t count;
} valk_tests_t;

typedef struct valk_test_suite_t {
  char *filename;
  valk_tests_t tests;
  valk_test_fixtures_t fixtures;
} valk_test_suite_t;

valk_test_suite_t *valk_testsuite_empty(const char *filename);

void valk_testsuite_add_test(valk_test_suite_t *suite, const char *name,
                             valk_test_f *func);
