#pragma once

#include <stddef.h>

#define TEST_SUITE()

typedef struct valk_test_result_t valk_test_result_t;
typedef struct valk_test_t valk_test_t;

typedef valk_test_result_t *(valk_test_f)(valk_test_t *);
typedef void(_fixture_free)(void *);

typedef struct valk_test_fixtures_t {
  void **values;
  char **names;
  _fixture_free **frees;
  size_t count;
} valk_test_fixtures_t;

typedef struct valk_test_result_t {
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

typedef struct valk_test_t {
  char *name;
} valk_test_t;

valk_test_suite_t *valk_test_suite_empty(const char *filename);
valk_test_suite_t *valk_test_new();
