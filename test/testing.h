#pragma once

#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define VALK_TEST_ARGS() valk_test_suite_t *_suite

#define VALK_TEST()                                                            \
  valk_test_result_t *_result = valk_testsuite_new_result(_suite, __func__);   \
  _result->timePrecision = VALK_MICROS;                                        \
  _result->startTime = valk_get_time(_result->timePrecision);

#define VALK_PASS()                                                            \
  do {                                                                         \
    if (_result->type == VALK_TEST_UNDEFINED) {                                \
      _result->type = VALK_TEST_PASS;                                          \
      _result->stopTime = valk_get_time(_result->timePrecision);               \
    }                                                                          \
  } while (0)

#define VALK_FAIL(fmt, ...)                                                    \
  do {                                                                         \
    if (_result->type != VALK_TEST_UNDEFINED) {                                \
      printf(                                                                  \
          "%s:%d || Detected that test has already finished with result.... "  \
          "ABORTING \n[%d: %s]\n",                                             \
          __FILE__, __LINE__, _result->type, _result->error);                  \
      fflush(stdout);                                                          \
      abort();                                                                 \
    }                                                                          \
    size_t __len =                                                             \
        snprintf(NULL, 0, "%s:%d || %s", __FILE__, __LINE__, (fmt));           \
    char *__efmt = malloc(__len + 1);                                          \
    snprintf(__efmt, __len + 1, "%s:%d || %s", __FILE__, __LINE__, (fmt));     \
    __len = snprintf(NULL, 0, (__efmt), ##__VA_ARGS__);                        \
    char *__buf = calloc((__len + 1), sizeof(char));                           \
    snprintf(__buf, __len + 1, (__efmt), ##__VA_ARGS__);                       \
    free(__efmt);                                                              \
    _result->type = VALK_TEST_FAIL;                                            \
    _result->stopTime = valk_get_time(_result->timePrecision);                 \
    _result->error = __buf;                                                    \
  } while (0)

//  Not very useful right now, since this tyhing doesnt cleanup the resources
#define VALK_ASSERT(cond, fmt, ...)                                            \
  do {                                                                         \
    if (_result->type == VALK_TEST_UNDEFINED && !(cond)) {                     \
      VALK_FAIL((fmt), ##__VA_ARGS__);                                         \
    }                                                                          \
  } while (0)

#define VALK_FIXTURE(name) (valk_testsuite_fixture_get(_suite, (name)))

#define DA_INIT_CAPACITY 8
#define da_init(arr)                                                           \
  do {                                                                         \
    (arr)->count = 0;                                                          \
    (arr)->capacity = DA_INIT_CAPACITY;                                        \
    if ((arr)->items) {                                                        \
      printf("Reinitializing the array for some stupid reason, probably a "    \
             "memory leak, since items are not cleaned up\n");                 \
      free((arr)->items);                                                      \
    }                                                                          \
    (arr)->items = malloc(sizeof(*(arr)->items) * DA_INIT_CAPACITY);           \
  } while (0)

#define da_free(arr)                                                           \
  do {                                                                         \
    free((arr)->items);                                                        \
    free((arr));                                                               \
  } while (0)

#define da_add(arr, elem)                                                      \
  do {                                                                         \
    if ((arr)->count >= (arr)->capacity) {                                     \
      (arr)->capacity =                                                        \
          (arr)->capacity == 0 ? DA_INIT_CAPACITY : (arr)->capacity * 2;       \
      (arr)->items =                                                           \
          realloc((arr)->items, (arr)->capacity * sizeof(*(arr)->items));      \
      if ((arr)->items == NULL) {                                              \
        printf("Buy more ram LUlz\n");                                         \
        exit(1);                                                               \
      }                                                                        \
    }                                                                          \
    (arr)->items[(arr)->count++] = (elem);                                     \
  } while (0)

typedef struct valk_test_suite_t valk_test_suite_t;

typedef struct valk_test_result_t valk_test_result_t;

typedef void(valk_test_f)(valk_test_suite_t *);
typedef void(_fixture_free_f)(void *);
typedef void *(_fixture_copy_f)(void *);

typedef enum {
  VALK_TEST_UNDEFINED,
  VALK_TEST_PASS,
  VALK_TEST_FAIL,
} valk_test_result_type;

typedef enum {
  VALK_MILLIS,
  VALK_MICROS,
  VALK_NANOS,
} valk_time_precision_e;

typedef struct valk_test_fixture_t {
  void *value;
  char *name;
  _fixture_copy_f *copy;
  _fixture_free_f *free;
} valk_test_fixture_t;

typedef struct valk_test_fixtures_t {
  valk_test_fixture_t *items;
  size_t count;
  size_t capacity;
} valk_test_fixtures_t;

typedef struct valk_test_result_t {
  size_t testOffset;
  valk_test_result_type type;
  char *error;
  valk_time_precision_e timePrecision;
  uint64_t startTime;
  uint64_t stopTime;
} valk_test_result_t;

typedef struct valk_test_results_t {
  valk_test_result_t *items;
  size_t count;
  size_t capacity;
} valk_test_results_t;

typedef struct valk_test_t {
  char *name;
  valk_test_f *func;
} valk_test_t;

typedef struct valk_tests_t {
  valk_test_t *items;
  size_t count;
  size_t capacity;
} valk_tests_t;

typedef struct valk_test_suite_t {
  char *filename;
  valk_tests_t tests;
  valk_test_fixtures_t fixtures;
  valk_test_results_t results;
} valk_test_suite_t;

valk_test_suite_t *valk_testsuite_empty(const char *filename);
void valk_testsuite_free(valk_test_suite_t *suite);

size_t valk_testsuite_add_test(valk_test_suite_t *suite, const char *name,
                               valk_test_f *func);

void valk_testsuite_fixture_add(valk_test_suite_t *suite, const char *name,
                                void *value, _fixture_copy_f *copyFunc,
                                _fixture_free_f *freeFunc);

valk_test_result_t *valk_testsuite_new_result(valk_test_suite_t *suite,
                                              const char *testName);

int valk_testsuite_run(valk_test_suite_t *suite);

void valk_testsuite_print(valk_test_suite_t *suite);

void *valk_testsuite_fixture_get(valk_test_suite_t *suite, const char *name);

long valk_get_time(valk_time_precision_e p);
long valk_get_millis(void);
long valk_get_micros(void);
long valk_get_nanos(void);
