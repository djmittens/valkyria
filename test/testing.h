#pragma once

#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "memory.h"

#define DISABLE_FORMAT_NONLITERAL \
  _Pragma("GCC diagnostic push")  \
      _Pragma("GCC diagnostic ignored \"-Wformat-security\"")

#define ENABLE_FORMAT_NONLITERAL _Pragma("GCC diagnostic pop")

#define VALK_TEST_ARGS() valk_test_suite_t *_suite, valk_test_result_t *_result

#define VALK_TEST()                     \
  (void *)_suite;                       \
  _result->timePrecision = VALK_MICROS; \
  _result->startTime = valk_get_time(_result->timePrecision);

#define VALK_PASS()                                              \
  do {                                                           \
    if (_result->type == VALK_TEST_UNDEFINED) {                  \
      _result->type = VALK_TEST_PASS;                            \
      _result->stopTime = valk_get_time(_result->timePrecision); \
    }                                                            \
  } while (0)

// Mark test as skipped and optionally log a reason to stderr
// NOLINTBEGIN(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
#define VALK_SKIP(fmt, ...)                                                    \
  do {                                                                         \
    if (_result->type == VALK_TEST_UNDEFINED) {                                \
      if ((fmt) && *(fmt)) {                                                   \
        fprintf(stderr, "SKIP: %s:%d || " fmt "\n", __FILE__, __LINE__,      \
                ##__VA_ARGS__);                                                \
      }                                                                        \
      _result->type = VALK_TEST_SKIP;                                          \
      _result->stopTime = valk_get_time(_result->timePrecision);               \
    }                                                                          \
  } while (0)
// NOLINTEND(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)

// NOLINTBEGIN(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
#define VALK_FAIL(fmt, ...)                                                   \
  do {                                                                        \
    DISABLE_FORMAT_NONLITERAL;                                                \
    if (_result->type != VALK_TEST_UNDEFINED) {                               \
      printf(                                                                 \
          "%s:%d || Detected that test has already finished with result.... " \
          "ABORTING \n[%d]\n",                                                \
          __FILE__, __LINE__, _result->type);                                 \
      fflush(stdout);                                                         \
      abort();                                                                \
    }                                                                         \
    size_t __len =                                                            \
        snprintf(NULL, 0, "%s:%d || %s\n", __FILE__, __LINE__, (fmt));        \
    char __efmt[++__len];                                                     \
    snprintf((__efmt), __len, "%s:%d || %s\n", __FILE__, __LINE__, (fmt));    \
    fprintf(stderr, (__efmt), ##__VA_ARGS__);                                 \
    _result->type = VALK_TEST_FAIL;                                           \
    _result->stopTime = valk_get_time(_result->timePrecision);                \
    ENABLE_FORMAT_NONLITERAL;                                                 \
  } while (0)
// NOLINTEND(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)

//  Not very useful right now, since this thing doesnt cleanup the resources
#define VALK_TEST_ASSERT(cond, fmt, ...)                   \
  do {                                                     \
    if (_result->type == VALK_TEST_UNDEFINED && !(cond)) { \
      VALK_FAIL((fmt), ##__VA_ARGS__);                     \
    }                                                      \
  } while (0)

#define VALK_FIXTURE(name) (valk_testsuite_fixture_get(_suite, (name)))

typedef struct valk_test_suite_t valk_test_suite_t;

typedef struct valk_test_result_t valk_test_result_t;

typedef void(valk_test_f)(VALK_TEST_ARGS());
typedef void(_fixture_free_f)(void *);
typedef void *(_fixture_copy_f)(void *);

typedef enum {
  VALK_TEST_UNDEFINED,
  VALK_TEST_PASS,
  VALK_TEST_FAIL,
  VALK_TEST_CRSH,
  VALK_TEST_SKIP,
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

typedef struct valk_test_result_t {
  valk_test_result_type type;
  valk_time_precision_e timePrecision;
  uint64_t startTime;
  uint64_t stopTime;
} valk_test_result_t;

typedef struct valk_test_t {
  char *name;
  valk_test_f *func;
  struct {
    char **items;
    size_t count;
    size_t capacity;
  } labels;
  valk_test_result_t result;
  valk_ring_t *_stdout;
  valk_ring_t *_stderr;
} valk_test_t;

typedef struct valk_test_suite_t {
  char *filename;
  struct {
    size_t capacity;
    size_t count;
    valk_test_t *items;
  } tests;

  struct {
    size_t capacity;
    size_t count;
    valk_test_fixture_t *items;
  } fixtures;
} valk_test_suite_t;

valk_test_suite_t *valk_testsuite_empty(const char *filename);
void valk_testsuite_free(valk_test_suite_t *suite);

size_t valk_testsuite_add_test(valk_test_suite_t *suite, const char *name,
                               valk_test_f *func);

void valk_testsuite_fixture_add(valk_test_suite_t *suite, const char *name,
                                void *value, _fixture_copy_f *copyFunc,
                                _fixture_free_f *freeFunc);

int valk_testsuite_run(valk_test_suite_t *suite);

void valk_testsuite_print(valk_test_suite_t *suite);

void *valk_testsuite_fixture_get(valk_test_suite_t *suite, const char *name);

long valk_get_time(valk_time_precision_e p);
long valk_get_millis(void);
long valk_get_micros(void);
long valk_get_nanos(void);

#define ASSERT_LVAL_TYPE(lval, expected_type)                                  \
  do {                                                                         \
    if ((lval) == NULL) {                                                      \
      VALK_FAIL("ASSERT_LVAL_TYPE: lval is NULL");                             \
    } else if (LVAL_TYPE(lval) != (expected_type)) {                           \
      VALK_FAIL("ASSERT_LVAL_TYPE: expected type %d, got %d",                  \
                (int)(expected_type), (int)LVAL_TYPE(lval));                   \
    }                                                                          \
  } while (0)

#define ASSERT_LVAL_NUM(lval, expected_num)                                    \
  do {                                                                         \
    if ((lval) == NULL) {                                                      \
      VALK_FAIL("ASSERT_LVAL_NUM: lval is NULL");                              \
    } else if (LVAL_TYPE(lval) != LVAL_NUM) {                                  \
      VALK_FAIL("ASSERT_LVAL_NUM: expected LVAL_NUM, got %d",                  \
                (int)LVAL_TYPE(lval));                                         \
    } else if ((lval)->num != (expected_num)) {                                \
      VALK_FAIL("ASSERT_LVAL_NUM: expected %ld, got %ld",                      \
                (long)(expected_num), (long)(lval)->num);                      \
    }                                                                          \
  } while (0)

#define ASSERT_LVAL_ERROR(lval)                                                \
  do {                                                                         \
    if ((lval) == NULL) {                                                      \
      VALK_FAIL("ASSERT_LVAL_ERROR: lval is NULL");                            \
    } else if (LVAL_TYPE(lval) != LVAL_ERR) {                                  \
      VALK_FAIL("ASSERT_LVAL_ERROR: expected LVAL_ERR, got %d",                \
                (int)LVAL_TYPE(lval));                                         \
    }                                                                          \
  } while (0)

#define ASSERT_NOT_NULL(ptr)                                                   \
  do {                                                                         \
    if ((ptr) == NULL) {                                                       \
      VALK_FAIL("ASSERT_NOT_NULL: pointer is NULL");                           \
    }                                                                          \
  } while (0)

#define ASSERT_NULL(ptr)                                                       \
  do {                                                                         \
    if ((ptr) != NULL) {                                                       \
      VALK_FAIL("ASSERT_NULL: pointer is not NULL: %p", (void *)(ptr));        \
    }                                                                          \
  } while (0)

#define ASSERT_EQ(a, b)                                                        \
  do {                                                                         \
    if ((a) != (b)) {                                                          \
      VALK_FAIL("ASSERT_EQ: expected %lld == %lld",                            \
                (long long)(a), (long long)(b));                               \
    }                                                                          \
  } while (0)

#define ASSERT_NE(a, b)                                                        \
  do {                                                                         \
    if ((a) == (b)) {                                                          \
      VALK_FAIL("ASSERT_NE: expected %lld != %lld",                            \
                (long long)(a), (long long)(b));                               \
    }                                                                          \
  } while (0)

#define ASSERT_GT(a, b)                                                        \
  do {                                                                         \
    if (!((a) > (b))) {                                                        \
      VALK_FAIL("ASSERT_GT: expected %lld > %lld",                             \
                (long long)(a), (long long)(b));                               \
    }                                                                          \
  } while (0)

#define ASSERT_GE(a, b)                                                        \
  do {                                                                         \
    if (!((a) >= (b))) {                                                       \
      VALK_FAIL("ASSERT_GE: expected %lld >= %lld",                            \
                (long long)(a), (long long)(b));                               \
    }                                                                          \
  } while (0)

#define ASSERT_LT(a, b)                                                        \
  do {                                                                         \
    if (!((a) < (b))) {                                                        \
      VALK_FAIL("ASSERT_LT: expected %lld < %lld",                             \
                (long long)(a), (long long)(b));                               \
    }                                                                          \
  } while (0)

#define ASSERT_LE(a, b)                                                        \
  do {                                                                         \
    if (!((a) <= (b))) {                                                       \
      VALK_FAIL("ASSERT_LE: expected %lld <= %lld",                            \
                (long long)(a), (long long)(b));                               \
    }                                                                          \
  } while (0)

#define ASSERT_TRUE(cond)                                                      \
  do {                                                                         \
    if (!(cond)) {                                                             \
      VALK_FAIL("ASSERT_TRUE: condition is false");                            \
    }                                                                          \
  } while (0)

#define ASSERT_FALSE(cond)                                                     \
  do {                                                                         \
    if ((cond)) {                                                              \
      VALK_FAIL("ASSERT_FALSE: condition is true");                            \
    }                                                                          \
  } while (0)

#define ASSERT_STR_EQ(a, b)                                                    \
  do {                                                                         \
    if ((a) == NULL || (b) == NULL) {                                          \
      if ((a) != (b)) {                                                        \
        VALK_FAIL("ASSERT_STR_EQ: one string is NULL");                        \
      }                                                                        \
    } else if (strcmp((a), (b)) != 0) {                                        \
      VALK_FAIL("ASSERT_STR_EQ: expected \"%s\", got \"%s\"", (b), (a));        \
    }                                                                          \
  } while (0)

#define ASSERT_STR_CONTAINS(haystack, needle)                                  \
  do {                                                                         \
    if ((haystack) == NULL || (needle) == NULL) {                              \
      VALK_FAIL("ASSERT_STR_CONTAINS: NULL argument");                         \
    } else if (strstr((haystack), (needle)) == NULL) {                         \
      VALK_FAIL("ASSERT_STR_CONTAINS: \"%s\" not found in \"%s\"",             \
                (needle), (haystack));                                         \
    }                                                                          \
  } while (0)

#define ASSERT_MEM_EQ(a, b, len)                                               \
  do {                                                                         \
    if ((a) == NULL || (b) == NULL) {                                          \
      VALK_FAIL("ASSERT_MEM_EQ: NULL argument");                               \
    } else if (memcmp((a), (b), (len)) != 0) {                                 \
      VALK_FAIL("ASSERT_MEM_EQ: memory regions differ");                       \
    }                                                                          \
  } while (0)

#define ASSERT_DOUBLE_EQ(a, b, epsilon)                                        \
  do {                                                                         \
    double _diff = (a) - (b);                                                  \
    if (_diff < 0) _diff = -_diff;                                             \
    if (_diff > (epsilon)) {                                                   \
      VALK_FAIL("ASSERT_DOUBLE_EQ: expected %f == %f (epsilon=%f)",            \
                (double)(a), (double)(b), (double)(epsilon));                  \
    }                                                                          \
  } while (0)

#define ASSERT_IN_RANGE(val, min, max)                                         \
  do {                                                                         \
    if ((val) < (min) || (val) > (max)) {                                      \
      VALK_FAIL("ASSERT_IN_RANGE: %lld not in [%lld, %lld]",                   \
                (long long)(val), (long long)(min), (long long)(max));         \
    }                                                                          \
  } while (0)
