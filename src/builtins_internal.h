#pragma once
#include "parser.h"
#include "common.h"
#include "memory.h"

#define LVAL_RAISE(args, fmt, ...)                                       \
  do {                                                                   \
    char* _fmt =                                                         \
        valk_c_err_format((fmt), __FILE_NAME__, __LINE__, __FUNCTION__); \
    valk_lval_t* err = valk_lval_err(_fmt, ##__VA_ARGS__);               \
    valk_mem_free(_fmt);                                                 \
    return err;                                                          \
  } while (0)

#define VALK_SET_ORIGIN_ALLOCATOR(obj)                   \
  do {                                                   \
    (obj)->origin_allocator = valk_thread_ctx.allocator; \
    (obj)->gc_next = nullptr;                            \
  } while (0)

#define LVAL_ASSERT(args, cond, fmt, ...) \
  if ((cond)) {                           \
  } else {                                \
    LVAL_RAISE(args, fmt, ##__VA_ARGS__); \
  }

#define LVAL_ASSERT_TYPE(args, lval, _type, ...)                             \
  do {                                                                       \
    char _found = 0;                                                         \
    valk_ltype_e _expected[] = {(_type), ##__VA_ARGS__};                     \
    u64 _n_expected = sizeof(_expected) / sizeof(valk_ltype_e);           \
                                                                             \
    for (u64 i = 0; i < _n_expected; i++) {                               \
      if (LVAL_TYPE(lval) == _expected[i]) {                                 \
        _found = 1;                                                          \
        break;                                                               \
      }                                                                      \
    }                                                                        \
    if (!_found) {                                                           \
      char const* _expect_str[_n_expected];                                  \
      for (u64 i = 0; i < _n_expected; i++) {                             \
        _expect_str[i] = valk_ltype_name(_expected[i]);                      \
      }                                                                      \
      char* _estr = valk_str_join(_n_expected, _expect_str, ", ");           \
                                                                             \
      char* _fmt = valk_c_err_format("Actual: %s, Expected(One-Of): [%s]",   \
                                     __FILE_NAME__, __LINE__, __FUNCTION__); \
      valk_lval_t* err =                                                     \
          valk_lval_err(_fmt, valk_ltype_name(LVAL_TYPE(lval)), _estr);      \
      valk_mem_free(_estr);                                                  \
      valk_mem_free(_fmt);                                                   \
      return err;                                                            \
    }                                                                        \
  } while (0)

#define LVAL_ASSERT_COUNT_NEQ(args, lval, _count)                     \
  LVAL_ASSERT(args, valk_lval_list_count(lval) != _count,             \
              "Invalid argument count, Actual[%zu] != Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_EQ(args, lval, _count)                      \
  LVAL_ASSERT(args, valk_lval_list_count(lval) == _count,             \
              "Invalid argument count, Actual[%zu] == Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_LT(args, lval, _count)                     \
  LVAL_ASSERT(args, valk_lval_list_count(lval) < _count,             \
              "Invalid argument count, Actual[%zu] < Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_LE(args, lval, _count)                      \
  LVAL_ASSERT(args, valk_lval_list_count(lval) <= _count,             \
              "Invalid argument count, Actual[%zu] <= Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_GT(args, lval, _count)                     \
  LVAL_ASSERT(args, valk_lval_list_count(lval) > _count,             \
              "Invalid argument count, Actual[%zu] > Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#define LVAL_ASSERT_COUNT_GE(args, lval, _count)                      \
  LVAL_ASSERT(args, valk_lval_list_count(lval) >= _count,             \
              "Invalid argument count, Actual[%zu] >= Expected[%zu]", \
              valk_lval_list_count(lval), (u64)_count)

#include <string.h>

#define LVAL_ASSERT_AIO_SYSTEM(args, _ref)                                           \
  do {                                                                               \
    if (LVAL_TYPE(_ref) != LVAL_REF || strcmp((_ref)->ref.type, "aio_system") != 0) { \
      LVAL_RAISE(args, "Expected AIO system reference");                              \
    }                                                                                \
  } while (0)

valk_lval_t* valk_plist_get(valk_lval_t* plist, const char* key_str);
valk_lval_t* valk_qexpr_to_cons(valk_lval_t* qexpr);
valk_lval_t* valk_builtin_list(valk_lenv_t* e, valk_lval_t* a);

void valk_register_math_builtins(valk_lenv_t *env);
void valk_register_list_builtins(valk_lenv_t *env);
void valk_register_string_builtins(valk_lenv_t *env);
void valk_register_io_builtins(valk_lenv_t *env);
void valk_register_env_builtins(valk_lenv_t *env);
void valk_register_mem_builtins(valk_lenv_t *env);
void valk_register_http_builtins(valk_lenv_t *env);
void valk_register_aio_builtins(valk_lenv_t *env);
void valk_register_server_builtins(valk_lenv_t *env);
void valk_register_json_builtins(valk_lenv_t *env);
void valk_register_stdio_builtins(valk_lenv_t *env);
void valk_register_sqlite_builtins(valk_lenv_t *env);
