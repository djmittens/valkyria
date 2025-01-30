#pragma once

#include "parser.h"
#include "testing.h"

#define VALK_ASSERT_TYPE(lval, _type, ...)                                     \
  do {                                                                         \
    char _found = 0;                                                           \
    valk_ltype_t _expected[] = {(_type), __VA_ARGS__};                         \
    size_t _n_expected = sizeof(_expected) / sizeof(valk_ltype_t);             \
    for (size_t i = 0; i < _n_expected; i++) {                                 \
      if ((lval)->type == _expected[i]) {                                      \
        _found = 1;                                                            \
        break;                                                                 \
      }                                                                        \
    }                                                                          \
    if (!_found) {                                                             \
      char const *_expect_str[_n_expected];                                    \
      for (size_t i = 0; i < _n_expected; i++) {                               \
        _expect_str[i] = valk_ltype_name(_expected[i]);                        \
      }                                                                        \
      char *_estr = valk_str_join(_n_expected, _expect_str, ", ");             \
      VALK_FAIL(                                                               \
          "Received unexpected lval type Actual: %s, Expected(One-Of): [%s]",  \
          valk_ltype_name((lval)->type), _estr);                               \
      free(_estr);                                                             \
    }                                                                          \
  } while (0)

#define VALK_EXPECT_SUCCESS(lval)                                              \
  do {                                                                         \
    valk_lval_t *_err = valk_lval_find_error(lval);                            \
    if (_err) {                                                                \
      VALK_FAIL("Expected Successfull value but found error", _err->str);      \
    }                                                                          \
  } while (0)



valk_lval_t *valk_eval(valk_lenv_t* env , const char* expr);

valk_lval_t *valk_lval_find_error(valk_lval_t *ast);
