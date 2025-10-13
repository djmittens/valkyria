#include "parser.h"

#include <errno.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "concurrency.h"
#include "memory.h"

// TODO(networking): get rid of args everywhere, cause we dont need to release
// anymore
#define LVAL_RAISE(args, fmt, ...)                                       \
  do {                                                                   \
    char *_fmt =                                                         \
        valk_c_err_format((fmt), __FILE_NAME__, __LINE__, __FUNCTION__); \
    valk_lval_t *err = valk_lval_err(_fmt, ##__VA_ARGS__);               \
    free(_fmt);                                                          \
    return err;                                                          \
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
    size_t _n_expected = sizeof(_expected) / sizeof(valk_ltype_e);           \
                                                                             \
    for (size_t i = 0; i < _n_expected; i++) {                               \
      if (LVAL_TYPE(lval) == _expected[i]) {                                 \
        _found = 1;                                                          \
        break;                                                               \
      }                                                                      \
    }                                                                        \
    if (!_found) {                                                           \
      char const *_expect_str[_n_expected];                                  \
      for (size_t i = 0; i < _n_expected; i++) {                             \
        _expect_str[i] = valk_ltype_name(_expected[i]);                      \
      }                                                                      \
      char *_estr = valk_str_join(_n_expected, _expect_str, ", ");           \
                                                                             \
      char *_fmt = valk_c_err_format("Actual: %s, Expected(One-Of): [%s]",   \
                                     __FILE_NAME__, __LINE__, __FUNCTION__); \
      valk_lval_t *err =                                                     \
          valk_lval_err(_fmt, valk_ltype_name(LVAL_TYPE(lval)), _estr);      \
      free(_estr);                                                           \
      free(_fmt);                                                            \
      return err;                                                            \
    }                                                                        \
  } while (0)

#define LVAL_ASSERT_COUNT_NEQ(args, lval, _count)                   \
  LVAL_ASSERT(args, (lval)->expr.count != _count,                   \
              "Invalid argument count, Actual[%d] != Expected[%d]", \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_EQ(args, lval, _count)                    \
  LVAL_ASSERT(args, (lval)->expr.count == _count,                   \
              "Invalid argument count, Actual[%d] == Expected[%d]", \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_LT(args, lval, _count)                   \
  LVAL_ASSERT(args, (lval)->expr.count < _count,                   \
              "Invalid argument count, Actual[%d] < Expected[%d]", \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_LE(args, lval, _count)                    \
  LVAL_ASSERT(args, (lval)->expr.count <= _count,                   \
              "Invalid argument count, Actual[%d] <= Expected[%d]", \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_GT(args, lval, _count)                   \
  LVAL_ASSERT(args, (lval)->expr.count > _count,                   \
              "Invalid argument count, Actual[%d] > Expected[%d]", \
              (lval)->expr.count, _count)

#define LVAL_ASSERT_COUNT_GE(args, lval, _count)                    \
  LVAL_ASSERT(args, (lval)->expr.count >= _count,                   \
              "Invalid argument count, Actual[%d] >= Expected[%d]", \
              (lval)->expr.count, _count)

static valk_lval_t *valk_builtin_eval(valk_lenv_t *e, valk_lval_t *a);
static valk_lval_t *valk_builtin_list(valk_lenv_t *e, valk_lval_t *a);
static const char *valk_lval_str_escape(char x);
static char valk_lval_str_unescape(char x);

/* List of possible escapable characters */
static char *lval_str_escapable = "\a\b\f\n\r\t\v\\\'\"";

/* Possible unescapable characters */
static char *lval_str_unescapable = "abfnrtv\\\'\"";

char *valk_c_err_format(const char *fmt, const char *file, const size_t line,
                        const char *function) {
  // NOLINTBEGIN(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  size_t len =
      snprintf(nullptr, 0, "%s:%ld:%s || %s", file, line, function, fmt);
  char *buf = malloc(len + 1);
  snprintf(buf, len + 1, "%s:%ld:%s || %s", file, line, function, fmt);
  // NOLINTEND(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  return buf;
}

char *valk_str_join(const size_t n, const char **strs, const char *sep) {
  // TODO(main): I think i should get my own string type in here
  size_t res_len = 0;
  size_t sep_len = strlen(sep);
  size_t str_lens[n];
  for (size_t i = 0; i < n; i++) {
    size_t _len = strlen(strs[i]);
    res_len += _len;
    str_lens[i] = _len;
    if (i < n - 1) {
      res_len += sep_len;
    }
  }
  char *res = malloc(res_len + 1);
  size_t offset = 0;
  for (size_t i = 0; i < n; i++) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memcpy(&res[offset], strs[i], str_lens[i]);
    offset += str_lens[i];
    if (i < n - 1) {
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      memcpy(&res[offset], sep, sep_len);
      offset += sep_len;
    }
  }
  res[offset] = '\0';

  return res;
}

const char *valk_ltype_name(valk_ltype_e type) {
  switch (type) {
    case LVAL_NUM:
      return "Number";
    case LVAL_SYM:
      return "Symbol";
    case LVAL_FUN:
      return "Function";
    case LVAL_QEXPR:
      return "Quote-expr";
    case LVAL_SEXPR:
      return "Symbolic-expr";
    case LVAL_ERR:
      return "Error";
    case LVAL_STR:
      return "String";
    case LVAL_REF:
      return "Reference";
    case LVAL_UNDEFINED:
      return "UNDEFINED";
      break;
  }
}

valk_lval_t *valk_lval_ref(const char *type, void *ptr, void (*free)(void *)) {
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_REF;
  res->ref.type = strndup(type, 100);
  res->ref.ptr = ptr;
  res->ref.free = free;

  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t *valk_lval_num(long x) {
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_NUM;
  res->num = x;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// TODO(main): look into UTF-8 support
valk_lval_t *valk_lval_err(const char *fmt, ...) {
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_ERR;
  va_list va;
  va_start(va, fmt);

  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  size_t len = vsnprintf(nullptr, 0, fmt, va);
  va_end(va);
  va_start(va, fmt);

  // TODO(main): look into making this into a constant
  len = len < 10000 ? len : 511;
  res->str = malloc(len + 1);
  //NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  vsnprintf(res->str, len + 1, fmt, va);
  va_end(va);
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t *valk_lval_sym(const char *sym) {
  //NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_SYM;
  res->str = strndup(sym, 200);
  res->expr.count = 0;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t *valk_lval_str(const char *str) {
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_STR;
  // TODO(main): whats a reasonable max for a string length?
  res->str = strdup(str);
  res->expr.count = 0;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// valk_lval_t *valk_lval_builtin(valk_lval_builtin_t *fun) {
//   valk_lval_t *res = malloc(sizeof(valk_lval_t));
//   res->type = LVAL_SYM;
//   res->fun.builtin = fun;
//   res->fun.env = nullptr;
//   return res;
// }

valk_lval_t *valk_lval_lambda(valk_lval_t *formals, valk_lval_t *body) {
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_FUN;
  res->fun.builtin = nullptr;
  res->fun.env = valk_lenv_empty();
  res->fun.formals = formals;
  res->fun.body = body;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t *valk_lval_sexpr_empty(void) {
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_SEXPR;
  res->expr.cell = nullptr;
  res->expr.count = 0;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

valk_lval_t *valk_lval_qexpr_empty(void) {
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_QEXPR;
  res->expr.cell = nullptr;
  res->expr.count = 0;
  valk_capture_trace(VALK_TRACE_NEW, 1, res);
  return res;
}

// valk_lval_t *valk_lval_copy(valk_lval_t *lval) {
//   valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
//   res->type = lval->type;
//   switch (lval->type) {
//     case LVAL_NUM:
//       res->num = lval->num;
//       break;
//     case LVAL_FUN:
//       if (lval->fun.builtin) {
//         res->fun.builtin = lval->fun.builtin;
//         res->fun.env = nullptr;
//         res->fun.body = nullptr;
//         res->fun.formals = nullptr;
//       } else {
//         res->fun.builtin = nullptr;
//         res->fun.env = valk_lenv_copy(lval->fun.env);
//         res->fun.body = valk_lval_copy(lval->fun.body);
//         res->fun.formals = valk_lval_copy(lval->fun.formals);
//       }
//       break;
//     case LVAL_QEXPR:
//     case LVAL_SEXPR:
//       res->expr.cell =
//           valk_mem_alloc(sizeof(res->expr.cell) * lval->expr.count);
//       res->expr.count = lval->expr.count;
//       for (size_t i = 0; i < lval->expr.count; ++i) {
//         res->expr.cell[i] = valk_lval_copy(lval->expr.cell[i]);
//       }
//       break;
//     case LVAL_SYM:
//       res->str =
//           strndup(lval->str, 200);  //  TODO(main): Whats max symbol length?
//       break;
//     case LVAL_ERR:
//       // Pretty cool functionality in C23
//       res->str =
//           strndup(lval->str, 2000);  //  TODO(main): Whats max error length?
//       break;
//     case LVAL_STR:
//       res->str = strdup(lval->str);  //  TODO(main): Whats max string length?
//       break;
//     case LVAL_REF:
//       res->ref = lval->ref;
//       break;
//   }
//   return res;
// }

// void valk_lval_free(valk_lval_t *lval) {
//   if (lval == nullptr) {
//     return;
//   }
//   switch (LVAL_TYPE(lval)) {
//     case LVAL_FUN:
//       if (!lval->fun.builtin) {
//         valk_release(lval->fun.body);
//         valk_release(lval->fun.formals);
//         valk_release(lval->fun.env);
//       }
//       break;
//     case LVAL_NUM:
//       // nuttin to do but break;
//       break;
//     case LVAL_STR:
//     case LVAL_SYM:
//     case LVAL_ERR:
//       // TODO(networking): where should i store these stupid strings?
//       free(lval->str);
//       break;
//     case LVAL_QEXPR:
//     case LVAL_SEXPR:
//       while (lval->expr.count > 0) {
//         valk_release(lval->expr.cell[lval->expr.count - 1]);
//         --lval->expr.count;
//       }
//       // Should play around with valgrind on this. Pretty interesting thing
//       to
//       // forget
//       free(lval->expr.cell);
//       break;
//     case LVAL_REF:
//       lval->ref.free(lval->ref.ptr);
//       free(lval->ref.type);
//       break;
//   }
//   valk_mem_free(lval);
// }

int valk_lval_eq(valk_lval_t *x, valk_lval_t *y) {
  if (x->flags != y->flags) {
    return 0;
  }

  switch (LVAL_TYPE(x)) {
    case LVAL_NUM:
      return (x->num == y->num);
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      return (strcmp(x->str, y->str));
    case LVAL_FUN: {
      if (x->fun.builtin || y->fun.builtin) {
        return x->fun.builtin == y->fun.builtin;
      } else {
        return valk_lval_eq(x->fun.formals, y->fun.formals) &&
               valk_lval_eq(x->fun.body, y->fun.body);
      }
    }
    case LVAL_QEXPR:
    case LVAL_SEXPR:
      if (x->expr.count != y->expr.count) {
        return 0;
      }
      for (size_t i = 0; i < x->expr.count; ++i) {
        if (!valk_lval_eq(x->expr.cell[i], y->expr.cell[i])) {
          return 0;
        }
      }
      return 1;
    case LVAL_REF:
      return (x->ref.ptr == y->ref.ptr) && (x->ref.free == y->ref.free);
    case LVAL_ENV:
      VALK_RAISE("LVAL is LENV, comparison unimplemented, something went wrong");
      break;
    case LVAL_UNDEFINED:
      VALK_RAISE("LVAL is undefined, something went wrong");
      break;
  }

  return 0;
}

valk_lval_t *valk_lval_eval(valk_lenv_t *env, valk_lval_t *lval) {
  if (LVAL_TYPE(lval) == LVAL_SYM) {
    valk_lval_t *res = valk_lenv_get(env, lval);
    return res;
  }
  if (LVAL_TYPE(lval) == LVAL_SEXPR) {
    return valk_lval_eval_sexpr(env, lval);
  }

  return lval;
}

valk_lval_t *valk_lval_eval_sexpr(valk_lenv_t *env, valk_lval_t *sexpr) {
  LVAL_ASSERT_TYPE(sexpr, sexpr, LVAL_SEXPR);
  // no children? no problem
  if (sexpr->expr.count == 0) {
    return sexpr;
  }

  // count up the chillen
  for (size_t i = 0; i < sexpr->expr.count; ++i) {
    sexpr->expr.cell[i] = valk_lval_eval(env, sexpr->expr.cell[i]);
    if (LVAL_TYPE(sexpr->expr.cell[i]) == LVAL_ERR) {
      valk_lval_t *res = valk_lval_pop(sexpr, i);
      return res;
    }
  }

  // If we have a single node, collapse to it
  if (sexpr->expr.count == 1) {
    valk_lval_t *res = valk_lval_pop(sexpr, 0);
    return res;
  }

  valk_lval_t *fun = valk_lval_pop(sexpr, 0);
  if (LVAL_TYPE(fun) != LVAL_FUN) {
    // Make sure to free this shit.
    // TODO(main): should add more information here about the symbol
    valk_lval_t *res = valk_lval_err(
        "S-expr doesnt start with a <function>, Actual: %s Expected: %s",
        valk_ltype_name(LVAL_TYPE(fun)), valk_ltype_name(LVAL_FUN));
    return res;
  }
  // valk_lval_err("hi");

  valk_lval_println(sexpr);
  valk_lval_t *res = valk_lval_eval_call(env, fun, sexpr);
  return res;
}

valk_lval_t *valk_lval_eval_call(valk_lenv_t *env, valk_lval_t *func,
                                 valk_lval_t *args) {
  LVAL_ASSERT_TYPE(args, func, LVAL_FUN);
  LVAL_ASSERT_TYPE(args, args, LVAL_SEXPR);

  if (func->fun.builtin) {
    return func->fun.builtin(env, args);
  }
  size_t given = args->expr.count;
  size_t requested = func->fun.formals->expr.count;
  valk_lval_t *res;

  while (args->expr.count) {
    if (func->fun.formals->expr.count == 0) {
      valk_lval_println(func);
      return valk_lval_err(
          "More arguments were given than required Actual [ %p ]: %ld, "
          "Expected: %ld",
          func, given, requested);
    }
    valk_lval_t *sym = valk_lval_pop(func->fun.formals, 0);
    if (strcmp(sym->str, "&") == 0) {
      // if we encountered this, the rest of arguments are varargs
      if (func->fun.formals->expr.count != 1) {
        return valk_lval_err(
            "Invalid  function format, the vararg symbol `&` "
            "is not followed by others [count: %d]",
            func->fun.formals->expr.count);
      }
      valk_lval_t *nsym = valk_lval_pop(func->fun.formals, 0);
      valk_lenv_put(func->fun.env, nsym, valk_builtin_list(nullptr, args));
      break;
    }
    valk_lval_t *val = valk_lval_pop(args, 0);
    valk_lenv_put(func->fun.env, sym, val);
  }

  // if whats remaining is the elipsis, then we expand to empty list
  if (func->fun.formals->expr.count > 0 &&
      (strcmp(func->fun.formals->expr.cell[0]->str, "&") == 0)) {
    if (func->fun.formals->expr.count != 2) {
      return valk_lval_err(
          "Invalid  function format, the vararg symbol `&` "
          "is not followed by others [count: %d]",
          func->fun.formals->expr.count);
    }

    // discard the &
    valk_lval_pop(func->fun.formals, 0);
    valk_lval_t *sym = valk_lval_pop(func->fun.formals, 0);
    valk_lval_t *val = valk_lval_qexpr_empty();
    valk_lenv_put(env, sym, val);
  }

  // If everything is bound we evalutate
  if (func->fun.formals->expr.count == 0) {
    func->fun.env->parent = env;
    // retain our parent n stuff

    res = valk_builtin_eval(
        func->fun.env, valk_lval_add(valk_lval_sexpr_empty(), func->fun.body));
  } else {
    res = func;
  }
  return res;
}

valk_lval_t *valk_lval_pop(valk_lval_t *lval, size_t i) {
  // TODO(networking): should this delete the lval or no ?
  LVAL_ASSERT((valk_lval_t *)0, i < lval->expr.count,
              "Cant pop from list at invalid position: [%d] total length: [%d]",
              i, lval->expr.count);
  LVAL_ASSERT((valk_lval_t *)0, lval->expr.count > 0, "Cant pop from empty");

  valk_lval_t *cell = lval->expr.cell[i];
  // shift dems down
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memmove(&lval->expr.cell[i], &lval->expr.cell[i + 1],
          sizeof(valk_lval_t *) * (lval->expr.count - i - 1));
  lval->expr.count--;
  // clang-tidy is a monster, i have to do this to shut it up
  if (lval->expr.count > 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    lval->expr.cell =
        realloc(lval->expr.cell, sizeof(valk_lval_t *) * lval->expr.count);
  }
  return cell;
}

valk_lval_t *valk_lval_add(valk_lval_t *lval, valk_lval_t *cell) {
  // TODO(main):  this will leak the cell, i need to expand this macro to free
  // more than 1 thing
  LVAL_ASSERT_TYPE(lval, lval, LVAL_SEXPR, LVAL_QEXPR);
  // TODO(main): i need to invest more into null checks in this file
  LVAL_ASSERT(lval, cell != nullptr, "Adding nullptr to LVAL is not allowed");

  lval->expr.count++;
  lval->expr.cell =
      realloc(lval->expr.cell, sizeof(valk_lval_t *) * lval->expr.count);
  lval->expr.cell[lval->expr.count - 1] = cell;
  return lval;
}

valk_lval_t *valk_lval_join(valk_lval_t *a, valk_lval_t *b) {
  while (b->expr.count) {
    a = valk_lval_add(a, valk_lval_pop(b, 0));
  }
  return a;
}

void valk_lval_print(valk_lval_t *val) {
  if (val == nullptr) {
    return;
  }
  switch (LVAL_TYPE(val)) {
    case LVAL_NUM:
      printf("Num[%li]", val->num);
      break;
    case LVAL_SYM:
      printf("Sym[%s]", val->str);
      break;
      // TODO(main): code duplication here, do i actually care??
    case LVAL_QEXPR:
      printf("Qexpr{ ");
      for (size_t i = 0; i < val->expr.count; ++i) {
        valk_lval_print(val->expr.cell[i]);
        if (i < val->expr.count - 1) {
          putchar(' ');
        }
      }
      printf(" }");
      break;
    case LVAL_SEXPR:
      printf("Sexpr( ");
      for (size_t i = 0; i < val->expr.count; ++i) {
        valk_lval_print(val->expr.cell[i]);
        if (i < val->expr.count - 1) {
          putchar(' ');
        }
      }
      printf(" )");
      break;
    case LVAL_ERR:
      printf("Error[%s]", val->str);
      break;
    case LVAL_FUN:
      if (val->fun.builtin) {
        printf("<builtin>");
      } else {
        printf("(\\ ");
        valk_lval_print(val->fun.formals);
        putchar(' ');
        valk_lval_print(val->fun.body);
        putchar(')');
      }
      break;
    case LVAL_STR: {
      // We want to escape the string before printing
      printf("String[");
      for (size_t i = 0; i < strlen(val->str); ++i) {
        if (strchr(lval_str_escapable, val->str[i])) {
          printf("%s", valk_lval_str_escape(val->str[i]));
        } else {
          putchar(val->str[i]);
        }
      }
      printf("]");
      break;
    }
    case LVAL_REF:
      printf("Reference[%s:%p]", val->ref.type, val->ref.ptr);
      break;
    case LVAL_ENV:
      printf("[LEnv]");
      break;
    case LVAL_UNDEFINED:
      printf("[Undefined]");
      break;
  }
}

static char valk_lval_str_unescape(char x) {
  switch (x) {
    case 'a':
      return '\a';
    case 'b':
      return '\b';
    case 'f':
      return '\f';
    case 'n':
      return '\n';
    case 'r':
      return '\r';
    case 't':
      return '\t';
    case 'v':
      return '\v';
    case '\\':
      return '\\';
    case '\'':
      return '\'';
    case '\"':
      return '\"';
  }
  return '\0';
}

static const char *valk_lval_str_escape(char x) {
  switch (x) {
    case '\a':
      return "\\a";
    case '\b':
      return "\\b";
    case '\f':
      return "\\f";
    case '\n':
      return "\\n";
    case '\r':
      return "\\r";
    case '\t':
      return "\\t";
    case '\v':
      return "\\v";
    case '\\':
      return "\\\\";
    case '\'':
      return "\\\'";
    case '\"':
      return "\\\"";
  }
  return "";
}

static valk_lval_t *valk_lval_read_sym(int *i, const char *s) {
  valk_lval_t *res;
  char next;
  int end = *i;
  // find the end of the string
  for (; (next = s[end]); ++end) {
    if (strchr("abcdefghijklmnopqrstuvwxyz"
               "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
               "0123456789_+-*\\/=<>!&",
               next) &&
        s[end] != '\0') {
      continue;
    }
    break;
  }

  // the  length of the new string
  size_t len = end - (*i);
  if (len) {
    char *sym = strndup(&s[*i], len);
    int isNum = strchr("-0123456789", sym[0]) != nullptr;
    for (size_t i = 1; i < len; ++i) {
      if (!strchr("0123456789", sym[i])) {
        isNum = 0;
        break;
      }
    }
    // Negative by itself is not a number
    if (strlen(sym) == 1 && sym[0] == '-') {
      isNum = 0;
    }

    if (isNum) {
      errno = 0;
      long x = strtol(sym, nullptr, 10);
      // TODO(main): i dont like that we return this error as a success....
      // this should yield a return 1;
      // but im too lazy to unfuck this function
      res = errno != ERANGE ? valk_lval_num(x)
                            : valk_lval_err("Invalid number format %s", sym);
    } else {
      res = valk_lval_sym(sym);
    }
    *i += len;
    free(sym);
    return res;
  }

  return valk_lval_str("");
}
static valk_lval_t *valk_lval_read_str(int *i, const char *s) {
  // Scan the string for size
  char next;
  int count = 1;  // Pad for nil terminator

  // Advance to start of string
  if (s[(*i)++] != '"') {
    return valk_lval_err(
        "Strings must start with `\"` but instead it started with %c", s[*i]);
  }

  // Read until the end
  for (int end = (*i); (next = s[end]) != '"'; ++end) {
    if (next == '\0') {
      return valk_lval_err("Unexpected  end of input at string literal");
    }
    if (next == '\\') {
      ++end;
      if (!strchr(lval_str_unescapable, s[end])) {
        return valk_lval_err("Invalid escape character \\%c", s[end]);
      }
    }
    count++;
  }

  // TODO(main): Hmmm can a string be so big, itll blow the stack? fun.
  char tmp[count] = {};

  int offset = 0;
  for (int end = *i; (next = s[end]) != '"'; ++end) {
    // next = s[end]; // why the heck is that here
    if (next == '\\') {
      ++end;
      next = valk_lval_str_unescape(s[end]);
    }
    tmp[offset++] = next;
  }

  (*i) += offset + 1;
  return valk_lval_str(tmp);
}

valk_lval_t *valk_lval_read(int *i, const char *s) {
  valk_lval_t *res;

  // Skip white space and comments
  while (strchr(" ;\t\v\r\n", s[*i]) && s[*i] != '\0') {
    // Read comment
    if (s[*i] == ';') {
      while (s[*i] != '\n' && s[*i] != '\0') {
        ++(*i);
      }
    } else {
      ++(*i);
    }
  }

  if (s[*i] == '\0') {
    return valk_lval_err("Unexpected  end of input");
  }

  if (strchr("({", s[*i])) {
    res = valk_lval_read_expr(i, s);
  }
  // Lets check for a symbol
  else if (strchr("abcdefghijklmnopqrstuvwxyz"
                  "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                  "0123456789_+-*\\/=<>!&",
                  s[*i])) {
    res = valk_lval_read_sym(i, s);
  } else if (s[*i] == '"') {
    res = valk_lval_read_str(i, s);
  } else {
    res = valk_lval_err("[offset: %ld] Unexpected character %c", *i, s[*i]);
  }

  // Skip white space and comments
  while (strchr(" \t\v\r\n", s[*i]) && s[*i] != '\0') {
    // Read comment
    if (s[*i] == ';') {
      while (s[*i] != '\n' && s[*i] != '\0') {
        ++(*i);
      }
    }
    ++(*i);
  }
  return res;
}

valk_lval_t *valk_lval_read_expr(int *i, const char *s) {
  char end;
  valk_lval_t *res;
  if (s[(*i)++] == '{') {
    res = valk_lval_qexpr_empty();
    end = '}';
  } else {
    res = valk_lval_sexpr_empty();
    end = ')';
  }

  while (s[*i] != end) {
    if (s[*i] == '\0') {
      LVAL_RAISE(res,
                 "[offset: %d] Unexpected end of input reading expr, while "
                 "looking for `%c`",
                 *i, end);
    }
    valk_lval_t *x = valk_lval_read(i, s);
    if (LVAL_TYPE(x) == LVAL_ERR) {
      return x;
    } else {
      valk_lval_add(res, x);
    }
  }
  (*i)++;

  return res;
}

//// LEnv ////
valk_lenv_t *valk_lenv_empty(void) {
  valk_lenv_t *res = valk_mem_alloc(sizeof(valk_lenv_t));
  memset(res, 0, sizeof(valk_lenv_t));
  valk_lenv_init(res);
  return res;
}
void valk_lenv_init(valk_lenv_t *env) {
  env->parent = nullptr;
  env->count = 0;
  env->symbols = nullptr;
  env->vals = nullptr;
}

valk_lenv_t *valk_lenv_copy(valk_lenv_t *env) {
  if (env == nullptr) {
    return nullptr;
  }
  valk_lenv_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  // TODO(main): Man lotta copying, especially deep copying, in case things
  // change the problem with this ofcourse is that, globals cant be changed
  res->parent = env->parent;
  res->count = env->count;
  res->symbols = valk_mem_alloc(sizeof(env->symbols) * env->count);
  res->vals = valk_mem_alloc(sizeof(env->vals) * env->count);

  for (size_t i = 0; i < env->count; i++) {
    res->symbols[i] = strdup(env->symbols[i]);
    res->vals[i] = env->vals[i];
  }
  return res;
}

valk_lval_t *valk_lenv_get(valk_lenv_t *env, valk_lval_t *key) {
  LVAL_ASSERT_TYPE((valk_lval_t *)nullptr, key, LVAL_SYM);

  for (size_t i = 0; i < env->count; i++) {
    if (strcmp(key->str, env->symbols[i]) == 0) {
      printf("Searching %d %s\n", i, env->symbols[i]);
      return env->vals[i];
    }
  }

  if (env->parent) {
    return valk_lenv_get(env->parent, key);
  } else {
    return valk_lval_err("LEnv: Symbol `%s` is not bound", key->str);
  }
}

void valk_lenv_put(valk_lenv_t *env, valk_lval_t *key, valk_lval_t *val) {
  // TODO: obviously this should probably not be void ???
  // especially since i cant assert this shit
  // LVAL_ASSERT_TYPE((valk_lval_t *)nullptr, key, LVAL_SYM);
  printf("Putting this dogshit bullshit %s \n", key->str);

  // TODO(main): technically this is a failure condition for us, but the
  // return's void LVAL_ASSERT(nullptr, key->type == LVAL_SYM, "LEnv only
  // supports symbolic keys");
  for (size_t i = 0; i < env->count; i++) {
    if (strcmp(key->str, env->symbols[i]) == 0) {
      // if we found it, we destroy it
      env->vals[i];
      env->vals[i] = val;
      return;
    }
  }
  // TODO(main): technically we should be able to do the ammortized arraylist
  // where we double the array on overflow, but i guess it doesnt matter for
  // now
  env->symbols = valk_mem_realloc(env->symbols,
                                  sizeof(env->symbols[0]) * (env->count + 1));
  env->vals =
      valk_mem_realloc(env->vals, sizeof(env->vals[0]) * (env->count + 1));

  // TODO(networking): Maybe have env builder ?? this should be a copy perhaps
  // or something??
  env->symbols[env->count] = valk_mem_alloc(201);
  strncpy(env->symbols[env->count], key->str, 200);
  env->vals[env->count] = val;

  ++env->count;
}

// Define the key in global scope
void valk_lenv_def(valk_lenv_t *env, valk_lval_t *key, valk_lval_t *val) {
  while (env->parent) {
    env = env->parent;
  }
  valk_lenv_put(env, key, val);
}

void valk_lenv_put_builtin(valk_lenv_t *env, char *key,
                           valk_lval_builtin_t *_fun) {
  valk_lval_t *lfun = valk_mem_alloc(sizeof(valk_lval_t));

  lfun->flags = LVAL_FUN;
  lfun->fun.builtin = _fun;
  lfun->fun.env = nullptr;

  valk_lenv_put(env, valk_lval_sym(key), lfun);
}

static valk_lval_t *builtin_math(valk_lval_t *lst, char *op) {
  for (size_t i = 0; i < lst->expr.count; ++i) {
    // TODO(main): Its not very straightforward to assert a type here
    if (LVAL_TYPE(lst->expr.cell[i]) != LVAL_NUM) {
      LVAL_RAISE(lst, "This function only supports Numbers : %s",
                 valk_ltype_name(LVAL_TYPE(lst->expr.cell[i])));
    }
  }

  valk_lval_t *x = valk_lval_pop(lst, 0);

  if (strcmp(op, "-") == 0 && lst->expr.count == 0) {
    // Negate the number if there is only 1
    x->num = -x->num;
  }

  while (lst->expr.count > 0) {
    valk_lval_t *y = valk_lval_pop(lst, 0);

    if (strcmp(op, "+") == 0) {
      x->num += y->num;
    }
    if (strcmp(op, "-") == 0) {
      x->num -= y->num;
    }
    if (strcmp(op, "*") == 0) {
      x->num *= y->num;
    }
    if (strcmp(op, "/") == 0) {
      if (y->num > 0) {
        x->num /= y->num;
      } else {
        x = valk_lval_err("Division By Zero");
        break;
      }
    }
  }
  return x;
}

static valk_lval_t *valk_builtin_cons(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, a->expr.cell[1], LVAL_QEXPR);

  valk_lval_t *head = valk_lval_pop(a, 0);
  valk_lval_t *tail = valk_lval_pop(a, 0);
  // TODO(main): this should be implmented as push
  tail->expr.cell = realloc(
      tail->expr.cell, sizeof(tail->expr.cell[0]) * (tail->expr.count + 1));
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memmove(&tail->expr.cell[1], tail->expr.cell,
          sizeof(tail->expr.cell) * tail->expr.count);
  tail->expr.cell[0] = head;
  tail->expr.count++;
  return tail;
}

static valk_lval_t *valk_builtin_len(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  // TODO(main): should this only work with Q expr?
  // sexpr gets evaluated immediately, so perhaps thats fine
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);

  valk_lval_t *res = valk_lval_num(a->expr.cell[0]->expr.count);
  return res;
}

static valk_lval_t *valk_builtin_head(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT(a, a->expr.count == 1,
              "Builtin `head` passed too many arguments");
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);
  LVAL_ASSERT_COUNT_GT(a, a->expr.cell[0], 0);
  valk_lval_t *list = valk_lval_pop(a, 0);
  while (list->expr.count > 1) {
    valk_lval_pop(list, 1);
  }
  return list;
}

static valk_lval_t *valk_builtin_tail(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT(a, a->expr.count == 1,
              "Builtin `tail` passed too many arguments");
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);
  LVAL_ASSERT(a, a->expr.cell[0]->expr.count != 0,
              "Builtin `tail` cannot operate on `{}`");
  valk_lval_t *v = valk_lval_pop(a, 0);

  valk_lval_pop(v, 0);
  return v;
}

static valk_lval_t *valk_builtin_init(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  // TODO(main): can i make this more flexible, that way these functions can
  // work over argument list as well? or is that something thats too obvious
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);
  LVAL_ASSERT_COUNT_GT(a, a->expr.cell[0], 0);
  valk_lval_pop(a->expr.cell[0], a->expr.cell[0]->expr.count - 1);
  valk_lval_t *res = valk_lval_pop(a, 0);
  return res;
}

static valk_lval_t *valk_builtin_join(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);

  valk_lval_t *x = valk_lval_pop(a, 0);
  while (a->expr.count) {
    x = valk_lval_join(x, valk_lval_pop(a, 0));
  }

  return x;
}

static valk_lval_t *valk_builtin_list(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  a->flags = ((a->flags & LVAL_FLAGS_MASK) & LVAL_QEXPR);
  return a;
}

static valk_lval_t *valk_builtin_eval(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_QEXPR);

  valk_lval_t *v = valk_lval_pop(a, 0);

  v->flags = ((v->flags & LVAL_FLAGS_MASK) & LVAL_SEXPR);
  return valk_lval_eval(e, v);
}
static valk_lval_t *valk_builtin_plus(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  return builtin_math(a, "+");
}
static valk_lval_t *valk_builtin_minus(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  return builtin_math(a, "-");
}
static valk_lval_t *valk_builtin_divide(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  return builtin_math(a, "/");
}
static valk_lval_t *valk_builtin_multiply(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  return builtin_math(a, "*");
}

static valk_lval_t *valk_builtin_def(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_GT(a, a, 1);

  valk_lval_t *syms = a->expr.cell[0];
  LVAL_ASSERT_TYPE(a, syms, LVAL_QEXPR);

  for (size_t i = 1; i < syms->expr.count; i++) {
    LVAL_ASSERT(a, LVAL_TYPE(syms->expr.cell[i]) == LVAL_SYM,
                "Builtin `def` requires that symbols parameter only has "
                "symbols found: %s",
                valk_ltype_name(LVAL_TYPE(a->expr.cell[i])));
  }

  LVAL_ASSERT_COUNT_EQ(a, syms, (a->expr.count - 1));

  for (size_t i = 0; i < syms->expr.count; i++) {
    valk_lenv_def(e, syms->expr.cell[i], a->expr.cell[i + 1]);
  }

  return valk_lval_sexpr_empty();
}

static valk_lval_t *valk_builtin_put(valk_lenv_t *e, valk_lval_t *a) {
  // TODO(main): should dedupe these functions perhaps? i dont care right now
  // tho
  LVAL_ASSERT_COUNT_GT(a, a, 1);

  valk_lval_t *syms = a->expr.cell[0];
  LVAL_ASSERT_TYPE(a, syms, LVAL_QEXPR);

  for (size_t i = 1; i < syms->expr.count; i++) {
    LVAL_ASSERT(a, LVAL_TYPE(syms->expr.cell[i]) == LVAL_SYM,
                "Builtin `def` requires that symbols parameter only has "
                "symbols found: %s",
                valk_ltype_name(LVAL_TYPE(a->expr.cell[i])));
  }

  LVAL_ASSERT_COUNT_EQ(a, syms, (a->expr.count - 1));

  for (size_t i = 0; i < syms->expr.count; i++) {
    valk_lenv_put(e, syms->expr.cell[i], a->expr.cell[i + 1]);
  }

  return valk_lval_sexpr_empty();
}

static valk_lval_t *valk_builtin_lambda(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t *formals = a->expr.cell[0];
  valk_lval_t *body = a->expr.cell[1];

  LVAL_ASSERT_TYPE(a, formals, LVAL_QEXPR);
  LVAL_ASSERT_TYPE(a, body, LVAL_QEXPR);

  for (size_t i = 0; i < formals->expr.count; i++) {
    LVAL_ASSERT(a, LVAL_TYPE(formals->expr.cell[i]) == LVAL_SYM,
                "Cannot use a non symbol[%s] for bind",
                valk_ltype_name(LVAL_TYPE(a->expr.cell[0]->expr.cell[i])));
  }

  formals = valk_lval_pop(a, 0);
  body = valk_lval_pop(a, 0);

  return valk_lval_lambda(formals, body);
}

static valk_lval_t *valk_builtin_penv(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  valk_lval_t *res = valk_lval_qexpr_empty();
  for (size_t i = 0; i < e->count; i++) {
    valk_lval_t *qexpr = valk_lval_qexpr_empty();
    // TODO(main): So each of these can fail, in that case we want to free the
    // intermediates, im too lazy to do that tho, so memory leaks n such.
    // really i can also check the pre-conditions here to make sure we dont
    // even allocate anything if they arent met
    valk_lval_add(qexpr, valk_lval_sym(e->symbols[i]));
    valk_lval_add(qexpr, e->vals[i]);
    valk_lval_add(res, qexpr);
  }
  return res;
}

static valk_lval_t *valk_builtin_ord(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_SYM);
  LVAL_ASSERT_TYPE(a, a->expr.cell[1], LVAL_NUM);
  LVAL_ASSERT_TYPE(a, a->expr.cell[2], LVAL_NUM);

  const char *op = a->expr.cell[0]->str;

  int r = 0;
  if (strcmp(op, ">") == 0) {
    r = (a->expr.cell[1]->num > a->expr.cell[2]->num);
  }
  if (strcmp(op, "<") == 0) {
    r = (a->expr.cell[1]->num < a->expr.cell[2]->num);
  }
  if (strcmp(op, ">=") == 0) {
    r = (a->expr.cell[1]->num >= a->expr.cell[2]->num);
  }
  if (strcmp(op, "<=") == 0) {
    r = (a->expr.cell[1]->num <= a->expr.cell[2]->num);
  }

  return valk_lval_num(r);
}
static valk_lval_t *valk_builtin_cmp(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_SYM);
  const char *op = a->expr.cell[0]->str;
  int r = 0;
  if (strcmp(op, "==") == 0) {
    r = valk_lval_eq(a->expr.cell[1], a->expr.cell[2]);
  }
  if (strcmp(op, "!=") == 0) {
    r = !valk_lval_eq(a->expr.cell[1], a->expr.cell[2]);
  }
  return valk_lval_num(r);
}

static valk_lval_t *valk_builtin_eq(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("=="));
  return valk_builtin_cmp(e, valk_lval_join(tmp, a));
}
static valk_lval_t *valk_builtin_ne(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("!="));
  return valk_builtin_cmp(e, valk_lval_join(tmp, a));
}
static valk_lval_t *valk_builtin_gt(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym(">"));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}
static valk_lval_t *valk_builtin_lt(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("<"));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}
static valk_lval_t *valk_builtin_ge(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym(">="));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}
static valk_lval_t *valk_builtin_le(valk_lenv_t *e, valk_lval_t *a) {
  valk_lval_t *tmp = valk_lval_sexpr_empty();
  valk_lval_add(tmp, valk_lval_sym("<="));
  return valk_builtin_ord(e, valk_lval_join(tmp, a));
}

static valk_lval_t *valk_builtin_load(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_STR);

  valk_lval_t *expr = valk_parse_file(a->expr.cell[0]->str);
  if (LVAL_TYPE(expr) == LVAL_ERR) {
    return expr;
  }
  while (expr->expr.count) {
    valk_lval_t *x = valk_lval_eval(e, valk_lval_pop(expr, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
    }
  }

  return valk_lval_sexpr_empty();
}

valk_lval_t *valk_parse_file(const char *filename) {
  FILE *f = fopen(filename, "rb");
  if (f == nullptr) {
    LVAL_RAISE(valk_lval_sexpr_empty(), "Could not open file (%s)", filename);
  }

  fseek(f, 0, SEEK_END);
  size_t length = ftell(f);
  fseek(f, 0, SEEK_SET);

  if (length == UINT64_MAX) {
    fclose(f);
    LVAL_RAISE(valk_lval_sexpr_empty(), "File is way too big buddy (%s)",
               filename);
  }

  char *input = calloc(length + 1, sizeof(char));
  fread(input, 1, length, f);
  fclose(f);

  int pos = 0;
  valk_lval_t *res = valk_lval_sexpr_empty();
  valk_lval_t *tmp;
  do {
    tmp = valk_lval_read(&pos, input);
    valk_lval_add(res, tmp);
  } while ((LVAL_TYPE(tmp) != LVAL_ERR) && (input[pos] != '\0'));

  free(input);

  return res;
}

static valk_lval_t *valk_builtin_if(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_NUM);
  LVAL_ASSERT_TYPE(a, a->expr.cell[1], LVAL_QEXPR);
  LVAL_ASSERT_TYPE(a, a->expr.cell[2], LVAL_QEXPR);

  // Make em both executable
  valk_lval_t *x;
  a->expr.cell[1]->flags = ((a->flags & LVAL_FLAGS_MASK) & LVAL_SEXPR);
  a->expr.cell[2]->flags = ((a->flags & LVAL_FLAGS_MASK) & LVAL_SEXPR);

  // execute only the winning one.
  if (a->expr.cell[0]->num) {
    x = valk_lval_eval(e, valk_lval_pop(a, 1));
  } else {
    x = valk_lval_eval(e, valk_lval_pop(a, 2));
  }

  return x;
}

static valk_lval_t *valk_builtin_print(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  for (size_t i = 0; i < a->expr.count; i++) {
    valk_lval_print(a->expr.cell[i]);
    putchar(' ');
  }
  putchar('\n');
  return valk_lval_sexpr_empty();
}

static valk_lval_t *valk_builtin_error(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_STR);
  valk_lval_t *err = valk_lval_err(a->expr.cell[0]->str);
  return err;
}

static void __valk_arc_box_release(void *arg) {
  valk_arc_release((valk_arc_box *)arg - 1);
}

static valk_lval_t *valk_builtin_await(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, a->expr.cell[0], LVAL_REF);
  LVAL_ASSERT(a, strcmp(a->expr.cell[0]->ref.type, "future") == 0,
              "Await only works with futures but received: %s",
              a->expr.cell[0]->ref.type);

  valk_future *fut = a->expr.cell[0]->ref.ptr;
  valk_arc_box *box = valk_future_await_timeout(fut, 100000);

  valk_lval_t *res;
  if (box->type == VALK_SUC) {
    res = valk_lval_ref("success", box->item, __valk_arc_box_release);
    valk_arc_retain(box);
  } else {
    res = valk_lval_err("ERR: %s", box->item);
  }

  return res;
}

void valk_lenv_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "error", valk_builtin_error);
  valk_lenv_put_builtin(env, "load", valk_builtin_load);
  valk_lenv_put_builtin(env, "print", valk_builtin_print);

  valk_lenv_put_builtin(env, "list", valk_builtin_list);
  valk_lenv_put_builtin(env, "cons", valk_builtin_cons);
  valk_lenv_put_builtin(env, "len", valk_builtin_len);
  valk_lenv_put_builtin(env, "init", valk_builtin_init);
  valk_lenv_put_builtin(env, "head", valk_builtin_head);
  valk_lenv_put_builtin(env, "tail", valk_builtin_tail);
  valk_lenv_put_builtin(env, "join", valk_builtin_join);
  valk_lenv_put_builtin(env, "eval", valk_builtin_eval);

  valk_lenv_put_builtin(env, "+", valk_builtin_plus);
  valk_lenv_put_builtin(env, "-", valk_builtin_minus);
  valk_lenv_put_builtin(env, "/", valk_builtin_divide);
  valk_lenv_put_builtin(env, "*", valk_builtin_multiply);

  valk_lenv_put_builtin(env, "def", valk_builtin_def);
  valk_lenv_put_builtin(env, "=", valk_builtin_put);
  valk_lenv_put_builtin(env, "\\", valk_builtin_lambda);
  valk_lenv_put_builtin(env, "penv", valk_builtin_penv);

  // TODO(main):  Doesnt actually work lols, no idea why
  valk_lenv_put_builtin(env, "ord", valk_builtin_ord);

  valk_lenv_put_builtin(env, "if", valk_builtin_if);
  valk_lenv_put_builtin(env, ">", valk_builtin_gt);
  valk_lenv_put_builtin(env, "<", valk_builtin_lt);
  valk_lenv_put_builtin(env, ">=", valk_builtin_ge);
  valk_lenv_put_builtin(env, "<=", valk_builtin_le);
  valk_lenv_put_builtin(env, "==", valk_builtin_eq);
  valk_lenv_put_builtin(env, "!=", valk_builtin_ne);

  // Async
  valk_lenv_put_builtin(env, "await", valk_builtin_await);
  valk_lenv_put_builtin(env, "http2-client", valk_builtin_await);

  // HTTP
}
