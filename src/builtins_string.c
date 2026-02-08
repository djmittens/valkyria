#include "builtins_internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// LCOV_EXCL_BR_START - print_user: type dispatch covers all LVAL types
static void valk_lval_print_user(valk_lval_t* val) {
  if (val == nullptr) {
    printf("nil");
    return;
  }
  switch (LVAL_TYPE(val)) {
    case LVAL_NUM:
      printf("%li", val->num);
      break;
    case LVAL_SYM:
      printf("%s", val->str);
      break;
    case LVAL_NIL:
      printf("()");
      break;
    case LVAL_CONS: {
      bool is_quoted = (val->flags & LVAL_FLAG_QUOTED) != 0;
      printf(is_quoted ? "{" : "(");
      valk_lval_t* curr = val;
      int first = 1;
      while (curr != nullptr && LVAL_TYPE(curr) == LVAL_CONS) {
        if (!first) putchar(' ');
        valk_lval_print_user(curr->cons.head);
        curr = curr->cons.tail;
        first = 0;
      }
      if (curr != nullptr && LVAL_TYPE(curr) != LVAL_NIL) {
        printf(" . ");
        valk_lval_print_user(curr);
      }
      printf(is_quoted ? "}" : ")");
      break;
    }
    case LVAL_ERR:
      printf("Error: %s", val->str);
      break;
    case LVAL_FUN:
      if (val->fun.builtin) {
        printf("<builtin>");
      } else {
        printf("<lambda>");
      }
      break;
    case LVAL_STR:
      printf("%s", val->str);
      break;
    case LVAL_REF:
      printf("<ref:%s>", val->ref.type);
      break;
    case LVAL_HANDLE:
      printf("<handle>");
      break;
    case LVAL_UNDEFINED:
      printf("<undefined>");
      break;
  }
}
// LCOV_EXCL_BR_STOP

static valk_lval_t* valk_builtin_str(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);

  u64 count = valk_lval_list_count(a);

  if (count == 0) {
    return valk_lval_str("");
  }

  u64 total_size = 0;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t* val = valk_lval_list_nth(a, i);
    if (LVAL_TYPE(val) == LVAL_STR) {
      total_size += strlen(val->str);
    } else {
      total_size += 256;
    }
  }

  total_size += 1;

  char* buffer = malloc(total_size);
  if (!buffer) { // LCOV_EXCL_BR_LINE - OOM
    return valk_lval_err("str: out of memory allocating %zu bytes", total_size); // LCOV_EXCL_LINE
  }

  u64 offset = 0;
  u64 remaining = total_size;

  for (u64 i = 0; i < count; i++) {
    valk_lval_t* val = valk_lval_list_nth(a, i);

    if (LVAL_TYPE(val) == LVAL_STR) {
      u64 len = strlen(val->str);
      memcpy(buffer + offset, val->str, len);
      offset += len;
      remaining -= len;
    } else {
      FILE* stream = fmemopen(buffer + offset, remaining, "w");
      if (!stream) { // LCOV_EXCL_BR_LINE - platform failure
        buffer[offset] = '\0';
        valk_lval_t* result = valk_lval_str(buffer);
        free(buffer);
        return result;
      }

      FILE* old_stdout = stdout;
      stdout = stream;
      valk_lval_print_user(val);
      stdout = old_stdout;
      fclose(stream);

      u64 written = strlen(buffer + offset);
      offset += written;
      remaining -= written;
    }
  }

  buffer[offset] = '\0';
  valk_lval_t* result = valk_lval_str(buffer);
  free(buffer);
  return result;
}

static valk_lval_t* valk_builtin_printf(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GT(a, a, 0);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char* fmt = valk_lval_list_nth(a, 0)->str;
  u64 arg_idx = 1;

  for (const char* p = fmt; *p != '\0'; p++) {
    if (*p == '%' && *(p + 1) != '\0') {
      p++;
      switch (*p) {
        case 's': {
          if (arg_idx >= valk_lval_list_count(a)) {
            return valk_lval_err(
                "printf: not enough arguments for format string");
          }
          valk_lval_t* arg = valk_lval_list_nth(a, arg_idx++);
          if (LVAL_TYPE(arg) != LVAL_STR) {
            return valk_lval_err("printf: %%s requires string argument");
          }
          printf("%s", arg->str);
          break;
        }
        case 'd':
        case 'l': {
          if (*p == 'l' && *(p + 1) == 'd') {
            p++;
          }
          if (arg_idx >= valk_lval_list_count(a)) {
            return valk_lval_err(
                "printf: not enough arguments for format string");
          }
          valk_lval_t* arg = valk_lval_list_nth(a, arg_idx++);
          if (LVAL_TYPE(arg) != LVAL_NUM) {
            return valk_lval_err("printf: %%d/%%ld requires number argument");
          }
          printf("%ld", arg->num);
          break;
        }
        case '%':
          putchar('%');
          break;
        default:
          putchar('%');
          putchar(*p);
          break;
      }
    } else {
      putchar(*p);
    }
  }

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_print(valk_lenv_t* e, valk_lval_t* a) {
  for (u64 i = 0; i < valk_lval_list_count(a); i++) {
    valk_lval_t* arg = valk_lval_list_nth(a, i);

    const char* str_to_print;
    valk_lval_t* str_val = nullptr;

    if (LVAL_TYPE(arg) == LVAL_STR) {
      str_to_print = arg->str;
    } else {
      valk_lval_t* str_args_arr[1] = {arg};
      valk_lval_t* str_args = valk_lval_list(str_args_arr, 1);
      str_val = valk_builtin_str(e, str_args);

      if (LVAL_TYPE(str_val) == LVAL_ERR) { // LCOV_EXCL_BR_LINE
        return str_val;
      }

      str_to_print = str_val->str;
    }

    printf("%s", str_to_print);

    if (i < valk_lval_list_count(a) - 1) {
      putchar(' ');
    }
  }
  putchar('\n');
  fflush(stdout);
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_println(valk_lenv_t* e, valk_lval_t* a) {
  valk_lval_t* result = valk_builtin_printf(e, a);
  if (LVAL_TYPE(result) != LVAL_ERR) {
    putchar('\n');
    fflush(stdout);
  }
  return result;
}

static valk_lval_t* valk_builtin_make_string(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2); // LCOV_EXCL_BR_LINE

  valk_lval_t* count_val = valk_lval_list_nth(a, 0);
  valk_lval_t* pattern_val = valk_lval_list_nth(a, 1);

  LVAL_ASSERT(a, LVAL_TYPE(count_val) == LVAL_NUM,
              "make-string: first argument must be a number");

  long count = count_val->num;
  if (count < 0) {
    return valk_lval_err("make-string: count must be non-negative");
  }
  if (count == 0) {
    return valk_lval_str("");
  }

  const char* pattern;
  u64 pattern_len;

  if (LVAL_TYPE(pattern_val) == LVAL_STR) {
    pattern = pattern_val->str;
    pattern_len = strlen(pattern);
  } else if (LVAL_TYPE(pattern_val) == LVAL_NUM) {
    static char char_buf[2];
    char_buf[0] = (char)pattern_val->num;
    char_buf[1] = '\0';
    pattern = char_buf;
    pattern_len = 1;
  } else {
    return valk_lval_err("make-string: second argument must be string or number (char code)");
  }

  if (pattern_len == 0) {
    return valk_lval_str("");
  }

  u64 total_size = (u64)count * pattern_len;

  if (total_size > 100 * 1024 * 1024) { // LCOV_EXCL_BR_LINE
    return valk_lval_err("make-string: requested size %zu exceeds 100MB limit", total_size);
  }

  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_STR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->str = valk_mem_alloc(total_size + 1);

  if (pattern_len == 1) {
    memset(res->str, pattern[0], total_size);
  } else {
    char* ptr = res->str;
    for (long i = 0; i < count; i++) {
      memcpy(ptr, pattern, pattern_len);
      ptr += pattern_len;
    }
  }
  res->str[total_size] = '\0';

  return res;
}

// LCOV_EXCL_BR_START - str/split arg validation
static valk_lval_t* valk_builtin_str_split(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t* str_arg = valk_lval_list_nth(a, 0);
  valk_lval_t* delim_arg = valk_lval_list_nth(a, 1);

  LVAL_ASSERT_TYPE(a, str_arg, LVAL_STR);
  LVAL_ASSERT_TYPE(a, delim_arg, LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* str = str_arg->str;
  const char* delim = delim_arg->str;
  u64 delim_len = strlen(delim);

  if (delim_len == 0) {
    return valk_lval_err("str/split: delimiter cannot be empty");
  }

  u64 count = 0;
  const char* p = str;
  while ((p = strstr(p, delim)) != NULL) {
    count++;
    p += delim_len;
  }
  count++;

  valk_lval_t** parts = malloc(count * sizeof(valk_lval_t*));
  if (!parts) { // LCOV_EXCL_BR_LINE - OOM
    return valk_lval_err("str/split: out of memory"); // LCOV_EXCL_LINE
  }

  u64 idx = 0;
  const char* start = str;
  const char* found;
  // NOLINTBEGIN(clang-analyzer-security.ArrayBound) - idx always < count
  while ((found = strstr(start, delim)) != NULL) {
    u64 part_len = found - start;
    parts[idx++] = valk_lval_str_n(start, part_len);
    start = found + delim_len;
  }
  parts[idx++] = valk_lval_str(start);
  // NOLINTEND(clang-analyzer-security.ArrayBound)

  valk_lval_t* result = valk_lval_nil();
  for (u64 i = count; i > 0; i--) {
    // NOLINTNEXTLINE(clang-analyzer-core.CallAndMessage) - parts fully populated by loop above
    result = valk_lval_cons(parts[i - 1], result);
  }

  free(parts);
  return result;
}

// LCOV_EXCL_BR_START - str/replace arg validation
static valk_lval_t* valk_builtin_str_replace(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);

  valk_lval_t* str_arg = valk_lval_list_nth(a, 0);
  valk_lval_t* from_arg = valk_lval_list_nth(a, 1);
  valk_lval_t* to_arg = valk_lval_list_nth(a, 2);

  LVAL_ASSERT_TYPE(a, str_arg, LVAL_STR);
  LVAL_ASSERT_TYPE(a, from_arg, LVAL_STR);
  LVAL_ASSERT_TYPE(a, to_arg, LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* str = str_arg->str;
  const char* from = from_arg->str;
  const char* to = to_arg->str;
  u64 str_len = strlen(str);
  u64 from_len = strlen(from);
  u64 to_len = strlen(to);

  if (from_len == 0) {
    return valk_lval_err("str/replace: search string cannot be empty");
  }

  u64 count = 0;
  const char* p = str;
  while ((p = strstr(p, from)) != NULL) {
    count++;
    p += from_len;
  }

  if (count == 0) {
    return valk_lval_str(str);
  }

  u64 new_len = str_len + count * (to_len - from_len);
  char* result = malloc(new_len + 1);
  if (!result) { // LCOV_EXCL_BR_LINE - OOM
    return valk_lval_err("str/replace: out of memory"); // LCOV_EXCL_LINE
  }

  char* dest = result;
  const char* src = str;
  const char* found_ptr;

  while ((found_ptr = strstr(src, from)) != NULL) {
    u64 prefix_len = found_ptr - src;
    memcpy(dest, src, prefix_len);
    dest += prefix_len;
    memcpy(dest, to, to_len);
    dest += to_len;
    src = found_ptr + from_len;
  }

  strcpy(dest, src);

  valk_lval_t* res = valk_lval_str(result);
  free(result);
  return res;
}

// LCOV_EXCL_BR_START - str/slice arg validation
static valk_lval_t* valk_builtin_str_slice(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);

  valk_lval_t* str_arg = valk_lval_list_nth(a, 0);
  valk_lval_t* start_arg = valk_lval_list_nth(a, 1);
  valk_lval_t* end_arg = valk_lval_list_nth(a, 2);

  LVAL_ASSERT_TYPE(a, str_arg, LVAL_STR);
  LVAL_ASSERT_TYPE(a, start_arg, LVAL_NUM);
  LVAL_ASSERT_TYPE(a, end_arg, LVAL_NUM);
  // LCOV_EXCL_BR_STOP

  const char* str = str_arg->str;
  i64 str_len = strlen(str);
  i64 start = start_arg->num;
  i64 end = end_arg->num;

  if (start < 0) start = 0;
  if (end > str_len) end = str_len;
  if (start > end) start = end;

  u64 slice_len = end - start;
  return valk_lval_str_n(str + start, slice_len);
}

void valk_register_string_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "print", valk_builtin_print);
  valk_lenv_put_builtin(env, "printf", valk_builtin_printf);
  valk_lenv_put_builtin(env, "println", valk_builtin_println);
  valk_lenv_put_builtin(env, "str", valk_builtin_str);
  valk_lenv_put_builtin(env, "make-string", valk_builtin_make_string);
  valk_lenv_put_builtin(env, "str/split", valk_builtin_str_split);
  valk_lenv_put_builtin(env, "str/replace", valk_builtin_str_replace);
  valk_lenv_put_builtin(env, "str/slice", valk_builtin_str_slice);
}
