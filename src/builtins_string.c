#include "builtins_internal.h"
#include "dict.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// LCOV_EXCL_BR_START - print_user: type dispatch covers all LVAL types
static void valk_lval_fprint_user(FILE *f, valk_lval_t* val) {
  if (val == nullptr) {
    fprintf(f, "nil");
    return;
  }
  switch (LVAL_TYPE(val)) {
    case LVAL_NUM:
      fprintf(f, "%li", val->num);
      break;
    case LVAL_SYM:
      fprintf(f, "%s", val->str);
      break;
    case LVAL_NIL:
      fprintf(f, "()");
      break;
    case LVAL_CONS: {
      bool is_quoted = (val->flags & LVAL_FLAG_QUOTED) != 0;
      fputc(is_quoted ? '{' : '(', f);
      valk_lval_t* curr = val;
      int first = 1;
      while (curr != nullptr && LVAL_TYPE(curr) == LVAL_CONS) {
        if (!first) fputc(' ', f);
        valk_lval_fprint_user(f, curr->cons.head);
        curr = curr->cons.tail;
        first = 0;
      }
      if (curr != nullptr && LVAL_TYPE(curr) != LVAL_NIL) {
        fprintf(f, " . ");
        valk_lval_fprint_user(f, curr);
      }
      fputc(is_quoted ? '}' : ')', f);
      break;
    }
    case LVAL_ERR:
      fprintf(f, "Error: %s", val->str);
      break;
    case LVAL_FUN:
      if (val->fun.builtin) {
        fprintf(f, "<builtin>");
      } else {
        fprintf(f, "<lambda>");
      }
      break;
    case LVAL_STR:
      fprintf(f, "%s", val->str);
      break;
    case LVAL_REF:
      fprintf(f, "<ref:%s>", val->ref.type);
      break;
    case LVAL_DICT:
      fprintf(f, "<dict:%u>", val->dict.data ? val->dict.data->count : 0);
      break;
    case LVAL_HANDLE:
      fprintf(f, "<handle>");
      break;
    case LVAL_UNDEFINED:
      fprintf(f, "<undefined>");
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

  u64 cap = 256;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t* val = valk_lval_list_nth(a, i);
    if (LVAL_TYPE(val) == LVAL_STR) {
      cap += strlen(val->str);
    } else {
      cap += 256;
    }
  }

  char* buffer = malloc(cap);
  if (!buffer) { // LCOV_EXCL_BR_LINE - OOM
    return valk_lval_err("str: out of memory allocating %zu bytes", cap); // LCOV_EXCL_LINE
  }

  u64 offset = 0;

  for (u64 i = 0; i < count; i++) {
    valk_lval_t* val = valk_lval_list_nth(a, i);

    if (LVAL_TYPE(val) == LVAL_STR) {
      u64 len = strlen(val->str);
      if (offset + len >= cap) {
        cap = (offset + len) * 2 + 1;
        buffer = realloc(buffer, cap);
      }
      memcpy(buffer + offset, val->str, len);
      offset += len;
    } else {
      char tmp[4096];
      FILE* stream = fmemopen(tmp, sizeof(tmp), "w");
      if (!stream) { // LCOV_EXCL_BR_LINE - platform failure
        buffer[offset] = '\0'; // LCOV_EXCL_LINE
        valk_lval_t* result = valk_lval_str(buffer); // LCOV_EXCL_LINE
        free(buffer); // LCOV_EXCL_LINE
        return result; // LCOV_EXCL_LINE
      }

      valk_lval_fprint_user(stream, val);
      fclose(stream);

      u64 written = strlen(tmp);
      if (offset + written >= cap) {
        cap = (offset + written) * 2 + 1;
        buffer = realloc(buffer, cap);
      }
      memcpy(buffer + offset, tmp, written);
      offset += written;
    }
  }

  buffer[offset] = '\0';
  valk_lval_t* result = valk_lval_str(buffer);
  free(buffer);
  return result;
}

// LCOV_EXCL_BR_START - printf arg validation and format dispatch
static valk_lval_t* valk_builtin_printf(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GT(a, a, 0);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

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
  LVAL_ASSERT_COUNT_EQ(a, a, 2);

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

  char char_buf[2];
  if (LVAL_TYPE(pattern_val) == LVAL_STR) {
    pattern = pattern_val->str;
    pattern_len = strlen(pattern);
  } else if (LVAL_TYPE(pattern_val) == LVAL_NUM) {
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

// LCOV_EXCL_BR_START - str/contains? arg validation
static valk_lval_t* valk_builtin_str_contains(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* haystack = valk_lval_list_nth(a, 0)->str;
  const char* needle = valk_lval_list_nth(a, 1)->str;
  return valk_lval_num(strstr(haystack, needle) != NULL ? 1 : 0);
}

// LCOV_EXCL_BR_START - str/starts-with? arg validation
static valk_lval_t* valk_builtin_str_starts_with(valk_lenv_t* e,
                                                  valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* str = valk_lval_list_nth(a, 0)->str;
  const char* prefix = valk_lval_list_nth(a, 1)->str;
  u64 prefix_len = strlen(prefix);
  return valk_lval_num(strncmp(str, prefix, prefix_len) == 0 ? 1 : 0);
}

// LCOV_EXCL_BR_START - str/ends-with? arg validation
static valk_lval_t* valk_builtin_str_ends_with(valk_lenv_t* e,
                                                valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* str = valk_lval_list_nth(a, 0)->str;
  const char* suffix = valk_lval_list_nth(a, 1)->str;
  u64 str_len = strlen(str);
  u64 suffix_len = strlen(suffix);
  if (suffix_len > str_len) return valk_lval_num(0);
  return valk_lval_num(
      memcmp(str + str_len - suffix_len, suffix, suffix_len) == 0 ? 1 : 0);
}

// LCOV_EXCL_BR_START - str/join arg validation
static valk_lval_t* valk_builtin_str_join(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* list_arg = valk_lval_list_nth(a, 0);
  valk_lval_t* sep_arg = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, list_arg, LVAL_CONS, LVAL_NIL);
  LVAL_ASSERT_TYPE(a, sep_arg, LVAL_STR);
  // LCOV_EXCL_BR_STOP

  u64 count = valk_lval_list_count(list_arg);
  if (count == 0) return valk_lval_str("");

  const char* sep = sep_arg->str;
  u64 sep_len = strlen(sep);

  u64 total = 0;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t* item = valk_lval_list_nth(list_arg, i);
    LVAL_ASSERT_TYPE(a, item, LVAL_STR);
    total += strlen(item->str);
  }
  total += sep_len * (count - 1);

  char* buf = malloc(total + 1);
  if (!buf) return valk_lval_err("str/join: out of memory"); // LCOV_EXCL_LINE

  char* ptr = buf;
  for (u64 i = 0; i < count; i++) {
    if (i > 0) {
      memcpy(ptr, sep, sep_len);
      ptr += sep_len;
    }
    const char* s = valk_lval_list_nth(list_arg, i)->str;
    u64 len = strlen(s);
    memcpy(ptr, s, len);
    ptr += len;
  }
  *ptr = '\0';

  valk_lval_t* result = valk_lval_str(buf);
  free(buf);
  return result;
}

// LCOV_EXCL_BR_START - str/index-of arg validation
static valk_lval_t* valk_builtin_str_index_of(valk_lenv_t* e,
                                               valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* haystack = valk_lval_list_nth(a, 0)->str;
  const char* needle = valk_lval_list_nth(a, 1)->str;
  const char* found = strstr(haystack, needle);
  if (!found) return valk_lval_num(-1);
  return valk_lval_num(found - haystack);
}

// (str/last-index-of haystack needle limit?) — find LAST occurrence
// of needle in haystack[0:limit]. limit defaults to len(haystack).
// Returns -1 if not found. Implemented in C so callers don't have to
// recurse character-by-character (which blows the C stack on long
// strings — see lsp/find-line-start).
// LCOV_EXCL_BR_START - str/last-index-of arg validation
static valk_lval_t* valk_builtin_str_last_index_of(valk_lenv_t* e,
                                                    valk_lval_t* a) {
  UNUSED(e);
  i64 argc = valk_lval_list_count(a);
  LVAL_ASSERT_COUNT_GE(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* haystack = valk_lval_list_nth(a, 0)->str;
  const char* needle = valk_lval_list_nth(a, 1)->str;
  size_t hlen = strlen(haystack);
  size_t nlen = strlen(needle);
  if (nlen == 0 || nlen > hlen) return valk_lval_num(-1);

  size_t limit = hlen;
  if (argc >= 3) {
    valk_lval_t* lim = valk_lval_list_nth(a, 2);
    LVAL_ASSERT_TYPE(a, lim, LVAL_NUM);
    if (lim->num < 0) return valk_lval_num(-1);
    if ((size_t)lim->num < limit) limit = (size_t)lim->num;
  }
  if (limit < nlen) return valk_lval_num(-1);

  // Scan from limit-nlen down to 0 for the last needle occurrence.
  for (ssize_t i = (ssize_t)(limit - nlen); i >= 0; i--) {
    if (memcmp(haystack + i, needle, nlen) == 0) {
      return valk_lval_num(i);
    }
  }
  return valk_lval_num(-1);
}

// LCOV_EXCL_BR_START - str/lower arg validation
static valk_lval_t* valk_builtin_str_lower(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* src = valk_lval_list_nth(a, 0)->str;
  u64 len = strlen(src);
  char* buf = malloc(len + 1);
  if (!buf) return valk_lval_err("str/lower: out of memory"); // LCOV_EXCL_LINE
  for (u64 i = 0; i < len; i++) buf[i] = (char)tolower((unsigned char)src[i]);
  buf[len] = '\0';
  valk_lval_t* result = valk_lval_str(buf);
  free(buf);
  return result;
}

// LCOV_EXCL_BR_START - str/upper arg validation
static valk_lval_t* valk_builtin_str_upper(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* src = valk_lval_list_nth(a, 0)->str;
  u64 len = strlen(src);
  char* buf = malloc(len + 1);
  if (!buf) return valk_lval_err("str/upper: out of memory"); // LCOV_EXCL_LINE
  for (u64 i = 0; i < len; i++) buf[i] = (char)toupper((unsigned char)src[i]);
  buf[len] = '\0';
  valk_lval_t* result = valk_lval_str(buf);
  free(buf);
  return result;
}

// LCOV_EXCL_BR_START - str/trim arg validation
static valk_lval_t* valk_builtin_str_trim(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* src = valk_lval_list_nth(a, 0)->str;
  while (*src && isspace((unsigned char)*src)) src++;
  u64 len = strlen(src);
  while (len > 0 && isspace((unsigned char)src[len - 1])) len--;
  return valk_lval_str_n(src, len);
}

// LCOV_EXCL_BR_START - str/trim-left arg validation
static valk_lval_t* valk_builtin_str_trim_left(valk_lenv_t* e,
                                                valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* src = valk_lval_list_nth(a, 0)->str;
  while (*src && isspace((unsigned char)*src)) src++;
  return valk_lval_str(src);
}

// LCOV_EXCL_BR_START - str/trim-right arg validation
static valk_lval_t* valk_builtin_str_trim_right(valk_lenv_t* e,
                                                 valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* src = valk_lval_list_nth(a, 0)->str;
  u64 len = strlen(src);
  while (len > 0 && isspace((unsigned char)src[len - 1])) len--;
  return valk_lval_str_n(src, len);
}

void valk_register_string_builtins(valk_lenv_t* env) {
  // Accept errors so user code can serialize/print error values.
  valk_lenv_put_builtin_err_ok(env, "print", valk_builtin_print);
  valk_lenv_put_builtin_err_ok(env, "printf", valk_builtin_printf);
  valk_lenv_put_builtin_err_ok(env, "println", valk_builtin_println);
  valk_lenv_put_builtin_err_ok(env, "str", valk_builtin_str);
  valk_lenv_put_builtin(env, "make-string", valk_builtin_make_string);
  valk_lenv_put_builtin(env, "str/split", valk_builtin_str_split);
  valk_lenv_put_builtin(env, "str/replace", valk_builtin_str_replace);
  valk_lenv_put_builtin(env, "str/slice", valk_builtin_str_slice);
  valk_lenv_put_builtin(env, "str/contains?", valk_builtin_str_contains);
  valk_lenv_put_builtin(env, "str/starts-with?", valk_builtin_str_starts_with);
  valk_lenv_put_builtin(env, "str/ends-with?", valk_builtin_str_ends_with);
  valk_lenv_put_builtin(env, "str/join", valk_builtin_str_join);
  valk_lenv_put_builtin(env, "str/index-of", valk_builtin_str_index_of);
  valk_lenv_put_builtin(env, "str/last-index-of", valk_builtin_str_last_index_of);
  valk_lenv_put_builtin(env, "str/lower", valk_builtin_str_lower);
  valk_lenv_put_builtin(env, "str/upper", valk_builtin_str_upper);
  valk_lenv_put_builtin(env, "str/trim", valk_builtin_str_trim);
  valk_lenv_put_builtin(env, "str/trim-left", valk_builtin_str_trim_left);
  valk_lenv_put_builtin(env, "str/trim-right", valk_builtin_str_trim_right);
}
