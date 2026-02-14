#include "parser.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "builtins_internal.h"
#include "collections.h"
#include "common.h"
#include "coverage.h"
#include "memory.h"

#ifdef VALK_COVERAGE
#include "source_loc.h"
void valk_coverage_mark_tree(valk_lval_t* lval);
#endif

static char valk_lval_str_unescape(char x);

static char* lval_str_unescapable = "abfnrtv\\\'\"";

static valk_lval_t* valk_lval_read_sym(int* i, const char* s) {
  valk_lval_t* res;
  char next;
  int end = *i;
  for (; (next = s[end]); ++end) {
    if (strchr("abcdefghijklmnopqrstuvwxyz"
               "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
               "0123456789_+-*\\/=<>!&?:",
               next) &&
        s[end] != '\0') {
      continue;
    }
    break;
  }

  u64 len = end - (*i);
  if (len) {
    char* sym = strndup(&s[*i], len);
    int isNum = strchr("-0123456789", sym[0]) != nullptr;
    for (u64 i = 1; i < len; ++i) {
      if (!strchr("0123456789", sym[i])) {
        isNum = 0;
        break;
      }
    }
    if (strlen(sym) == 1 && sym[0] == '-') {
      isNum = 0;
    }

    if (isNum) {
      errno = 0;
      long x = strtol(sym, nullptr, 10);
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

static valk_lval_t* valk_lval_read_str(int* i, const char* s) {
  char next;
  int count = 1;

  if (s[(*i)++] != '"') {
    return valk_lval_err(
        "Strings must start with `\"` but instead it started with %c", s[*i]);
  }

  for (int end = (*i); (next = s[end]) != '"'; ++end) {
    if (next == '\0') {
      return valk_lval_err("Unexpected  end of input at string literal");
    }
    if (next == '\\') {
      ++end;
      if (s[end] == '\0') {
        return valk_lval_err("Unexpected end of input after escape character");
      }
      if (!strchr(lval_str_unescapable, s[end])) {
        return valk_lval_err("Invalid escape character \\%c", s[end]);
      }
    }
    count++;
  }

  char tmp[count] = {};

  int offset = 0;
  int end;
  for (end = *i; (next = s[end]) != '"'; ++end) {
    if (next == '\\') {
      ++end;
      next = valk_lval_str_unescape(s[end]);
    }
    tmp[offset++] = next;
  }

  *i = end + 1;
  return valk_lval_str(tmp);
}

valk_lval_t* valk_lval_read(int* i, const char* s) {
  valk_lval_t* res;

  while (strchr(" ;\t\v\r\n", s[*i]) && s[*i] != '\0') {
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

  if (s[*i] == '\'') {
    (*i)++;
    valk_lval_t* quoted = valk_lval_read(i, s);
    if (LVAL_TYPE(quoted) == LVAL_ERR) {
      return quoted;
    }
    res = valk_lval_qcons(quoted, valk_lval_nil());
  }
  else if (s[*i] == '`') {
    (*i)++;
    valk_lval_t* quoted = valk_lval_read(i, s);
    if (LVAL_TYPE(quoted) == LVAL_ERR) {
      return quoted;
    }
    valk_lval_t* sym = valk_lval_sym("quasiquote");
    res = valk_lval_cons(sym, valk_lval_cons(quoted, valk_lval_nil()));
  }
  else if (s[*i] == ',') {
    (*i)++;
    bool splicing = false;
    if (s[*i] == '@') {
      (*i)++;
      splicing = true;
    }
    valk_lval_t* unquoted = valk_lval_read(i, s);
    if (LVAL_TYPE(unquoted) == LVAL_ERR) {
      return unquoted;
    }
    valk_lval_t* sym = valk_lval_sym(splicing ? "unquote-splicing" : "unquote");
    res = valk_lval_cons(sym, valk_lval_cons(unquoted, valk_lval_nil()));
  } else if (strchr("({", s[*i])) {
    res = valk_lval_read_expr(i, s);
  }
  else if (strchr("abcdefghijklmnopqrstuvwxyz"
                  "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                  "0123456789_+-*\\/=<>!&?:",
                  s[*i])) {
    res = valk_lval_read_sym(i, s);
  } else if (s[*i] == '"') {
    res = valk_lval_read_str(i, s);
  } else {
    res = valk_lval_err("[offset: %ld] Unexpected character %c", *i, s[*i]);
    ++(*i);
  }

  while (strchr(" ;\t\v\r\n", s[*i]) && s[*i] != '\0') {
    if (s[*i] == ';') {
      while (s[*i] != '\n' && s[*i] != '\0') {
        ++(*i);
      }
    } else {
      ++(*i);
    }
  }
  return res;
}

valk_lval_t* valk_lval_read_expr(int* i, const char* s) {
  char end;
  bool is_quoted = false;
  if (s[(*i)++] == '{') {
    is_quoted = true;
    end = '}';
  } else {
    end = ')';
  }

  u64 capacity = 16;
  u64 count = 0;
  valk_lval_t** elements = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);

  while (s[*i] != end) {
    if (s[*i] == '\0') {
      valk_lval_t* err = valk_lval_err(
          "[offset: %d] Unexpected end of input reading expr, while looking "
          "for `%c`",
          *i, end);
      return err;
    }
    valk_lval_t* x = valk_lval_read(i, s);
    if (LVAL_TYPE(x) == LVAL_ERR) {
      return x;
    }

    if (count >= capacity) {
      capacity *= 2;
      valk_lval_t** new_elements =
          valk_mem_alloc(sizeof(valk_lval_t*) * capacity);
      memcpy(new_elements, elements, sizeof(valk_lval_t*) * count);
      elements = new_elements;
    }
    elements[count++] = x;
  }
  (*i)++;

  valk_lval_t* result = valk_lval_nil();
  for (u64 j = count; j > 0; j--) {
    if (is_quoted) {
      result = valk_lval_qcons(elements[j - 1], result);
    } else {
      result = valk_lval_cons(elements[j - 1], result);
    }
  }

  return result;
}

#ifdef VALK_COVERAGE
static valk_lval_t *valk_lval_read_ctx(valk_parse_ctx_t *ctx);
static valk_lval_t *valk_lval_read_expr_ctx(valk_parse_ctx_t *ctx);
#endif

valk_lval_t* valk_parse_file(const char* filename) {
  valk_coverage_record_file(filename);
#ifdef VALK_COVERAGE
  u16 file_id = valk_source_register_file(filename);
#endif
  
  FILE* f = fopen(filename, "rb");
  if (f == nullptr) {
    LVAL_RAISE(valk_lval_nil(), "Could not open file (%s)", filename);
  }

  fseek(f, 0, SEEK_END);
  u64 length = ftell(f);
  fseek(f, 0, SEEK_SET);

  if (length == UINT64_MAX) {
    fclose(f);
    LVAL_RAISE(valk_lval_nil(), "File is way too big buddy (%s)", filename);
  }

  char* input = calloc(length + 1, sizeof(char));
  fread(input, 1, length, f);
  fclose(f);

  struct tmp_arr {
    valk_lval_t** items;
    u64 count;
    u64 capacity;
  } tmp = {0};

  da_init(&tmp);

#ifdef VALK_COVERAGE
  valk_parse_ctx_t ctx = {
    .source = input,
    .pos = 0,
    .line = 1,
    .line_start = 0,
    .file_id = file_id
  };
  
  while (ctx.source[ctx.pos] != '\0') {
    valk_lval_t* expr = valk_lval_read_ctx(&ctx);
    if (LVAL_TYPE(expr) == LVAL_ERR) {
      if (strstr(expr->str, "Unexpected end of input")) break;
      da_add(&tmp, expr);
      break;
    }
    valk_coverage_mark_tree(expr);
    da_add(&tmp, expr);
  }
#else
  int pos = 0;

  #define SKIP_WS_AND_COMMENTS() do { \
    while (strchr(" ;\t\v\r\n", input[pos]) && input[pos] != '\0') { \
      if (input[pos] == ';') { \
        while (input[pos] != '\n' && input[pos] != '\0') pos++; \
      } else { \
        pos++; \
      } \
    } \
  } while(0)

  SKIP_WS_AND_COMMENTS();

  while (input[pos] != '\0') {
    da_add(&tmp, valk_lval_read(&pos, input));
    valk_lval_t* last = tmp.items[tmp.count - 1];
    if (LVAL_TYPE(last) == LVAL_ERR) break;
    if (LVAL_TYPE(last) == LVAL_CONS && LVAL_TYPE(last->cons.head) == LVAL_ERR)
      break;
    SKIP_WS_AND_COMMENTS();
  }

  #undef SKIP_WS_AND_COMMENTS
#endif

  free(input);
  valk_lval_t* res = valk_lval_list(tmp.items, tmp.count);
  da_free(&tmp);
  return res;
}

// LCOV_EXCL_BR_START - coverage-mode parser functions not exercised in normal test runs
#ifdef VALK_COVERAGE

static void parse_ctx_skip_whitespace(valk_parse_ctx_t *ctx) {
  while (strchr(" ;\t\v\r\n", ctx->source[ctx->pos]) && ctx->source[ctx->pos] != '\0') {
    if (ctx->source[ctx->pos] == '\n') {
      ctx->line++;
      ctx->line_start = ctx->pos + 1;
    }
    if (ctx->source[ctx->pos] == ';') {
      while (ctx->source[ctx->pos] != '\n' && ctx->source[ctx->pos] != '\0') {
        ctx->pos++;
      }
    } else {
      ctx->pos++;
    }
  }
}

static valk_lval_t *valk_lval_read_sym_ctx(valk_parse_ctx_t *ctx) {
  int saved_line = ctx->line;
  int saved_col = ctx->pos - ctx->line_start + 1;
  
  valk_lval_t *res = valk_lval_read_sym(&ctx->pos, ctx->source);
  LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  return res;
}

static valk_lval_t *valk_lval_read_str_ctx(valk_parse_ctx_t *ctx) {
  int saved_line = ctx->line;
  int saved_col = ctx->pos - ctx->line_start + 1;
  
  valk_lval_t *res = valk_lval_read_str(&ctx->pos, ctx->source);
  LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  return res;
}

static valk_lval_t *valk_lval_read_ctx(valk_parse_ctx_t *ctx) {
  valk_lval_t *res;
  int saved_line = ctx->line;
  int saved_col = ctx->pos - ctx->line_start + 1;
  
  parse_ctx_skip_whitespace(ctx);
  saved_line = ctx->line;
  saved_col = ctx->pos - ctx->line_start + 1;
  
  if (ctx->source[ctx->pos] == '\0') {
    return valk_lval_err("Unexpected end of input");
  }
  
  if (ctx->source[ctx->pos] == '\'') {
    ctx->pos++;
    valk_lval_t *quoted = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(quoted) == LVAL_ERR) return quoted;
    res = valk_lval_qcons(quoted, valk_lval_nil());
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  } else if (ctx->source[ctx->pos] == '`') {
    ctx->pos++;
    valk_lval_t *quoted = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(quoted) == LVAL_ERR) return quoted;
    valk_lval_t *sym = valk_lval_sym("quasiquote");
    LVAL_SET_SOURCE_LOC(sym, ctx->file_id, saved_line, saved_col);
    res = valk_lval_cons(sym, valk_lval_cons(quoted, valk_lval_nil()));
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  } else if (ctx->source[ctx->pos] == ',') {
    ctx->pos++;
    bool splicing = false;
    if (ctx->source[ctx->pos] == '@') {
      ctx->pos++;
      splicing = true;
    }
    valk_lval_t *unquoted = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(unquoted) == LVAL_ERR) return unquoted;
    valk_lval_t *sym = valk_lval_sym(splicing ? "unquote-splicing" : "unquote");
    LVAL_SET_SOURCE_LOC(sym, ctx->file_id, saved_line, saved_col);
    res = valk_lval_cons(sym, valk_lval_cons(unquoted, valk_lval_nil()));
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  } else if (strchr("({", ctx->source[ctx->pos])) {
    res = valk_lval_read_expr_ctx(ctx);
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col);
  } else if (strchr("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_+-*\\/=<>!&?:", ctx->source[ctx->pos])) {
    res = valk_lval_read_sym_ctx(ctx);
  } else if (ctx->source[ctx->pos] == '"') {
    res = valk_lval_read_str_ctx(ctx);
  } else {
    res = valk_lval_err("[offset: %d] Unexpected character %c", ctx->pos, ctx->source[ctx->pos]);
    ctx->pos++;
  }
  
  parse_ctx_skip_whitespace(ctx);
  return res;
}

static valk_lval_t *valk_lval_read_expr_ctx(valk_parse_ctx_t *ctx) {
  char end;
  bool is_quoted = false;
  int saved_line = ctx->line;
  int saved_col = ctx->pos - ctx->line_start + 1;
  
  if (ctx->source[ctx->pos++] == '{') {
    is_quoted = true;
    end = '}';
  } else {
    end = ')';
  }
  
  u64 capacity = 16;
  u64 count = 0;
  valk_lval_t **elements = valk_mem_alloc(sizeof(valk_lval_t *) * capacity);
  
  while (ctx->source[ctx->pos] != end) {
    if (ctx->source[ctx->pos] == '\0') {
      return valk_lval_err("[offset: %d] Unexpected end of input reading expr", ctx->pos);
    }
    valk_lval_t *x = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(x) == LVAL_ERR) return x;
    
    if (count >= capacity) {
      capacity *= 2;
      valk_lval_t **new_elements = valk_mem_alloc(sizeof(valk_lval_t *) * capacity);
      memcpy(new_elements, elements, sizeof(valk_lval_t *) * count);
      elements = new_elements;
    }
    elements[count++] = x;
  }
  ctx->pos++;
  
  valk_lval_t *result = valk_lval_nil();
  LVAL_SET_SOURCE_LOC(result, ctx->file_id, saved_line, saved_col);
  for (u64 j = count; j > 0; j--) {
    if (is_quoted) {
      result = valk_lval_qcons(elements[j - 1], result);
    } else {
      result = valk_lval_cons(elements[j - 1], result);
    }
    LVAL_SET_SOURCE_LOC(result, ctx->file_id, saved_line, saved_col);
  }
  
  return result;
}

#endif // VALK_COVERAGE
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_START - coverage builtins are meta-level code for Valk coverage tracking
#ifdef VALK_COVERAGE

static valk_lval_t* valk_builtin_coverage_mark(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  VALK_COVERAGE_MARK_LVAL(expr);
  return expr;
}

static valk_lval_t* valk_builtin_coverage_record(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  VALK_COVERAGE_RECORD_LVAL(expr);
  return expr;
}

static valk_lval_t* valk_builtin_coverage_branch(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* line_val = valk_lval_list_nth(a, 0);
  valk_lval_t* taken_val = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, line_val, LVAL_NUM);
  LVAL_ASSERT_TYPE(a, taken_val, LVAL_NUM);
  u16 file_id = line_val->cov_file_id;
  u16 line = (u16)line_val->num;
  bool taken = taken_val->num != 0;
  valk_coverage_record_branch(file_id, line, taken);
  return valk_lval_num(taken ? 1 : 0);
}

static valk_lval_t* valk_builtin_source_line(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  return valk_lval_num(expr->cov_line);
}

static valk_lval_t* valk_builtin_source_column(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  return valk_lval_num(expr->cov_column);
}

static valk_lval_t* valk_builtin_source_file(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  u16 file_id = expr->cov_file_id;
  const char* filename = valk_source_get_filename(file_id);
  if (filename == NULL) {
    return valk_lval_str("<unknown>");
  }
  return valk_lval_str(filename);
}
#endif
// LCOV_EXCL_STOP

void valk_register_coverage_builtins(valk_lenv_t* env) {
#ifdef VALK_COVERAGE
  valk_lenv_put_builtin(env, "coverage-mark", valk_builtin_coverage_mark);
  valk_lenv_put_builtin(env, "coverage-record", valk_builtin_coverage_record);
  valk_lenv_put_builtin(env, "coverage-branch", valk_builtin_coverage_branch);
  valk_lenv_put_builtin(env, "source-line", valk_builtin_source_line);
  valk_lenv_put_builtin(env, "source-column", valk_builtin_source_column);
  valk_lenv_put_builtin(env, "source-file", valk_builtin_source_file);
#else
  UNUSED(env);
#endif
}

static char valk_lval_str_unescape(char x) {
  switch (x) {  // LCOV_EXCL_BR_LINE - not all escape sequences tested
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
