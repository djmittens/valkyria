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
#include "source_loc.h"

#ifdef VALK_COVERAGE
void valk_coverage_mark_tree(valk_lval_t* lval);
#endif

static char valk_lval_str_unescape(char x);

static char* lval_str_unescapable = "abfnrtv\\\'\"";

// Immortal singletons (nil, small-int cache) are shared process-wide: stamping
// a source position on one would make every occurrence in every file report
// the offset of whichever occurrence was parsed last.
static inline void reader_set_src_pos(valk_lval_t* v, int pos) {
  if (v->flags & LVAL_FLAG_IMMORTAL) return;
  LVAL_SRC_POS_SET(v, pos);
}

// ---------------------------------------------------------------------------
// Leaf parsers — shared by ctx reader
// ---------------------------------------------------------------------------

static valk_lval_t* valk_lval_read_sym(int* i, const char* s) {
  valk_lval_t* res;
  int start = *i;
  char next;
  int end = *i;
  for (; (next = s[end]); ++end) { // LCOV_EXCL_BR_LINE - character set dispatch
    if (strchr("abcdefghijklmnopqrstuvwxyz"
               "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
               "0123456789_+-*\\/=<>!&?:|.",
               next) &&
        s[end] != '\0') { // LCOV_EXCL_BR_LINE - redundant null guard
      continue;
    }
    break;
  }

  u64 len = end - (*i);
  if (len) { // LCOV_EXCL_BR_LINE - only called when sym chars present
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
      res = errno != ERANGE ? valk_lval_num_uncached(x)
                            : valk_lval_err("Invalid number format %s", sym);
    } else {
      res = valk_lval_sym(sym);
    }
    reader_set_src_pos(res, start);
    *i += len;
    free(sym);
    return res;
  }

  return valk_lval_str("");
}

static valk_lval_t* valk_lval_read_str(int* i, const char* s) {
  int start = *i;
  char next;
  int count = 1;

  if (s[(*i)++] != '"') { // LCOV_EXCL_BR_LINE - only called at string start
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
  valk_lval_t *result = valk_lval_str(tmp);
  reader_set_src_pos(result, start);
  return result;
}

// ---------------------------------------------------------------------------
// Forward declarations for mutually recursive ctx reader
// ---------------------------------------------------------------------------

static valk_lval_t *valk_lval_read_ctx(valk_parse_ctx_t *ctx);
static valk_lval_t *valk_lval_read_expr_ctx(valk_parse_ctx_t *ctx);

// ---------------------------------------------------------------------------
// Whitespace + line tracking
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Ctx-aware leaf wrappers
// ---------------------------------------------------------------------------

static valk_lval_t *valk_lval_read_sym_ctx(valk_parse_ctx_t *ctx) {
  __attribute__((unused)) int saved_line = ctx->line;
  __attribute__((unused)) int saved_col = ctx->pos - ctx->line_start + 1;
  valk_lval_t *res = valk_lval_read_sym(&ctx->pos, ctx->source);
  LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col); // LCOV_EXCL_BR_LINE - coverage macro
  return res;
}

static valk_lval_t *valk_lval_read_str_ctx(valk_parse_ctx_t *ctx) {
  __attribute__((unused)) int saved_line = ctx->line;
  __attribute__((unused)) int saved_col = ctx->pos - ctx->line_start + 1;
  valk_lval_t *res = valk_lval_read_str(&ctx->pos, ctx->source);
  LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col); // LCOV_EXCL_BR_LINE - coverage macro
  return res;
}

// ---------------------------------------------------------------------------
// Core reader — single unified implementation
// ---------------------------------------------------------------------------

static valk_lval_t *valk_lval_read_ctx(valk_parse_ctx_t *ctx) {
  valk_lval_t *res;

  parse_ctx_skip_whitespace(ctx);
  int saved_pos = ctx->pos;
  __attribute__((unused)) int saved_line = ctx->line;
  __attribute__((unused)) int saved_col = ctx->pos - ctx->line_start + 1;

  if (ctx->source[ctx->pos] == '\0') {
    return valk_lval_err("Unexpected  end of input");
  }

  if (ctx->source[ctx->pos] == '\'') {
    ctx->pos++;
    valk_lval_t *quoted = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(quoted) == LVAL_ERR) return quoted;
    res = valk_lval_qcons(quoted, valk_lval_nil());
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col); // LCOV_EXCL_BR_LINE - coverage macro
  } else if (ctx->source[ctx->pos] == '`') {
    ctx->pos++;
    valk_lval_t *quoted = valk_lval_read_ctx(ctx);
    if (LVAL_TYPE(quoted) == LVAL_ERR) return quoted;
    valk_lval_t *sym = valk_lval_sym("quasiquote");
    LVAL_SRC_POS_SET(sym, saved_pos);
    LVAL_SET_SOURCE_LOC(sym, ctx->file_id, saved_line, saved_col); // LCOV_EXCL_BR_LINE - coverage macro
    res = valk_lval_cons(sym, valk_lval_cons(quoted, valk_lval_nil()));
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col); // LCOV_EXCL_BR_LINE - coverage macro
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
    LVAL_SRC_POS_SET(sym, saved_pos);
    LVAL_SET_SOURCE_LOC(sym, ctx->file_id, saved_line, saved_col); // LCOV_EXCL_BR_LINE - coverage macro
    res = valk_lval_cons(sym, valk_lval_cons(unquoted, valk_lval_nil()));
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col); // LCOV_EXCL_BR_LINE - coverage macro
  } else if (strchr("({", ctx->source[ctx->pos])) {
    res = valk_lval_read_expr_ctx(ctx);
    LVAL_SET_SOURCE_LOC(res, ctx->file_id, saved_line, saved_col); // LCOV_EXCL_BR_LINE - coverage macro
  } else if (strchr("abcdefghijklmnopqrstuvwxyz"
                     "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                     "0123456789_+-*\\/=<>!&?:|",
                     ctx->source[ctx->pos])) {
    res = valk_lval_read_sym_ctx(ctx);
  } else if (ctx->source[ctx->pos] == '"') {
    res = valk_lval_read_str_ctx(ctx);
  } else {
    res = valk_lval_err("[offset: %d] Unexpected character %c", ctx->pos, ctx->source[ctx->pos]);
    ctx->pos++;
  }

  if (LVAL_SRC_POS(res) < 0) reader_set_src_pos(res, saved_pos);

  parse_ctx_skip_whitespace(ctx);
  return res;
}

static valk_lval_t *valk_lval_read_expr_ctx(valk_parse_ctx_t *ctx) {
  int saved_pos = ctx->pos;
  __attribute__((unused)) int saved_line = ctx->line;
  __attribute__((unused)) int saved_col = ctx->pos - ctx->line_start + 1;

  // Was this expression's opener at column 0? Only top-level forms start
  // at column 0 in idiomatic Valkyria code, so this is the signal we use
  // to gate the "missing close paren" recovery heuristic below. Nested
  // forms routinely have column-0 content inside them (e.g. under
  // `{do ...}`) and must not trigger recovery.
  bool opener_at_col0 = (saved_pos == 0) || (ctx->source[saved_pos - 1] == '\n');

  char end;
  bool is_quoted = false;
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
      return valk_lval_err(
          "[offset: %d] Unexpected end of input reading expr, while looking "
          "for `%c`",
          ctx->pos, end);
    }
    // Recovery heuristic: if this expression's opener was itself at
    // column 0 (i.e. a top-level form) and we now see a `(` or `{` at
    // column 0, the user almost certainly deleted a closing `)` / `}`
    // and the new column-0 char is the start of the next top-level form.
    // Bail out so the outer loop can resume there instead of consuming
    // the rest of the file. Gated on opener_at_col0 so that valid nested
    // code with column-0 content (e.g. `{do (a)\n(b)}`) keeps parsing.
    if (opener_at_col0 &&
        (ctx->source[ctx->pos] == '(' || ctx->source[ctx->pos] == '{') &&
        ctx->pos == ctx->line_start) {
      return valk_lval_err(
          "[offset: %d] Missing `%c`; next top-level form started here",
          saved_pos, end);
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
  for (u64 j = count; j > 0; j--) {
    if (is_quoted) {
      result = valk_lval_qcons(elements[j - 1], result);
    } else {
      result = valk_lval_cons(elements[j - 1], result);
    }
    LVAL_SET_SOURCE_LOC(result, ctx->file_id, saved_line, saved_col); // LCOV_EXCL_BR_LINE - coverage macro
  }

  reader_set_src_pos(result, saved_pos);
  return result;
}

// ---------------------------------------------------------------------------
// Public API — thin wrappers over ctx reader
// ---------------------------------------------------------------------------

valk_lval_t* valk_lval_read(int* i, const char* s) {
  valk_parse_ctx_t ctx = {
    .source = s,
    .pos = *i,
    .line = 1,
    .line_start = 0,
    .file_id = 0
  };
  valk_lval_t* res = valk_lval_read_ctx(&ctx);
  *i = ctx.pos;
  return res;
}

valk_lval_t* valk_lval_read_expr(int* i, const char* s) {
  valk_parse_ctx_t ctx = {
    .source = s,
    .pos = *i,
    .line = 1,
    .line_start = 0,
    .file_id = 0
  };
  valk_lval_t* res = valk_lval_read_expr_ctx(&ctx);
  *i = ctx.pos;
  return res;
}

// ---------------------------------------------------------------------------
// File and text parsing — both use ctx reader
// ---------------------------------------------------------------------------

valk_lval_t* valk_parse_file(const char* filename) {
  valk_coverage_record_file(filename);
  u16 file_id = 0;
#ifdef VALK_COVERAGE
  file_id = valk_source_register_file(filename);
#endif

  FILE* f = fopen(filename, "rb");
  if (f == nullptr) { // LCOV_EXCL_BR_LINE - file open failure
    LVAL_RAISE(valk_lval_nil(), "Could not open file (%s)", filename); // LCOV_EXCL_LINE
  }

  fseek(f, 0, SEEK_END);
  u64 length = ftell(f);
  fseek(f, 0, SEEK_SET);

  if (length == UINT64_MAX) { // LCOV_EXCL_BR_LINE - impossible file size
    fclose(f); // LCOV_EXCL_LINE
    LVAL_RAISE(valk_lval_nil(), "File is way too big buddy (%s)", filename); // LCOV_EXCL_LINE
  }

  char* input = calloc(length + 1, sizeof(char));
  u64 nread = fread(input, 1, length, f);
  (void)nread;
  fclose(f);

  struct tmp_arr {
    valk_lval_t** items;
    u64 count;
    u64 capacity;
  } tmp = {0};

  da_init(&tmp); // LCOV_EXCL_BR_LINE - macro reinit check

  valk_parse_ctx_t ctx = {
    .source = input,
    .pos = 0,
    .line = 1,
    .line_start = 0,
    .file_id = file_id
  };

  // LCOV_EXCL_BR_START - parse error handling and da_add branches
  while (ctx.source[ctx.pos] != '\0') {
    valk_lval_t* expr = valk_lval_read_ctx(&ctx);
    if (LVAL_TYPE(expr) == LVAL_ERR) {
      if (strstr(expr->str, "Unexpected") && strstr(expr->str, "end of input"))
        break;
      da_add(&tmp, expr);
      break;
    }
#ifdef VALK_COVERAGE
    valk_coverage_mark_tree(expr);
#endif
    da_add(&tmp, expr);
  }
  // LCOV_EXCL_BR_STOP

  free(input);
  valk_lval_t* res = valk_lval_list(tmp.items, tmp.count);
  da_free(&tmp);
  return res;
}

// Parse a complete text buffer into a list of top-level expressions.
// Errors (including unexpected end-of-input) are appended to the result list
// so callers can inspect them. The reader's interactive multi-line variant
// (valk_lval_read) is unaffected — that's what the REPL uses.
valk_lval_t* valk_parse_text(const char* text) {
  return valk_parse_text_named(text, nullptr);
}

valk_lval_t* valk_parse_text_named(const char* text, const char* filename) {
  u16 file_id = 0;
  if (filename != nullptr) {
    valk_coverage_record_file(filename);
#ifdef VALK_COVERAGE
    file_id = valk_source_register_file(filename);
#endif
  }

  struct { valk_lval_t** items; u64 count; u64 capacity; } tmp = {0};
  da_init(&tmp); // LCOV_EXCL_BR_LINE - macro reinit check

  valk_parse_ctx_t ctx = {
    .source = text,
    .pos = 0,
    .line = 1,
    .line_start = 0,
    .file_id = file_id
  };

  // LCOV_EXCL_BR_START - parse error handling and da_add branches
  while (ctx.source[ctx.pos] != '\0') {
    int before = ctx.pos;
    valk_lval_t* expr = valk_lval_read_ctx(&ctx);
    da_add(&tmp, expr);
    if (LVAL_TYPE(expr) != LVAL_ERR && file_id != 0) {
#ifdef VALK_COVERAGE
      valk_coverage_mark_tree(expr);
#endif
    }
    if (LVAL_TYPE(expr) == LVAL_ERR) {
      // "End of input" errors mean we've consumed everything — no recovery
      // possible. Everything else (unclosed paren, unexpected char) should
      // let subsequent top-level forms still parse, so the LSP can keep
      // validating the rest of the file while the user fixes the broken
      // region. The error carries [offset: N] for diagnostics.
      if (expr->str && strstr(expr->str, "end of input")) break;
      // Force forward progress if the reader didn't advance; prevents an
      // infinite loop on pathological inputs.
      if (ctx.pos == before && ctx.source[ctx.pos] != '\0') ctx.pos++;
    }
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t* res = valk_lval_list(tmp.items, tmp.count);
  da_free(&tmp);
  return res;
}

// ---------------------------------------------------------------------------
// Coverage builtins — only compiled in coverage mode
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// String unescape
// ---------------------------------------------------------------------------

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
