#include "builtins_internal.h"

#ifdef __APPLE__
#include <mach-o/dyld.h>
#endif

#include <errno.h>
#include <limits.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "coverage.h"
#include "diag.h"
#include "gc.h"
#include "macro.h"
#include "type_env.h"

extern void valk_register_file_builtins(valk_lenv_t *env);
extern void valk_register_load_builtins(valk_lenv_t *env);

static valk_lval_t* valk_builtin_read(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* input = valk_lval_list_nth(a, 0)->str;
  int pos = 0;
  return valk_lval_read(&pos, input);
}

static valk_lval_t* valk_builtin_parse(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  return valk_parse_text(valk_lval_list_nth(a, 0)->str);
}

static valk_lval_t* valk_builtin_src_pos(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_SRC_POS(v));
}

static valk_lval_t* valk_builtin_quoted_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num((v->flags & LVAL_FLAG_QUOTED) ? 1 : 0);
}

static valk_lval_t* valk_builtin_offset_to_line_col(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);
  // LCOV_EXCL_BR_STOP
  const char *text = valk_lval_list_nth(a, 0)->str;
  int offset = (int)valk_lval_list_nth(a, 1)->num;
  int line = 0, col = 0;
  for (int i = 0; i < offset && text[i]; i++) {
    if (text[i] == '\n') { line++; col = 0; }
    else col++;
  }
  valk_lval_t *items[2] = {valk_lval_num(line), valk_lval_num(col)};
  return valk_lval_qlist(items, 2);
}

static valk_lval_t* valk_builtin_qcons(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* arg1 = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, arg1, LVAL_CONS, LVAL_NIL);
  // LCOV_EXCL_BR_STOP
  return valk_lval_qcons(valk_lval_list_nth(a, 0), arg1);
}

static valk_lval_t* valk_builtin_type_of(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_str(valk_ltype_name(LVAL_TYPE(v)));
}

static valk_lval_t* valk_builtin_str_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_STR ? 1 : 0);
}

static valk_lval_t* valk_builtin_sym_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_SYM ? 1 : 0);
}

static valk_lval_t* valk_builtin_num_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_NUM ? 1 : 0);
}

static valk_lval_t* valk_builtin_fun_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_FUN ? 1 : 0);
}

static valk_lval_t* valk_builtin_read_file(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* filename = valk_lval_list_nth(a, 0)->str;
  FILE* f = fopen(filename, "rb");
  if (f == nullptr) {
    LVAL_RAISE(a, "Could not open file (%s)", filename);
  }

  fseek(f, 0, SEEK_END);
  u64 length = ftell(f);
  fseek(f, 0, SEEK_SET);

  // LCOV_EXCL_START - ftell overflow and partial fread are platform failures
  if (length == UINT64_MAX) {
    fclose(f);
    LVAL_RAISE(a, "File is too large (%s)", filename);
  }
  // LCOV_EXCL_STOP

  char* content = calloc(length + 1, sizeof(char));
  u64 read_len = fread(content, 1, length, f);
  fclose(f);

  // LCOV_EXCL_START - partial fread requires I/O failure mid-read
  if (read_len != length) {
    free(content);
    LVAL_RAISE(a, "Failed to read file (%s)", filename);
  }
  // LCOV_EXCL_STOP

  valk_lval_t* result = valk_lval_str(content);
  free(content);
  return result;
}

static valk_lval_t* valk_builtin_error(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  valk_lval_t* err = valk_lval_err("%s", valk_lval_list_nth(a, 0)->str);
  return err;
}

static valk_lval_t* valk_builtin_error_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_TYPE(v) == LVAL_ERR ? 1 : 0);
}

static valk_lval_t* valk_builtin_list_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  valk_ltype_e t = LVAL_TYPE(v);
  return valk_lval_num(t == LVAL_CONS || t == LVAL_NIL || t == LVAL_QEXPR ? 1 : 0);
}

static valk_lval_t* valk_builtin_ref_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1); // LCOV_EXCL_BR_LINE
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_TYPE(v) == LVAL_REF ? 1 : 0);
}

void valk_register_io_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "error", valk_builtin_error);
  valk_lenv_put_builtin_err_ok(env, "error?", valk_builtin_error_p);
  valk_lenv_put_builtin(env, "list?", valk_builtin_list_p);
  valk_lenv_put_builtin(env, "ref?", valk_builtin_ref_p);
  valk_register_load_builtins(env);
  valk_lenv_put_builtin(env, "read", valk_builtin_read);
  valk_lenv_put_builtin(env, "parse", valk_builtin_parse);
  valk_lenv_put_builtin(env, "read-file", valk_builtin_read_file);
  valk_lenv_put_builtin(env, "src-pos", valk_builtin_src_pos);
  valk_lenv_put_builtin(env, "qcons", valk_builtin_qcons);
  valk_lenv_put_builtin_err_ok(env, "type-of", valk_builtin_type_of);
  valk_lenv_put_builtin(env, "str?", valk_builtin_str_p);
  valk_lenv_put_builtin(env, "sym?", valk_builtin_sym_p);
  valk_lenv_put_builtin(env, "num?", valk_builtin_num_p);
  valk_lenv_put_builtin(env, "fun?", valk_builtin_fun_p);
  valk_lenv_put_builtin(env, "quoted?", valk_builtin_quoted_p);
  valk_lenv_put_builtin(env, "offset->line-col", valk_builtin_offset_to_line_col);
  valk_register_file_builtins(env);
}
