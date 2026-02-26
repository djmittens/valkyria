#include "builtins_internal.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "coverage.h"
#include "diag.h"
#include "gc.h"
#include "type_env.h"

static bool env_has_name(const char *name, void *ctx) {
  valk_lenv_t *env = ctx;
  while (env) {
    for (u64 i = 0; i < env->symbols.count; i++)
      if (strcmp(env->symbols.items[i], name) == 0) return true;
    env = env->parent;
  }
  return false;
}

static char *read_file_text(const char *filename) {
  FILE *f = fopen(filename, "rb");
  if (!f) return nullptr;
  fseek(f, 0, SEEK_END);
  long flen = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (flen <= 0) { fclose(f); return nullptr; } // LCOV_EXCL_LINE
  char *text = calloc(flen + 1, 1);
  fread(text, 1, flen, f);
  fclose(f);
  return text;
}

static valk_lval_t* valk_builtin_load(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char *filename = valk_lval_list_nth(a, 0)->str;
  valk_coverage_record_file(filename);

  char *text = read_file_text(filename);
  if (!text)
    return valk_lval_err("Could not open file (%s)", filename);

  // Stage 1: Parse
  valk_lval_t *ast = valk_parse_text(text);
  if (LVAL_TYPE(ast) == LVAL_ERR) {
    valk_lval_println(ast);
    free(text);
    return ast;
  }

  // Stage 2: Validate
  valk_name_resolver_t resolver = {.is_known = env_has_name, .ctx = e};
  valk_diag_list_t diags = valk_validate_ast(ast, text, resolver);
  if (valk_diag_error_count(&diags) > 0) {
    valk_diag_fprint(&diags, filename, text, stderr);
    valk_diag_free(&diags);
    free(text);
    return valk_lval_err("Diagnostics found errors in %s", filename);
  }
  valk_diag_free(&diags);
  free(text);

  // Stage 3: Evaluate
  valk_lval_t* last = nullptr;
  while (valk_lval_list_count(ast)) {
    valk_lval_t* x = valk_type_transform_expr(valk_lval_pop(ast, 0));
    if (LVAL_TYPE(x) == LVAL_NIL) continue;
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
      return x;
    }
    x = valk_lval_eval(e, x);
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
    } else {
      last = x;
    }
    valk_gc_heap_t* gc_heap =
        (valk_gc_heap_t*)valk_thread_ctx.allocator;
    if (gc_heap->type == VALK_ALLOC_GC_HEAP && // LCOV_EXCL_BR_LINE - allocator is always GC heap
        valk_gc_should_collect(gc_heap)) {
      valk_gc_heap_collect(gc_heap);
    }
  }
  if (last) {
    valk_lenv_put(e, valk_lval_sym("VALK_LAST_VALUE"), last);
  }

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_read(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char* input = valk_lval_list_nth(a, 0)->str;
  int pos = 0;
  return valk_lval_read(&pos, input);
}

static valk_lval_t* valk_builtin_parse(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  return valk_parse_text(valk_lval_list_nth(a, 0)->str);
}

static void offset_to_line_col(const char *text, int offset, int *line, int *col) {
  *line = 0; *col = 0;
  for (int i = 0; i < offset && text[i]; i++) {
    if (text[i] == '\n') { (*line)++; *col = 0; }
    else (*col)++;
  }
}

static valk_lval_t* valk_builtin_validate(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);

  valk_lval_t *ast = valk_lval_list_nth(a, 0);
  const char *text = valk_lval_list_nth(a, 1)->str;

  valk_name_resolver_t resolver = {.is_known = env_has_name, .ctx = e};
  valk_diag_list_t diags = valk_validate_ast(ast, text, resolver);

  valk_lval_t **items = malloc(diags.count * sizeof(valk_lval_t *));
  for (size_t i = 0; i < diags.count; i++) {
    int line, col;
    offset_to_line_col(text, diags.items[i].offset, &line, &col);
    int end_col = col + diags.items[i].len;

    valk_lval_t *fields[10] = {
      valk_lval_sym(":line"),    valk_lval_num(line),
      valk_lval_sym(":col"),     valk_lval_num(col),
      valk_lval_sym(":end-col"), valk_lval_num(end_col),
      valk_lval_sym(":severity"), valk_lval_num(diags.items[i].severity),
      valk_lval_sym(":message"), valk_lval_str(diags.items[i].message),
    };
    items[i] = valk_lval_qlist(fields, 10);
  }

  valk_lval_t *result = valk_lval_qlist(items, diags.count);
  free(items);
  valk_diag_free(&diags);
  return result;
}

static valk_lval_t* valk_builtin_read_file(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

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
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  valk_lval_t* err = valk_lval_err(valk_lval_list_nth(a, 0)->str);
  return err;
}

static valk_lval_t* valk_builtin_error_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_TYPE(v) == LVAL_ERR ? 1 : 0);
}

static valk_lval_t* valk_builtin_list_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  valk_ltype_e t = LVAL_TYPE(v);
  return valk_lval_num(t == LVAL_CONS || t == LVAL_NIL || t == LVAL_QEXPR ? 1 : 0);
}

static valk_lval_t* valk_builtin_ref_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_TYPE(v) == LVAL_REF ? 1 : 0);
}

void valk_register_io_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "error", valk_builtin_error);
  valk_lenv_put_builtin(env, "error?", valk_builtin_error_p);
  valk_lenv_put_builtin(env, "list?", valk_builtin_list_p);
  valk_lenv_put_builtin(env, "ref?", valk_builtin_ref_p);
  valk_lenv_put_builtin(env, "load", valk_builtin_load);
  valk_lenv_put_builtin(env, "read", valk_builtin_read);
  valk_lenv_put_builtin(env, "parse", valk_builtin_parse);
  valk_lenv_put_builtin(env, "validate", valk_builtin_validate);
  valk_lenv_put_builtin(env, "read-file", valk_builtin_read_file);
}
