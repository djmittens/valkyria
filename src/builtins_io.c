#include "builtins_internal.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "gc.h"

static valk_lval_t* valk_builtin_load(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  valk_lval_t* expr = valk_parse_file(valk_lval_list_nth(a, 0)->str);
  if (LVAL_TYPE(expr) == LVAL_ERR) {
    valk_lval_println(expr);
    return expr;
  }
  valk_lval_t* prev_mode = valk_lenv_get(e, valk_lval_sym("VALK_MODE"));
  valk_lenv_put(e, valk_lval_sym("VALK_MODE"), valk_lval_str("load"));
  valk_lval_t* last = nullptr;
  while (valk_lval_list_count(expr)) {
    valk_lval_t* x = valk_lval_eval(e, valk_lval_pop(expr, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
    } else {
      last = x;
    }
    valk_gc_malloc_heap_t* gc_heap =
        (valk_gc_malloc_heap_t*)valk_thread_ctx.allocator;
    if (gc_heap->type == VALK_ALLOC_GC_HEAP &&
        valk_gc_malloc_should_collect(gc_heap)) {
      valk_gc_malloc_collect(gc_heap, NULL);
    }
  }
  if (LVAL_TYPE(prev_mode) == LVAL_STR) {
    valk_lenv_put(e, valk_lval_sym("VALK_MODE"), prev_mode);
  } else {
    valk_lenv_put(e, valk_lval_sym("VALK_MODE"), valk_lval_str(""));
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

  if (length == UINT64_MAX) {
    fclose(f);
    LVAL_RAISE(a, "File is too large (%s)", filename);
  }

  char* content = calloc(length + 1, sizeof(char));
  u64 read_len = fread(content, 1, length, f);
  fclose(f);

  if (read_len != length) {
    free(content);
    LVAL_RAISE(a, "Failed to read file (%s)", filename);
  }

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
  valk_lenv_put_builtin(env, "read-file", valk_builtin_read_file);
}
