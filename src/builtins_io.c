#include "builtins_internal.h"

#include <dirent.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

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

static valk_lval_t* valk_builtin_src_pos(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num(v->src_pos);
}

static valk_lval_t* valk_builtin_quoted_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_num((v->flags & LVAL_FLAG_QUOTED) ? 1 : 0);
}

static valk_lval_t* valk_builtin_offset_to_line_col(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);
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
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* arg1 = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, arg1, LVAL_CONS, LVAL_NIL);
  return valk_lval_qcons(valk_lval_list_nth(a, 0), arg1);
}

static valk_lval_t* valk_builtin_type_of(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* v = valk_lval_list_nth(a, 0);
  return valk_lval_str(valk_ltype_name(LVAL_TYPE(v)));
}

static valk_lval_t* valk_builtin_str_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_STR ? 1 : 0);
}

static valk_lval_t* valk_builtin_sym_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_SYM ? 1 : 0);
}

static valk_lval_t* valk_builtin_num_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_NUM ? 1 : 0);
}

static valk_lval_t* valk_builtin_fun_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  return valk_lval_num(LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_FUN ? 1 : 0);
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

static valk_lval_t* valk_builtin_list_dir(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char* path = valk_lval_list_nth(a, 0)->str;
  DIR* d = opendir(path);
  if (!d) LVAL_RAISE(a, "Could not open directory (%s)", path);

  size_t count = 0;
  size_t cap = 64;
  valk_lval_t** items = malloc(cap * sizeof(valk_lval_t*));

  struct dirent* ent;
  while ((ent = readdir(d))) {
    if (ent->d_name[0] == '.') continue;

    char full[4096];
    snprintf(full, sizeof(full), "%s/%s", path, ent->d_name);
    struct stat st;
    const char* type_str = "file";
    if (stat(full, &st) == 0 && S_ISDIR(st.st_mode))
      type_str = "dir";

    valk_lval_t* fields[4] = {
      valk_lval_sym(":name"), valk_lval_str(ent->d_name),
      valk_lval_sym(":type"), valk_lval_str(type_str),
    };
    if (count >= cap) {
      cap *= 2;
      items = realloc(items, cap * sizeof(valk_lval_t*));
    }
    items[count++] = valk_lval_qlist(fields, 4);
  }
  closedir(d);

  valk_lval_t* result = valk_lval_qlist(items, count);
  free(items);
  return result;
}

static valk_lval_t* valk_builtin_file_fingerprint(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  const char* path = valk_lval_list_nth(a, 0)->str;
  struct stat st;
  if (stat(path, &st) != 0)
    LVAL_RAISE(a, "file/fingerprint: cannot stat (%s)", path);
  char buf[64];
  snprintf(buf, sizeof(buf), "%lld:%lld", (long long)st.st_mtime, (long long)st.st_size);
  return valk_lval_str(buf);
}

static valk_lval_t* valk_builtin_file_size(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  const char* path = valk_lval_list_nth(a, 0)->str;
  struct stat st;
  if (stat(path, &st) != 0)
    LVAL_RAISE(a, "file/size: cannot stat (%s)", path);
  return valk_lval_num((long)st.st_size);
}

static valk_lval_t *valk_builtin_sem_encode_deltas(valk_lenv_t *e,
                                                    valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char *text = valk_lval_list_nth(a, 0)->str;
  valk_lval_t *tokens = valk_lval_list_nth(a, 1);

  int text_len = (int)strlen(text);
  int prev_line = 0, prev_col = 0, scan_pos = 0;
  valk_lval_t *result = valk_lval_nil();
  int count = 0;

  valk_lval_t *cur = tokens;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *tok = cur->cons.head;
    if (!tok || LVAL_TYPE(tok) != LVAL_CONS) break;

    valk_lval_t *off_v = tok->cons.head;
    valk_lval_t *r1 = tok->cons.tail;
    if (!r1 || LVAL_TYPE(r1) != LVAL_CONS) break;
    valk_lval_t *len_v = r1->cons.head;
    valk_lval_t *r2 = r1->cons.tail;
    if (!r2 || LVAL_TYPE(r2) != LVAL_CONS) break;
    valk_lval_t *type_v = r2->cons.head;
    valk_lval_t *r3 = r2->cons.tail;
    if (!r3 || LVAL_TYPE(r3) != LVAL_CONS) break;
    valk_lval_t *mods_v = r3->cons.head;

    int off = (int)off_v->num;
    int tok_len = (int)len_v->num;
    int tok_type = (int)type_v->num;
    int tok_mods = (int)mods_v->num;

    int line = prev_line, col = prev_col;
    if (off > scan_pos) {
      for (int i = scan_pos; i < off && i < text_len; i++) {
        if (text[i] == '\n') { line++; col = 0; }
        else col++;
      }
    } else if (off < scan_pos) {
      line = 0; col = 0;
      for (int i = 0; i < off && i < text_len; i++) {
        if (text[i] == '\n') { line++; col = 0; }
        else col++;
      }
    }
    scan_pos = off;

    int dl = line - prev_line;
    int dc = (dl == 0) ? col - prev_col : col;

    result = valk_lval_qcons(valk_lval_num(dl), result);
    result = valk_lval_qcons(valk_lval_num(dc), result);
    result = valk_lval_qcons(valk_lval_num(tok_len), result);
    result = valk_lval_qcons(valk_lval_num(tok_type), result);
    result = valk_lval_qcons(valk_lval_num(tok_mods), result);
    (void)count;
    count++;

    prev_line = line;
    prev_col = col;
    cur = cur->cons.tail;
  }

  valk_lval_t *reversed = valk_lval_nil();
  valk_lval_t *p = result;
  while (p && LVAL_TYPE(p) == LVAL_CONS) {
    reversed = valk_lval_qcons(p->cons.head, reversed);
    p = p->cons.tail;
  }
  return reversed;
}

static valk_lval_t *valk_builtin_offsets_to_lines(valk_lenv_t *e,
                                                    valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char *text = valk_lval_list_nth(a, 0)->str;
  valk_lval_t *offsets = valk_lval_list_nth(a, 1);
  int text_len = (int)strlen(text);

  int scan_pos = 0, line = 0, col = 0;
  valk_lval_t *result = valk_lval_nil();

  valk_lval_t *cur = offsets;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    int off = (int)cur->cons.head->num;
    if (off >= scan_pos) {
      for (int i = scan_pos; i < off && i < text_len; i++) {
        if (text[i] == '\n') { line++; col = 0; }
        else col++;
      }
    }
    scan_pos = off;
    valk_lval_t *pair[2] = {valk_lval_num(line), valk_lval_num(col)};
    result = valk_lval_qcons(valk_lval_qlist(pair, 2), result);
    cur = cur->cons.tail;
  }

  valk_lval_t *reversed = valk_lval_nil();
  valk_lval_t *p = result;
  while (p && LVAL_TYPE(p) == LVAL_CONS) {
    reversed = valk_lval_qcons(p->cons.head, reversed);
    p = p->cons.tail;
  }
  return reversed;
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
  valk_lenv_put_builtin(env, "src-pos", valk_builtin_src_pos);
  valk_lenv_put_builtin(env, "qcons", valk_builtin_qcons);
  valk_lenv_put_builtin(env, "type-of", valk_builtin_type_of);
  valk_lenv_put_builtin(env, "str?", valk_builtin_str_p);
  valk_lenv_put_builtin(env, "sym?", valk_builtin_sym_p);
  valk_lenv_put_builtin(env, "num?", valk_builtin_num_p);
  valk_lenv_put_builtin(env, "fun?", valk_builtin_fun_p);
  valk_lenv_put_builtin(env, "quoted?", valk_builtin_quoted_p);
  valk_lenv_put_builtin(env, "offset->line-col", valk_builtin_offset_to_line_col);
  valk_lenv_put_builtin(env, "list-dir", valk_builtin_list_dir);
  valk_lenv_put_builtin(env, "file/size", valk_builtin_file_size);
  valk_lenv_put_builtin(env, "file/fingerprint", valk_builtin_file_fingerprint);
  valk_lenv_put_builtin(env, "sem/encode-deltas", valk_builtin_sem_encode_deltas);
  valk_lenv_put_builtin(env, "offsets->line-cols", valk_builtin_offsets_to_lines);
}
