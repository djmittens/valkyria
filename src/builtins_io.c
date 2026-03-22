#include "builtins_internal.h"
extern valk_lval_t *valk_builtin_lsp_index_file(valk_lenv_t *e, valk_lval_t *a);

#include <dirent.h>
#include <errno.h>
#include <limits.h>
#include <poll.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

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
  valk_type_env_t *tenv = valk_type_env_global();
  if (valk_type_env_find_constructor(tenv, name)) return true;
  for (u64 i = 0; i < tenv->constructor_count; i++) {
    const char *full = tenv->constructors[i]->name;
    const char *sep = strstr(full, "::");
    if (sep && strcmp(sep + 2, name) == 0) return true;
  }
  if (valk_type_env_find_type(tenv, name)) return true;
  return false;
}

static char *read_file_text(const char *filename) {
  FILE *f = fopen(filename, "rb");
  if (!f) return nullptr;
  fseek(f, 0, SEEK_END);
  long flen = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (flen <= 0) { fclose(f); return nullptr; } // LCOV_EXCL_LINE // LCOV_EXCL_BR_LINE
  char *text = calloc(flen + 1, 1);
  fread(text, 1, flen, f);
  fclose(f);
  return text;
}

static valk_lval_t* valk_builtin_load(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char *filename = valk_lval_list_nth(a, 0)->str;
  valk_coverage_record_file(filename);

  char *text = read_file_text(filename);
  if (!text)
    return valk_lval_err("Could not open file (%s)", filename);

  // Stage 1: Parse
  valk_lval_t *ast = valk_parse_text(text);
  if (LVAL_TYPE(ast) == LVAL_ERR) { // LCOV_EXCL_BR_LINE - parse errors tested via parser tests
    valk_lval_println(ast); // LCOV_EXCL_LINE
    free(text); // LCOV_EXCL_LINE
    return ast; // LCOV_EXCL_LINE
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
    if (LVAL_TYPE(x) == LVAL_ERR) { // LCOV_EXCL_BR_LINE - type transform errors
      valk_lval_println(x); // LCOV_EXCL_LINE
      return x; // LCOV_EXCL_LINE
    }
    x = valk_lval_eval(e, x);
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
    } else {
      last = x;
    }
    // LCOV_EXCL_START - GC collection during load: non-deterministic timing
    valk_gc_heap_t* gc_heap =
        (valk_gc_heap_t*)valk_thread_ctx.allocator;
    if (gc_heap->type == VALK_ALLOC_GC_HEAP &&
        valk_gc_should_collect(gc_heap)) {
      valk_gc_heap_collect(gc_heap);
    }
    // LCOV_EXCL_STOP
  }
  if (last) {
    valk_lenv_put(e, valk_lval_sym("VALK_LAST_VALUE"), last);
  }

  return valk_lval_nil();
}

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

static valk_lval_t* valk_builtin_list_dir(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

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
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
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
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* path = valk_lval_list_nth(a, 0)->str;
  struct stat st;
  if (stat(path, &st) != 0)
    LVAL_RAISE(a, "file/size: cannot stat (%s)", path);
  return valk_lval_num((long)st.st_size);
}

static valk_lval_t *valk_builtin_sem_encode_deltas(valk_lenv_t *e,
                                                    valk_lval_t *a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char *text = valk_lval_list_nth(a, 0)->str;
  valk_lval_t *tokens = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, tokens, LVAL_CONS, LVAL_NIL); // LCOV_EXCL_BR_LINE

  int text_len = (int)strlen(text);
  int prev_line = 0, prev_col = 0, scan_pos = 0;
  valk_lval_t *result = valk_lval_nil();

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
        if (text[i] == '\n') { line++; col = 0; } // LCOV_EXCL_BR_LINE
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
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char *text = valk_lval_list_nth(a, 0)->str;
  valk_lval_t *offsets = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, offsets, LVAL_CONS, LVAL_NIL); // LCOV_EXCL_BR_LINE
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

static valk_lval_t* valk_builtin_write_file(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* path = valk_lval_list_nth(a, 0)->str;
  const char* content = valk_lval_list_nth(a, 1)->str;
  u64 len = strlen(content);

  FILE* f = fopen(path, "wb");
  if (!f)
    LVAL_RAISE(a, "write-file: could not open (%s): %s", path, strerror(errno));

  if (len > 0) {
    u64 written = fwrite(content, 1, len, f);
    if (written != len) { // LCOV_EXCL_START
      fclose(f);
      LVAL_RAISE(a, "write-file: partial write (%s)", path);
    } // LCOV_EXCL_STOP
  }
  fclose(f);
  return valk_lval_num((long)len);
}

static valk_lval_t* valk_builtin_file_exists(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  struct stat st;
  return valk_lval_num(stat(valk_lval_list_nth(a, 0)->str, &st) == 0 ? 1 : 0);
}

static valk_lval_t* valk_builtin_mkdir_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* path = valk_lval_list_nth(a, 0)->str;
  char tmp[4096];
  snprintf(tmp, sizeof(tmp), "%s", path);

  for (char* p = tmp + 1; *p; p++) {
    if (*p == '/') {
      *p = '\0';
      if (mkdir(tmp, 0755) != 0 && errno != EEXIST)
        LVAL_RAISE(a, "mkdir-p: failed at (%s): %s", tmp, strerror(errno));
      *p = '/';
    }
  }
  if (mkdir(tmp, 0755) != 0 && errno != EEXIST)
    LVAL_RAISE(a, "mkdir-p: failed (%s): %s", tmp, strerror(errno));

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_file_delete(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* path = valk_lval_list_nth(a, 0)->str;
  if (unlink(path) != 0)
    LVAL_RAISE(a, "file/delete: failed (%s): %s", path, strerror(errno));
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_rmdir(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* path = valk_lval_list_nth(a, 0)->str;
  if (rmdir(path) != 0)
    LVAL_RAISE(a, "rmdir: failed (%s): %s", path, strerror(errno));
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_symlink(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* target = valk_lval_list_nth(a, 0)->str;
  const char* link_path = valk_lval_list_nth(a, 1)->str;
  unlink(link_path);
  if (symlink(target, link_path) != 0)
    LVAL_RAISE(a, "symlink: failed (%s -> %s): %s", link_path, target, strerror(errno));
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_env_get(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* val = getenv(valk_lval_list_nth(a, 0)->str);
  if (!val) return valk_lval_nil();
  return valk_lval_str(val);
}

static valk_lval_t* valk_builtin_env_set(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  setenv(valk_lval_list_nth(a, 0)->str, valk_lval_list_nth(a, 1)->str, 1);
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_realpath(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  char resolved[PATH_MAX];
  if (!realpath(valk_lval_list_nth(a, 0)->str, resolved))
    LVAL_RAISE(a, "realpath: failed (%s): %s",
               valk_lval_list_nth(a, 0)->str, strerror(errno));
  return valk_lval_str(resolved);
}

static valk_lval_t* valk_builtin_exec(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_GE(a, a, 1);

  u64 nargs = valk_lval_list_count(a);
  for (u64 i = 0; i < nargs; i++) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, i), LVAL_STR);
  }
  // LCOV_EXCL_BR_STOP

  char** argv_exec = calloc(nargs + 1, sizeof(char*));
  for (u64 i = 0; i < nargs; i++) {
    argv_exec[i] = (char*)valk_lval_list_nth(a, i)->str;
  }
  argv_exec[nargs] = nullptr;

  int stdout_pipe[2], stderr_pipe[2];
  if (pipe(stdout_pipe) != 0 || pipe(stderr_pipe) != 0) { // LCOV_EXCL_START
    free(argv_exec);
    LVAL_RAISE(a, "exec: pipe() failed: %s", strerror(errno));
  } // LCOV_EXCL_STOP

  pid_t pid = fork();
  if (pid < 0) { // LCOV_EXCL_START
    free(argv_exec);
    close(stdout_pipe[0]); close(stdout_pipe[1]);
    close(stderr_pipe[0]); close(stderr_pipe[1]);
    LVAL_RAISE(a, "exec: fork() failed: %s", strerror(errno));
  } // LCOV_EXCL_STOP

  // LCOV_EXCL_START - runs in forked child process, unreachable by coverage instrumentation
  if (pid == 0) {
    close(stdout_pipe[0]);
    close(stderr_pipe[0]);
    dup2(stdout_pipe[1], STDOUT_FILENO);
    dup2(stderr_pipe[1], STDERR_FILENO);
    close(stdout_pipe[1]);
    close(stderr_pipe[1]);
    execvp(argv_exec[0], argv_exec);
    _exit(127);
  }
  // LCOV_EXCL_STOP

  free(argv_exec);
  close(stdout_pipe[1]);
  close(stderr_pipe[1]);

  size_t out_cap = 4096, out_len = 0;
  char* out_buf = malloc(out_cap);
  size_t err_cap = 4096, err_len = 0;
  char* err_buf = malloc(err_cap);

  struct pollfd fds[2] = {
    {.fd = stdout_pipe[0], .events = POLLIN},
    {.fd = stderr_pipe[0], .events = POLLIN},
  };
  // LCOV_EXCL_BR_START - poll/read loop: branch edges depend on pipe timing and buffer state
  int open_fds = 2;
  while (open_fds > 0) {
    int ret = poll(fds, 2, -1);
    if (ret < 0) {
      if (errno == EINTR) continue;
      break; // LCOV_EXCL_LINE
    }
    for (int fi = 0; fi < 2; fi++) {
      if (fds[fi].fd < 0) continue;
      if (!(fds[fi].revents & (POLLIN | POLLHUP))) continue;
      char **buf = fi == 0 ? &out_buf : &err_buf;
      size_t *len = fi == 0 ? &out_len : &err_len;
      size_t *cap = fi == 0 ? &out_cap : &err_cap;
      if (*len >= *cap) { *cap *= 2; *buf = realloc(*buf, *cap); }
      ssize_t n = read(fds[fi].fd, *buf + *len, *cap - *len);
      if (n > 0) {
        *len += n;
      } else if (n == 0 || (n < 0 && errno != EINTR)) {
        close(fds[fi].fd);
        fds[fi].fd = -1;
        open_fds--;
      }
    }
  }
  if (fds[0].fd >= 0) close(fds[0].fd);
  if (fds[1].fd >= 0) close(fds[1].fd);

  if (out_len >= out_cap) { out_cap = out_len + 1; out_buf = realloc(out_buf, out_cap); }
  out_buf[out_len] = '\0';
  if (err_len >= err_cap) { err_cap = err_len + 1; err_buf = realloc(err_buf, err_cap); }
  err_buf[err_len] = '\0';
  // LCOV_EXCL_BR_STOP

  int status = 0;
  waitpid(pid, &status, 0);

  valk_lval_t* out_str = valk_lval_str(out_buf);
  valk_lval_t* err_str = valk_lval_str(err_buf);
  free(out_buf);
  free(err_buf);

  // LCOV_EXCL_BR_START - process exit status: WIFEXITED/WIFSIGNALED macro branches
  long exit_code;
  if (WIFEXITED(status)) {
    exit_code = WEXITSTATUS(status);
  } else if (WIFSIGNALED(status)) {
    exit_code = -(long)WTERMSIG(status);
  } else {
    exit_code = -1; // LCOV_EXCL_LINE
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t* fields[6] = {
    valk_lval_sym(":exit-code"), valk_lval_num(exit_code),
    valk_lval_sym(":stdout"),    out_str,
    valk_lval_sym(":stderr"),    err_str,
  };
  return valk_lval_qlist(fields, 6);
}

// LCOV_EXCL_START - GC destructor: called non-deterministically during garbage collection
static void file_handle_free(void *ptr) {
  FILE *f = ptr;
  if (f) fclose(f);
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_file_open(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char *path = valk_lval_list_nth(a, 0)->str;
  const char *mode = valk_lval_list_nth(a, 1)->str;
  FILE *f = fopen(path, mode);
  if (f == nullptr) {
    LVAL_RAISE(a, "file/open: could not open '%s' with mode '%s'", path, mode);
  }
  return valk_lval_ref("file_handle", f, file_handle_free);
}

static valk_lval_t* valk_builtin_file_write_str(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  LVAL_ASSERT_COUNT_EQ(a, a, 2); // LCOV_EXCL_BR_LINE - arg validation
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  // LCOV_EXCL_BR_START - type validation: ref type + null check
  if (LVAL_TYPE(ref) != LVAL_REF || ref->ref.ptr == nullptr) {
    LVAL_RAISE(a, "file/write: first argument must be a file handle");
  }
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  FILE *f = ref->ref.ptr;
  const char *s = valk_lval_list_nth(a, 1)->str;
  u64 len = strlen(s);
  if (len > 0) {
    u64 written = fwrite(s, 1, len, f);
    if (written != len) // LCOV_EXCL_BR_LINE
      LVAL_RAISE(a, "file/write: partial write (%zu of %zu bytes)", written, len); // LCOV_EXCL_LINE
  }
  return valk_lval_num((long)len);
}

static valk_lval_t* valk_builtin_file_close(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ref) != LVAL_REF || ref->ref.ptr == nullptr) {
    LVAL_RAISE(a, "file/close: argument must be a file handle");
  }
  // LCOV_EXCL_BR_STOP
  FILE *f = ref->ref.ptr;
  ref->ref.ptr = nullptr;
  ref->ref.free = nullptr;
  fclose(f);
  return valk_lval_num(0);
}

static valk_lval_t* valk_builtin_for_each_line(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  valk_lval_t* fn = valk_lval_list_nth(a, 1);
  // LCOV_EXCL_BR_START - type validation
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    LVAL_RAISE(a, "for-each-line: second argument must be a function");
  }
  // LCOV_EXCL_BR_STOP
  VALK_GC_ROOT(fn);

  const char* filename = valk_lval_list_nth(a, 0)->str;
  FILE* f = fopen(filename, "r");
  if (f == nullptr) {
    LVAL_RAISE(a, "for-each-line: could not open file (%s)", filename);
  }

  char *buf = nullptr;
  size_t buf_cap = 0;
  ssize_t len;
  u64 lines_read = 0;

  while ((len = getline(&buf, &buf_cap, f)) != -1) {
    if (len > 0 && buf[len - 1] == '\n') buf[len - 1] = '\0';
    valk_lval_t *line_str = valk_lval_str(buf);
    valk_lval_t *call_args[] = {fn, line_str};
    valk_lval_t *call_expr = valk_lval_list(call_args, 2);
    valk_lval_t *result = valk_lval_eval(e, call_expr);
    if (LVAL_TYPE(result) == LVAL_ERR) { // LCOV_EXCL_BR_LINE - callback error propagation
      free(buf); // LCOV_EXCL_LINE
      fclose(f); // LCOV_EXCL_LINE
      return result; // LCOV_EXCL_LINE
    }
    lines_read++;
    VALK_GC_SAFE_POINT();
  }

  free(buf);
  fclose(f);
  return valk_lval_num((long)lines_read);
}

void valk_register_io_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "error", valk_builtin_error);
  valk_lenv_put_builtin(env, "error?", valk_builtin_error_p);
  valk_lenv_put_builtin(env, "list?", valk_builtin_list_p);
  valk_lenv_put_builtin(env, "ref?", valk_builtin_ref_p);
  valk_lenv_put_builtin(env, "load", valk_builtin_load);
  valk_lenv_put_builtin(env, "read", valk_builtin_read);
  valk_lenv_put_builtin(env, "parse", valk_builtin_parse);
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
  valk_lenv_put_builtin(env, "lsp/index-ast", valk_builtin_lsp_index_file);
  valk_lenv_put_builtin(env, "offsets->line-cols", valk_builtin_offsets_to_lines);
  valk_lenv_put_builtin(env, "write-file", valk_builtin_write_file);
  valk_lenv_put_builtin(env, "file/exists?", valk_builtin_file_exists);
  valk_lenv_put_builtin(env, "file/delete", valk_builtin_file_delete);
  valk_lenv_put_builtin(env, "mkdir-p", valk_builtin_mkdir_p);
  valk_lenv_put_builtin(env, "rmdir", valk_builtin_rmdir);
  valk_lenv_put_builtin(env, "symlink", valk_builtin_symlink);
  valk_lenv_put_builtin(env, "env/get", valk_builtin_env_get);
  valk_lenv_put_builtin(env, "env/set", valk_builtin_env_set);
  valk_lenv_put_builtin(env, "realpath", valk_builtin_realpath);
  valk_lenv_put_builtin(env, "exec", valk_builtin_exec);
  valk_lenv_put_builtin(env, "for-each-line", valk_builtin_for_each_line);
  valk_lenv_put_builtin(env, "file/open", valk_builtin_file_open);
  valk_lenv_put_builtin(env, "file/write", valk_builtin_file_write_str);
  valk_lenv_put_builtin(env, "file/close", valk_builtin_file_close);
}

