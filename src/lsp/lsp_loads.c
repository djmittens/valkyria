#include "lsp_doc.h"
#include "lsp_builtins_gen.h"
#include "lsp_types.h"

#include <libgen.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../parser.h"

void lsp_set_workspace_root(const char *root) {
  lsp_workspace_set_root(root);
}

void uri_to_path(const char *uri, char *path, size_t path_size) {
  if (strncmp(uri, "file://", 7) == 0)
    snprintf(path, path_size, "%s", uri + 7);
  else
    snprintf(path, path_size, "%s", uri);
}

// ---------------------------------------------------------------------------
// Load file contents helper
// ---------------------------------------------------------------------------

static char *read_load_file(const char *path, const char *base_dir,
                            char *real_out) {
  char resolved[PATH_MAX];
  bool found = false;

  if (path[0] == '/') {
    snprintf(resolved, sizeof(resolved), "%s", path);
    found = realpath(resolved, real_out) != nullptr;
  } else {
    snprintf(resolved, sizeof(resolved), "%s/%s", base_dir, path);
    found = realpath(resolved, real_out) != nullptr;
    const char *ws_root = lsp_workspace_root();
    if (!found && ws_root) {
      snprintf(resolved, sizeof(resolved), "%s/%s", ws_root, path);
      found = realpath(resolved, real_out) != nullptr;
    }
  }
  if (!found) return nullptr;

  FILE *f = fopen(real_out, "rb");
  if (!f) return nullptr;
  fseek(f, 0, SEEK_END);
  long flen = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (flen <= 0 || flen > 10 * 1024 * 1024) { fclose(f); return nullptr; }
  char *contents = calloc(flen + 1, 1);
  fread(contents, 1, flen, f);
  fclose(f);
  return contents;
}

// ---------------------------------------------------------------------------
// Parse load directives from text
// ---------------------------------------------------------------------------

void lsp_for_each_load(const char *text, const char *base_dir,
                       lsp_symset_t *visited, lsp_load_callback_fn cb, void *ctx) {
  int pos = 0, len = (int)strlen(text);
  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;
    if (text[pos] == ';') { while (pos < len && text[pos] != '\n') pos++; continue; }
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    if (LVAL_TYPE(expr) != LVAL_CONS) continue;

    valk_lval_t *head = valk_lval_head(expr);
    if (!head || LVAL_TYPE(head) != LVAL_SYM || strcmp(head->str, "load") != 0)
      continue;
    valk_lval_t *tail = valk_lval_tail(expr);
    if (LVAL_TYPE(tail) != LVAL_CONS) continue;
    valk_lval_t *arg = valk_lval_head(tail);
    if (!arg || LVAL_TYPE(arg) != LVAL_STR) continue;

    char real[PATH_MAX];
    char *contents = read_load_file(arg->str, base_dir, real);
    if (!contents) continue;
    if (symset_contains(visited, real)) { free(contents); continue; }
    symset_add(visited, real);

    char *dir_copy = strdup(real);
    char *dir = dirname(dir_copy);
    lsp_for_each_load(contents, dir, visited, cb, ctx);
    free(dir_copy);

    cb(contents, real, ctx);
    free(contents);
  }
}

// ---------------------------------------------------------------------------
// Symbol name extraction from loaded files
// ---------------------------------------------------------------------------

static void extract_def_or_fun(valk_lval_t *head, valk_lval_t *tail,
                               lsp_symset_t *globals) {
  if (strcmp(head->str, "def") != 0 && strcmp(head->str, "fun") != 0) return;
  if (LVAL_TYPE(tail) != LVAL_CONS) return;
  valk_lval_t *binding = valk_lval_head(tail);
  if (!binding) return;

  if (LVAL_TYPE(binding) == LVAL_CONS) {
    valk_lval_t *first = valk_lval_head(binding);
    if (first && LVAL_TYPE(first) == LVAL_SYM)
      symset_add(globals, first->str);
  } else if (LVAL_TYPE(binding) == LVAL_SYM) {
    symset_add(globals, binding->str);
  }
}

static void extract_type_ctors(valk_lval_t *tail, lsp_symset_t *globals) {
  const char *type_name = NULL;
  if (LVAL_TYPE(tail) == LVAL_CONS) {
    valk_lval_t *name_q = valk_lval_head(tail);
    if (name_q && LVAL_TYPE(name_q) == LVAL_CONS) {
      valk_lval_t *tn = valk_lval_head(name_q);
      if (tn && LVAL_TYPE(tn) == LVAL_SYM) type_name = tn->str;
    }
    tail = valk_lval_tail(tail);
  }
  while (tail && LVAL_TYPE(tail) == LVAL_CONS) {
    valk_lval_t *variant = valk_lval_head(tail);
    if (variant && LVAL_TYPE(variant) == LVAL_CONS) {
      valk_lval_t *ctor_name = valk_lval_head(variant);
      if (ctor_name && LVAL_TYPE(ctor_name) == LVAL_SYM) {
        symset_add(globals, ctor_name->str);
        if (type_name && ctor_name->str[0] != ':') {
          char qname[256];
          snprintf(qname, sizeof(qname), "%s::%s", type_name, ctor_name->str);
          symset_add(globals, qname);
        }
      }
    }
    tail = valk_lval_tail(tail);
  }
}

static void extract_global_symbols_from_text(const char *text,
                                             lsp_symset_t *globals) {
  int pos = 0, len = (int)strlen(text);
  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;
    if (text[pos] == ';') { while (pos < len && text[pos] != '\n') pos++; continue; }
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    if (LVAL_TYPE(expr) != LVAL_CONS) continue;

    valk_lval_t *head = valk_lval_head(expr);
    if (!head || LVAL_TYPE(head) != LVAL_SYM) continue;
    valk_lval_t *tail = valk_lval_tail(expr);

    extract_def_or_fun(head, tail, globals);
    if (strcmp(head->str, "type") == 0)
      extract_type_ctors(tail, globals);
  }
}

// Callback: extract symbol names
static void load_symbols_cb(const char *contents, const char *real_path,
                            void *ctx) {
  (void)real_path;
  extract_global_symbols_from_text(contents, ctx);
}

// ---------------------------------------------------------------------------
// Load builtins.valk for LSP (not loaded at runtime)
// ---------------------------------------------------------------------------

static void lsp_load_builtins_valk(lsp_symset_t *visited,
                                   lsp_load_callback_fn cb, void *ctx) {
  const char *ws_root = lsp_workspace_root();
  if (!ws_root) return;

  char path[PATH_MAX];
  snprintf(path, sizeof(path), "%s/src/builtins.valk", ws_root);

  char real[PATH_MAX];
  if (!realpath(path, real)) return;
  if (symset_contains(visited, real)) return;

  FILE *f = fopen(real, "rb");
  if (!f) return;
  fseek(f, 0, SEEK_END);
  long flen = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (flen <= 0 || flen > 10 * 1024 * 1024) { fclose(f); return; }
  char *contents = calloc(flen + 1, 1);
  fread(contents, 1, flen, f);
  fclose(f);

  symset_add(visited, real);
  cb(contents, real, ctx);
  free(contents);
}

void build_global_symset(lsp_document_t *doc, lsp_symset_t *globals) {
  symset_init(globals);

  for (int i = 0; LSP_BUILTINS[i].name; i++)
    symset_add(globals, LSP_BUILTINS[i].name);
  for (size_t i = 0; i < doc->symbol_count; i++)
    symset_add(globals, doc->symbols[i].name);

  char file_path[PATH_MAX];
  uri_to_path(doc->uri, file_path, sizeof(file_path));
  char *dir_copy = strdup(file_path);
  char *dir = dirname(dir_copy);

  lsp_symset_t visited;
  symset_init(&visited);
  char real[PATH_MAX];
  if (realpath(file_path, real))
    symset_add(&visited, real);

  lsp_load_builtins_valk(&visited, load_symbols_cb, globals);
  lsp_for_each_load(doc->text, dir, &visited, load_symbols_cb, globals);
  symset_free(&visited);
  free(dir_copy);
}

// ---------------------------------------------------------------------------
// Type inference from loaded files
// ---------------------------------------------------------------------------

static void infer_text_into_scope(type_arena_t *arena, typed_scope_t *scope,
                                  const char *text,
                                  plist_type_reg_t *plist_types,
                                  int *plist_type_count) {
  int pos = 0, len = (int)strlen(text), cursor = 0;
  infer_ctx_t ctx = {
    .arena = arena, .scope = scope,
    .doc = nullptr, .text = text, .cursor = &cursor,
    .floor_var_id = arena->next_var_id,
    .hover_offset = -1, .hover_result = nullptr,
  };
  if (plist_types && plist_type_count) {
    memcpy(ctx.plist_types, plist_types,
           *plist_type_count * sizeof(plist_type_reg_t));
    ctx.plist_type_count = *plist_type_count;
  }
  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;
    if (text[pos] == ';') { while (pos < len && text[pos] != '\n') pos++; continue; }
    cursor = pos;
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    infer_expr(&ctx, expr);
  }
  if (plist_types && plist_type_count) {
    memcpy(plist_types, ctx.plist_types,
           ctx.plist_type_count * sizeof(plist_type_reg_t));
    *plist_type_count = ctx.plist_type_count;
  }
}

typedef struct {
  type_arena_t *arena;
  typed_scope_t *scope;
  plist_type_reg_t *plist_types;
  int *plist_type_count;
} load_types_ctx_t;

static void load_types_cb(const char *contents, const char *real_path,
                          void *ctx) {
  (void)real_path;
  load_types_ctx_t *lt = ctx;
  infer_text_into_scope(lt->arena, lt->scope, contents,
                        lt->plist_types, lt->plist_type_count);
}

void init_typed_scope_with_loads(type_arena_t *arena, typed_scope_t *scope,
                                 lsp_document_t *doc) {
  lsp_builtin_schemes_init(arena, scope);

  char file_path[PATH_MAX];
  uri_to_path(doc->uri, file_path, sizeof(file_path));
  char *dir_copy = strdup(file_path);
  char *dir = dirname(dir_copy);

  lsp_symset_t visited;
  symset_init(&visited);
  char real[PATH_MAX];
  if (realpath(file_path, real))
    symset_add(&visited, real);

  plist_type_reg_t plist_regs[MAX_PLIST_TYPES];
  int plist_count = 0;
  load_types_ctx_t lt = {.arena = arena, .scope = scope,
                         .plist_types = plist_regs, .plist_type_count = &plist_count};
  lsp_load_builtins_valk(&visited, load_types_cb, &lt);
  lsp_for_each_load(doc->text, dir, &visited, load_types_cb, &lt);
  symset_free(&visited);
  free(dir_copy);
}

void init_typed_scope_with_plist_reg(type_arena_t *arena, typed_scope_t *scope,
                                    lsp_document_t *doc,
                                    plist_type_reg_t *out_regs, int *out_count) {
  lsp_builtin_schemes_init(arena, scope);

  char file_path[PATH_MAX];
  uri_to_path(doc->uri, file_path, sizeof(file_path));
  char *dir_copy = strdup(file_path);
  char *dir = dirname(dir_copy);

  lsp_symset_t visited;
  symset_init(&visited);
  char real[PATH_MAX];
  if (realpath(file_path, real))
    symset_add(&visited, real);

  plist_type_reg_t plist_regs[MAX_PLIST_TYPES];
  int plist_count = 0;
  load_types_ctx_t lt = {.arena = arena, .scope = scope,
                         .plist_types = plist_regs, .plist_type_count = &plist_count};
  lsp_load_builtins_valk(&visited, load_types_cb, &lt);
  lsp_for_each_load(doc->text, dir, &visited, load_types_cb, &lt);
  symset_free(&visited);
  free(dir_copy);

  if (out_regs && out_count) {
    memcpy(out_regs, plist_regs, plist_count * sizeof(plist_type_reg_t));
    *out_count = plist_count;
  }
}
