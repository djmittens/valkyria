#include "lsp_db.h"
#include "lsp_doc.h"
#include "lsp_types.h"

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>

#include "../parser.h"

static valk_symdb_t *g_symdb = NULL;

// Forward declarations
static void collect_refs_recursive(valk_symdb_t *db, symdb_file_id file_id,
                                   lsp_document_t *doc, valk_lval_t *expr,
                                   const char *text);

// ---------------------------------------------------------------------------
// Lifecycle — called from lsp.c
// ---------------------------------------------------------------------------

void lsp_db_init(const char *workspace_root) {
  if (!workspace_root || !workspace_root[0]) return;

  char dir_path[PATH_MAX];
  snprintf(dir_path, sizeof(dir_path), "%s/.valk", workspace_root);

  struct stat st;
  if (stat(dir_path, &st) != 0) {
    if (mkdir(dir_path, 0755) != 0) {
      fprintf(stderr, "[valk-lsp] cannot create %s\n", dir_path);
      return;
    }
  }

  char db_path[PATH_MAX];
  snprintf(db_path, sizeof(db_path), "%s/symdb.sqlite", dir_path);

  g_symdb = valk_symdb_open(db_path);
  if (g_symdb)
    fprintf(stderr, "[valk-lsp] symdb: %s\n", db_path);
}

void lsp_db_shutdown(void) {
  if (g_symdb) {
    valk_symdb_close(g_symdb);
    g_symdb = NULL;
  }
}

valk_symdb_t *lsp_db_get(void) { return g_symdb; }

// ---------------------------------------------------------------------------
// Sync a document's analysis results to the symdb
//
// Runs after analyze_document(). Re-infers the document to get types,
// then persists symbols + types. References are collected by walking
// the AST and matching symbol names to definitions.
// ---------------------------------------------------------------------------

void lsp_db_sync_document(lsp_document_t *doc) {
  if (!g_symdb) return;
  if (!doc || !doc->text || !doc->uri) return;

  char file_path[PATH_MAX];
  if (strncmp(doc->uri, "file://", 7) == 0)
    snprintf(file_path, sizeof(file_path), "%s", doc->uri + 7);
  else
    snprintf(file_path, sizeof(file_path), "%s", doc->uri);

  char content_hash[32];
  valk_symdb_content_hash(doc->text, doc->text_len,
                          content_hash, sizeof(content_hash));

  if (!valk_symdb_file_stale(g_symdb, file_path, 0,
                             (int64_t)doc->text_len, content_hash))
    return;

  valk_symdb_begin(g_symdb);

  symdb_file_id file_id = valk_symdb_upsert_file(
    g_symdb, file_path, 0, (int64_t)doc->text_len, content_hash);
  if (file_id < 0) {
    valk_symdb_rollback(g_symdb);
    return;
  }

  valk_symdb_invalidate_file(g_symdb, file_id);

  type_arena_t arena;
  type_arena_init(&arena);

  typed_scope_t *top = typed_scope_push(&arena, NULL);
  plist_type_reg_t plist_regs_db[MAX_PLIST_TYPES];
  int plist_count_db = 0;
  init_typed_scope_with_plist_reg(&arena, top, doc, plist_regs_db, &plist_count_db);

  const char *text = doc->text;
  int pos = 0;
  int len = (int)doc->text_len;
  int cursor = 0;

  infer_ctx_t ctx = {
    .arena = &arena,
    .scope = top,
    .doc = doc,
    .text = text,
    .cursor = &cursor,
    .floor_var_id = arena.next_var_id,
    .hover_offset = -1,
    .hover_result = NULL,
    .collect_hints = true,
  };

  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;
    if (text[pos] == ';') {
      while (pos < len && text[pos] != '\n') pos++;
      continue;
    }
    cursor = pos;
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    infer_expr(&ctx, expr);
  }

  for (size_t i = 0; i < doc->symbol_count; i++) {
    lsp_symbol_t *sym = &doc->symbols[i];

    symdb_sym_kind_e kind = SYMKIND_VARIABLE;
    if (sym->arity >= 0) kind = SYMKIND_FUNCTION;
    if (sym->doc && strstr(sym->doc, "constructor")) kind = SYMKIND_CONSTRUCTOR;
    if (sym->doc && strstr(sym->doc, "(type ")) kind = SYMKIND_TYPE;

    symdb_type_id type_id = -1;
    type_scheme_t *scheme = typed_scope_lookup(top, sym->name);
    if (scheme) {
      valk_type_t *ty = scheme_instantiate(&arena, scheme);
      ty = ty_resolve(ty);
      if (ty && ty->kind != TY_VAR && ty->kind != TY_ANY)
        type_id = valk_symdb_intern_type(g_symdb, ty);
    }

    int end_line = sym->pos.line;
    int end_col = sym->pos.col + (int)strlen(sym->name);

    valk_symdb_add_symbol(g_symdb, sym->name, file_id,
                          sym->pos.line, sym->pos.col,
                          end_line, end_col,
                          kind, type_id, -1, true);
  }

  for (size_t i = 0; i < ctx.hint_count; i++) {
    valk_type_t *ty = ty_resolve(ctx.hints[i].type);
    if (!ty || ty->kind == TY_VAR || ty->kind == TY_ANY) continue;
    valk_symdb_intern_type(g_symdb, ty);
  }

  pos = 0;
  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;
    if (text[pos] == ';') {
      while (pos < len && text[pos] != '\n') pos++;
      continue;
    }
    cursor = pos;
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    collect_refs_recursive(g_symdb, file_id, doc, expr, text);
  }

  free(ctx.hints);
  typed_scope_pop(top);
  type_arena_free(&arena);

  valk_symdb_commit(g_symdb);
}

// ---------------------------------------------------------------------------
// Reference collector — walks AST and records symbol uses
// ---------------------------------------------------------------------------

static void collect_refs_recursive(valk_symdb_t *db, symdb_file_id file_id,
                                   lsp_document_t *doc, valk_lval_t *expr,
                                   const char *text) {
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM && expr->str) {
    const char *name = expr->str;
    if (name[0] == ':') return;
    if (strcmp(name, "true") == 0 || strcmp(name, "false") == 0 ||
        strcmp(name, "nil") == 0 || strcmp(name, "otherwise") == 0)
      return;

    symdb_sym_id sym_id = valk_symdb_find_symbol(db, name, file_id);
    if (sym_id < 0)
      sym_id = valk_symdb_find_symbol_any(db, name);
    if (sym_id >= 0) {
      int src = expr->src_pos;
      if (src >= 0) {
        lsp_pos_t p = offset_to_pos(text, src);
        valk_symdb_add_ref(db, sym_id, file_id, p.line, p.col, REF_CALL);
      }
    }
    return;
  }

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = valk_lval_head(expr);
  valk_lval_t *tail = valk_lval_tail(expr);

  if (head && LVAL_TYPE(head) == LVAL_SYM && head->str) {
    const char *form = head->str;
    if (strcmp(form, "def") == 0 || strcmp(form, "fun") == 0 ||
        strcmp(form, "\\") == 0 || strcmp(form, "type") == 0) {
      if (tail && LVAL_TYPE(tail) == LVAL_CONS) {
        valk_lval_t *body = valk_lval_tail(tail);
        while (body && LVAL_TYPE(body) == LVAL_CONS) {
          collect_refs_recursive(db, file_id, doc,
                                valk_lval_head(body), text);
          body = valk_lval_tail(body);
        }
      }
      return;
    }
  }

  collect_refs_recursive(db, file_id, doc, head, text);
  while (tail && LVAL_TYPE(tail) == LVAL_CONS) {
    collect_refs_recursive(db, file_id, doc, valk_lval_head(tail), text);
    tail = valk_lval_tail(tail);
  }
}
