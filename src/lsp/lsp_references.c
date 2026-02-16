#include "lsp_doc.h"
#include "lsp_builtins_gen.h"
#include "lsp_io.h"
#include "lsp_json.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../parser.h"

typedef struct {
  char *uri;
  int line;
  int col;
  int len;
  bool is_definition;
} lsp_ref_loc_t;

typedef struct {
  lsp_ref_loc_t *locs;
  size_t count;
  size_t cap;
} lsp_ref_result_t;

static void ref_result_add(lsp_ref_result_t *r, const char *uri,
                           int line, int col, int len, bool is_def) {
  if (r->count >= r->cap) {
    r->cap = r->cap == 0 ? 32 : r->cap * 2;
    r->locs = realloc(r->locs, sizeof(lsp_ref_loc_t) * r->cap);
  }
  r->locs[r->count++] = (lsp_ref_loc_t){
    .uri = strdup(uri), .line = line, .col = col, .len = len, .is_definition = is_def,
  };
}

static void ref_result_free(lsp_ref_result_t *r) {
  for (size_t i = 0; i < r->count; i++)
    free(r->locs[i].uri);
  free(r->locs);
}

// ---------------------------------------------------------------------------
// Global references (text-based, cross-file)
// ---------------------------------------------------------------------------

static bool is_definition_pos(lsp_document_t *doc, const char *name,
                              int line, int col) {
  for (size_t i = 0; i < doc->symbol_count; i++) {
    if (strcmp(doc->symbols[i].name, name) != 0) continue;
    int off = lsp_find_sym_offset(doc->text, name, doc->symbols[i].src_start);
    if (off < 0) continue;
    lsp_pos_t p = offset_to_pos(doc->text, off);
    if (p.line == line && p.col == col) return true;
  }
  return false;
}

static void collect_refs_in_doc(lsp_document_t *doc, const char *name,
                                lsp_ref_result_t *result) {
  int slen = (int)strlen(name);
  int search = 0;
  for (;;) {
    int off = lsp_find_sym_offset(doc->text, name, search);
    if (off < 0) break;
    lsp_pos_t p = offset_to_pos(doc->text, off);
    bool is_def = is_definition_pos(doc, name, p.line, p.col);
    ref_result_add(result, doc->uri, p.line, p.col, slen, is_def);
    search = off + slen;
  }
}

static lsp_ref_result_t find_global_references(lsp_doc_store_t *store,
                                               const char *name) {
  lsp_ref_result_t result = {0};
  for (size_t d = 0; d < store->count; d++)
    collect_refs_in_doc(&store->docs[d], name, &result);
  return result;
}

// ---------------------------------------------------------------------------
// Scope-aware local reference collection (AST walk)
// ---------------------------------------------------------------------------

typedef struct ref_scope {
  int id;
  char **names;
  size_t name_count;
  size_t name_cap;
  struct ref_scope *parent;
} ref_scope_t;

static int g_scope_id = 0;

static ref_scope_t *ref_scope_push(ref_scope_t *parent) {
  ref_scope_t *s = calloc(1, sizeof(ref_scope_t));
  s->id = ++g_scope_id;
  s->parent = parent;
  return s;
}

static void ref_scope_pop(ref_scope_t *s) {
  for (size_t i = 0; i < s->name_count; i++)
    free(s->names[i]);
  free(s->names);
  free(s);
}

static void ref_scope_add(ref_scope_t *s, const char *name) {
  if (s->name_count >= s->name_cap) {
    s->name_cap = s->name_cap == 0 ? 8 : s->name_cap * 2;
    s->names = realloc(s->names, sizeof(char *) * s->name_cap);
  }
  s->names[s->name_count++] = strdup(name);
}

static bool ref_scope_has_local(ref_scope_t *s, const char *name) {
  for (size_t i = 0; i < s->name_count; i++)
    if (strcmp(s->names[i], name) == 0) return true;
  return false;
}

static int ref_scope_resolve(ref_scope_t *s, const char *name) {
  while (s) {
    if (ref_scope_has_local(s, name)) return s->id;
    s = s->parent;
  }
  return -1;
}

typedef struct {
  const char *text;
  const char *target;
  int target_len;
  int cursor;
  ref_scope_t *scope;
  int target_scope_id;
  int query_offset;
  bool found_target;

  int *ref_offsets;
  bool *ref_is_def;
  size_t ref_count;
  size_t ref_cap;
} ref_walk_ctx_t;

static void rw_add_ref(ref_walk_ctx_t *rw, int offset, bool is_def) {
  if (rw->ref_count >= rw->ref_cap) {
    rw->ref_cap = rw->ref_cap == 0 ? 32 : rw->ref_cap * 2;
    rw->ref_offsets = realloc(rw->ref_offsets, sizeof(int) * rw->ref_cap);
    rw->ref_is_def = realloc(rw->ref_is_def, sizeof(bool) * rw->ref_cap);
  }
  rw->ref_offsets[rw->ref_count] = offset;
  rw->ref_is_def[rw->ref_count] = is_def;
  rw->ref_count++;
}

static int rw_find_sym(ref_walk_ctx_t *rw, const char *sym) {
  int off = lsp_find_sym_offset(rw->text, sym, rw->cursor);
  if (off >= 0) rw->cursor = off + (int)strlen(sym);
  return off;
}

static void rw_check_sym(ref_walk_ctx_t *rw, const char *sym, bool is_def) {
  if (strcmp(sym, rw->target) != 0) {
    rw_find_sym(rw, sym);
    return;
  }
  int off = rw_find_sym(rw, sym);
  if (off < 0) return;

  int scope_id = ref_scope_resolve(rw->scope, sym);

  if (off == rw->query_offset) {
    rw->target_scope_id = scope_id;
    rw->found_target = true;
  }

  if (rw->target_scope_id >= 0 && scope_id == rw->target_scope_id)
    rw_add_ref(rw, off, is_def);
}

static void rw_walk_expr(ref_walk_ctx_t *rw, valk_lval_t *expr);

static void rw_walk_body(ref_walk_ctx_t *rw, valk_lval_t *rest) {
  while (rest && LVAL_TYPE(rest) == LVAL_CONS) {
    rw_walk_expr(rw, valk_lval_head(rest));
    rest = valk_lval_tail(rest);
  }
}

static void rw_walk_annotated_formals(ref_walk_ctx_t *rw, valk_lval_t *formals) {
  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *h = valk_lval_head(cur);

    if (h && LVAL_TYPE(h) == LVAL_SYM &&
        (strcmp(h->str, "::") == 0 || strcmp(h->str, "->") == 0)) {
      rw_find_sym(rw, h->str);
      cur = valk_lval_tail(cur);
      if (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        rw_find_sym(rw, "");
        cur = valk_lval_tail(cur);
      }
      continue;
    }

    if (h && LVAL_TYPE(h) == LVAL_SYM && h->str[0] != '&') {
      ref_scope_add(rw->scope, h->str);
      rw_check_sym(rw, h->str, true);
    } else if (h && LVAL_TYPE(h) == LVAL_SYM) {
      rw_find_sym(rw, h->str);
    }
    cur = valk_lval_tail(cur);
  }
}

static void rw_walk_lambda(ref_walk_ctx_t *rw, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *formals = valk_lval_head(rest);
  valk_lval_t *body_rest = valk_lval_tail(rest);

  ref_scope_t *inner = ref_scope_push(rw->scope);
  ref_scope_t *saved = rw->scope;
  rw->scope = inner;
  if (formals && LVAL_TYPE(formals) == LVAL_CONS)
    rw_walk_annotated_formals(rw, formals);
  rw_walk_body(rw, body_rest);
  rw->scope = saved;
  ref_scope_pop(inner);
}

static void rw_walk_fun(ref_walk_ctx_t *rw, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *name_formals = valk_lval_head(rest);
  valk_lval_t *body_rest = valk_lval_tail(rest);

  if (!name_formals || LVAL_TYPE(name_formals) != LVAL_CONS) return;

  valk_lval_t *fname = valk_lval_head(name_formals);
  if (fname && LVAL_TYPE(fname) == LVAL_SYM)
    rw_find_sym(rw, fname->str);

  ref_scope_t *inner = ref_scope_push(rw->scope);
  ref_scope_t *saved = rw->scope;
  rw->scope = inner;
  valk_lval_t *params = valk_lval_tail(name_formals);
  if (params && LVAL_TYPE(params) == LVAL_CONS)
    rw_walk_annotated_formals(rw, params);
  rw_walk_body(rw, body_rest);
  rw->scope = saved;
  ref_scope_pop(inner);
}

static void rw_walk_binding(ref_walk_ctx_t *rw, const char *form,
                            valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *binding = valk_lval_head(rest);
  valk_lval_t *val_rest = valk_lval_tail(rest);
  bool is_local = strcmp(form, "=") == 0;

  if (binding && LVAL_TYPE(binding) == LVAL_CONS) {
    valk_lval_t *cur = binding;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      valk_lval_t *s = valk_lval_head(cur);
      if (s && LVAL_TYPE(s) == LVAL_SYM) {
        if (is_local)
          ref_scope_add(rw->scope, s->str);
        rw_check_sym(rw, s->str, true);
      }
      cur = valk_lval_tail(cur);
    }
  } else if (binding && LVAL_TYPE(binding) == LVAL_SYM) {
    if (is_local)
      ref_scope_add(rw->scope, binding->str);
    rw_check_sym(rw, binding->str, true);
  }

  rw_walk_body(rw, val_rest);
}

static void rw_walk_match(ref_walk_ctx_t *rw, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  rw_walk_expr(rw, valk_lval_head(rest));

  valk_lval_t *clauses = valk_lval_tail(rest);
  while (clauses && LVAL_TYPE(clauses) == LVAL_CONS) {
    valk_lval_t *clause = valk_lval_head(clauses);
    if (!clause || LVAL_TYPE(clause) != LVAL_CONS) goto next;

    valk_lval_t *pattern = valk_lval_head(clause);
    valk_lval_t *body = valk_lval_tail(clause);

    ref_scope_t *inner = ref_scope_push(rw->scope);
    ref_scope_t *saved = rw->scope;
    rw->scope = inner;

    if (pattern && LVAL_TYPE(pattern) == LVAL_CONS) {
      valk_lval_t *pat_head = valk_lval_head(pattern);
      if (pat_head && LVAL_TYPE(pat_head) == LVAL_SYM)
        rw_find_sym(rw, pat_head->str);
      valk_lval_t *pat_args = valk_lval_tail(pattern);
      while (pat_args && LVAL_TYPE(pat_args) == LVAL_CONS) {
        valk_lval_t *pv = valk_lval_head(pat_args);
        if (pv && LVAL_TYPE(pv) == LVAL_SYM && pv->str[0] != ':') {
          ref_scope_add(inner, pv->str);
          rw_check_sym(rw, pv->str, true);
        } else if (pv && LVAL_TYPE(pv) == LVAL_SYM) {
          rw_find_sym(rw, pv->str);
        }
        pat_args = valk_lval_tail(pat_args);
      }
    } else if (pattern && LVAL_TYPE(pattern) == LVAL_SYM) {
      rw_find_sym(rw, pattern->str);
    }

    rw_walk_body(rw, body);
    rw->scope = saved;
    ref_scope_pop(inner);

  next:
    clauses = valk_lval_tail(clauses);
  }
}

static void rw_walk_expr(ref_walk_ctx_t *rw, valk_lval_t *expr) {
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    rw_check_sym(rw, expr->str, false);
    return;
  }

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = valk_lval_head(expr);
  valk_lval_t *rest = valk_lval_tail(expr);
  if (!head) return;

  if (LVAL_TYPE(head) != LVAL_SYM) {
    rw_walk_expr(rw, head);
    rw_walk_body(rw, rest);
    return;
  }

  const char *name = head->str;
  rw_check_sym(rw, name, false);

  if (strcmp(name, "\\") == 0)      { rw_walk_lambda(rw, rest); return; }
  if (strcmp(name, "fun") == 0)     { rw_walk_fun(rw, rest); return; }
  if (strcmp(name, "def") == 0)     { rw_walk_binding(rw, "def", rest); return; }
  if (strcmp(name, "=") == 0)       { rw_walk_binding(rw, "=", rest); return; }
  if (strcmp(name, "match") == 0)   { rw_walk_match(rw, rest); return; }

  rw_walk_body(rw, rest);
}

static lsp_ref_result_t find_local_references(lsp_document_t *doc,
                                              const char *name,
                                              int query_offset) {
  lsp_ref_result_t result = {0};

  g_scope_id = 0;
  ref_walk_ctx_t rw = {
    .text = doc->text,
    .target = name,
    .target_len = (int)strlen(name),
    .cursor = 0,
    .scope = ref_scope_push(nullptr),
    .target_scope_id = -1,
    .query_offset = query_offset,
    .found_target = false,
  };

  const char *text = doc->text;
  int pos = 0, len = (int)doc->text_len;

  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;
    if (text[pos] == ';') { while (pos < len && text[pos] != '\n') pos++; continue; }
    rw.cursor = pos;
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    rw_walk_expr(&rw, expr);
  }

  if (!rw.found_target || rw.target_scope_id < 0) {
    ref_scope_pop(rw.scope);
    free(rw.ref_offsets);
    free(rw.ref_is_def);
    return result;
  }

  for (size_t i = 0; i < rw.ref_count; i++) {
    lsp_pos_t p = offset_to_pos(doc->text, rw.ref_offsets[i]);
    ref_result_add(&result, doc->uri, p.line, p.col, rw.target_len,
                   rw.ref_is_def[i]);
  }

  ref_scope_pop(rw.scope);
  free(rw.ref_offsets);
  free(rw.ref_is_def);
  return result;
}

// ---------------------------------------------------------------------------
// Unified find_all_references: scope walk first, global fallback
// ---------------------------------------------------------------------------

static lsp_ref_result_t find_all_references(lsp_doc_store_t *store,
                                            lsp_document_t *origin_doc,
                                            const char *name,
                                            int query_offset) {
  lsp_ref_result_t local = find_local_references(origin_doc, name, query_offset);
  if (local.count > 0)
    return local;
  ref_result_free(&local);
  return find_global_references(store, name);
}

// ---------------------------------------------------------------------------
// textDocument/references
// ---------------------------------------------------------------------------

void handle_references(int id, void *params_raw, void *store_raw) {
  json_value_t *params = params_raw;
  lsp_doc_store_t *store = store_raw;

  json_value_t *td = json_get(params, "textDocument");
  json_value_t *pos = json_get(params, "position");
  if (!td || !pos) { lsp_send_response(id, "[]"); return; }

  const char *uri = json_get_string(td, "uri");
  int line = json_get_int(pos, "line");
  int col = json_get_int(pos, "character");

  lsp_document_t *doc = uri ? doc_store_find(store, uri) : nullptr;
  if (!doc) { lsp_send_response(id, "[]"); return; }

  int offset = pos_to_offset(doc->text, line, col);
  char *word = get_word_at(doc->text, offset);
  if (!word) { lsp_send_response(id, "[]"); return; }

  json_value_t *ctx = json_get(params, "context");
  bool include_decl = ctx ? json_get_bool(ctx, "includeDeclaration") : true;

  int sym_offset = lsp_find_sym_offset(doc->text, word, offset);
  if (sym_offset < 0) sym_offset = offset;

  lsp_ref_result_t refs = find_all_references(store, doc, word, sym_offset);

  size_t max_len = 64 + refs.count * 256;
  char *buf = malloc(max_len);
  char *p = buf;
  char *end = buf + max_len;
  *p++ = '[';

  bool first = true;
  for (size_t i = 0; i < refs.count && p < end - 256; i++) {
    if (!include_decl && refs.locs[i].is_definition) continue;
    if (!first) *p++ = ',';
    first = false;
    p += snprintf(p, end - p,
      "{\"uri\":\"%s\",\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
      "\"end\":{\"line\":%d,\"character\":%d}}}",
      refs.locs[i].uri, refs.locs[i].line, refs.locs[i].col,
      refs.locs[i].line, refs.locs[i].col + refs.locs[i].len);
  }

  *p++ = ']';
  *p = '\0';
  lsp_send_response(id, buf);

  free(buf);
  free(word);
  ref_result_free(&refs);
}

// ---------------------------------------------------------------------------
// workspace/symbol
// ---------------------------------------------------------------------------

void handle_workspace_symbol(int id, void *params_raw, void *store_raw) {
  json_value_t *params = params_raw;
  lsp_doc_store_t *store = store_raw;

  const char *query = json_get_string(params, "query");
  if (!query) query = "";
  int qlen = (int)strlen(query);

  size_t max_len = 64;
  size_t result_count = 0;

  for (size_t d = 0; d < store->count; d++) {
    lsp_document_t *doc = &store->docs[d];
    for (size_t s = 0; s < doc->symbol_count; s++) {
      if (qlen > 0 && !strstr(doc->symbols[s].name, query)) continue;
      max_len += 512;
      result_count++;
      if (result_count >= 200) break;
    }
    if (result_count >= 200) break;
  }

  char *buf = malloc(max_len);
  char *p = buf;
  char *end = buf + max_len;
  *p++ = '[';
  bool first = true;
  size_t emitted = 0;

  for (size_t d = 0; d < store->count && emitted < 200; d++) {
    lsp_document_t *doc = &store->docs[d];
    for (size_t s = 0; s < doc->symbol_count && emitted < 200; s++) {
      if (qlen > 0 && !strstr(doc->symbols[s].name, query)) continue;
      if (!first) *p++ = ',';
      first = false;
      char *escaped_name = json_escape_string(doc->symbols[s].name);
      char *escaped_uri = json_escape_string(doc->uri);
      int kind = doc->symbols[s].arity >= 0 ? 12 : 13;
      int name_len = (int)strlen(doc->symbols[s].name);
      p += snprintf(p, end - p,
        "{\"name\":%s,\"kind\":%d,"
        "\"location\":{\"uri\":%s,"
        "\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
        "\"end\":{\"line\":%d,\"character\":%d}}}}",
        escaped_name, kind, escaped_uri,
        doc->symbols[s].pos.line, doc->symbols[s].pos.col,
        doc->symbols[s].pos.line, doc->symbols[s].pos.col + name_len);
      free(escaped_name);
      free(escaped_uri);
      emitted++;
    }
  }

  *p++ = ']';
  *p = '\0';
  lsp_send_response(id, buf);
  free(buf);
}

// ---------------------------------------------------------------------------
// textDocument/prepareRename
// ---------------------------------------------------------------------------

static bool is_builtin_name(const char *name) {
  for (int i = 0; LSP_BUILTINS[i].name; i++)
    if (strcmp(LSP_BUILTINS[i].name, name) == 0) return true;
  return false;
}

void handle_prepare_rename(int id, void *params_raw, void *store_raw) {
  json_value_t *params = params_raw;
  lsp_doc_store_t *store = store_raw;

  json_value_t *td = json_get(params, "textDocument");
  json_value_t *pos = json_get(params, "position");
  if (!td || !pos) { lsp_send_response(id, "null"); return; }

  const char *uri = json_get_string(td, "uri");
  int line = json_get_int(pos, "line");
  int col = json_get_int(pos, "character");

  lsp_document_t *doc = uri ? doc_store_find(store, uri) : nullptr;
  if (!doc) { lsp_send_response(id, "null"); return; }

  int offset = pos_to_offset(doc->text, line, col);
  char *word = get_word_at(doc->text, offset);
  if (!word) { lsp_send_response(id, "null"); return; }

  if (is_builtin_name(word)) {
    free(word);
    lsp_send_error(id, -32602, "Cannot rename a builtin");
    return;
  }

  int wlen = (int)strlen(word);
  char buf[512];
  snprintf(buf, sizeof(buf),
    "{\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
    "\"end\":{\"line\":%d,\"character\":%d}},\"placeholder\":\"%s\"}",
    line, col, line, col + wlen, word);
  free(word);
  lsp_send_response(id, buf);
}

// ---------------------------------------------------------------------------
// textDocument/rename
// ---------------------------------------------------------------------------

void handle_rename(int id, void *params_raw, void *store_raw) {
  json_value_t *params = params_raw;
  lsp_doc_store_t *store = store_raw;

  json_value_t *td = json_get(params, "textDocument");
  json_value_t *pos = json_get(params, "position");
  if (!td || !pos) { lsp_send_response(id, "null"); return; }

  const char *uri = json_get_string(td, "uri");
  int line = json_get_int(pos, "line");
  int col = json_get_int(pos, "character");
  const char *new_name = json_get_string(params, "newName");

  lsp_document_t *doc = uri ? doc_store_find(store, uri) : nullptr;
  if (!doc || !new_name) { lsp_send_response(id, "null"); return; }

  int offset = pos_to_offset(doc->text, line, col);
  char *word = get_word_at(doc->text, offset);
  if (!word) { lsp_send_response(id, "null"); return; }

  if (is_builtin_name(word)) {
    free(word);
    lsp_send_error(id, -32602, "Cannot rename a builtin");
    return;
  }

  int sym_offset = lsp_find_sym_offset(doc->text, word, offset);
  if (sym_offset < 0) sym_offset = offset;

  lsp_ref_result_t refs = find_all_references(store, doc, word, sym_offset);
  free(word);

  if (refs.count == 0) {
    lsp_send_response(id, "null");
    ref_result_free(&refs);
    return;
  }

  char *escaped_new = json_escape_string(new_name);

  size_t max_len = 128 + refs.count * 512;
  char *buf = malloc(max_len);
  char *p = buf;
  char *end = buf + max_len;

  p += snprintf(p, end - p, "{\"changes\":{");

  const char *cur_uri = nullptr;
  bool first_uri = true;
  bool first_edit = true;

  for (size_t i = 0; i < refs.count && p < end - 512; i++) {
    if (!cur_uri || strcmp(cur_uri, refs.locs[i].uri) != 0) {
      if (cur_uri) {
        *p++ = ']';
      }
      if (!first_uri) *p++ = ',';
      first_uri = false;

      char *escaped_uri = json_escape_string(refs.locs[i].uri);
      p += snprintf(p, end - p, "%s:[", escaped_uri);
      free(escaped_uri);

      cur_uri = refs.locs[i].uri;
      first_edit = true;
    }

    if (!first_edit) *p++ = ',';
    first_edit = false;

    p += snprintf(p, end - p,
      "{\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
      "\"end\":{\"line\":%d,\"character\":%d}},\"newText\":%s}",
      refs.locs[i].line, refs.locs[i].col,
      refs.locs[i].line, refs.locs[i].col + refs.locs[i].len,
      escaped_new);
  }

  if (cur_uri) *p++ = ']';
  p += snprintf(p, end - p, "}}");

  lsp_send_response(id, buf);
  free(buf);
  free(escaped_new);
  ref_result_free(&refs);
}
