#include "lsp_doc.h"

#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// Document management
// ---------------------------------------------------------------------------

void doc_symbols_clear(lsp_document_t *doc) {
  for (size_t i = 0; i < doc->symbol_count; i++) {
    free(doc->symbols[i].name);
    free(doc->symbols[i].doc);
  }
  doc->symbol_count = 0;
}

void doc_diag_clear(lsp_document_t *doc) {
  for (size_t i = 0; i < doc->diag_count; i++)
    free(doc->diag_messages[i]);
  doc->diag_count = 0;
}

void doc_add_symbol(lsp_document_t *doc, const char *name, int line, int col,
                    int arity, int src_start, int src_end) {
  if (doc->symbol_count >= doc->symbol_cap) {
    doc->symbol_cap = doc->symbol_cap == 0 ? 16 : doc->symbol_cap * 2;
    doc->symbols = realloc(doc->symbols, sizeof(lsp_symbol_t) * doc->symbol_cap);
  }
  lsp_symbol_t *sym = &doc->symbols[doc->symbol_count++];
  sym->name = strdup(name);
  sym->pos = (lsp_pos_t){line, col};
  sym->arity = arity;
  sym->doc = nullptr;
  sym->src_start = src_start;
  sym->src_end = src_end;
}

void doc_add_diag_full(lsp_document_t *doc, const char *msg, int line, int col,
                       int len, int severity) {
  if (doc->diag_count == 0) {
    doc->diag_messages = malloc(sizeof(char *) * 16);
    doc->diag_positions = malloc(sizeof(lsp_pos_t) * 16);
    doc->diag_severities = malloc(sizeof(int) * 16);
    doc->diag_lengths = malloc(sizeof(int) * 16);
  } else if ((doc->diag_count & (doc->diag_count - 1)) == 0 && doc->diag_count >= 16) {
    doc->diag_messages = realloc(doc->diag_messages, sizeof(char *) * doc->diag_count * 2);
    doc->diag_positions = realloc(doc->diag_positions, sizeof(lsp_pos_t) * doc->diag_count * 2);
    doc->diag_severities = realloc(doc->diag_severities, sizeof(int) * doc->diag_count * 2);
    doc->diag_lengths = realloc(doc->diag_lengths, sizeof(int) * doc->diag_count * 2);
  }
  doc->diag_messages[doc->diag_count] = strdup(msg);
  doc->diag_positions[doc->diag_count] = (lsp_pos_t){line, col};
  doc->diag_severities[doc->diag_count] = severity;
  doc->diag_lengths[doc->diag_count] = len > 0 ? len : 1;
  doc->diag_count++;
}

void doc_add_diag(lsp_document_t *doc, const char *msg, int line, int col) {
  doc_add_diag_full(doc, msg, line, col, 1, 1);
}

void doc_sem_clear(lsp_document_t *doc) {
  doc->sem_token_count = 0;
}

void doc_add_sem(lsp_document_t *doc, int line, int col, int len, int type, int mods) {
  if (doc->sem_token_count >= doc->sem_token_cap) {
    doc->sem_token_cap = doc->sem_token_cap == 0 ? 256 : doc->sem_token_cap * 2;
    doc->sem_tokens = realloc(doc->sem_tokens, sizeof(lsp_sem_token_t) * doc->sem_token_cap);
  }
  doc->sem_tokens[doc->sem_token_count++] = (lsp_sem_token_t){line, col, len, type, mods};
}

void doc_free(lsp_document_t *doc) {
  doc_symbols_clear(doc);
  doc_diag_clear(doc);
  free(doc->uri);
  free(doc->text);
  free(doc->symbols);
  free(doc->diag_messages);
  free(doc->diag_positions);
  free(doc->diag_severities);
  free(doc->diag_lengths);
  free(doc->sem_tokens);
}

// ---------------------------------------------------------------------------
// Document store
// ---------------------------------------------------------------------------

lsp_document_t *doc_store_find(lsp_doc_store_t *store, const char *uri) {
  for (size_t i = 0; i < store->count; i++)
    if (strcmp(store->docs[i].uri, uri) == 0)
      return &store->docs[i];
  return nullptr;
}

lsp_document_t *doc_store_open(lsp_doc_store_t *store, const char *uri,
                                const char *text, int version) {
  lsp_document_t *existing = doc_store_find(store, uri);
  if (existing) {
    free(existing->text);
    existing->text = strdup(text);
    existing->text_len = strlen(text);
    existing->version = version;
    return existing;
  }

  if (store->count >= store->cap) {
    store->cap = store->cap == 0 ? 8 : store->cap * 2;
    store->docs = realloc(store->docs, sizeof(lsp_document_t) * store->cap);
  }

  lsp_document_t *doc = &store->docs[store->count++];
  memset(doc, 0, sizeof(*doc));
  doc->uri = strdup(uri);
  doc->text = strdup(text);
  doc->text_len = strlen(text);
  doc->version = version;
  return doc;
}

void doc_store_close(lsp_doc_store_t *store, const char *uri) {
  for (size_t i = 0; i < store->count; i++) {
    if (strcmp(store->docs[i].uri, uri) == 0) {
      doc_free(&store->docs[i]);
      store->docs[i] = store->docs[--store->count];
      return;
    }
  }
}

void doc_store_free(lsp_doc_store_t *store) {
  for (size_t i = 0; i < store->count; i++)
    doc_free(&store->docs[i]);
  free(store->docs);
  *store = (lsp_doc_store_t){0};
}

// ---------------------------------------------------------------------------
// Position helpers
// ---------------------------------------------------------------------------

lsp_pos_t offset_to_pos(const char *text, int offset) {
  int line = 0, col = 0;
  for (int i = 0; i < offset && text[i]; i++) {
    if (text[i] == '\n') { line++; col = 0; }
    else col++;
  }
  return (lsp_pos_t){line, col};
}

int pos_to_offset(const char *text, int line, int col) {
  int l = 0, c = 0;
  for (int i = 0; text[i]; i++) {
    if (l == line && c == col) return i;
    if (text[i] == '\n') { l++; c = 0; }
    else c++;
  }
  return -1;
}

// ---------------------------------------------------------------------------
// Symbol set
// ---------------------------------------------------------------------------

void symset_init(lsp_symset_t *s) {
  s->names = nullptr;
  s->count = 0;
  s->cap = 0;
}

void symset_free(lsp_symset_t *s) {
  for (size_t i = 0; i < s->count; i++)
    free(s->names[i]);
  free(s->names);
  s->names = nullptr;
  s->count = s->cap = 0;
}

bool symset_contains(lsp_symset_t *s, const char *name) {
  for (size_t i = 0; i < s->count; i++)
    if (strcmp(s->names[i], name) == 0) return true;
  return false;
}

void symset_add(lsp_symset_t *s, const char *name) {
  if (symset_contains(s, name)) return;
  if (s->count >= s->cap) {
    s->cap = s->cap == 0 ? 64 : s->cap * 2;
    s->names = realloc(s->names, sizeof(char *) * s->cap);
  }
  s->names[s->count++] = strdup(name);
}

// ---------------------------------------------------------------------------
// Scope
// ---------------------------------------------------------------------------

lsp_scope_t *scope_push(lsp_scope_t *parent) {
  lsp_scope_t *s = calloc(1, sizeof(lsp_scope_t));
  symset_init(&s->locals);
  s->parent = parent;
  return s;
}

void scope_pop(lsp_scope_t *s) {
  symset_free(&s->locals);
  free(s);
}

bool scope_has(lsp_scope_t *s, const char *name) {
  while (s) {
    if (symset_contains(&s->locals, name)) return true;
    s = s->parent;
  }
  return false;
}

// ---------------------------------------------------------------------------
// Text utilities
// ---------------------------------------------------------------------------

char *get_word_at(const char *text, int offset) {
  if (!text || offset < 0) return nullptr;
  int start = offset, end = offset;
  int len = (int)strlen(text);
  const char *chars = LSP_SYM_CHARS;

  while (start > 0 && strchr(chars, text[start - 1]))
    start--;
  while (end < len && strchr(chars, text[end]))
    end++;

  if (start == end) return nullptr;
  return strndup(text + start, end - start);
}

static bool in_comment_or_string(const char *text, int pos) {
  bool in_str = false;
  for (int i = 0; i < pos; i++) {
    if (text[i] == '"' && !in_str)
      in_str = true;
    else if (text[i] == '"' && in_str)
      in_str = false;
    else if (text[i] == '\\' && in_str)
      i++;
    else if (text[i] == ';' && !in_str) {
      while (i < pos && text[i] != '\n') i++;
      if (i >= pos) return true;
    }
  }
  return in_str;
}

int lsp_find_sym_offset(const char *text, const char *sym, int search_start) {
  int slen = (int)strlen(sym);
  int tlen = (int)strlen(text);
  const char *chars = LSP_SYM_CHARS;
  for (int i = search_start; i <= tlen - slen; i++) {
    if (memcmp(text + i, sym, slen) != 0) continue;
    if (i > 0 && strchr(chars, text[i - 1])) continue;
    if (i + slen < tlen && strchr(chars, text[i + slen])) continue;
    if (in_comment_or_string(text, i)) continue;
    return i;
  }
  return -1;
}
