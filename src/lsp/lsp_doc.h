#pragma once
#include <stdbool.h>
#include <stddef.h>

#define LSP_SYM_CHARS ("abcdefghijklmnopqrstuvwxyz" \
                       "ABCDEFGHIJKLMNOPQRSTUVWXYZ" \
                       "0123456789_+-*/\\=<>!&?:/")

typedef struct {
  int line;
  int col;
} lsp_pos_t;

typedef struct {
  char *name;
  lsp_pos_t pos;
  int arity;
  char *doc;
  int src_start;
  int src_end;
} lsp_symbol_t;

enum {
  SEM_KEYWORD,
  SEM_FUNCTION,
  SEM_VARIABLE,
  SEM_PARAMETER,
  SEM_STRING,
  SEM_NUMBER,
  SEM_OPERATOR,
  SEM_COMMENT,
  SEM_TYPE,
  SEM_MACRO,
  SEM_PROPERTY,
  SEM_ENUM_MEMBER,
  SEM_TYPE_PARAM,
  SEM__COUNT,
};

enum {
  SEM_MOD_DEFINITION    = 1 << 0,
  SEM_MOD_READONLY      = 1 << 1,
  SEM_MOD_DEFAULT_LIB   = 1 << 2,
  SEM_MOD_DECLARATION   = 1 << 3,
};

typedef struct {
  int line;
  int col;
  int length;
  int type;
  int modifiers;
} lsp_sem_token_t;

typedef struct {
  char *uri;
  char *text;
  size_t text_len;
  int version;

  lsp_symbol_t *symbols;
  size_t symbol_count;
  size_t symbol_cap;

  char **diag_messages;
  lsp_pos_t *diag_positions;
  int *diag_severities;
  int *diag_lengths;
  size_t diag_count;

  lsp_sem_token_t *sem_tokens;
  size_t sem_token_count;
  size_t sem_token_cap;
} lsp_document_t;

typedef struct {
  lsp_document_t *docs;
  size_t count;
  size_t cap;
} lsp_doc_store_t;

typedef struct {
  char **names;
  size_t count;
  size_t cap;
} lsp_symset_t;

typedef struct lsp_scope {
  lsp_symset_t locals;
  struct lsp_scope *parent;
} lsp_scope_t;

// Document management
void doc_symbols_clear(lsp_document_t *doc);
void doc_diag_clear(lsp_document_t *doc);
void doc_add_symbol(lsp_document_t *doc, const char *name, int line, int col,
                    int arity, int src_start, int src_end);
void doc_add_diag(lsp_document_t *doc, const char *msg, int line, int col);
void doc_add_diag_full(lsp_document_t *doc, const char *msg, int line, int col,
                       int len, int severity);
void doc_sem_clear(lsp_document_t *doc);
void doc_add_sem(lsp_document_t *doc, int line, int col, int len, int type, int mods);
void doc_free(lsp_document_t *doc);

// Document store
lsp_document_t *doc_store_find(lsp_doc_store_t *store, const char *uri);
lsp_document_t *doc_store_open(lsp_doc_store_t *store, const char *uri,
                                const char *text, int version);
void doc_store_close(lsp_doc_store_t *store, const char *uri);
void doc_store_free(lsp_doc_store_t *store);

// Position helpers
lsp_pos_t offset_to_pos(const char *text, int offset);
int pos_to_offset(const char *text, int line, int col);

// Symbol set
void symset_init(lsp_symset_t *s);
void symset_free(lsp_symset_t *s);
bool symset_contains(lsp_symset_t *s, const char *name);
void symset_add(lsp_symset_t *s, const char *name);

// Scope
lsp_scope_t *scope_push(lsp_scope_t *parent);
void scope_pop(lsp_scope_t *s);
bool scope_has(lsp_scope_t *s, const char *name);

// Text utilities
char *get_word_at(const char *text, int offset);
int lsp_find_sym_offset(const char *text, const char *sym, int search_start);

// Analysis entry points
void analyze_document(lsp_document_t *doc);
void lsp_set_workspace_root(const char *root);
char *lsp_type_at_pos(lsp_document_t *doc, int offset);
