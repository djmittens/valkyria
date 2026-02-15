#pragma once
#include <stddef.h>

typedef struct {
  int line;
  int col;
} lsp_pos_t;

typedef struct {
  char *name;
  lsp_pos_t pos;
  int arity;
  char *doc;
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

void doc_symbols_clear(lsp_document_t *doc);
void doc_diag_clear(lsp_document_t *doc);
void doc_add_symbol(lsp_document_t *doc, const char *name, int line, int col, int arity);
void doc_add_diag(lsp_document_t *doc, const char *msg, int line, int col);
void doc_add_diag_full(lsp_document_t *doc, const char *msg, int line, int col, int len, int severity);

lsp_pos_t offset_to_pos(const char *text, int offset);
int pos_to_offset(const char *text, int line, int col);

void analyze_document(lsp_document_t *doc);
void lsp_set_workspace_root(const char *root);

extern const char *BUILTIN_NAMES[];
