#pragma once

#include "builtins_internal.h"

#include "../vendor/sqlite3/sqlite3.h"

// Internal indexer primitives shared between lsp_index.c (AST walker) and
// lsp_index_emit.c (context, qualification, scopes, sqlite emission).

// Token types (must match SEM_* in lsp-analysis.valk)
enum {
  TOK_KEYWORD = 0, TOK_FUNCTION = 1, TOK_PARAMETER = 2, TOK_VARIABLE = 3,
  TOK_NUMBER = 4, TOK_STRING = 5, TOK_TYPE = 6, TOK_OPERATOR = 7,
  TOK_PROPERTY = 8,
};

enum { SYMKIND_FUNCTION = 1, SYMKIND_VARIABLE = 2, SYMKIND_TYPE = 3,
       SYMKIND_CONSTRUCTOR = 4 };

// Max scope depth for lexical chain
#define MAX_SCOPE_DEPTH 128
// Max params/bindings tracked per scope entry
#define MAX_SCOPE_PARAMS 64
// Max top-level bare defs tracked per file for module qualification
#define MAX_LOCAL_DEFS 1024
#define MOD_PREFIX_MAX 128
#define QUAL_NAME_MAX 256

typedef struct {
  int pos;
  int parent_pos;
  const char *params[MAX_SCOPE_PARAMS];
  bool is_param[MAX_SCOPE_PARAMS];  // true for fun/lambda params, false for = bindings
  int param_count;
} scope_entry_t;

typedef struct {
  sqlite3 *db;
  int file_id;
  const char *text;
  int text_len;
  const char *current_call;
  bool is_top_level;
  bool fast_mode;

  sqlite3_stmt *stmt_node;
  sqlite3_stmt *stmt_semtok;
  sqlite3_stmt *stmt_ref;
  sqlite3_stmt *stmt_scope;
  sqlite3_stmt *stmt_symbol;
  sqlite3_stmt *stmt_global_ref;

  scope_entry_t scopes[MAX_SCOPE_DEPTH];
  int scope_depth;

  // Module qualification. `(module X)` at top level makes every bare
  // top-level def in the file resolve as `X/name` at runtime — see
  // valk_module_apply_prefix in macro.c. The index must record the same
  // qualified name or reference sites (which are written qualified) can
  // never match the definition.
  char module_prefix[MOD_PREFIX_MAX];
  const char *local_defs[MAX_LOCAL_DEFS];
  int local_def_count;

  char sig_buf[512];
  char doc_buf[1024];
} index_ctx_t;

// Sig expression serializer — convert AST to string like "{-> Num Num}"
const char *valk_lspi_sig_to_string(index_ctx_t *ctx, valk_lval_t *sig_expr);

const char *valk_lspi_extract_doc_comment(index_ctx_t *ctx, int offset);

// Module qualification — mirrors valk_module_apply_prefix (macro.c)
const char *valk_lspi_qualify(index_ctx_t *ctx, const char *name, char *buf,
                              size_t bufsz);
void valk_lspi_collect_module_and_defs(index_ctx_t *ctx, valk_lval_t *ast);

// Scope management
int valk_lspi_current_scope_pos(index_ctx_t *ctx);
int valk_lspi_resolve_scope(index_ctx_t *ctx, const char *name);
bool valk_lspi_is_scope_param(index_ctx_t *ctx, const char *name);
void valk_lspi_push_scope(index_ctx_t *ctx, int pos);
void valk_lspi_add_scope_name(index_ctx_t *ctx, const char *name,
                              bool is_param);
void valk_lspi_pop_scope(index_ctx_t *ctx);

// Emit functions — insert into prepared statements
void valk_lspi_emit_symbol(index_ctx_t *ctx, const char *name, int pos,
                           int kind, int arity, const char *doc,
                           const char *sig);
void valk_lspi_emit_global_ref(index_ctx_t *ctx, const char *name, int pos);
void valk_lspi_emit_node_ctx(index_ctx_t *ctx, int pos, int end,
                             const char *type, const char *name,
                             const char *context);
void valk_lspi_emit_node(index_ctx_t *ctx, int pos, int end, const char *type,
                         const char *name);
void valk_lspi_emit_semtok(index_ctx_t *ctx, int pos, int len, int type,
                           int mods);
void valk_lspi_emit_ref(index_ctx_t *ctx, const char *name, int pos, int len,
                        int scope_id, int is_def);
