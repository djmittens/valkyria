#include "lsp_index_internal.h"

#include <string.h>

// ---------------------------------------------------------------------------
// Sig expression serializer — convert AST to string like "{-> Num Num}"
// ---------------------------------------------------------------------------

static int serialize_sig_expr(valk_lval_t *expr, char *buf, int size, int pos) {
  if (!expr || pos >= size - 1) return pos;
  if (LVAL_TYPE(expr) == LVAL_SYM) {
    int len = (int)strlen(expr->str);
    if (pos + len < size - 1) {
      memcpy(buf + pos, expr->str, len);
      pos += len;
    }
    return pos;
  }
  if (LVAL_TYPE(expr) == LVAL_CONS) {
    if (pos < size - 1) buf[pos++] = '{';
    valk_lval_t *cur = expr;
    bool first = true;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      if (!first && pos < size - 1) buf[pos++] = ' ';
      first = false;
      pos = serialize_sig_expr(cur->cons.head, buf, size, pos);
      cur = cur->cons.tail;
    }
    if (pos < size - 1) buf[pos++] = '}';
    return pos;
  }
  return pos;
}

const char *valk_lspi_sig_to_string(index_ctx_t *ctx, valk_lval_t *sig_expr) {
  int len = serialize_sig_expr(sig_expr, ctx->sig_buf, sizeof(ctx->sig_buf), 0);
  ctx->sig_buf[len] = '\0';
  return ctx->sig_buf;
}

// ---------------------------------------------------------------------------
// Position helpers
// ---------------------------------------------------------------------------

static void offset_to_line_col(const char *text, int tlen, int offset,
                                int *out_line, int *out_col) {
  int line = 0, col = 0;
  int limit = offset < tlen ? offset : tlen;
  for (int i = 0; i < limit; i++) {
    if (text[i] == '\n') { line++; col = 0; }
    else { col++; }
  }
  *out_line = line;
  *out_col = col;
}

const char *valk_lspi_extract_doc_comment(index_ctx_t *ctx, int offset) {
  const char *text = ctx->text;
  int tlen = ctx->text_len;
  (void)tlen;
  int line_start = offset;
  while (line_start > 0 && text[line_start - 1] != '\n') line_start--;
  int prev_end = line_start > 0 ? line_start - 1 : 0;
  while (prev_end > 0 && text[prev_end - 1] != '\n') prev_end--;
  if (prev_end >= line_start) return NULL;
  while (prev_end < line_start && (text[prev_end] == ' ' || text[prev_end] == '\t'))
    prev_end++;
  if (prev_end >= line_start || text[prev_end] != ';') return NULL;
  prev_end++;
  while (prev_end < line_start && text[prev_end] == ' ') prev_end++;
  int len = (line_start > 0 ? line_start - 1 : 0) - prev_end;
  if (len <= 0 || len >= (int)sizeof(ctx->doc_buf)) return NULL;
  memcpy(ctx->doc_buf, &text[prev_end], len);
  ctx->doc_buf[len] = '\0';
  return ctx->doc_buf;
}

// ---------------------------------------------------------------------------
// Module qualification — mirrors valk_module_apply_prefix (macro.c)
// ---------------------------------------------------------------------------

static bool is_bare_name(const char *n) {
  return n && n[0] != '\0' && n[0] != ':' && strchr(n, '/') == NULL;
}

static bool is_local_def(index_ctx_t *ctx, const char *name) {
  for (int i = 0; i < ctx->local_def_count; i++)
    if (strcmp(ctx->local_defs[i], name) == 0) return true;
  return false;
}

static void add_local_def(index_ctx_t *ctx, const char *name) {
  if (ctx->local_def_count >= MAX_LOCAL_DEFS) return;
  if (is_local_def(ctx, name)) return;
  ctx->local_defs[ctx->local_def_count++] = name;
}

// Returns `prefix/name` in `buf` when this file declares a module and
// `name` is a bare top-level def of this file; otherwise returns `name`
// unchanged. Matches the runtime rules: keywords and already-qualified
// names are never rewritten (macro.c rewrite_node), and only names that
// are actually defined locally get the prefix.
const char *valk_lspi_qualify(index_ctx_t *ctx, const char *name, char *buf,
                              size_t bufsz) {
  if (!ctx->module_prefix[0]) return name;
  if (!is_bare_name(name)) return name;
  if (!is_local_def(ctx, name)) return name;
  snprintf(buf, bufsz, "%s/%s", ctx->module_prefix, name);
  return buf;
}

// Pre-pass over top-level forms: record the `(module X)` prefix and every
// bare name defined by a top-level `def` or `fun`. The LSP indexes the raw
// parsed AST (io.valk `lsp/parse-and-remember` calls `parse` with no macro
// expansion), so `fun` has not yet been rewritten to `def` here — both
// spellings must be recognised.
void valk_lspi_collect_module_and_defs(index_ctx_t *ctx, valk_lval_t *ast) {
  for (valk_lval_t *cur = ast; cur && LVAL_TYPE(cur) == LVAL_CONS;
       cur = cur->cons.tail) {
    valk_lval_t *form = cur->cons.head;
    if (!form || LVAL_TYPE(form) != LVAL_CONS) continue;
    if (form->flags & LVAL_FLAG_QUOTED) continue;
    valk_lval_t *head = form->cons.head;
    if (!head || LVAL_TYPE(head) != LVAL_SYM) continue;
    valk_lval_t *rest = form->cons.tail;
    if (!rest || LVAL_TYPE(rest) != LVAL_CONS) continue;

    if (strcmp(head->str, "module") == 0) {
      valk_lval_t *m = rest->cons.head;
      if (m && (LVAL_TYPE(m) == LVAL_SYM || LVAL_TYPE(m) == LVAL_STR) &&
          m->str && m->str[0])
        snprintf(ctx->module_prefix, sizeof ctx->module_prefix, "%s", m->str);
      continue;
    }

    // Position-sensitive, matching the runtime: only defs after the
    // (module X) form belong to the module and get qualified. Defs before
    // it stay in the enclosing (bare) scope.
    if (!ctx->module_prefix[0]) continue;

    if (strcmp(head->str, "def") != 0 && strcmp(head->str, "fun") != 0)
      continue;

    valk_lval_t *sym = rest->cons.head;
    const char *nm = NULL;
    if (LVAL_TYPE(sym) == LVAL_SYM) {
      nm = sym->str;
    } else if (LVAL_TYPE(sym) == LVAL_CONS && sym->cons.head &&
               LVAL_TYPE(sym->cons.head) == LVAL_SYM) {
      nm = sym->cons.head->str;
    }
    if (nm && is_bare_name(nm)) add_local_def(ctx, nm);
  }
}

// ---------------------------------------------------------------------------
// Symbol & ref emission
// ---------------------------------------------------------------------------

// The namespace a symbol belongs to is the part of its qualified name
// before the final `/` — whether the prefix came from `(module X)` or was
// written explicitly. Storing it lets short-name search rank by module
// without doing string surgery in SQL.
static const char *split_module(const char *name, char *buf, size_t bufsz) {
  const char *slash = strrchr(name, '/');
  if (!slash || slash == name) return NULL;
  size_t n = (size_t)(slash - name);
  if (n >= bufsz) n = bufsz - 1;
  memcpy(buf, name, n);
  buf[n] = '\0';
  return buf;
}

void valk_lspi_emit_symbol(index_ctx_t *ctx, const char *name, int pos,
                           int kind, int arity, const char *doc,
                           const char *sig) {
  int line, col;
  char modbuf[MOD_PREFIX_MAX];
  const char *module = split_module(name, modbuf, sizeof modbuf);
  offset_to_line_col(ctx->text, ctx->text_len, pos, &line, &col);
  sqlite3_reset(ctx->stmt_symbol);
  sqlite3_bind_text(ctx->stmt_symbol, 1, name, -1, SQLITE_STATIC);
  sqlite3_bind_int(ctx->stmt_symbol, 2, ctx->file_id);
  sqlite3_bind_int(ctx->stmt_symbol, 3, line);
  sqlite3_bind_int(ctx->stmt_symbol, 4, col);
  sqlite3_bind_int(ctx->stmt_symbol, 5, kind);
  sqlite3_bind_int(ctx->stmt_symbol, 6, arity);
  if (doc) sqlite3_bind_text(ctx->stmt_symbol, 7, doc, -1, SQLITE_STATIC);
  else sqlite3_bind_null(ctx->stmt_symbol, 7);
  if (sig) sqlite3_bind_text(ctx->stmt_symbol, 8, sig, -1, SQLITE_STATIC);
  else sqlite3_bind_null(ctx->stmt_symbol, 8);
  if (module) sqlite3_bind_text(ctx->stmt_symbol, 9, module, -1, SQLITE_STATIC);
  else sqlite3_bind_null(ctx->stmt_symbol, 9);
  sqlite3_step(ctx->stmt_symbol);
}

void valk_lspi_emit_global_ref(index_ctx_t *ctx, const char *name, int pos) {
  int line, col;
  offset_to_line_col(ctx->text, ctx->text_len, pos, &line, &col);
  sqlite3_reset(ctx->stmt_global_ref);
  sqlite3_bind_text(ctx->stmt_global_ref, 1, name, -1, SQLITE_STATIC);
  sqlite3_bind_int(ctx->stmt_global_ref, 2, ctx->file_id);
  sqlite3_bind_int(ctx->stmt_global_ref, 3, line);
  sqlite3_bind_int(ctx->stmt_global_ref, 4, col);
  sqlite3_step(ctx->stmt_global_ref);
}

// ---------------------------------------------------------------------------
// Scope management
// ---------------------------------------------------------------------------

int valk_lspi_current_scope_pos(index_ctx_t *ctx) {
  return ctx->scope_depth > 0 ? ctx->scopes[ctx->scope_depth - 1].pos : -1;
}

int valk_lspi_resolve_scope(index_ctx_t *ctx, const char *name) {
  for (int i = ctx->scope_depth - 1; i >= 0; i--) {
    scope_entry_t *s = &ctx->scopes[i];
    for (int j = 0; j < s->param_count; j++) {
      if (strcmp(s->params[j], name) == 0) return s->pos;
    }
  }
  return -1;
}

bool valk_lspi_is_scope_param(index_ctx_t *ctx, const char *name) {
  for (int i = ctx->scope_depth - 1; i >= 0; i--) {
    scope_entry_t *s = &ctx->scopes[i];
    for (int j = 0; j < s->param_count; j++) {
      if (strcmp(s->params[j], name) == 0) return s->is_param[j];
    }
  }
  return false;
}

void valk_lspi_push_scope(index_ctx_t *ctx, int pos) {
  if (ctx->fast_mode) { ctx->scope_depth++; return; }
  if (ctx->scope_depth >= MAX_SCOPE_DEPTH) { // LCOV_EXCL_START
    fprintf(stderr, "[lsp-index] warning: max scope depth (%d) exceeded\n", MAX_SCOPE_DEPTH);
    return;
  } // LCOV_EXCL_STOP
  scope_entry_t *s = &ctx->scopes[ctx->scope_depth];
  s->pos = pos;
  s->parent_pos = valk_lspi_current_scope_pos(ctx);
  s->param_count = 0;

  // Insert scope record
  sqlite3_reset(ctx->stmt_scope);
  sqlite3_bind_int(ctx->stmt_scope, 1, ctx->file_id);
  sqlite3_bind_int(ctx->stmt_scope, 2, pos);
  sqlite3_bind_int(ctx->stmt_scope, 3, s->parent_pos);
  sqlite3_step(ctx->stmt_scope);

  ctx->scope_depth++;
}

void valk_lspi_add_scope_name(index_ctx_t *ctx, const char *name,
                              bool is_param) {
  if (ctx->scope_depth <= 0) return;
  scope_entry_t *s = &ctx->scopes[ctx->scope_depth - 1];
  if (s->param_count < MAX_SCOPE_PARAMS) {
    s->params[s->param_count] = name;
    s->is_param[s->param_count] = is_param;
    s->param_count++;
  } else {
    static bool warned = false;
    if (!warned) {
      fprintf(stderr, "[lsp-index] warning: max params per scope (%d) exceeded, later params untracked\n",
              MAX_SCOPE_PARAMS);
      warned = true;
    }
  }
}

void valk_lspi_pop_scope(index_ctx_t *ctx) {
  if (ctx->scope_depth > 0) ctx->scope_depth--;
}

// ---------------------------------------------------------------------------
// Emit functions — insert into prepared statements
// ---------------------------------------------------------------------------

void valk_lspi_emit_node_ctx(index_ctx_t *ctx, int pos, int end,
                             const char *type, const char *name,
                             const char *context) {
  if (ctx->fast_mode) return;
  sqlite3_reset(ctx->stmt_node);
  sqlite3_bind_int(ctx->stmt_node, 1, ctx->file_id);
  sqlite3_bind_int(ctx->stmt_node, 2, pos);
  sqlite3_bind_int(ctx->stmt_node, 3, end);
  sqlite3_bind_text(ctx->stmt_node, 4, type, -1, SQLITE_STATIC);
  sqlite3_bind_text(ctx->stmt_node, 5, name, -1, SQLITE_STATIC);
  if (context)
    sqlite3_bind_text(ctx->stmt_node, 6, context, -1, SQLITE_STATIC);
  else
    sqlite3_bind_null(ctx->stmt_node, 6);
  sqlite3_step(ctx->stmt_node);
}

void valk_lspi_emit_node(index_ctx_t *ctx, int pos, int end, const char *type,
                         const char *name) {
  valk_lspi_emit_node_ctx(ctx, pos, end, type, name, NULL);
}


void valk_lspi_emit_ref(index_ctx_t *ctx, const char *name, int pos, int len,
                        int scope_id, int is_def) {
  if (ctx->fast_mode) return;
  sqlite3_reset(ctx->stmt_ref);
  sqlite3_bind_int(ctx->stmt_ref, 1, ctx->file_id);
  sqlite3_bind_text(ctx->stmt_ref, 2, name, -1, SQLITE_STATIC);
  sqlite3_bind_int(ctx->stmt_ref, 3, pos);
  sqlite3_bind_int(ctx->stmt_ref, 4, len);
  sqlite3_bind_int(ctx->stmt_ref, 5, scope_id);
  sqlite3_bind_int(ctx->stmt_ref, 6, is_def);
  sqlite3_step(ctx->stmt_ref);
}
