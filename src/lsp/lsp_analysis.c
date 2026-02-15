#include "lsp_doc.h"

#include <libgen.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../parser.h"

static char g_workspace_root[PATH_MAX] = {0};

void lsp_set_workspace_root(const char *root) {
  if (root)
    snprintf(g_workspace_root, sizeof(g_workspace_root), "%s", root);
}

const char *BUILTIN_NAMES[] = {
  // Core special forms
  "def", "=", "\\", "fun", "if", "do", "select", "quote",
  // List operations
  "list", "head", "tail", "join", "cons", "len", "init", "range", "repeat",
  // Evaluation & I/O
  "eval", "load", "read", "read-file", "error", "error?", "list?", "ref?",
  "print", "println", "printf", "str", "make-string", "ord",
  // String operations
  "str/split", "str/replace", "str/slice", "str->num",
  // Arithmetic & comparison
  "+", "-", "*", "/", ">", "<", ">=", "<=", "==", "!=",
  // System
  "penv", "time-us", "sleep", "stack-depth", "exit", "shutdown",
  "sys/log/set-level",
  // Higher-order (prelude defines these, but treat as known)
  "map", "filter", "foldl", "reverse", "sum", "product",
  "nth", "fst", "snd", "trd", "last", "take", "drop", "split", "exists",
  "not", "and", "or", "id", "flip", "comp", "curry", "uncurry", "pack", "unpack",
  "nil?", "handle?", "as-handle",
  "let", "case",
  // Constants
  "true", "false", "nil", "otherwise",
  // Async combinators
  "aio/start", "aio/run", "aio/stop", "aio/await", "aio/sleep",
  "aio/then", "aio/catch", "aio/finally",
  "aio/all", "aio/race", "aio/any", "aio/all-settled",
  "aio/within", "aio/retry", "aio/bracket", "aio/scope",
  "aio/pure", "aio/fail", "aio/never", "aio/cancel",
  "aio/status", "aio/result", "aio/error", "aio/cancelled?",
  "aio/on-cancel", "aio/schedule", "aio/interval",
  "aio/let", "aio/do", "aio/traverse", "aio/on-loop-thread?",
  "aio/map", "aio/try",
  "aio/pool-stats", "aio/slab-buckets",
  "aio/diagnostics-state-json", "aio/diagnostics-state-json-compact",
  "aio/metrics-json", "aio/metrics-json-compact",
  "aio/systems-json",
  // HTTP/2
  "http2/server-listen", "http2/server-port", "http2/server-stop", "http2/server-handle",
  "http2/client-request", "http2/client-request-with-headers",
  "http2/connect", "http2/request", "http2/request-add-header",
  "http2/response-body", "http2/response-status", "http2/response-headers",
  "http2/mock-response",
  // Request accessors
  "req/method", "req/path", "req/authority", "req/scheme",
  "req/headers", "req/header", "req/body", "req/stream-id",
  // Streams
  "stream/open", "stream/write", "stream/close", "stream/writable?",
  "stream/on-drain", "stream/on-close", "stream/cancel", "stream/closed",
  "stream/id", "stream/set-max-session", "stream/set-timeout",
  // SSE
  "sse/open", "sse/send", "sse/event", "sse/close",
  // Metrics
  "metrics/counter", "metrics/counter-inc",
  "metrics/gauge", "metrics/gauge-set", "metrics/gauge-inc", "metrics/gauge-dec",
  "metrics/histogram", "metrics/histogram-observe",
  "metrics/baseline", "metrics/collect-delta", "metrics/collect-delta-stateless",
  "metrics/delta-json", "metrics/json", "metrics/prometheus", "metrics/registry-json",
  // Context
  "ctx/with-deadline", "ctx/with", "ctx/get", "ctx/deadline",
  "ctx/deadline-exceeded?", "ctx/locals",
  // Memory & GC
  "mem/stats", "mem/gc/stats", "mem/gc/collect", "mem/gc/usage",
  "mem/gc/threshold", "mem/gc/set-threshold",
  "mem/gc/min-interval", "mem/gc/set-min-interval",
  "mem/heap/usage", "mem/heap/hard-limit", "mem/heap/set-hard-limit",
  "mem/arena/usage", "mem/arena/capacity", "mem/arena/high-water",
  "mem/checkpoint/stats",
  // Testing
  "test", "test-async", "test/assert", "test/assert-eq",
  "test/run", "test/run-async", "test/suite", "test/context-new",
  "test/capture-start", "test/capture-stop",
  // Property lists
  "plist/get", "plist/set", "plist/has?", "plist/keys", "plist/vals",
  // Coverage / source introspection
  "coverage-mark", "coverage-branch", "coverage-record",
  "source-file", "source-line", "source-column",
  // Tracing
  "trace/id", "trace/span", "trace/parent-span",
  // VM metrics
  "vm/metrics-json", "vm/metrics-json-compact", "vm/metrics-prometheus",
  // Misc
  "get",
  nullptr
};

// ---------------------------------------------------------------------------
// Shared helpers (also used by lsp.c via lsp_doc.h)
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

void doc_add_symbol(lsp_document_t *doc, const char *name, int line, int col, int arity) {
  if (doc->symbol_count >= doc->symbol_cap) {
    doc->symbol_cap = doc->symbol_cap == 0 ? 16 : doc->symbol_cap * 2;
    doc->symbols = realloc(doc->symbols, sizeof(lsp_symbol_t) * doc->symbol_cap);
  }
  lsp_symbol_t *sym = &doc->symbols[doc->symbol_count++];
  sym->name = strdup(name);
  sym->pos = (lsp_pos_t){line, col};
  sym->arity = arity;
  sym->doc = nullptr;
}

void doc_add_diag_full(lsp_document_t *doc, const char *msg, int line, int col, int len, int severity) {
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

static void doc_sem_clear(lsp_document_t *doc) {
  doc->sem_token_count = 0;
}

static void doc_add_sem(lsp_document_t *doc, int line, int col, int len, int type, int mods) {
  if (doc->sem_token_count >= doc->sem_token_cap) {
    doc->sem_token_cap = doc->sem_token_cap == 0 ? 256 : doc->sem_token_cap * 2;
    doc->sem_tokens = realloc(doc->sem_tokens, sizeof(lsp_sem_token_t) * doc->sem_token_cap);
  }
  doc->sem_tokens[doc->sem_token_count++] = (lsp_sem_token_t){line, col, len, type, mods};
}

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

typedef struct {
  char **names;
  size_t count;
  size_t cap;
} lsp_symset_t;

static void symset_init(lsp_symset_t *s) {
  s->names = nullptr;
  s->count = 0;
  s->cap = 0;
}

static void symset_free(lsp_symset_t *s) {
  for (size_t i = 0; i < s->count; i++)
    free(s->names[i]);
  free(s->names);
  s->names = nullptr;
  s->count = s->cap = 0;
}

static bool symset_contains(lsp_symset_t *s, const char *name) {
  for (size_t i = 0; i < s->count; i++)
    if (strcmp(s->names[i], name) == 0) return true;
  return false;
}

static void symset_add(lsp_symset_t *s, const char *name) {
  if (symset_contains(s, name)) return;
  if (s->count >= s->cap) {
    s->cap = s->cap == 0 ? 64 : s->cap * 2;
    s->names = realloc(s->names, sizeof(char *) * s->cap);
  }
  s->names[s->count++] = strdup(name);
}

// ---------------------------------------------------------------------------
// Load graph: resolve (load "path") transitively, collect global symbols
// ---------------------------------------------------------------------------

static void uri_to_path(const char *uri, char *path, size_t path_size) {
  if (strncmp(uri, "file://", 7) == 0)
    snprintf(path, path_size, "%s", uri + 7);
  else
    snprintf(path, path_size, "%s", uri);
}

static void extract_global_symbols_from_text(const char *text, lsp_symset_t *globals) {
  int pos = 0;
  int len = (int)strlen(text);

  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;

    if (text[pos] == ';') {
      while (pos < len && text[pos] != '\n') pos++;
      continue;
    }

    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    if (LVAL_TYPE(expr) != LVAL_CONS) continue;

    valk_lval_t *head = valk_lval_head(expr);
    if (!head || LVAL_TYPE(head) != LVAL_SYM) continue;

    if (strcmp(head->str, "def") == 0 || strcmp(head->str, "fun") == 0) {
      valk_lval_t *tail = valk_lval_tail(expr);
      if (LVAL_TYPE(tail) != LVAL_CONS) continue;

      valk_lval_t *binding = valk_lval_head(tail);
      if (!binding) continue;

      if (LVAL_TYPE(binding) == LVAL_CONS) {
        valk_lval_t *first = valk_lval_head(binding);
        if (first && LVAL_TYPE(first) == LVAL_SYM)
          symset_add(globals, first->str);
      } else if (LVAL_TYPE(binding) == LVAL_SYM) {
        symset_add(globals, binding->str);
      }
    }
  }
}

static void resolve_loads_from_text(const char *text, const char *base_dir,
                                    lsp_symset_t *globals, lsp_symset_t *visited) {
  int pos = 0;
  int len = (int)strlen(text);

  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;

    if (text[pos] == ';') {
      while (pos < len && text[pos] != '\n') pos++;
      continue;
    }

    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    if (LVAL_TYPE(expr) != LVAL_CONS) continue;

    valk_lval_t *head = valk_lval_head(expr);
    if (!head || LVAL_TYPE(head) != LVAL_SYM) continue;

    if (strcmp(head->str, "load") != 0) continue;

    valk_lval_t *tail = valk_lval_tail(expr);
    if (LVAL_TYPE(tail) != LVAL_CONS) continue;

    valk_lval_t *arg = valk_lval_head(tail);
    if (!arg || LVAL_TYPE(arg) != LVAL_STR) continue;

    char resolved[PATH_MAX];
    char real[PATH_MAX];
    bool found = false;

    if (arg->str[0] == '/') {
      snprintf(resolved, sizeof(resolved), "%s", arg->str);
      found = realpath(resolved, real) != nullptr;
    } else {
      snprintf(resolved, sizeof(resolved), "%s/%s", base_dir, arg->str);
      found = realpath(resolved, real) != nullptr;
      if (!found && g_workspace_root[0]) {
        snprintf(resolved, sizeof(resolved), "%s/%s", g_workspace_root, arg->str);
        found = realpath(resolved, real) != nullptr;
      }
    }
    if (!found) continue;

    if (symset_contains(visited, real)) continue;
    symset_add(visited, real);

    FILE *f = fopen(real, "rb");
    if (!f) continue;

    fseek(f, 0, SEEK_END);
    long flen = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (flen <= 0 || flen > 10 * 1024 * 1024) { fclose(f); continue; }

    char *contents = calloc(flen + 1, 1);
    fread(contents, 1, flen, f);
    fclose(f);

    extract_global_symbols_from_text(contents, globals);

    char *dir_copy = strdup(real);
    char *dir = dirname(dir_copy);
    resolve_loads_from_text(contents, dir, globals, visited);
    free(dir_copy);
    free(contents);
  }
}

static void build_global_symset(lsp_document_t *doc, lsp_symset_t *globals) {
  symset_init(globals);

  for (int i = 0; BUILTIN_NAMES[i]; i++)
    symset_add(globals, BUILTIN_NAMES[i]);

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

  resolve_loads_from_text(doc->text, dir, globals, &visited);
  symset_free(&visited);
  free(dir_copy);
}

// ---------------------------------------------------------------------------
// Scope-aware symbol checker
// ---------------------------------------------------------------------------

typedef struct lsp_scope {
  lsp_symset_t locals;
  struct lsp_scope *parent;
} lsp_scope_t;

static lsp_scope_t *scope_push(lsp_scope_t *parent) {
  lsp_scope_t *s = calloc(1, sizeof(lsp_scope_t));
  symset_init(&s->locals);
  s->parent = parent;
  return s;
}

static void scope_pop(lsp_scope_t *s) {
  symset_free(&s->locals);
  free(s);
}

static bool scope_has(lsp_scope_t *s, const char *name) {
  while (s) {
    if (symset_contains(&s->locals, name)) return true;
    s = s->parent;
  }
  return false;
}

static void check_expr(valk_lval_t *expr, lsp_symset_t *globals, lsp_scope_t *scope,
                        lsp_document_t *doc, const char *text, int *cursor);

static void extract_qexpr_syms(valk_lval_t *qexpr, lsp_scope_t *scope) {
  while (qexpr && LVAL_TYPE(qexpr) == LVAL_CONS) {
    valk_lval_t *h = valk_lval_head(qexpr);
    if (h && LVAL_TYPE(h) == LVAL_SYM && h->str[0] != '&')
      symset_add(&scope->locals, h->str);
    qexpr = valk_lval_tail(qexpr);
  }
}

static void check_body_exprs(valk_lval_t *rest, lsp_symset_t *globals,
                              lsp_scope_t *scope, lsp_document_t *doc, const char *text,
                              int *cursor) {
  while (rest && LVAL_TYPE(rest) == LVAL_CONS) {
    check_expr(valk_lval_head(rest), globals, scope, doc, text, cursor);
    rest = valk_lval_tail(rest);
  }
}

static bool in_comment_or_string(const char *text, int pos) {
  bool in_str = false;
  for (int i = 0; i < pos; i++) {
    if (text[i] == '"' && !in_str) {
      in_str = true;
    } else if (text[i] == '"' && in_str) {
      in_str = false;
    } else if (text[i] == '\\' && in_str) {
      i++;
    } else if (text[i] == ';' && !in_str) {
      while (i < pos && text[i] != '\n') i++;
      if (i >= pos) return true;
    }
  }
  return in_str;
}

static int find_sym_offset(const char *text, const char *sym, int search_start) {
  int slen = (int)strlen(sym);
  int tlen = (int)strlen(text);
  for (int i = search_start; i <= tlen - slen; i++) {
    if (memcmp(text + i, sym, slen) == 0) {
      if (i > 0 && strchr("abcdefghijklmnopqrstuvwxyz"
                           "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                           "0123456789_+-*/\\=<>!&?:/",
                           text[i - 1]))
        continue;
      if (i + slen < tlen && strchr("abcdefghijklmnopqrstuvwxyz"
                                     "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                                     "0123456789_+-*/\\=<>!&?:/",
                                     text[i + slen]))
        continue;
      if (in_comment_or_string(text, i))
        continue;
      return i;
    }
  }
  return -1;
}

static void check_expr(valk_lval_t *expr, lsp_symset_t *globals, lsp_scope_t *scope,
                        lsp_document_t *doc, const char *text, int *cursor) {
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    if (expr->str[0] == ':') {
      int off = find_sym_offset(text, expr->str, *cursor);
      if (off >= 0) *cursor = off + (int)strlen(expr->str);
      return;
    }
    if (symset_contains(globals, expr->str) || scope_has(scope, expr->str)) {
      int off = find_sym_offset(text, expr->str, *cursor);
      if (off >= 0) *cursor = off + (int)strlen(expr->str);
      return;
    }

    int off = find_sym_offset(text, expr->str, *cursor);
    if (off >= 0) {
      *cursor = off + (int)strlen(expr->str);
      lsp_pos_t p = offset_to_pos(text, off);
      char msg[256];
      snprintf(msg, sizeof(msg), "Symbol '%s' is not defined", expr->str);
      doc_add_diag_full(doc, msg, p.line, p.col, (int)strlen(expr->str), 1);
    }
    return;
  }

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = valk_lval_head(expr);
  valk_lval_t *rest = valk_lval_tail(expr);

  if (expr->flags & LVAL_FLAG_QUOTED) return;
  if (!head) return;

  if (LVAL_TYPE(head) == LVAL_SYM) {
    if (strcmp(head->str, "quote") == 0) return;

    if (strcmp(head->str, "\\") == 0) {
      if (LVAL_TYPE(rest) != LVAL_CONS) return;
      valk_lval_t *formals = valk_lval_head(rest);
      valk_lval_t *body_rest = valk_lval_tail(rest);

      lsp_scope_t *inner = scope_push(scope);
      if (formals && LVAL_TYPE(formals) == LVAL_CONS)
        extract_qexpr_syms(formals, inner);

      check_body_exprs(body_rest, globals, inner, doc, text, cursor);
      scope_pop(inner);
      return;
    }

    if (strcmp(head->str, "def") == 0) {
      if (LVAL_TYPE(rest) != LVAL_CONS) return;
      valk_lval_t *binding = valk_lval_head(rest);
      valk_lval_t *val_rest = valk_lval_tail(rest);

      if (binding && LVAL_TYPE(binding) == LVAL_CONS) {
        valk_lval_t *cur = binding;
        while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
          valk_lval_t *s = valk_lval_head(cur);
          if (s && LVAL_TYPE(s) == LVAL_SYM)
            symset_add(globals, s->str);
          cur = valk_lval_tail(cur);
        }
      } else if (binding && LVAL_TYPE(binding) == LVAL_SYM) {
        symset_add(globals, binding->str);
      }

      check_body_exprs(val_rest, globals, scope, doc, text, cursor);
      return;
    }

    if (strcmp(head->str, "=") == 0) {
      if (LVAL_TYPE(rest) != LVAL_CONS) return;
      valk_lval_t *binding = valk_lval_head(rest);
      valk_lval_t *val_rest = valk_lval_tail(rest);

      if (binding && LVAL_TYPE(binding) == LVAL_CONS) {
        valk_lval_t *cur = binding;
        while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
          valk_lval_t *s = valk_lval_head(cur);
          if (s && LVAL_TYPE(s) == LVAL_SYM)
            symset_add(&scope->locals, s->str);
          cur = valk_lval_tail(cur);
        }
      } else if (binding && LVAL_TYPE(binding) == LVAL_SYM) {
        symset_add(&scope->locals, binding->str);
      }

      check_body_exprs(val_rest, globals, scope, doc, text, cursor);
      return;
    }

    if (strcmp(head->str, "fun") == 0) {
      if (LVAL_TYPE(rest) != LVAL_CONS) return;
      valk_lval_t *name_formals = valk_lval_head(rest);
      valk_lval_t *body_rest = valk_lval_tail(rest);

      if (name_formals && LVAL_TYPE(name_formals) == LVAL_CONS) {
        valk_lval_t *fname = valk_lval_head(name_formals);
        if (fname && LVAL_TYPE(fname) == LVAL_SYM)
          symset_add(globals, fname->str);

        lsp_scope_t *inner = scope_push(scope);
        valk_lval_t *params = valk_lval_tail(name_formals);
        extract_qexpr_syms(params, inner);
        check_body_exprs(body_rest, globals, inner, doc, text, cursor);
        scope_pop(inner);
      }
      return;
    }

    if (strcmp(head->str, "if") == 0 ||
        strcmp(head->str, "do") == 0 ||
        strcmp(head->str, "select") == 0 ||
        strcmp(head->str, "load") == 0 ||
        strcmp(head->str, "eval") == 0 ||
        strcmp(head->str, "aio/let") == 0 ||
        strcmp(head->str, "aio/do") == 0) {
      check_body_exprs(rest, globals, scope, doc, text, cursor);
      return;
    }
  }

  check_expr(head, globals, scope, doc, text, cursor);
  check_body_exprs(rest, globals, scope, doc, text, cursor);
}

static void check_undefined_symbols(lsp_document_t *doc) {
  lsp_symset_t globals;
  build_global_symset(doc, &globals);

  const char *text = doc->text;
  int pos = 0;
  int len = (int)doc->text_len;
  int cursor = 0;

  lsp_scope_t *top = scope_push(nullptr);

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

    check_expr(expr, &globals, top, doc, text, &cursor);
  }

  scope_pop(top);
  symset_free(&globals);
}

// ---------------------------------------------------------------------------
// Semantic token generation
// ---------------------------------------------------------------------------

static const char *SPECIAL_FORMS[] = {
  "def", "=", "fun", "\\", "if", "do", "select", "case", "quote", "load",
  "eval", "read", "aio/let", "aio/do", "<-", nullptr
};

static bool is_special_form(const char *name) {
  for (int i = 0; SPECIAL_FORMS[i]; i++)
    if (strcmp(SPECIAL_FORMS[i], name) == 0) return true;
  return false;
}

static bool is_builtin(const char *name) {
  for (int i = 0; BUILTIN_NAMES[i]; i++)
    if (strcmp(BUILTIN_NAMES[i], name) == 0) return true;
  return false;
}

static void sem_expr(valk_lval_t *expr, lsp_symset_t *globals, lsp_scope_t *scope,
                      lsp_document_t *doc, const char *text, int *cursor, bool in_qexpr);

static void sem_body(valk_lval_t *rest, lsp_symset_t *globals, lsp_scope_t *scope,
                      lsp_document_t *doc, const char *text, int *cursor, bool in_qexpr) {
  while (rest && LVAL_TYPE(rest) == LVAL_CONS) {
    sem_expr(valk_lval_head(rest), globals, scope, doc, text, cursor, in_qexpr);
    rest = valk_lval_tail(rest);
  }
}

static void sem_emit_sym(const char *sym, lsp_document_t *doc, const char *text,
                          int *cursor, int type, int mods) {
  int off = find_sym_offset(text, sym, *cursor);
  if (off >= 0) {
    *cursor = off + (int)strlen(sym);
    lsp_pos_t p = offset_to_pos(text, off);
    doc_add_sem(doc, p.line, p.col, (int)strlen(sym), type, mods);
  }
}

static void sem_expr(valk_lval_t *expr, lsp_symset_t *globals, lsp_scope_t *scope,
                      lsp_document_t *doc, const char *text, int *cursor, bool in_qexpr) {
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    if (expr->str[0] == ':') {
      sem_emit_sym(expr->str, doc, text, cursor, SEM_PROPERTY, 0);
      return;
    }
    if (strcmp(expr->str, "true") == 0 || strcmp(expr->str, "false") == 0 ||
        strcmp(expr->str, "nil") == 0 || strcmp(expr->str, "otherwise") == 0) {
      sem_emit_sym(expr->str, doc, text, cursor, SEM_MACRO, SEM_MOD_READONLY);
      return;
    }
    if (in_qexpr) {
      sem_emit_sym(expr->str, doc, text, cursor, SEM_VARIABLE, 0);
      return;
    }
    if (scope_has(scope, expr->str)) {
      sem_emit_sym(expr->str, doc, text, cursor, SEM_PARAMETER, 0);
      return;
    }
    if (is_builtin(expr->str)) {
      sem_emit_sym(expr->str, doc, text, cursor, SEM_VARIABLE, SEM_MOD_DEFAULT_LIB);
      return;
    }
    if (symset_contains(globals, expr->str)) {
      sem_emit_sym(expr->str, doc, text, cursor, SEM_VARIABLE, 0);
      return;
    }
    int off = find_sym_offset(text, expr->str, *cursor);
    if (off >= 0) *cursor = off + (int)strlen(expr->str);
    return;
  }

  if (LVAL_TYPE(expr) == LVAL_NUM) {
    char num_str[64];
    snprintf(num_str, sizeof(num_str), "%li", expr->num);
    int off = find_sym_offset(text, num_str, *cursor);
    if (off >= 0) {
      *cursor = off + (int)strlen(num_str);
      lsp_pos_t p = offset_to_pos(text, off);
      doc_add_sem(doc, p.line, p.col, (int)strlen(num_str), SEM_NUMBER, 0);
    }
    return;
  }

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  if (expr->flags & LVAL_FLAG_QUOTED) {
    sem_body(expr, globals, scope, doc, text, cursor, true);
    return;
  }

  valk_lval_t *head = valk_lval_head(expr);
  valk_lval_t *rest = valk_lval_tail(expr);
  if (!head) return;

  if (LVAL_TYPE(head) == LVAL_SYM) {
    if (strcmp(head->str, "quote") == 0) {
      sem_emit_sym(head->str, doc, text, cursor, SEM_KEYWORD, 0);
      sem_body(rest, globals, scope, doc, text, cursor, true);
      return;
    }

    if (is_special_form(head->str)) {
      sem_emit_sym(head->str, doc, text, cursor, SEM_KEYWORD, 0);
    } else if (is_builtin(head->str)) {
      sem_emit_sym(head->str, doc, text, cursor, SEM_FUNCTION, SEM_MOD_DEFAULT_LIB);
    } else if (scope_has(scope, head->str)) {
      sem_emit_sym(head->str, doc, text, cursor, SEM_FUNCTION, 0);
    } else if (symset_contains(globals, head->str)) {
      sem_emit_sym(head->str, doc, text, cursor, SEM_FUNCTION, 0);
    } else {
      sem_emit_sym(head->str, doc, text, cursor, SEM_FUNCTION, 0);
    }

    if (strcmp(head->str, "\\") == 0 && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *formals = valk_lval_head(rest);
      valk_lval_t *body_rest = valk_lval_tail(rest);
      lsp_scope_t *inner = scope_push(scope);
      if (formals && LVAL_TYPE(formals) == LVAL_CONS) {
        valk_lval_t *cur = formals;
        while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
          valk_lval_t *h = valk_lval_head(cur);
          if (h && LVAL_TYPE(h) == LVAL_SYM && h->str[0] != '&') {
            symset_add(&inner->locals, h->str);
            sem_emit_sym(h->str, doc, text, cursor, SEM_PARAMETER, SEM_MOD_DECLARATION);
          } else if (h && LVAL_TYPE(h) == LVAL_SYM) {
            sem_emit_sym(h->str, doc, text, cursor, SEM_OPERATOR, 0);
          }
          cur = valk_lval_tail(cur);
        }
      }
      sem_body(body_rest, globals, inner, doc, text, cursor, false);
      scope_pop(inner);
      return;
    }

    if (strcmp(head->str, "fun") == 0 && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *name_formals = valk_lval_head(rest);
      valk_lval_t *body_rest = valk_lval_tail(rest);
      if (name_formals && LVAL_TYPE(name_formals) == LVAL_CONS) {
        valk_lval_t *fname = valk_lval_head(name_formals);
        if (fname && LVAL_TYPE(fname) == LVAL_SYM)
          sem_emit_sym(fname->str, doc, text, cursor, SEM_FUNCTION, SEM_MOD_DEFINITION);
        lsp_scope_t *inner = scope_push(scope);
        valk_lval_t *params = valk_lval_tail(name_formals);
        while (params && LVAL_TYPE(params) == LVAL_CONS) {
          valk_lval_t *h = valk_lval_head(params);
          if (h && LVAL_TYPE(h) == LVAL_SYM && h->str[0] != '&') {
            symset_add(&inner->locals, h->str);
            sem_emit_sym(h->str, doc, text, cursor, SEM_PARAMETER, SEM_MOD_DECLARATION);
          } else if (h && LVAL_TYPE(h) == LVAL_SYM) {
            sem_emit_sym(h->str, doc, text, cursor, SEM_OPERATOR, 0);
          }
          params = valk_lval_tail(params);
        }
        sem_body(body_rest, globals, inner, doc, text, cursor, false);
        scope_pop(inner);
      }
      return;
    }

    if (strcmp(head->str, "def") == 0 && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *binding = valk_lval_head(rest);
      valk_lval_t *val_rest = valk_lval_tail(rest);
      if (binding && LVAL_TYPE(binding) == LVAL_CONS) {
        valk_lval_t *cur = binding;
        while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
          valk_lval_t *s = valk_lval_head(cur);
          if (s && LVAL_TYPE(s) == LVAL_SYM)
            sem_emit_sym(s->str, doc, text, cursor, SEM_VARIABLE, SEM_MOD_DEFINITION);
          cur = valk_lval_tail(cur);
        }
      } else if (binding && LVAL_TYPE(binding) == LVAL_SYM) {
        sem_emit_sym(binding->str, doc, text, cursor, SEM_VARIABLE, SEM_MOD_DEFINITION);
      }
      sem_body(val_rest, globals, scope, doc, text, cursor, false);
      return;
    }

    if (strcmp(head->str, "=") == 0 && LVAL_TYPE(rest) == LVAL_CONS) {
      valk_lval_t *binding = valk_lval_head(rest);
      valk_lval_t *val_rest = valk_lval_tail(rest);
      if (binding && LVAL_TYPE(binding) == LVAL_CONS) {
        valk_lval_t *cur = binding;
        while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
          valk_lval_t *s = valk_lval_head(cur);
          if (s && LVAL_TYPE(s) == LVAL_SYM)
            sem_emit_sym(s->str, doc, text, cursor, SEM_VARIABLE, SEM_MOD_DEFINITION);
          cur = valk_lval_tail(cur);
        }
      } else if (binding && LVAL_TYPE(binding) == LVAL_SYM) {
        sem_emit_sym(binding->str, doc, text, cursor, SEM_VARIABLE, SEM_MOD_DEFINITION);
      }
      sem_body(val_rest, globals, scope, doc, text, cursor, false);
      return;
    }

    sem_body(rest, globals, scope, doc, text, cursor, in_qexpr);
    return;
  }

  sem_expr(head, globals, scope, doc, text, cursor, in_qexpr);
  sem_body(rest, globals, scope, doc, text, cursor, in_qexpr);
}

static int sem_token_cmp(const void *a, const void *b) {
  const lsp_sem_token_t *ta = a, *tb = b;
  if (ta->line != tb->line) return ta->line - tb->line;
  return ta->col - tb->col;
}

static void generate_semantic_tokens(lsp_document_t *doc) {
  doc_sem_clear(doc);

  lsp_symset_t globals;
  build_global_symset(doc, &globals);

  const char *text = doc->text;
  int pos = 0;
  int len = (int)doc->text_len;
  int cursor = 0;

  lsp_scope_t *top = scope_push(nullptr);

  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;

    if (text[pos] == ';') {
      int start = pos;
      while (pos < len && text[pos] != '\n') pos++;
      lsp_pos_t p = offset_to_pos(text, start);
      doc_add_sem(doc, p.line, p.col, pos - start, SEM_COMMENT, 0);
      continue;
    }

    cursor = pos;
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    sem_expr(expr, &globals, top, doc, text, &cursor, false);
  }

  scope_pop(top);
  symset_free(&globals);

  if (doc->sem_token_count > 1) {
    qsort(doc->sem_tokens, doc->sem_token_count, sizeof(lsp_sem_token_t), sem_token_cmp);

    size_t w = 0;
    for (size_t r = 0; r < doc->sem_token_count; r++) {
      if (w > 0 && doc->sem_tokens[r].line == doc->sem_tokens[w - 1].line &&
          doc->sem_tokens[r].col == doc->sem_tokens[w - 1].col) {
        doc->sem_tokens[w - 1] = doc->sem_tokens[r];
        continue;
      }
      doc->sem_tokens[w++] = doc->sem_tokens[r];
    }
    doc->sem_token_count = w;
  }
}

// ---------------------------------------------------------------------------
// Document analysis: extract symbols, diagnostics, check undefined symbols
// ---------------------------------------------------------------------------

void analyze_document(lsp_document_t *doc) {
  doc_symbols_clear(doc);
  doc_diag_clear(doc);

  const char *text = doc->text;
  int pos = 0;
  int len = (int)doc->text_len;

  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;

    if (text[pos] == ';') {
      while (pos < len && text[pos] != '\n') pos++;
      continue;
    }

    if (text[pos] != '(') {
      valk_lval_t *val = valk_lval_read(&pos, text);
      if (LVAL_TYPE(val) == LVAL_ERR) {
        lsp_pos_t p = offset_to_pos(text, pos > 0 ? pos - 1 : 0);
        doc_add_diag(doc, val->str, p.line, p.col);
        break;
      }
      continue;
    }

    int form_start = pos;
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) {
      lsp_pos_t p = offset_to_pos(text, form_start);
      doc_add_diag(doc, expr->str, p.line, p.col);
      break;
    }

    if (LVAL_TYPE(expr) != LVAL_CONS) continue;

    valk_lval_t *head = valk_lval_head(expr);
    if (!head || LVAL_TYPE(head) != LVAL_SYM) continue;

    if (strcmp(head->str, "def") == 0 || strcmp(head->str, "fun") == 0) {
      valk_lval_t *tail = valk_lval_tail(expr);
      if (LVAL_TYPE(tail) != LVAL_CONS) continue;

      valk_lval_t *binding = valk_lval_head(tail);
      if (!binding) continue;

      const char *sym_name = nullptr;
      int arity = -1;

      if (LVAL_TYPE(binding) == LVAL_CONS) {
        valk_lval_t *first = valk_lval_head(binding);
        if (first && LVAL_TYPE(first) == LVAL_SYM) {
          sym_name = first->str;
          if (strcmp(head->str, "fun") == 0)
            arity = (int)valk_lval_list_count(binding) - 1;
        }
      } else if (LVAL_TYPE(binding) == LVAL_SYM) {
        sym_name = binding->str;
      }

      if (sym_name) {
        lsp_pos_t p = offset_to_pos(text, form_start);
        doc_add_symbol(doc, sym_name, p.line, p.col, arity);
      }
    }
  }

  check_undefined_symbols(doc);
  generate_semantic_tokens(doc);
}
