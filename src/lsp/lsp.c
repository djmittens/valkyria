#include "lsp.h"
#include "lsp_doc.h"
#include "lsp_builtins_gen.h"
#include "lsp_io.h"
#include "lsp_json.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../parser.h"

// ---------------------------------------------------------------------------
// Document store
// ---------------------------------------------------------------------------

static lsp_doc_store_t g_store = {0};

static lsp_document_t *doc_find(const char *uri) {
  for (size_t i = 0; i < g_store.count; i++)
    if (strcmp(g_store.docs[i].uri, uri) == 0)
      return &g_store.docs[i];
  return nullptr;
}

static lsp_document_t *doc_open(const char *uri, const char *text, int version) {
  lsp_document_t *existing = doc_find(uri);
  if (existing) {
    free(existing->text);
    existing->text = strdup(text);
    existing->text_len = strlen(text);
    existing->version = version;
    return existing;
  }

  if (g_store.count >= g_store.cap) {
    g_store.cap = g_store.cap == 0 ? 8 : g_store.cap * 2;
    g_store.docs = realloc(g_store.docs, sizeof(lsp_document_t) * g_store.cap);
  }

  lsp_document_t *doc = &g_store.docs[g_store.count++];
  memset(doc, 0, sizeof(*doc));
  doc->uri = strdup(uri);
  doc->text = strdup(text);
  doc->text_len = strlen(text);
  doc->version = version;
  return doc;
}

static void doc_close(const char *uri) {
  for (size_t i = 0; i < g_store.count; i++) {
    if (strcmp(g_store.docs[i].uri, uri) == 0) {
      doc_symbols_clear(&g_store.docs[i]);
      doc_diag_clear(&g_store.docs[i]);
      free(g_store.docs[i].uri);
      free(g_store.docs[i].text);
      free(g_store.docs[i].symbols);
      free(g_store.docs[i].diag_messages);
      free(g_store.docs[i].diag_positions);
      free(g_store.docs[i].diag_severities);
      free(g_store.docs[i].diag_lengths);
      free(g_store.docs[i].sem_tokens);
      g_store.docs[i] = g_store.docs[--g_store.count];
      return;
    }
  }
}

// ---------------------------------------------------------------------------
// Get word at a position (for hover/completion context)
// ---------------------------------------------------------------------------

static char *get_word_at(const char *text, int offset) {
  if (!text || offset < 0) return nullptr;
  int start = offset, end = offset;
  int len = (int)strlen(text);

  while (start > 0 && strchr("abcdefghijklmnopqrstuvwxyz"
                              "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                              "0123456789_+-*/\\=<>!&?:/",
                              text[start - 1]))
    start--;

  while (end < len && strchr("abcdefghijklmnopqrstuvwxyz"
                             "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                             "0123456789_+-*/\\=<>!&?:/",
                             text[end]))
    end++;

  if (start == end) return nullptr;
  return strndup(text + start, end - start);
}

// ---------------------------------------------------------------------------
// LSP method handlers
// ---------------------------------------------------------------------------

static void handle_initialize(int id) {
  lsp_send_response(id,
    "{"
      "\"capabilities\":{"
        "\"positionEncoding\":\"utf-8\","
        "\"textDocumentSync\":{"
          "\"openClose\":true,"
          "\"change\":1,"
          "\"save\":{\"includeText\":true}"
        "},"
        "\"completionProvider\":{"
          "\"triggerCharacters\":[\"(\",\"/\",\":\"],"
          "\"resolveProvider\":false"
        "},"
        "\"hoverProvider\":true,"
        "\"definitionProvider\":true,"
        "\"documentSymbolProvider\":true,"
        "\"semanticTokensProvider\":{"
          "\"legend\":{"
            "\"tokenTypes\":[\"keyword\",\"function\",\"variable\","
              "\"parameter\",\"string\",\"number\",\"operator\","
              "\"comment\",\"type\",\"macro\",\"property\"],"
            "\"tokenModifiers\":[\"definition\",\"readonly\","
              "\"defaultLibrary\",\"declaration\"]"
          "},"
          "\"full\":true"
        "}"
      "},"
      "\"serverInfo\":{"
        "\"name\":\"valk-lsp\","
        "\"version\":\"0.1.0\""
      "}"
    "}");
}

static void publish_diagnostics(lsp_document_t *doc) {
  char buf[65536];
  char *p = buf;
  char *end = buf + sizeof(buf);

  p += snprintf(p, end - p, "{\"uri\":\"%s\",\"diagnostics\":[", doc->uri);

  for (size_t i = 0; i < doc->diag_count && p < end - 256; i++) {
    if (i > 0) *p++ = ',';
    char *escaped_msg = json_escape_string(doc->diag_messages[i]);
    p += snprintf(p, end - p,
                  "{\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
                  "\"end\":{\"line\":%d,\"character\":%d}},"
                  "\"severity\":%d,\"source\":\"valk\",\"message\":%s}",
                  doc->diag_positions[i].line, doc->diag_positions[i].col,
                  doc->diag_positions[i].line, doc->diag_positions[i].col + doc->diag_lengths[i],
                  doc->diag_severities[i], escaped_msg);
    free(escaped_msg);
  }

  p += snprintf(p, end - p, "]}");
  lsp_send_notification("textDocument/publishDiagnostics", buf);
}

static void handle_did_open(json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  if (!td) return;
  const char *uri = json_get_string(td, "uri");
  const char *text = json_get_string(td, "text");
  int version = json_get_int(td, "version");
  if (!uri || !text) return;

  lsp_document_t *doc = doc_open(uri, text, version);
  analyze_document(doc);
  publish_diagnostics(doc);
}

static void handle_did_change(json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  if (!td) return;
  const char *uri = json_get_string(td, "uri");
  int version = json_get_int(td, "version");
  if (!uri) return;

  json_value_t *changes = json_get(params, "contentChanges");
  if (!changes || changes->type != JSON_ARRAY || changes->array.count == 0)
    return;

  const char *text = json_get_string(&changes->array.items[0], "text");
  if (!text) return;

  lsp_document_t *doc = doc_open(uri, text, version);
  analyze_document(doc);
  publish_diagnostics(doc);
}

static void handle_did_close(json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  if (!td) return;
  const char *uri = json_get_string(td, "uri");
  if (uri) doc_close(uri);
}

static const char *builtin_doc(const char *name);
static void extract_source_snippet(const char *text, int start, int end,
                                   char *out, size_t out_size);

static bool special_form_snippet(const char *name, char *out, size_t sz,
                                 bool wrap) {
  const char *body = nullptr;
  if (strcmp(name, "def") == 0)        body = "def {${1:name}} ${2:value}";
  else if (strcmp(name, "=") == 0)     body = "= {${1:name}} ${2:value}";
  else if (strcmp(name, "fun") == 0)   body = "fun {${1:name} ${2:params}} ${3:body}";
  else if (strcmp(name, "\\") == 0)    body = "\\\\ {${1:params}} ${2:body}";
  else if (strcmp(name, "if") == 0)    body = "if ${1:cond} ${2:then} ${3:else}";
  else if (strcmp(name, "do") == 0)    body = "do $0";
  else if (strcmp(name, "select") == 0) body = "select {${1:cond} ${2:body}}";
  else if (strcmp(name, "case") == 0)  body = "case ${1:val} {${2:pat} ${3:body}}";
  else if (strcmp(name, "let") == 0)   body = "let {${1:bindings}} ${2:body}";
  else if (strcmp(name, "load") == 0)  body = "load \"${1:path}\"";
  else if (strcmp(name, "eval") == 0)  body = "eval ${1:expr}";
  else if (strcmp(name, "read") == 0)  body = "read ${1:string}";
  else if (strcmp(name, "quote") == 0) body = "quote ${1:expr}";
  else if (strcmp(name, "aio/let") == 0) body = "aio/let {${1:bindings}} ${2:body}";
  else if (strcmp(name, "aio/do") == 0)  body = "aio/do $0";
  else if (strcmp(name, "<-") == 0)    body = "<- ${1:handle}";
  if (!body) return false;
  if (wrap)
    snprintf(out, sz, "(%s)", body);
  else
    snprintf(out, sz, "%s", body);
  return true;
}

static bool generate_snippet_from_sig(const char *name, const char *sig,
                                      char *out, size_t out_size,
                                      bool wrap_parens) {
  char *p = out;
  char *pe = out + out_size - 1;

  if (wrap_parens) *p++ = '(';
  p += snprintf(p, pe - p, "%s", name);

  if (!sig || *sig != '(') return false;
  const char *s = sig + 1;
  while (*s && *s != ' ' && *s != ')') s++;
  if (*s != ' ') { *p = '\0'; return false; }

  int tab = 1;
  while (*s == ' ') s++;
  while (*s && *s != ')' && p < pe) {
    if (*s == '-' && s[1] == '>') break;

    const char *start = s;
    while (*s && *s != ' ' && *s != ')') s++;
    int len = (int)(s - start);

    if (len > 0 && !(len >= 3 && start[len - 3] == '.' &&
                      start[len - 2] == '.' && start[len - 1] == '.')) {
      if (start[0] == '{' || start[0] == '(' || start[0] == '[')
        return false;
      p += snprintf(p, pe - p, " ${%d:%.*s}", tab++, len, start);
    } else if (len > 0) {
      char clean[64];
      int clen = len >= 3 ? len - 3 : len;
      if (clen > 0 && clen < (int)sizeof(clean)) {
        memcpy(clean, start, clen);
        clean[clen] = '\0';
        p += snprintf(p, pe - p, " ${%d:%s}", tab++, clean);
      }
    }
    while (*s == ' ') s++;
  }

  if (wrap_parens && p < pe) *p++ = ')';
  *p = '\0';
  return tab > 1;
}

static void emit_text_edit(char **p, char *end, int line, int sc, int ec,
                           const char *text) {
  char *esc = json_escape_string(text);
  *p += snprintf(*p, end - *p,
    ",\"textEdit\":{\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
    "\"end\":{\"line\":%d,\"character\":%d}},\"newText\":%s}"
    ",\"insertTextFormat\":2", line, sc, line, ec, esc);
  free(esc);
}

static void completion_add_sym_doc(char **p, char *end, lsp_document_t *sdoc,
                                   lsp_symbol_t *sym, bool in_parens,
                                   int edit_line, int edit_start, int edit_end) {
  char snippet[4096];
  if (sym->src_start >= 0 && sym->src_end > sym->src_start &&
      sym->src_end <= (int)sdoc->text_len) {
    extract_source_snippet(sdoc->text, sym->src_start, sym->src_end,
                           snippet, sizeof(snippet));
  } else if (sym->doc) {
    snprintf(snippet, sizeof(snippet), "%s", sym->doc);
  } else {
    snippet[0] = '\0';
  }

  bool has_snippet = false;
  bool is_func = sym->arity >= 0;

  if (is_func && sym->doc) {
    const char *inner = strstr(sym->doc, "(fun (");
    if (inner) {
      const char *name_start = inner + 6;
      const char *sp = strchr(name_start, ' ');
      const char *close = sp ? strchr(sp, ')') : nullptr;
      if (sp && close) {
        char params[256];
        snprintf(params, sizeof(params), " (%.*s)", (int)(close - sp - 1), sp + 1);
        char *escaped_detail = json_escape_string(params);
        *p += snprintf(*p, end - *p, ",\"labelDetails\":{\"detail\":%s}", escaped_detail);
        free(escaped_detail);

        char inner_sig[512];
        snprintf(inner_sig, sizeof(inner_sig), "(%.*s)",
                 (int)(close + 1 - (inner + 5)), inner + 5);
        char snip[512];
        if (generate_snippet_from_sig(sym->name, inner_sig, snip, sizeof(snip), !in_parens)) {
          emit_text_edit(p, end, edit_line, edit_start, edit_end, snip);
          has_snippet = true;
        }
      }
    }
  }

  if (is_func && !has_snippet && !in_parens) {
    char snip[256];
    snprintf(snip, sizeof(snip), "(%s $0)", sym->name);
    emit_text_edit(p, end, edit_line, edit_start, edit_end, snip);
  }

  if (snippet[0]) {
    char md[4608];
    snprintf(md, sizeof(md), "```valk\n%s\n```", snippet);
    char *escaped_doc = json_escape_string(md);
    *p += snprintf(*p, end - *p,
      ",\"documentation\":{\"kind\":\"markdown\",\"value\":%s}", escaped_doc);
    free(escaped_doc);
  }
}

static void handle_completion(int id, json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  json_value_t *pos = json_get(params, "position");
  if (!td || !pos) { lsp_send_response(id, "[]"); return; }

  const char *uri = json_get_string(td, "uri");
  int line = json_get_int(pos, "line");
  int col = json_get_int(pos, "character");

  lsp_document_t *doc = uri ? doc_find(uri) : nullptr;

  size_t buf_size = 262144;
  char *buf = malloc(buf_size);
  char *p = buf;
  char *end_buf = buf + buf_size;
  *p++ = '[';

  int count = 0;
  char *prefix = nullptr;
  bool in_parens = false;
  int prefix_len = 0;
  int edit_start = col, edit_end = col;
  if (doc) {
    int offset = pos_to_offset(doc->text, line, col);
    prefix = get_word_at(doc->text, offset > 0 ? offset - 1 : 0);
    prefix_len = prefix ? (int)strlen(prefix) : 0;
    edit_start = col - prefix_len;
    int before = offset - prefix_len - 1;
    if (before >= 0 && doc->text[before] == '(')
      in_parens = true;
  }

  for (size_t i = 0; i < (doc ? doc->symbol_count : 0) && p < end_buf - 8192; i++) {
    if (prefix && strncmp(doc->symbols[i].name, prefix, strlen(prefix)) != 0)
      continue;
    if (count > 0) *p++ = ',';
    char *escaped = json_escape_string(doc->symbols[i].name);
    int kind = doc->symbols[i].arity >= 0 ? 3 : 6;
    p += snprintf(p, end_buf - p, "{\"label\":%s,\"kind\":%d", escaped, kind);
    free(escaped);
    completion_add_sym_doc(&p, end_buf, doc, &doc->symbols[i], in_parens,
                           line, edit_start, edit_end);
    *p++ = '}';
    count++;
  }

  for (size_t d = 0; d < g_store.count && p < end_buf - 8192; d++) {
    if (doc && &g_store.docs[d] == doc) continue;
    for (size_t i = 0; i < g_store.docs[d].symbol_count; i++) {
      if (prefix && strncmp(g_store.docs[d].symbols[i].name, prefix, strlen(prefix)) != 0)
        continue;
      if (count > 0) *p++ = ',';
      char *escaped = json_escape_string(g_store.docs[d].symbols[i].name);
      int kind = g_store.docs[d].symbols[i].arity >= 0 ? 3 : 6;
      p += snprintf(p, end_buf - p, "{\"label\":%s,\"kind\":%d", escaped, kind);
      free(escaped);
      completion_add_sym_doc(&p, end_buf, &g_store.docs[d],
                             &g_store.docs[d].symbols[i], in_parens,
                             line, edit_start, edit_end);
      *p++ = '}';
      count++;
    }
  }

  for (int i = 0; LSP_BUILTINS[i].name && p < end_buf - 8192; i++) {
    const lsp_builtin_entry_t *bi = &LSP_BUILTINS[i];
    if (prefix && strncmp(bi->name, prefix, strlen(prefix)) != 0)
      continue;
    if (count > 0) *p++ = ',';
    char *escaped = json_escape_string(bi->name);
    bool is_const = strcmp(bi->name, "true") == 0 ||
                    strcmp(bi->name, "false") == 0 ||
                    strcmp(bi->name, "nil") == 0 ||
                    strcmp(bi->name, "otherwise") == 0;
    int kind = is_const ? 21 : 3;
    p += snprintf(p, end_buf - p, "{\"label\":%s,\"kind\":%d", escaped, kind);
    free(escaped);
    const char *bdoc = builtin_doc(bi->name);
    const char *sig = bi->signature;
    bool has_snippet = false;

    if (sig && sig[0]) {
      char detail[280];
      snprintf(detail, sizeof(detail), " %s", sig);
      char *escaped_detail = json_escape_string(detail);
      p += snprintf(p, end_buf - p, ",\"labelDetails\":{\"detail\":%s}", escaped_detail);
      free(escaped_detail);

      char snip[512];
      if (special_form_snippet(bi->name, snip, sizeof(snip), !in_parens)) {
        emit_text_edit(&p, end_buf, line, edit_start, edit_end, snip);
        has_snippet = true;
      } else if (!is_const) {
        if (generate_snippet_from_sig(bi->name, sig, snip, sizeof(snip), !in_parens)) {
          emit_text_edit(&p, end_buf, line, edit_start, edit_end, snip);
          has_snippet = true;
        }
      }
    }

    if (bdoc) {
      const char *nl = strstr(bdoc, "\n\n");
      if (nl) {
        char md[2048];
        snprintf(md, sizeof(md), "```valk\n%s\n```\n\n%s", sig, nl + 2);
        char *escaped_doc = json_escape_string(md);
        p += snprintf(p, end_buf - p,
          ",\"documentation\":{\"kind\":\"markdown\",\"value\":%s}", escaped_doc);
        free(escaped_doc);
      } else {
        char md[2048];
        snprintf(md, sizeof(md), "```valk\n%s\n```\n\n%s", sig, bdoc);
        char *escaped_doc = json_escape_string(md);
        p += snprintf(p, end_buf - p,
          ",\"documentation\":{\"kind\":\"markdown\",\"value\":%s}", escaped_doc);
        free(escaped_doc);
      }
    }

    if (!has_snippet && !is_const && !in_parens) {
      char snip[256];
      snprintf(snip, sizeof(snip), "(%s$0)", bi->name);
      emit_text_edit(&p, end_buf, line, edit_start, edit_end, snip);
    }
    *p++ = '}';
    count++;
  }

  free(prefix);
  *p++ = ']';
  *p = '\0';
  lsp_send_response(id, buf);
  free(buf);
}

static const char *builtin_doc(const char *name) {
  if (!name) return nullptr;

  // Core special forms
  if (strcmp(name, "def") == 0) return "Define a global variable.";
  if (strcmp(name, "=") == 0) return "Bind a local variable.";
  if (strcmp(name, "\\") == 0) return "Create an anonymous function (lambda).";
  if (strcmp(name, "fun") == 0) return "Define a named function.";
  if (strcmp(name, "if") == 0) return "Conditional expression.";
  if (strcmp(name, "do") == 0) return "Evaluate expressions sequentially, return last.";
  if (strcmp(name, "select") == 0) return "Pattern matching / cond expression.";
  if (strcmp(name, "case") == 0) return "Case expression with value matching.";
  if (strcmp(name, "quote") == 0) return "Return expression unevaluated (Q-expression).";
  if (strcmp(name, "eval") == 0) return "Evaluate a Q-expression as code.";
  if (strcmp(name, "load") == 0) return "Load and evaluate a file.";
  if (strcmp(name, "read") == 0) return "Parse a string into a Q-expression.";
  if (strcmp(name, "let") == 0) return "Local bindings expression.";
  if (strcmp(name, "<-") == 0) return "Bind async handle result in aio/do block.";

  // List operations
  if (strcmp(name, "list") == 0) return "Create a Q-expression from arguments.";
  if (strcmp(name, "head") == 0) return "Return first element of a Q-expression.";
  if (strcmp(name, "tail") == 0) return "Return all elements except the first.";
  if (strcmp(name, "join") == 0) return "Concatenate Q-expressions.";
  if (strcmp(name, "cons") == 0) return "Prepend a value to a Q-expression.";
  if (strcmp(name, "len") == 0) return "Return length of a Q-expression or string.";
  if (strcmp(name, "init") == 0) return "Return all elements except the last.";
  if (strcmp(name, "range") == 0) return "Generate a list of integers [start, end).";
  if (strcmp(name, "repeat") == 0) return "Create a list with value repeated n times.";

  // I/O & strings
  if (strcmp(name, "print") == 0) return "Print a value without newline.";
  if (strcmp(name, "println") == 0) return "Print a value followed by newline.";
  if (strcmp(name, "printf") == 0) return "Formatted print (C-style format string).";
  if (strcmp(name, "str") == 0) return "Concatenate arguments as strings.";
  if (strcmp(name, "make-string") == 0) return "Repeat pattern n times into a string.";
  if (strcmp(name, "read-file") == 0) return "Read entire file contents as string.";
  if (strcmp(name, "error") == 0) return "Create an error value.";
  if (strcmp(name, "error?") == 0) return "Test if value is an error.";
  if (strcmp(name, "list?") == 0) return "Test if value is a Q-expression.";
  if (strcmp(name, "ref?") == 0) return "Test if value is an opaque reference.";

  // String operations
  if (strcmp(name, "str/split") == 0) return "Split string by delimiter.";
  if (strcmp(name, "str/replace") == 0) return "Replace occurrences in string.";
  if (strcmp(name, "str/slice") == 0) return "Extract substring.";
  if (strcmp(name, "str->num") == 0) return "Parse string to number.";
  if (strcmp(name, "ord") == 0) return "Compare two values by ordering.";

  // Arithmetic & comparison
  if (strcmp(name, "+") == 0) return "Addition.";
  if (strcmp(name, "-") == 0) return "Subtraction (or negation with 1 arg).";
  if (strcmp(name, "*") == 0) return "Multiplication.";
  if (strcmp(name, "/") == 0) return "Integer division.";
  if (strcmp(name, ">") == 0) return "Greater than.";
  if (strcmp(name, "<") == 0) return "Less than.";
  if (strcmp(name, ">=") == 0) return "Greater or equal.";
  if (strcmp(name, "<=") == 0) return "Less or equal.";
  if (strcmp(name, "==") == 0) return "Equality test.";
  if (strcmp(name, "!=") == 0) return "Inequality test.";

  // System
  if (strcmp(name, "time-us") == 0) return "Current time in microseconds.";
  if (strcmp(name, "sleep") == 0) return "Sleep for ms milliseconds (blocking).";
  if (strcmp(name, "exit") == 0) return "Exit process with status code.";
  if (strcmp(name, "shutdown") == 0) return "Alias for exit.";
  if (strcmp(name, "penv") == 0) return "Print the current environment.";
  if (strcmp(name, "stack-depth") == 0) return "Return current call stack depth.";
  if (strcmp(name, "sys/log/set-level") == 0) return "Set log level (debug/info/warn/error).";

  // Constants
  if (strcmp(name, "true") == 0) return "Boolean true constant.";
  if (strcmp(name, "false") == 0) return "Boolean false constant.";
  if (strcmp(name, "nil") == 0) return "Empty list / null value.";
  if (strcmp(name, "otherwise") == 0) return "Wildcard pattern for select/case (always true).";

  // Async
  if (strcmp(name, "aio/start") == 0) return "Create async I/O system. Config is optional plist.";
  if (strcmp(name, "aio/run") == 0) return "Run event loop (blocks until stopped).";
  if (strcmp(name, "aio/stop") == 0) return "Signal event loop to stop.";
  if (strcmp(name, "aio/await") == 0) return "Block until async handle completes, return result.";
  if (strcmp(name, "aio/sleep") == 0) return "Async sleep for ms milliseconds.";
  if (strcmp(name, "aio/let") == 0) return "Parallel async bindings with optional :then sequential phases.";
  if (strcmp(name, "aio/do") == 0) return "Sequential async block. Use <- to bind async results.";
  if (strcmp(name, "aio/all") == 0) return "Wait for all handles to complete.";
  if (strcmp(name, "aio/race") == 0) return "Resolve with first completed handle.";
  if (strcmp(name, "aio/any") == 0) return "Resolve with first successful handle.";
  if (strcmp(name, "aio/all-settled") == 0) return "Wait for all handles to settle (complete or fail).";
  if (strcmp(name, "aio/within") == 0) return "Timeout: fail if handle doesn't complete in ms.";
  if (strcmp(name, "aio/retry") == 0) return "Retry with exponential backoff.";
  if (strcmp(name, "aio/then") == 0) return "Chain: run f with result when handle completes.";
  if (strcmp(name, "aio/catch") == 0) return "Handle errors: run f if handle fails.";
  if (strcmp(name, "aio/finally") == 0) return "Run f when handle settles (success or failure).";
  if (strcmp(name, "aio/pure") == 0) return "Wrap a value in an immediately-resolved handle.";
  if (strcmp(name, "aio/fail") == 0) return "Create an immediately-failed handle.";
  if (strcmp(name, "aio/never") == 0) return "Create a handle that never completes.";
  if (strcmp(name, "aio/cancel") == 0) return "Cancel an async operation.";
  if (strcmp(name, "aio/status") == 0) return "Get handle status (:pending, :completed, :failed, :cancelled).";
  if (strcmp(name, "aio/result") == 0) return "Get result of completed handle.";
  if (strcmp(name, "aio/error") == 0) return "Get error of failed handle.";
  if (strcmp(name, "aio/cancelled?") == 0) return "Check if handle was cancelled.";
  if (strcmp(name, "aio/on-cancel") == 0) return "Register cancellation callback.";
  if (strcmp(name, "aio/bracket") == 0) return "Acquire/release resource pattern for async.";
  if (strcmp(name, "aio/scope") == 0) return "Run async operation with automatic cleanup.";
  if (strcmp(name, "aio/schedule") == 0) return "Schedule a callback after delay.";
  if (strcmp(name, "aio/interval") == 0) return "Schedule a repeating callback.";
  if (strcmp(name, "aio/traverse") == 0) return "Apply async function to each list element.";

  // Namespace-based fallbacks
  if (strncmp(name, "aio/", 4) == 0) return "Async I/O builtin.";
  if (strncmp(name, "http2/", 6) == 0) return "HTTP/2 builtin.";
  if (strncmp(name, "req/", 4) == 0) return "Request accessor builtin.";
  if (strncmp(name, "stream/", 7) == 0) return "Streaming response builtin.";
  if (strncmp(name, "sse/", 4) == 0) return "Server-Sent Events builtin.";
  if (strncmp(name, "metrics/", 8) == 0) return "Metrics/observability builtin.";
  if (strncmp(name, "test", 4) == 0) return "Testing framework builtin.";
  if (strncmp(name, "mem/", 4) == 0) return "Memory/GC introspection builtin.";
  if (strncmp(name, "ctx/", 4) == 0) return "Request context builtin.";
  if (strncmp(name, "vm/", 3) == 0) return "VM metrics builtin.";
  if (strncmp(name, "trace/", 6) == 0) return "Distributed tracing builtin.";
  if (strncmp(name, "coverage", 8) == 0) return "Coverage instrumentation builtin.";
  if (strncmp(name, "source-", 7) == 0) return "Source location introspection.";

  return nullptr;
}

static const char *extract_doc_comment(const char *text, int def_line) {
  if (def_line <= 0 || !text) return nullptr;

  const char *lines[64];
  int line_starts[64];
  int count = 0;

  int cur_line = 0;
  int i = 0;
  while (text[i] && cur_line < def_line) {
    int start = i;
    while (text[i] && text[i] != '\n') i++;
    if (cur_line >= def_line - 64 && cur_line < def_line) {
      int idx = count % 64;
      lines[idx] = text + start;
      line_starts[idx] = i - start;
      count++;
    }
    if (text[i]) i++;
    cur_line++;
  }

  if (count == 0) return nullptr;

  int end_idx = (count - 1) % 64;
  int start_idx = end_idx;
  int n_comment = 0;

  while (n_comment < count && n_comment < 10) {
    int idx = ((count - 1 - n_comment) % 64);
    const char *l = lines[idx];
    int llen = line_starts[idx];
    int j = 0;
    while (j < llen && (l[j] == ' ' || l[j] == '\t')) j++;
    if (j < llen && l[j] == ';') {
      start_idx = idx;
      n_comment++;
    } else if (j == llen) {
      break;
    } else {
      break;
    }
  }

  if (n_comment == 0) return nullptr;

  static char doc_buf[2048];
  char *p = doc_buf;
  char *pe = doc_buf + sizeof(doc_buf) - 1;

  for (int c = 0; c < n_comment && p < pe; c++) {
    int idx = (start_idx + c) % 64;
    const char *l = lines[idx];
    int llen = line_starts[idx];
    int j = 0;
    while (j < llen && (l[j] == ' ' || l[j] == '\t')) j++;
    if (j < llen && l[j] == ';') j++;
    if (j < llen && l[j] == ' ') j++;
    while (j < llen && p < pe)
      *p++ = l[j++];
    if (c < n_comment - 1 && p < pe)
      *p++ = '\n';
  }
  *p = '\0';
  return doc_buf;
}

static void extract_source_snippet(const char *text, int start, int end,
                                   char *out, size_t out_size) {
  int len = end - start;
  if (len <= 0 || !text) { out[0] = '\0'; return; }

  int max_lines = 8;
  int trunc_lines = 5;

  int nlines = 1;
  for (int i = start; i < end; i++)
    if (text[i] == '\n') nlines++;

  if (nlines <= max_lines && len < (int)out_size - 1) {
    memcpy(out, text + start, len);
    out[len] = '\0';
    return;
  }

  char *p = out;
  char *pe = out + out_size - 16;
  int line = 0;
  int i = start;

  while (i < end && line < trunc_lines && p < pe) {
    if (text[i] == '\n') {
      *p++ = '\n';
      line++;
    } else {
      *p++ = text[i];
    }
    i++;
  }

  if (i < end) {
    if (p > out && p[-1] != '\n') *p++ = '\n';
    memcpy(p, "  ...)", 6);
    p += 6;
  }
  *p = '\0';
}

static void handle_hover(int id, json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  json_value_t *pos = json_get(params, "position");
  if (!td || !pos) { lsp_send_response(id, "null"); return; }

  const char *uri = json_get_string(td, "uri");
  int line = json_get_int(pos, "line");
  int col = json_get_int(pos, "character");

  lsp_document_t *doc = uri ? doc_find(uri) : nullptr;
  if (!doc) { lsp_send_response(id, "null"); return; }

  int offset = pos_to_offset(doc->text, line, col);
  char *word = get_word_at(doc->text, offset);
  if (!word) { lsp_send_response(id, "null"); return; }

  char hover[8192];
  char *p = hover;
  char *pe = hover + sizeof(hover) - 1;
  bool found = false;

  for (size_t d = 0; d < g_store.count && !found; d++) {
    for (size_t i = 0; i < g_store.docs[d].symbol_count; i++) {
      if (strcmp(g_store.docs[d].symbols[i].name, word) != 0) continue;
      lsp_symbol_t *sym = &g_store.docs[d].symbols[i];

      char snippet[4096];
      if (sym->src_start >= 0 && sym->src_end > sym->src_start &&
          sym->src_end <= (int)g_store.docs[d].text_len) {
        extract_source_snippet(g_store.docs[d].text,
                               sym->src_start, sym->src_end,
                               snippet, sizeof(snippet));
      } else {
        snprintf(snippet, sizeof(snippet), "%s",
                 sym->doc ? sym->doc : word);
      }
      p += snprintf(p, pe - p, "```valk\n%s\n```", snippet);

      const char *doc_comment = extract_doc_comment(
        g_store.docs[d].text, sym->pos.line);
      if (doc_comment)
        p += snprintf(p, pe - p, "\n\n%s", doc_comment);

      const char *file = g_store.docs[d].uri;
      const char *fname = strrchr(file, '/');
      fname = fname ? fname + 1 : file;
      p += snprintf(p, pe - p, "\n\n*Defined in %s:%d*",
                    fname, sym->pos.line + 1);
      found = true;
      break;
    }
  }

  if (!found) {
    const lsp_builtin_entry_t *bi = nullptr;
    for (int i = 0; LSP_BUILTINS[i].name; i++) {
      if (strcmp(LSP_BUILTINS[i].name, word) == 0) {
        bi = &LSP_BUILTINS[i];
        break;
      }
    }
    if (bi) {
      p += snprintf(p, pe - p, "```valk\n%s\n```", bi->signature);
      const char *desc = builtin_doc(word);
      if (desc)
        p += snprintf(p, pe - p, "\n\n%s", desc);
      found = true;
    }
  }

  free(word);
  if (!found) { lsp_send_response(id, "null"); return; }

  *p = '\0';
  char *escaped = json_escape_string(hover);
  char buf[16384];
  snprintf(buf, sizeof(buf),
           "{\"contents\":{\"kind\":\"markdown\",\"value\":%s}}", escaped);
  free(escaped);
  lsp_send_response(id, buf);
}

static void handle_definition(int id, json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  json_value_t *pos = json_get(params, "position");
  if (!td || !pos) { lsp_send_response(id, "null"); return; }

  const char *uri = json_get_string(td, "uri");
  int line = json_get_int(pos, "line");
  int col = json_get_int(pos, "character");

  lsp_document_t *doc = uri ? doc_find(uri) : nullptr;
  if (!doc) { lsp_send_response(id, "null"); return; }

  int offset = pos_to_offset(doc->text, line, col);
  char *word = get_word_at(doc->text, offset);
  if (!word) { lsp_send_response(id, "null"); return; }

  for (size_t d = 0; d < g_store.count; d++) {
    for (size_t i = 0; i < g_store.docs[d].symbol_count; i++) {
      if (strcmp(g_store.docs[d].symbols[i].name, word) == 0) {
        char buf[4096];
        snprintf(buf, sizeof(buf),
                 "{\"uri\":\"%s\",\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
                 "\"end\":{\"line\":%d,\"character\":%d}}}",
                 g_store.docs[d].uri,
                 g_store.docs[d].symbols[i].pos.line,
                 g_store.docs[d].symbols[i].pos.col,
                 g_store.docs[d].symbols[i].pos.line,
                 g_store.docs[d].symbols[i].pos.col + (int)strlen(word));
        free(word);
        lsp_send_response(id, buf);
        return;
      }
    }
  }

  free(word);
  lsp_send_response(id, "null");
}

static void handle_document_symbol(int id, json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  if (!td) { lsp_send_response(id, "[]"); return; }

  const char *uri = json_get_string(td, "uri");
  lsp_document_t *doc = uri ? doc_find(uri) : nullptr;
  if (!doc) { lsp_send_response(id, "[]"); return; }

  char buf[65536];
  char *p = buf;
  char *end_buf = buf + sizeof(buf);
  *p++ = '[';

  for (size_t i = 0; i < doc->symbol_count && p < end_buf - 512; i++) {
    if (i > 0) *p++ = ',';
    char *escaped = json_escape_string(doc->symbols[i].name);
    int kind = doc->symbols[i].arity >= 0 ? 12 : 13;
    p += snprintf(p, end_buf - p,
                  "{\"name\":%s,\"kind\":%d,"
                  "\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
                  "\"end\":{\"line\":%d,\"character\":%d}},"
                  "\"selectionRange\":{\"start\":{\"line\":%d,\"character\":%d},"
                  "\"end\":{\"line\":%d,\"character\":%d}}}",
                  escaped, kind,
                  doc->symbols[i].pos.line, doc->symbols[i].pos.col,
                  doc->symbols[i].pos.line, doc->symbols[i].pos.col + (int)strlen(doc->symbols[i].name),
                  doc->symbols[i].pos.line, doc->symbols[i].pos.col,
                  doc->symbols[i].pos.line, doc->symbols[i].pos.col + (int)strlen(doc->symbols[i].name));
    free(escaped);
  }

  *p++ = ']';
  *p = '\0';
  lsp_send_response(id, buf);
}

static void handle_semantic_tokens(int id, json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  if (!td) { lsp_send_response(id, "{\"data\":[]}"); return; }

  const char *uri = json_get_string(td, "uri");
  lsp_document_t *doc = uri ? doc_find(uri) : nullptr;
  if (!doc || doc->sem_token_count == 0) {
    lsp_send_response(id, "{\"data\":[]}");
    return;
  }

  size_t max_len = 32 + doc->sem_token_count * 60;
  char *buf = malloc(max_len);
  char *p = buf;
  char *end = buf + max_len;

  p += snprintf(p, end - p, "{\"data\":[");

  int prev_line = 0, prev_col = 0;
  for (size_t i = 0; i < doc->sem_token_count && p < end - 64; i++) {
    if (i > 0) *p++ = ',';
    int dl = doc->sem_tokens[i].line - prev_line;
    int dc = dl == 0 ? doc->sem_tokens[i].col - prev_col : doc->sem_tokens[i].col;
    p += snprintf(p, end - p, "%d,%d,%d,%d,%d",
                  dl, dc, doc->sem_tokens[i].length,
                  doc->sem_tokens[i].type, doc->sem_tokens[i].modifiers);
    prev_line = doc->sem_tokens[i].line;
    prev_col = doc->sem_tokens[i].col;
  }

  p += snprintf(p, end - p, "]}");
  lsp_send_response(id, buf);
  free(buf);
}

// ---------------------------------------------------------------------------
// Main loop
// ---------------------------------------------------------------------------

int valk_lsp_main(int argc, char *argv[]) {
  (void)argc;
  (void)argv;

  fprintf(stderr, "[valk-lsp] starting\n");

  bool initialized = false;
  bool shutdown_requested = false;

  while (!shutdown_requested) {
    lsp_message_t msg = {0};
    if (!lsp_read_message(&msg)) break;

    json_value_t root = json_parse(msg.body, msg.len);
    const char *method = json_get_string(&root, "method");
    json_value_t *id_val = json_get(&root, "id");
    int id = id_val && id_val->type == JSON_NUMBER ? (int)id_val->number : -1;
    json_value_t *params = json_get(&root, "params");

    if (!method) {
      goto next;
    }

    fprintf(stderr, "[valk-lsp] <- %s\n", method);

    if (strcmp(method, "initialize") == 0) {
      if (params) {
        const char *root_uri = json_get_string(params, "rootUri");
        if (root_uri && strncmp(root_uri, "file://", 7) == 0)
          lsp_set_workspace_root(root_uri + 7);
      }
      handle_initialize(id);
      initialized = true;
    } else if (strcmp(method, "initialized") == 0) {
      // no-op
    } else if (strcmp(method, "shutdown") == 0) {
      lsp_send_response(id, "null");
      shutdown_requested = true;
    } else if (strcmp(method, "exit") == 0) {
      break;
    } else if (!initialized) {
      if (id >= 0)
        lsp_send_error(id, -32002, "Server not initialized");
    } else if (strcmp(method, "textDocument/didOpen") == 0) {
      handle_did_open(params);
    } else if (strcmp(method, "textDocument/didChange") == 0) {
      handle_did_change(params);
    } else if (strcmp(method, "textDocument/didClose") == 0) {
      handle_did_close(params);
    } else if (strcmp(method, "textDocument/didSave") == 0) {
      if (params) {
        json_value_t *td = json_get(params, "textDocument");
        const char *uri = td ? json_get_string(td, "uri") : nullptr;
        lsp_document_t *doc = uri ? doc_find(uri) : nullptr;
        if (doc) {
          const char *text = json_get_string(params, "text");
          if (text) {
            free(doc->text);
            doc->text = strdup(text);
            doc->text_len = strlen(text);
          }
          analyze_document(doc);
          publish_diagnostics(doc);
        }
      }
    } else if (strcmp(method, "textDocument/completion") == 0) {
      handle_completion(id, params);
    } else if (strcmp(method, "textDocument/hover") == 0) {
      handle_hover(id, params);
    } else if (strcmp(method, "textDocument/definition") == 0) {
      handle_definition(id, params);
    } else if (strcmp(method, "textDocument/documentSymbol") == 0) {
      handle_document_symbol(id, params);
    } else if (strcmp(method, "textDocument/semanticTokens/full") == 0) {
      handle_semantic_tokens(id, params);
    } else if (strncmp(method, "$/", 2) == 0 ||
               strncmp(method, "window/", 7) == 0 ||
               strncmp(method, "workspace/", 10) == 0 ||
               strncmp(method, "notebookDocument/", 17) == 0) {
    } else {
      if (id >= 0)
        lsp_send_error(id, -32601, "Method not found");
      else
        fprintf(stderr, "[valk-lsp] ignoring unknown notification: %s\n", method);
    }

  next:
    json_free(&root);
    lsp_message_free(&msg);
  }

  for (size_t i = 0; i < g_store.count; i++) {
    doc_symbols_clear(&g_store.docs[i]);
    doc_diag_clear(&g_store.docs[i]);
    free(g_store.docs[i].uri);
    free(g_store.docs[i].text);
    free(g_store.docs[i].symbols);
    free(g_store.docs[i].diag_messages);
    free(g_store.docs[i].diag_positions);
    free(g_store.docs[i].diag_severities);
    free(g_store.docs[i].diag_lengths);
    free(g_store.docs[i].sem_tokens);
  }
  free(g_store.docs);

  fprintf(stderr, "[valk-lsp] shutdown\n");
  return 0;
}
