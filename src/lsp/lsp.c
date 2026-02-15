#include "lsp.h"
#include "lsp_doc.h"
#include "lsp_builtins_gen.h"
#include "lsp_types.h"
#include "lsp_io.h"
#include "lsp_json.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../parser.h"

static lsp_doc_store_t g_store = {0};

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
              "\"comment\",\"type\",\"macro\",\"property\","
              "\"enumMember\",\"typeParameter\"],"
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

  lsp_document_t *doc = doc_store_open(&g_store, uri, text, version);
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

  lsp_document_t *doc = doc_store_open(&g_store, uri, text, version);
  analyze_document(doc);
  publish_diagnostics(doc);
}

static void handle_did_close(json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  if (!td) return;
  const char *uri = json_get_string(td, "uri");
  if (uri) doc_store_close(&g_store, uri);
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

  lsp_document_t *doc = uri ? doc_store_find(&g_store, uri) : nullptr;

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
      {
        type_arena_t ta;
        type_arena_init(&ta);
        typed_scope_t *ts = typed_scope_push(&ta, nullptr);
        lsp_builtin_schemes_init(&ta, ts);
        type_scheme_t *sch = typed_scope_lookup(ts, bi->name);
        if (sch) {
          valk_type_t *fn = ty_resolve(scheme_instantiate(&ta, sch));
          if (fn->kind == TY_FUN) {
            char *ret_str = valk_type_display_pretty(fn->fun.ret);
            snprintf(detail, sizeof(detail), " %s -> %s", sig, ret_str);
            free(ret_str);
          } else {
            snprintf(detail, sizeof(detail), " %s", sig);
          }
        } else {
          snprintf(detail, sizeof(detail), " %s", sig);
        }
        typed_scope_pop(ts);
        type_arena_free(&ta);
      }
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

static const struct { const char *name; const char *doc; } BUILTIN_DOCS[] = {
  {"!", "Logical NOT."},
  {"!=", "Inequality test."},
  {"*", "Multiplication."},
  {"+", "Addition."},
  {"-", "Subtraction (or negation with 1 arg)."},
  {"/", "Integer division."},
  {"<", "Less than."},
  {"<-", "Bind async handle result in aio/do block."},
  {"<=", "Less or equal."},
  {"=", "Bind a local variable."},
  {"==", "Equality test."},
  {">", "Greater than."},
  {">=", "Greater or equal."},
  {"\\", "Create an anonymous function (lambda)."},
  {"aio/all", "Wait for all handles to complete."},
  {"aio/all-settled", "Wait for all handles to settle (complete or fail)."},
  {"aio/any", "Resolve with first successful handle."},
  {"aio/await", "Block until async handle completes, return result."},
  {"aio/bracket", "Acquire/release resource pattern for async."},
  {"aio/cancel", "Cancel an async operation."},
  {"aio/cancelled?", "Check if handle was cancelled."},
  {"aio/catch", "Handle errors: run f if handle fails."},
  {"aio/do", "Sequential async block. Use <- to bind async results."},
  {"aio/error", "Get error of failed handle."},
  {"aio/fail", "Create an immediately-failed handle."},
  {"aio/finally", "Run f when handle settles (success or failure)."},
  {"aio/interval", "Schedule a repeating callback."},
  {"aio/let", "Parallel async bindings with optional :then sequential phases."},
  {"aio/never", "Create a handle that never completes."},
  {"aio/on-cancel", "Register cancellation callback."},
  {"aio/pure", "Wrap a value in an immediately-resolved handle."},
  {"aio/race", "Resolve with first completed handle."},
  {"aio/result", "Get result of completed handle."},
  {"aio/retry", "Retry with exponential backoff."},
  {"aio/run", "Run event loop (blocks until stopped)."},
  {"aio/schedule", "Schedule a callback after delay."},
  {"aio/scope", "Run async operation with automatic cleanup."},
  {"aio/sleep", "Async sleep for ms milliseconds."},
  {"aio/start", "Create async I/O system. Config is optional plist."},
  {"aio/status", "Get handle status (:pending, :completed, :failed, :cancelled)."},
  {"aio/stop", "Signal event loop to stop."},
  {"aio/then", "Chain: run f with result when handle completes."},
  {"aio/traverse", "Apply async function to each list element."},
  {"aio/within", "Timeout: fail if handle doesn't complete in ms."},
  {"case", "Case expression with value matching."},
  {"cons", "Prepend a value to a Q-expression."},
  {"def", "Define a global variable."},
  {"do", "Evaluate expressions sequentially, return last."},
  {"error", "Create an error value."},
  {"error?", "Test if value is an error."},
  {"eval", "Evaluate a Q-expression as code."},
  {"exit", "Exit process with status code."},
  {"false", "Boolean false constant."},
  {"fun", "Define a named function."},
  {"head", "Return first element of a Q-expression."},
  {"if", "Conditional expression."},
  {"init", "Return all elements except the last."},
  {"join", "Concatenate Q-expressions."},
  {"len", "Return length of a Q-expression or string."},
  {"let", "Local bindings expression."},
  {"list", "Create a Q-expression from arguments."},
  {"list?", "Test if value is a Q-expression."},
  {"load", "Load and evaluate a file."},
  {"make-string", "Repeat pattern n times into a string."},
  {"nil", "Empty list / null value."},
  {"ord", "Compare two values by ordering."},
  {"otherwise", "Wildcard pattern for select/case (always true)."},
  {"penv", "Print the current environment."},
  {"print", "Print a value without newline."},
  {"printf", "Formatted print (C-style format string)."},
  {"println", "Print a value followed by newline."},
  {"range", "Generate a list of integers [start, end)."},
  {"read", "Parse a string into a Q-expression."},
  {"read-file", "Read entire file contents as string."},
  {"ref?", "Test if value is an opaque reference."},
  {"repeat", "Create a list with value repeated n times."},
  {"select", "Pattern matching / cond expression."},
  {"shutdown", "Alias for exit."},
  {"sleep", "Sleep for ms milliseconds (blocking)."},
  {"stack-depth", "Return current call stack depth."},
  {"str", "Concatenate arguments as strings."},
  {"str->num", "Parse string to number."},
  {"str/replace", "Replace occurrences in string."},
  {"str/slice", "Extract substring."},
  {"str/split", "Split string by delimiter."},
  {"sys/log/set-level", "Set log level (debug/info/warn/error)."},
  {"tail", "Return all elements except the first."},
  {"time-us", "Current time in microseconds."},
  {"true", "Boolean true constant."},
};

static const struct { const char *prefix; const char *doc; } NAMESPACE_DOCS[] = {
  {"aio/", "Async I/O builtin."},
  {"coverage", "Coverage instrumentation builtin."},
  {"ctx/", "Request context builtin."},
  {"http2/", "HTTP/2 builtin."},
  {"mem/", "Memory/GC introspection builtin."},
  {"metrics/", "Metrics/observability builtin."},
  {"req/", "Request accessor builtin."},
  {"source-", "Source location introspection."},
  {"sse/", "Server-Sent Events builtin."},
  {"stream/", "Streaming response builtin."},
  {"test", "Testing framework builtin."},
  {"trace/", "Distributed tracing builtin."},
  {"vm/", "VM metrics builtin."},
};

static const char *builtin_doc(const char *name) {
  if (!name) return nullptr;

  int lo = 0, hi = (int)(sizeof(BUILTIN_DOCS) / sizeof(BUILTIN_DOCS[0])) - 1;
  while (lo <= hi) {
    int mid = (lo + hi) / 2;
    int cmp = strcmp(name, BUILTIN_DOCS[mid].name);
    if (cmp == 0) return BUILTIN_DOCS[mid].doc;
    if (cmp < 0) hi = mid - 1;
    else lo = mid + 1;
  }

  for (size_t i = 0; i < sizeof(NAMESPACE_DOCS) / sizeof(NAMESPACE_DOCS[0]); i++)
    if (strncmp(name, NAMESPACE_DOCS[i].prefix, strlen(NAMESPACE_DOCS[i].prefix)) == 0)
      return NAMESPACE_DOCS[i].doc;

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

  lsp_document_t *doc = uri ? doc_store_find(&g_store, uri) : nullptr;
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

      int sym_off = lsp_find_sym_offset(g_store.docs[d].text, sym->name, sym->src_start);
      char *type_str = sym_off >= 0 ? lsp_type_at_pos(&g_store.docs[d], sym_off) : nullptr;
      if (type_str) {
        p += snprintf(p, pe - p, "\n\n**Type:** `%s`", type_str);
        free(type_str);
      }

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
      type_arena_t ta;
      type_arena_init(&ta);
      typed_scope_t *ts = typed_scope_push(&ta, nullptr);
      lsp_builtin_schemes_init(&ta, ts);
      type_scheme_t *sch = typed_scope_lookup(ts, bi->name);
      if (sch) {
        valk_type_t *fn = ty_resolve(scheme_instantiate(&ta, sch));
        if (fn->kind == TY_FUN) {
          char *ret_str = valk_type_display_pretty(fn->fun.ret);
          p += snprintf(p, pe - p, "```valk\n%s -> %s\n```", bi->signature, ret_str);
          free(ret_str);
        } else {
          p += snprintf(p, pe - p, "```valk\n%s\n```", bi->signature);
        }
      } else {
        p += snprintf(p, pe - p, "```valk\n%s\n```", bi->signature);
      }
      typed_scope_pop(ts);
      type_arena_free(&ta);
      const char *desc = builtin_doc(word);
      if (desc)
        p += snprintf(p, pe - p, "\n\n%s", desc);
      found = true;
    }
  }

  if (!found) {
    char *type_str = lsp_type_at_pos(doc, offset);
    if (type_str) {
      p += snprintf(p, pe - p, "```valk\n%s :: %s\n```", word, type_str);
      free(type_str);
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

  lsp_document_t *doc = uri ? doc_store_find(&g_store, uri) : nullptr;
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
  lsp_document_t *doc = uri ? doc_store_find(&g_store, uri) : nullptr;
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
  lsp_document_t *doc = uri ? doc_store_find(&g_store, uri) : nullptr;
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
        lsp_document_t *doc = uri ? doc_store_find(&g_store, uri) : nullptr;
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

  doc_store_free(&g_store);

  fprintf(stderr, "[valk-lsp] shutdown\n");
  return 0;
}
