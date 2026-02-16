#include "lsp_doc.h"
#include "lsp_builtins_gen.h"
#include "lsp_types.h"
#include "lsp_io.h"
#include "lsp_json.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// Builtin documentation tables
// ---------------------------------------------------------------------------

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

const char *builtin_doc(const char *name) {
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

// ---------------------------------------------------------------------------
// Doc comment extraction
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Source snippet extraction
// ---------------------------------------------------------------------------

void extract_source_snippet(const char *text, int start, int end,
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

// ---------------------------------------------------------------------------
// Hover handler
// ---------------------------------------------------------------------------

void handle_hover(int id, void *params_raw, void *store_raw) {
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

  char hover[8192];
  char *p = hover;
  char *pe = hover + sizeof(hover) - 1;
  bool found = false;

  for (size_t d = 0; d < store->count && !found; d++) {
    for (size_t i = 0; i < store->docs[d].symbol_count; i++) {
      if (strcmp(store->docs[d].symbols[i].name, word) != 0) continue;
      lsp_symbol_t *sym = &store->docs[d].symbols[i];

      char snippet[4096];
      if (sym->src_start >= 0 && sym->src_end > sym->src_start &&
          sym->src_end <= (int)store->docs[d].text_len) {
        extract_source_snippet(store->docs[d].text,
                               sym->src_start, sym->src_end,
                               snippet, sizeof(snippet));
      } else {
        snprintf(snippet, sizeof(snippet), "%s",
                 sym->doc ? sym->doc : word);
      }
      p += snprintf(p, pe - p, "```valk\n%s\n```", snippet);

      int sym_off = lsp_find_sym_offset(store->docs[d].text, sym->name, sym->src_start);
      char *type_str = sym_off >= 0 ? lsp_type_at_pos(&store->docs[d], sym_off) : nullptr;
      if (type_str) {
        p += snprintf(p, pe - p, "\n\n**Type:** `%s`", type_str);
        free(type_str);
      }

      const char *doc_comment = extract_doc_comment(
        store->docs[d].text, sym->pos.line);
      if (doc_comment)
        p += snprintf(p, pe - p, "\n\n%s", doc_comment);

      const char *file = store->docs[d].uri;
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

// ---------------------------------------------------------------------------
// Definition handler
// ---------------------------------------------------------------------------

void handle_definition(int id, void *params_raw, void *store_raw) {
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

  for (size_t d = 0; d < store->count; d++) {
    for (size_t i = 0; i < store->docs[d].symbol_count; i++) {
      if (strcmp(store->docs[d].symbols[i].name, word) == 0) {
        char buf[4096];
        snprintf(buf, sizeof(buf),
                 "{\"uri\":\"%s\",\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
                 "\"end\":{\"line\":%d,\"character\":%d}}}",
                 store->docs[d].uri,
                 store->docs[d].symbols[i].pos.line,
                 store->docs[d].symbols[i].pos.col,
                 store->docs[d].symbols[i].pos.line,
                 store->docs[d].symbols[i].pos.col + (int)strlen(word));
        free(word);
        lsp_send_response(id, buf);
        return;
      }
    }
  }

  free(word);
  lsp_send_response(id, "null");
}
