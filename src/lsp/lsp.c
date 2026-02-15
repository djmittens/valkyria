#include "lsp.h"
#include "lsp_doc.h"
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

static void handle_completion(int id, json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  json_value_t *pos = json_get(params, "position");
  if (!td || !pos) { lsp_send_response(id, "[]"); return; }

  const char *uri = json_get_string(td, "uri");
  int line = json_get_int(pos, "line");
  int col = json_get_int(pos, "character");

  lsp_document_t *doc = uri ? doc_find(uri) : nullptr;

  char buf[65536];
  char *p = buf;
  char *end_buf = buf + sizeof(buf);
  *p++ = '[';

  int count = 0;
  char *prefix = nullptr;
  if (doc) {
    int offset = pos_to_offset(doc->text, line, col);
    prefix = get_word_at(doc->text, offset > 0 ? offset - 1 : 0);
  }

  for (size_t i = 0; i < (doc ? doc->symbol_count : 0) && p < end_buf - 256; i++) {
    if (prefix && strncmp(doc->symbols[i].name, prefix, strlen(prefix)) != 0)
      continue;
    if (count > 0) *p++ = ',';
    char *escaped = json_escape_string(doc->symbols[i].name);
    p += snprintf(p, end_buf - p,
                  "{\"label\":%s,\"kind\":3}", escaped);
    free(escaped);
    count++;
  }

  for (size_t d = 0; d < g_store.count && p < end_buf - 256; d++) {
    if (doc && &g_store.docs[d] == doc) continue;
    for (size_t i = 0; i < g_store.docs[d].symbol_count; i++) {
      if (prefix && strncmp(g_store.docs[d].symbols[i].name, prefix, strlen(prefix)) != 0)
        continue;
      if (count > 0) *p++ = ',';
      char *escaped = json_escape_string(g_store.docs[d].symbols[i].name);
      p += snprintf(p, end_buf - p,
                    "{\"label\":%s,\"kind\":3}", escaped);
      free(escaped);
      count++;
    }
  }

  for (int i = 0; BUILTIN_NAMES[i] && p < end_buf - 256; i++) {
    if (prefix && strncmp(BUILTIN_NAMES[i], prefix, strlen(prefix)) != 0)
      continue;
    if (count > 0) *p++ = ',';
    char *escaped = json_escape_string(BUILTIN_NAMES[i]);
    int kind = 21;
    if (strcmp(BUILTIN_NAMES[i], "true") == 0 ||
        strcmp(BUILTIN_NAMES[i], "false") == 0 ||
        strcmp(BUILTIN_NAMES[i], "nil") == 0 ||
        strcmp(BUILTIN_NAMES[i], "otherwise") == 0)
      kind = 21;
    else
      kind = 3;
    p += snprintf(p, end_buf - p,
                  "{\"label\":%s,\"kind\":%d}", escaped, kind);
    free(escaped);
    count++;
  }

  free(prefix);
  *p++ = ']';
  *p = '\0';
  lsp_send_response(id, buf);
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

  char hover_text[4096] = {0};

  for (size_t d = 0; d < g_store.count; d++) {
    for (size_t i = 0; i < g_store.docs[d].symbol_count; i++) {
      if (strcmp(g_store.docs[d].symbols[i].name, word) == 0) {
        if (g_store.docs[d].symbols[i].arity >= 0)
          snprintf(hover_text, sizeof(hover_text),
                   "(fun {%s ...}) — %d parameter(s)\\n\\nDefined in %s:%d",
                   word, g_store.docs[d].symbols[i].arity,
                   g_store.docs[d].uri, g_store.docs[d].symbols[i].pos.line + 1);
        else
          snprintf(hover_text, sizeof(hover_text),
                   "(def {%s} ...)\\n\\nDefined in %s:%d",
                   word, g_store.docs[d].uri, g_store.docs[d].symbols[i].pos.line + 1);
        goto found;
      }
    }
  }

  for (int i = 0; BUILTIN_NAMES[i]; i++) {
    if (strcmp(BUILTIN_NAMES[i], word) == 0) {
      snprintf(hover_text, sizeof(hover_text), "**%s** — builtin", word);
      goto found;
    }
  }

  free(word);
  lsp_send_response(id, "null");
  return;

found:
  free(word);
  char buf[8192];
  snprintf(buf, sizeof(buf),
           "{\"contents\":{\"kind\":\"markdown\",\"value\":\"%s\"}}",
           hover_text);
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
