#include "lsp.h"
#include "lsp_doc.h"
#include "lsp_io.h"
#include "lsp_json.h"
#include "lsp_types.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
        "\"referencesProvider\":true,"
        "\"renameProvider\":{\"prepareProvider\":true},"
        "\"documentSymbolProvider\":true,"
        "\"workspaceSymbolProvider\":true,"
        "\"inlayHintProvider\":true,"
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
  doc->is_background = false;
  analyze_document(doc);
  publish_diagnostics(doc);
  lsp_db_sync_document(doc);
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
  lsp_db_sync_document(doc);
}

static void handle_did_close(json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  if (!td) return;
  const char *uri = json_get_string(td, "uri");
  if (!uri) return;

  lsp_document_t *doc = doc_store_find(&g_store, uri);
  if (doc)
    doc->is_background = true;
}

static void handle_did_save(json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  const char *uri = td ? json_get_string(td, "uri") : nullptr;
  lsp_document_t *doc = uri ? doc_store_find(&g_store, uri) : nullptr;
  if (!doc) return;
  const char *text = json_get_string(params, "text");
  if (text) {
    free(doc->text);
    doc->text = strdup(text);
    doc->text_len = strlen(text);
  }
  analyze_document(doc);
  publish_diagnostics(doc);
  lsp_db_sync_document(doc);
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

static void handle_inlay_hint_impl(int id, json_value_t *params) {
  json_value_t *td = json_get(params, "textDocument");
  if (!td) { lsp_send_response(id, "[]"); return; }

  const char *uri = json_get_string(td, "uri");
  lsp_document_t *doc = uri ? doc_store_find(&g_store, uri) : nullptr;
  if (!doc) { lsp_send_response(id, "[]"); return; }

  lsp_inlay_hint_t *hints = nullptr;
  size_t hint_count = 0;
  lsp_collect_inlay_hints(doc, &hints, &hint_count);

  if (hint_count == 0) {
    lsp_send_response(id, "[]");
    free(hints);
    return;
  }

  size_t max_len = 64 + hint_count * 256;
  char *buf = malloc(max_len);
  char *p = buf;
  char *end = buf + max_len;

  *p++ = '[';
  for (size_t i = 0; i < hint_count && p < end - 256; i++) {
    if (i > 0) *p++ = ',';
    lsp_pos_t pos = offset_to_pos(doc->text, hints[i].offset);
    char *escaped = json_escape_string(hints[i].label);
    p += snprintf(p, end - p,
      "{\"position\":{\"line\":%d,\"character\":%d},"
      "\"label\":%s,"
      "\"kind\":%d,"
      "\"paddingLeft\":true,"
      "\"paddingRight\":false}",
      pos.line, pos.col, escaped, hints[i].kind);
    free(escaped);
  }
  *p++ = ']';
  *p = '\0';

  lsp_send_response(id, buf);
  free(buf);

  for (size_t i = 0; i < hint_count; i++)
    free(hints[i].label);
  free(hints);
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
        if (root_uri && strncmp(root_uri, "file://", 7) == 0) {
          const char *path = root_uri + 7;
          lsp_set_workspace_root(path);
          lsp_workspace_set_root(path);
          lsp_db_init(path);
        }
      }
      handle_initialize(id);
      initialized = true;
    } else if (strcmp(method, "initialized") == 0) {
      lsp_workspace_scan(&g_store);
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
      handle_did_save(params);
    } else if (strcmp(method, "textDocument/completion") == 0) {
      handle_completion(id, params, &g_store);
    } else if (strcmp(method, "textDocument/hover") == 0) {
      handle_hover(id, params, &g_store);
    } else if (strcmp(method, "textDocument/definition") == 0) {
      handle_definition(id, params, &g_store);
    } else if (strcmp(method, "textDocument/references") == 0) {
      handle_references(id, params, &g_store);
    } else if (strcmp(method, "textDocument/prepareRename") == 0) {
      handle_prepare_rename(id, params, &g_store);
    } else if (strcmp(method, "textDocument/rename") == 0) {
      handle_rename(id, params, &g_store);
    } else if (strcmp(method, "textDocument/documentSymbol") == 0) {
      handle_document_symbol(id, params);
    } else if (strcmp(method, "textDocument/semanticTokens/full") == 0) {
      handle_semantic_tokens(id, params);
    } else if (strcmp(method, "textDocument/inlayHint") == 0) {
      handle_inlay_hint_impl(id, params);
    } else if (strcmp(method, "workspace/symbol") == 0) {
      handle_workspace_symbol(id, params, &g_store);
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

  lsp_db_shutdown();
  doc_store_free(&g_store);

  fprintf(stderr, "[valk-lsp] shutdown\n");
  return 0;
}
