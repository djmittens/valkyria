#include "lsp_doc.h"
#include "lsp_io.h"
#include "lsp_json.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

  int comment_lines[10];
  int n_actual = 0;
  int scan = 0;

  while (scan < count && scan < 10) {
    int idx = ((count - 1 - scan) % 64);
    const char *l = lines[idx];
    int llen = line_starts[idx];
    int j = 0;
    while (j < llen && (l[j] == ' ' || l[j] == '\t')) j++;
    if (j < llen && l[j] == ';') {
      comment_lines[n_actual++] = idx;
    } else if (j == llen) {
      break;
    } else if (j + 4 < llen && l[j] == '(' && l[j+1] == 's' &&
               l[j+2] == 'i' && l[j+3] == 'g' && l[j+4] == ' ') {
      /* skip (sig ...) lines between comment and definition */
    } else {
      break;
    }
    scan++;
  }

  if (n_actual == 0) return nullptr;

  static char doc_buf[2048];
  char *p = doc_buf;
  char *pe = doc_buf + sizeof(doc_buf) - 1;

  for (int c = n_actual - 1; c >= 0 && p < pe; c--) {
    const char *l = lines[comment_lines[c]];
    int llen = line_starts[comment_lines[c]];
    int j = 0;
    while (j < llen && (l[j] == ' ' || l[j] == '\t')) j++;
    if (j < llen && l[j] == ';') j++;
    if (j < llen && l[j] == ' ') j++;
    while (j < llen && p < pe)
      *p++ = l[j++];
    if (c > 0 && p < pe)
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
