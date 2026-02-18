#include "lsp_doc.h"
#include "lsp_io.h"
#include "lsp_json.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// Snippet generation
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Completion for user-defined symbols
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Completion handler
// ---------------------------------------------------------------------------

void handle_completion(int id, void *params_raw, void *store_raw) {
  json_value_t *params = params_raw;
  lsp_doc_store_t *store = store_raw;

  json_value_t *td = json_get(params, "textDocument");
  json_value_t *pos = json_get(params, "position");
  if (!td || !pos) { lsp_send_response(id, "[]"); return; }

  const char *uri = json_get_string(td, "uri");
  int line = json_get_int(pos, "line");
  int col = json_get_int(pos, "character");

  lsp_document_t *doc = uri ? doc_store_find(store, uri) : nullptr;

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

  for (size_t d = 0; d < store->count && p < end_buf - 8192; d++) {
    if (doc && &store->docs[d] == doc) continue;
    for (size_t i = 0; i < store->docs[d].symbol_count; i++) {
      const char *sym_name = store->docs[d].symbols[i].name;
      if (prefix && strncmp(sym_name, prefix, strlen(prefix)) != 0)
        continue;
      if (count > 0) *p++ = ',';

      bool is_bi = lsp_is_builtin(sym_name);
      bool is_const = strcmp(sym_name, "true") == 0 ||
                      strcmp(sym_name, "false") == 0 ||
                      strcmp(sym_name, "nil") == 0 ||
                      strcmp(sym_name, "otherwise") == 0;
      int kind = is_const ? 21 : (store->docs[d].symbols[i].arity >= 0 ? 3 : 6);

      char *escaped = json_escape_string(sym_name);
      p += snprintf(p, end_buf - p, "{\"label\":%s,\"kind\":%d", escaped, kind);
      free(escaped);

      if (is_bi) {
        bool has_snippet = false;
        char snip[512];
        if (special_form_snippet(sym_name, snip, sizeof(snip), !in_parens)) {
          emit_text_edit(&p, end_buf, line, edit_start, edit_end, snip);
          has_snippet = true;
        }

        const char *sig_doc = store->docs[d].symbols[i].doc;
        if (sig_doc && strncmp(sig_doc, "(sig ", 5) == 0) {
          char detail[280];
          snprintf(detail, sizeof(detail), " %s", sig_doc);
          char *escaped_detail = json_escape_string(detail);
          p += snprintf(p, end_buf - p, ",\"labelDetails\":{\"detail\":%s}",
                        escaped_detail);
          free(escaped_detail);
        }

        if (!has_snippet && !is_const && !in_parens) {
          snprintf(snip, sizeof(snip), "(%s $0)", sym_name);
          emit_text_edit(&p, end_buf, line, edit_start, edit_end, snip);
        }
      } else {
        completion_add_sym_doc(&p, end_buf, &store->docs[d],
                               &store->docs[d].symbols[i], in_parens,
                               line, edit_start, edit_end);
      }
      *p++ = '}';
      count++;
    }
  }

  free(prefix);
  *p++ = ']';
  *p = '\0';
  lsp_send_response(id, buf);
  free(buf);
}
