#include "lsp_doc.h"
#include "lsp_builtins_gen.h"
#include "lsp_types.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../parser.h"

// ---------------------------------------------------------------------------
// Type checking pass
// ---------------------------------------------------------------------------

static void check_types(lsp_document_t *doc) {
  type_arena_t arena;
  type_arena_init(&arena);

  typed_scope_t *top = typed_scope_push(&arena, nullptr);
  plist_type_reg_t plist_regs[MAX_PLIST_TYPES];
  int plist_count = 0;
  init_typed_scope_with_plist_reg(&arena, top, doc, plist_regs, &plist_count);

  const char *text = doc->text;
  int pos = 0;
  int len = (int)doc->text_len;
  int cursor = 0;

  infer_ctx_t ctx = {
    .arena = &arena,
    .scope = top,
    .doc = doc,
    .text = text,
    .cursor = &cursor,
    .floor_var_id = arena.next_var_id,
    .hover_offset = -1,
    .hover_result = nullptr,
    .hints = nullptr,
    .hint_count = 0,
    .hint_cap = 0,
    .collect_hints = true,
    .plist_type_count = plist_count,
  };
  memcpy(ctx.plist_types, plist_regs, plist_count * sizeof(plist_type_reg_t));

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

    infer_expr(&ctx, expr);
  }

  for (size_t i = 0; i < ctx.hint_count; i++) {
    if (ctx.hints[i].kind == INLAY_PARAM) { free(ctx.hints[i].label); continue; }
    valk_type_t *ty = ctx.hints[i].type ? ty_resolve(ctx.hints[i].type) : nullptr;
    if (!ty || !ty_has_inference_failure(ty) || ctx.hints[i].is_return) continue;
    int end = ctx.hints[i].offset;
    int start = end - 1;
    while (start > 0 && text[start - 1] != ' ' && text[start - 1] != '('
           && text[start - 1] != '{' && text[start - 1] != '\t'
           && text[start - 1] != '\n' && text[start - 1] != '\r')
      start--;
    int sym_len = end - start;
    if (sym_len > 0 && sym_len < 128) {
      lsp_pos_t p = offset_to_pos(text, start);
      doc_add_diag_full(doc, "Type resolves to ??", p.line, p.col, sym_len, 1);
    }
  }

  free(ctx.hints);
  typed_scope_pop(top);
  type_arena_free(&arena);
}

// ---------------------------------------------------------------------------
// Inlay hints — collect type annotations for all bindings
// ---------------------------------------------------------------------------

void lsp_collect_inlay_hints(lsp_document_t *doc,
                             lsp_inlay_hint_t **out_hints, size_t *out_count) {
  type_arena_t arena;
  type_arena_init(&arena);

  typed_scope_t *top = typed_scope_push(&arena, nullptr);
  plist_type_reg_t plist_regs2[MAX_PLIST_TYPES];
  int plist_count2 = 0;
  init_typed_scope_with_plist_reg(&arena, top, doc, plist_regs2, &plist_count2);

  const char *text = doc->text;
  int pos = 0;
  int len = (int)doc->text_len;
  int cursor = 0;

  infer_ctx_t ctx = {
    .arena = &arena,
    .scope = top,
    .doc = doc,
    .text = text,
    .cursor = &cursor,
    .floor_var_id = arena.next_var_id,
    .hover_offset = -1,
    .hover_result = nullptr,
    .hints = nullptr,
    .hint_count = 0,
    .hint_cap = 0,
    .collect_hints = true,
    .plist_type_count = plist_count2,
  };
  memcpy(ctx.plist_types, plist_regs2, plist_count2 * sizeof(plist_type_reg_t));

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

    infer_expr(&ctx, expr);
  }

  size_t out_n = 0;
  for (size_t i = 0; i < ctx.hint_count; i++) {
    if (ctx.hints[i].kind == INLAY_PARAM) {
      if (!ctx.hints[i].label) continue;
      char buf[128];
      snprintf(buf, sizeof(buf), "%s:", ctx.hints[i].label);
      free(ctx.hints[i].label);
      ctx.hints[out_n] = ctx.hints[i];
      ctx.hints[out_n].label = strdup(buf);
      out_n++;
      continue;
    }
    valk_type_t *ty = ctx.hints[i].type ? ty_resolve(ctx.hints[i].type) : nullptr;
    if (!ty || ty->kind == TY_VAR || ty->kind == TY_ANY) continue;
    char *display = valk_type_display_pretty(ty);
    char buf[256];
    snprintf(buf, sizeof(buf), "%s %s", ctx.hints[i].is_return ? "->" : "::", display);
    free(display);
    ctx.hints[out_n] = ctx.hints[i];
    ctx.hints[out_n].label = strdup(buf);
    out_n++;
  }
  *out_hints = ctx.hints;
  *out_count = out_n;

  typed_scope_pop(top);
  type_arena_free(&arena);
}

// ---------------------------------------------------------------------------
// Type-at-position query for hover
// ---------------------------------------------------------------------------

char *lsp_type_at_pos(lsp_document_t *doc, int offset) {
  type_arena_t arena;
  type_arena_init(&arena);

  typed_scope_t *top = typed_scope_push(&arena, nullptr);
  plist_type_reg_t plist_regs3[MAX_PLIST_TYPES];
  int plist_count3 = 0;
  init_typed_scope_with_plist_reg(&arena, top, doc, plist_regs3, &plist_count3);

  const char *text = doc->text;
  int pos = 0;
  int len = (int)doc->text_len;
  int cursor = 0;

  infer_ctx_t ctx = {
    .arena = &arena,
    .scope = top,
    .doc = doc,
    .text = text,
    .cursor = &cursor,
    .floor_var_id = arena.next_var_id,
    .hover_offset = offset,
    .hover_result = nullptr,
    .plist_type_count = plist_count3,
  };
  memcpy(ctx.plist_types, plist_regs3, plist_count3 * sizeof(plist_type_reg_t));

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

    infer_expr(&ctx, expr);
  }

  char *result = nullptr;
  if (ctx.hover_result)
    result = valk_type_display_pretty(ctx.hover_result);

  typed_scope_pop(top);
  type_arena_free(&arena);
  return result;
}

// ---------------------------------------------------------------------------
// Symbol extraction for document outline
// ---------------------------------------------------------------------------

static void extract_symbols_visitor(valk_lval_t *expr, lsp_document_t *doc,
                                    int form_start) {
  const char *text = doc->text;

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = valk_lval_head(expr);
  if (!head || LVAL_TYPE(head) != LVAL_SYM) return;

  int tmp = form_start;
  valk_lval_read(&tmp, text);
  int pos_end = tmp;

  if (strcmp(head->str, "def") == 0 || strcmp(head->str, "fun") == 0) {
    valk_lval_t *tail = valk_lval_tail(expr);
    if (LVAL_TYPE(tail) != LVAL_CONS) return;
    valk_lval_t *binding = valk_lval_head(tail);
    if (!binding) return;

    const char *sym_name = nullptr;
    int arity = -1;

    if (LVAL_TYPE(binding) == LVAL_CONS) {
      valk_lval_t *first = valk_lval_head(binding);
      if (first && LVAL_TYPE(first) == LVAL_SYM) {
        sym_name = first->str;
        if (strcmp(head->str, "fun") == 0) {
          int n = 0;
          valk_lval_t *pc = valk_lval_tail(binding);
          while (pc && LVAL_TYPE(pc) == LVAL_CONS) {
            valk_lval_t *ph = valk_lval_head(pc);
            if (ph && LVAL_TYPE(ph) == LVAL_SYM &&
                (strcmp(ph->str, "::") == 0 || strcmp(ph->str, "->") == 0)) {
              pc = valk_lval_tail(pc);
              if (pc && LVAL_TYPE(pc) == LVAL_CONS)
                pc = valk_lval_tail(pc);
              continue;
            }
            if (ph && LVAL_TYPE(ph) == LVAL_SYM && ph->str[0] != '&') n++;
            pc = valk_lval_tail(pc);
          }
          arity = n;
        }
      }
    } else if (LVAL_TYPE(binding) == LVAL_SYM) {
      sym_name = binding->str;
    }

    if (!sym_name) return;

    lsp_pos_t p = offset_to_pos(text, form_start);
    doc_add_symbol(doc, sym_name, p.line, p.col, arity, form_start, pos_end);
    lsp_symbol_t *sym = &doc->symbols[doc->symbol_count - 1];

    if (strcmp(head->str, "fun") == 0 && LVAL_TYPE(binding) == LVAL_CONS) {
      char sig[512];
      char *sp = sig;
      char *se = sig + sizeof(sig) - 1;
      sp += snprintf(sp, se - sp, "(fun {%s", sym_name);
      valk_lval_t *param = valk_lval_tail(binding);
      while (param && LVAL_TYPE(param) == LVAL_CONS && sp < se) {
        valk_lval_t *ph = valk_lval_head(param);
        if (ph && LVAL_TYPE(ph) == LVAL_SYM &&
            (strcmp(ph->str, "::") == 0 || strcmp(ph->str, "->") == 0)) {
          param = valk_lval_tail(param);
          if (param && LVAL_TYPE(param) == LVAL_CONS)
            param = valk_lval_tail(param);
          continue;
        }
        if (ph && LVAL_TYPE(ph) == LVAL_SYM && ph->str[0] != '&')
          sp += snprintf(sp, se - sp, " %s", ph->str);
        param = valk_lval_tail(param);
      }
      snprintf(sp, se - sp, "} ...)");
      sym->doc = strdup(sig);
    } else {
      sym->doc = strdup(strcmp(head->str, "fun") == 0 ? "(fun ...)" : "(def ...)");
    }
    return;
  }

  if (strcmp(head->str, "type") == 0) {
    valk_lval_t *tail = valk_lval_tail(expr);
    if (LVAL_TYPE(tail) != LVAL_CONS) return;
    valk_lval_t *type_name_q = valk_lval_head(tail);
    const char *type_name = nullptr;
    if (type_name_q && LVAL_TYPE(type_name_q) == LVAL_CONS) {
      valk_lval_t *tn = valk_lval_head(type_name_q);
      if (tn && LVAL_TYPE(tn) == LVAL_SYM)
        type_name = tn->str;
    }

    valk_lval_t *variants = valk_lval_tail(tail);
    while (variants && LVAL_TYPE(variants) == LVAL_CONS) {
      valk_lval_t *variant = valk_lval_head(variants);
      if (variant && LVAL_TYPE(variant) == LVAL_CONS) {
        valk_lval_t *ctor = valk_lval_head(variant);
        if (ctor && LVAL_TYPE(ctor) == LVAL_SYM) {
          int field_count = -1;
          valk_lval_t *fc = valk_lval_tail(variant);
          valk_lval_t *first_field = (fc && LVAL_TYPE(fc) == LVAL_CONS) ? valk_lval_head(fc) : nullptr;
          bool keyword_style = first_field && LVAL_TYPE(first_field) == LVAL_SYM &&
                               first_field->str[0] == ':';
          if (!keyword_style) {
            field_count = 0;
            while (fc && LVAL_TYPE(fc) == LVAL_CONS) {
              field_count++;
              fc = valk_lval_tail(fc);
            }
          }
          lsp_pos_t p = offset_to_pos(text, form_start);
          char sig[256];
          if (type_name && ctor->str[0] != ':') {
            char qname[256];
            snprintf(qname, sizeof(qname), "%s::%s", type_name, ctor->str);
            doc_add_symbol(doc, qname, p.line, p.col, field_count, form_start, pos_end);
            snprintf(sig, sizeof(sig), "(type %s) constructor", type_name);
            doc->symbols[doc->symbol_count - 1].doc = strdup(sig);
            doc_add_symbol(doc, ctor->str, p.line, p.col, field_count, form_start, pos_end);
            doc->symbols[doc->symbol_count - 1].doc = strdup(sig);
          } else {
            doc_add_symbol(doc, ctor->str, p.line, p.col, field_count, form_start, pos_end);
            if (type_name)
              snprintf(sig, sizeof(sig), "(type %s) constructor", type_name);
            else
              snprintf(sig, sizeof(sig), "constructor");
            doc->symbols[doc->symbol_count - 1].doc = strdup(sig);
          }
        }
      }
      variants = valk_lval_tail(variants);
    }
  }
}

// ---------------------------------------------------------------------------
// Main entry point: analyze_document
// ---------------------------------------------------------------------------

static void extract_symbols_pass(lsp_document_t *doc) {
  doc_symbols_clear(doc);

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
      if (LVAL_TYPE(val) == LVAL_ERR) break;
      continue;
    }

    int form_start = pos;
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;

    extract_symbols_visitor(expr, doc, form_start);
  }
}

void analyze_document_light(lsp_document_t *doc) {
  extract_symbols_pass(doc);
}

void analyze_document(lsp_document_t *doc) {
  doc_diag_clear(doc);
  extract_symbols_pass(doc);

  check_and_sem_pass(doc, true);
  check_types(doc);
}
