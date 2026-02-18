#include "lsp_doc.h"
#include "lsp_builtins_gen.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../parser.h"

// ---------------------------------------------------------------------------
// Builtin lookup
// ---------------------------------------------------------------------------

static const lsp_builtin_entry_t *find_builtin(const char *name) {
  for (int i = 0; LSP_BUILTINS[i].name; i++)
    if (strcmp(LSP_BUILTINS[i].name, name) == 0)
      return &LSP_BUILTINS[i];
  return nullptr;
}

static bool is_special_form(const char *name) {
  const lsp_builtin_entry_t *e = find_builtin(name);
  return e && e->is_special_form;
}

static bool is_builtin(const char *name) {
  return find_builtin(name) != nullptr;
}

static bool builtin_arity(const char *name, int *min_out, int *max_out) {
  const lsp_builtin_entry_t *e = find_builtin(name);
  if (e && e->min_arity >= 0) {
    *min_out = e->min_arity;
    *max_out = e->max_arity;
    return true;
  }
  return false;
}

// ---------------------------------------------------------------------------
// AST walker context + helpers
// ---------------------------------------------------------------------------

typedef struct {
  lsp_symset_t *globals;
  lsp_scope_t *scope;
  lsp_document_t *doc;
  const char *text;
  int *cursor;
  bool emit_sem;
  bool emit_diag;
} walk_ctx_t;

static void walk_expr(walk_ctx_t *w, valk_lval_t *expr);

static void walk_body(walk_ctx_t *w, valk_lval_t *rest) {
  while (rest && LVAL_TYPE(rest) == LVAL_CONS) {
    walk_expr(w, valk_lval_head(rest));
    rest = valk_lval_tail(rest);
  }
}

static int count_args(valk_lval_t *rest) {
  int n = 0;
  while (rest && LVAL_TYPE(rest) == LVAL_CONS) { n++; rest = valk_lval_tail(rest); }
  return n;
}

#define find_sym_offset lsp_find_sym_offset

static void emit_sym(walk_ctx_t *w, const char *sym, int type, int mods) {
  int off = find_sym_offset(w->text, sym, *w->cursor);
  if (off < 0) return;
  *w->cursor = off + (int)strlen(sym);
  if (w->emit_sem) {
    lsp_pos_t p = offset_to_pos(w->text, off);
    doc_add_sem(w->doc, p.line, p.col, (int)strlen(sym), type, mods);
  }
}

static void advance_cursor(walk_ctx_t *w, const char *sym) {
  int off = find_sym_offset(w->text, sym, *w->cursor);
  if (off >= 0) *w->cursor = off + (int)strlen(sym);
}

static void diag_at_sym(walk_ctx_t *w, const char *sym, const char *msg,
                        int severity) {
  if (!w->emit_diag) return;
  int off = find_sym_offset(w->text, sym, *w->cursor);
  if (off < 0) return;
  lsp_pos_t p = offset_to_pos(w->text, off);
  doc_add_diag_full(w->doc, msg, p.line, p.col, (int)strlen(sym), severity);
}

// ---------------------------------------------------------------------------
// Symbol resolution
// ---------------------------------------------------------------------------

static void walk_sym(walk_ctx_t *w, valk_lval_t *expr) {
  const char *name = expr->str;

  if (name[0] == ':') {
    emit_sym(w, name, SEM_PROPERTY, 0);
    return;
  }

  if (strcmp(name, "true") == 0 || strcmp(name, "false") == 0 ||
      strcmp(name, "nil") == 0 || strcmp(name, "otherwise") == 0 ||
      strcmp(name, "_") == 0) {
    emit_sym(w, name, SEM_MACRO, SEM_MOD_READONLY);
    return;
  }

  if (scope_has(w->scope, name)) {
    emit_sym(w, name, SEM_PARAMETER, 0);
    return;
  }

  if (is_builtin(name)) {
    emit_sym(w, name, SEM_VARIABLE, SEM_MOD_DEFAULT_LIB);
    return;
  }

  if (symset_contains(w->globals, name)) {
    emit_sym(w, name, SEM_VARIABLE, 0);
    return;
  }

  if (name[0] >= 'A' && name[0] <= 'Z') {
    const char *colon = strchr(name, ':');
    if (colon && colon != name && colon[1] != '\0' && colon[1] != ':') {
      emit_sym(w, name, SEM_VARIABLE, 0);
      return;
    }
  }

  if (w->emit_diag) {
    char msg[256];
    snprintf(msg, sizeof(msg), "Symbol '%s' is not defined", name);
    diag_at_sym(w, name, msg, 1);
  }
  advance_cursor(w, name);
}

// ---------------------------------------------------------------------------
// Arity checking
// ---------------------------------------------------------------------------

static void check_arity(walk_ctx_t *w, const char *name, int nargs) {
  if (!w->emit_diag) return;

  int amin, amax;
  if (builtin_arity(name, &amin, &amax)) {
    if (nargs >= amin && (amax < 0 || nargs <= amax)) return;
    char msg[256];
    if (amin == amax)
      snprintf(msg, sizeof(msg), "'%s' expects %d argument%s, got %d",
               name, amin, amin == 1 ? "" : "s", nargs);
    else if (amax < 0)
      snprintf(msg, sizeof(msg), "'%s' expects at least %d argument%s, got %d",
               name, amin, amin == 1 ? "" : "s", nargs);
    else
      snprintf(msg, sizeof(msg), "'%s' expects %d-%d arguments, got %d",
               name, amin, amax, nargs);
    diag_at_sym(w, name, msg, 1);
    return;
  }

  for (size_t si = 0; si < w->doc->symbol_count; si++) {
    if (w->doc->symbols[si].arity < 0 ||
        strcmp(w->doc->symbols[si].name, name) != 0)
      continue;
    int expected = w->doc->symbols[si].arity;
    bool variadic = w->doc->symbols[si].doc &&
      (strstr(w->doc->symbols[si].doc, "& ") || strstr(w->doc->symbols[si].doc, "&}"));
    if ((!variadic && nargs == expected) || (variadic && nargs >= expected - 1))
      return;
    char msg[256];
    if (variadic)
      snprintf(msg, sizeof(msg), "'%s' expects at least %d argument%s, got %d",
               name, expected - 1, (expected - 1) == 1 ? "" : "s", nargs);
    else
      snprintf(msg, sizeof(msg), "'%s' expects %d argument%s, got %d",
               name, expected, expected == 1 ? "" : "s", nargs);
    diag_at_sym(w, name, msg, 1);
    break;
  }
}

// ---------------------------------------------------------------------------
// Form-specific handlers
// ---------------------------------------------------------------------------

static void walk_type_ann(walk_ctx_t *w, valk_lval_t *node) {
  if (!node) return;
  if (LVAL_TYPE(node) == LVAL_SYM) {
    const char *s = node->str;
    if (s[0] >= 'A' && s[0] <= 'Z') {
      bool is_ground = strcmp(s, "Num") == 0 || strcmp(s, "Str") == 0 ||
        strcmp(s, "Sym") == 0 || strcmp(s, "Nil") == 0 ||
        strcmp(s, "Err") == 0 || strcmp(s, "Any") == 0 ||
        strcmp(s, "PList") == 0;
      emit_sym(w, s, is_ground ? SEM_TYPE : SEM_TYPE_PARAM, 0);
    } else if (strcmp(s, "??") == 0) {
      emit_sym(w, s, SEM_TYPE, 0);
    } else if (strcmp(s, "->") == 0) {
      emit_sym(w, s, SEM_OPERATOR, 0);
    }
  } else if (LVAL_TYPE(node) == LVAL_CONS) {
    valk_lval_t *cur = node;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      walk_type_ann(w, valk_lval_head(cur));
      cur = valk_lval_tail(cur);
    }
  }
}

static void walk_annotated_formals(walk_ctx_t *w, valk_lval_t *formals,
                                   lsp_scope_t *inner) {
  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *h = valk_lval_head(cur);

    if (h && LVAL_TYPE(h) == LVAL_SYM && strcmp(h->str, "->") == 0) {
      emit_sym(w, h->str, SEM_OPERATOR, 0);
      cur = valk_lval_tail(cur);
      if (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        walk_type_ann(w, valk_lval_head(cur));
        cur = valk_lval_tail(cur);
      }
      continue;
    }

    if (h && LVAL_TYPE(h) == LVAL_SYM && strcmp(h->str, "::") == 0) {
      emit_sym(w, h->str, SEM_OPERATOR, 0);
      cur = valk_lval_tail(cur);
      if (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        walk_type_ann(w, valk_lval_head(cur));
        cur = valk_lval_tail(cur);
      }
      continue;
    }

    if (h && LVAL_TYPE(h) == LVAL_SYM) {
      if (h->str[0] != '&') {
        symset_add(&inner->locals, h->str);
        emit_sym(w, h->str, SEM_PARAMETER, SEM_MOD_DECLARATION);
      } else {
        emit_sym(w, h->str, SEM_OPERATOR, 0);
      }
    }
    cur = valk_lval_tail(cur);
  }
}

static void walk_lambda(walk_ctx_t *w, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *formals = valk_lval_head(rest);
  valk_lval_t *body_rest = valk_lval_tail(rest);

  lsp_scope_t *inner = scope_push(w->scope);
  if (formals && LVAL_TYPE(formals) == LVAL_CONS)
    walk_annotated_formals(w, formals, inner);

  lsp_scope_t *saved = w->scope;
  w->scope = inner;
  walk_body(w, body_rest);
  w->scope = saved;
  scope_pop(inner);
}

static void walk_fun(walk_ctx_t *w, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *name_formals = valk_lval_head(rest);
  valk_lval_t *body_rest = valk_lval_tail(rest);

  if (!name_formals || LVAL_TYPE(name_formals) != LVAL_CONS) return;

  valk_lval_t *fname = valk_lval_head(name_formals);
  if (fname && LVAL_TYPE(fname) == LVAL_SYM) {
    symset_add(w->globals, fname->str);
    emit_sym(w, fname->str, SEM_FUNCTION, SEM_MOD_DEFINITION);
  }

  lsp_scope_t *inner = scope_push(w->scope);
  valk_lval_t *params = valk_lval_tail(name_formals);
  if (params && LVAL_TYPE(params) == LVAL_CONS)
    walk_annotated_formals(w, params, inner);

  lsp_scope_t *saved = w->scope;
  w->scope = inner;
  walk_body(w, body_rest);
  w->scope = saved;
  scope_pop(inner);
}

static void walk_binding(walk_ctx_t *w, const char *form, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *binding = valk_lval_head(rest);
  valk_lval_t *val_rest = valk_lval_tail(rest);
  bool is_global = strcmp(form, "def") == 0;

  if (binding && LVAL_TYPE(binding) == LVAL_CONS) {
    valk_lval_t *cur = binding;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      valk_lval_t *s = valk_lval_head(cur);
      if (s && LVAL_TYPE(s) == LVAL_SYM) {
        if (is_global)
          symset_add(w->globals, s->str);
        else
          symset_add(&w->scope->locals, s->str);
        emit_sym(w, s->str, SEM_VARIABLE, SEM_MOD_DEFINITION);
      }
      cur = valk_lval_tail(cur);
    }
  } else if (binding && LVAL_TYPE(binding) == LVAL_SYM) {
    if (is_global)
      symset_add(w->globals, binding->str);
    else
      symset_add(&w->scope->locals, binding->str);
    emit_sym(w, binding->str, SEM_VARIABLE, SEM_MOD_DEFINITION);
  }

  walk_body(w, val_rest);
}

static void walk_type(walk_ctx_t *w, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *type_name_q = valk_lval_head(rest);
  const char *tname_str = NULL;

  if (type_name_q && LVAL_TYPE(type_name_q) == LVAL_CONS) {
    valk_lval_t *tname = valk_lval_head(type_name_q);
    if (tname && LVAL_TYPE(tname) == LVAL_SYM) {
      tname_str = tname->str;
      emit_sym(w, tname->str, SEM_TYPE, SEM_MOD_DEFINITION);
    }
    valk_lval_t *tparams = valk_lval_tail(type_name_q);
    while (tparams && LVAL_TYPE(tparams) == LVAL_CONS) {
      valk_lval_t *tp = valk_lval_head(tparams);
      if (tp && LVAL_TYPE(tp) == LVAL_SYM)
        emit_sym(w, tp->str, SEM_TYPE_PARAM, 0);
      tparams = valk_lval_tail(tparams);
    }
  }

  valk_lval_t *first_variant = valk_lval_head(valk_lval_tail(rest));
  bool is_product = first_variant && LVAL_TYPE(first_variant) == LVAL_CONS &&
    valk_lval_head(first_variant) && LVAL_TYPE(valk_lval_head(first_variant)) == LVAL_SYM &&
    valk_lval_head(first_variant)->str[0] == ':';
  if (is_product && tname_str)
    symset_add(w->globals, tname_str);

  valk_lval_t *variants = valk_lval_tail(rest);
  while (variants && LVAL_TYPE(variants) == LVAL_CONS) {
    valk_lval_t *variant = valk_lval_head(variants);
    if (variant && LVAL_TYPE(variant) == LVAL_CONS) {
      valk_lval_t *ctor = valk_lval_head(variant);
      if (ctor && LVAL_TYPE(ctor) == LVAL_SYM) {
        symset_add(w->globals, ctor->str);
        if (tname_str && ctor->str[0] != ':') {
          char qname[256];
          snprintf(qname, sizeof(qname), "%s::%s", tname_str, ctor->str);
          symset_add(w->globals, qname);
        }
        emit_sym(w, ctor->str, SEM_ENUM_MEMBER, SEM_MOD_DEFINITION);
      }
      valk_lval_t *fields = valk_lval_tail(variant);
      while (fields && LVAL_TYPE(fields) == LVAL_CONS) {
        valk_lval_t *fld = valk_lval_head(fields);
        if (fld && LVAL_TYPE(fld) == LVAL_SYM) {
          if (fld->str[0] == ':')
            emit_sym(w, fld->str, SEM_PROPERTY, 0);
          else
            emit_sym(w, fld->str, SEM_TYPE_PARAM, 0);
        }
        fields = valk_lval_tail(fields);
      }
    }
    variants = valk_lval_tail(variants);
  }
}

static void walk_aio_do(walk_ctx_t *w, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *body = valk_lval_head(rest);
  if (!body || LVAL_TYPE(body) != LVAL_CONS) return;

  lsp_scope_t *inner = scope_push(w->scope);
  lsp_scope_t *saved = w->scope;
  w->scope = inner;

  uint32_t sf = body->flags;
  if (body->flags & LVAL_FLAG_QUOTED)
    body->flags &= ~LVAL_FLAG_QUOTED;

  valk_lval_t *cur = body;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *stmt = valk_lval_head(cur);
    if (stmt && LVAL_TYPE(stmt) == LVAL_CONS) {
      valk_lval_t *sh = valk_lval_head(stmt);
      valk_lval_t *sh_rest = valk_lval_tail(stmt);
      valk_lval_t *arrow = sh_rest ? valk_lval_head(sh_rest) : nullptr;
      if (sh && LVAL_TYPE(sh) == LVAL_SYM &&
          arrow && LVAL_TYPE(arrow) == LVAL_SYM &&
          strcmp(arrow->str, "<-") == 0) {
        valk_lval_t *expr_rest = valk_lval_tail(sh_rest);
        if (sh->str[0] != '_' || sh->str[1] != '\0') {
          symset_add(&inner->locals, sh->str);
          emit_sym(w, sh->str, SEM_VARIABLE, SEM_MOD_DEFINITION);
        } else {
          emit_sym(w, sh->str, SEM_VARIABLE, 0);
        }
        emit_sym(w, "<-", SEM_KEYWORD, 0);
        walk_body(w, expr_rest);
        cur = valk_lval_tail(cur);
        continue;
      }
    }
    walk_expr(w, stmt);
    cur = valk_lval_tail(cur);
  }

  body->flags = sf;
  w->scope = saved;
  scope_pop(inner);
}

static void walk_match(walk_ctx_t *w, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  walk_expr(w, valk_lval_head(rest));

  valk_lval_t *clauses = valk_lval_tail(rest);
  while (clauses && LVAL_TYPE(clauses) == LVAL_CONS) {
    valk_lval_t *clause = valk_lval_head(clauses);
    if (!clause || LVAL_TYPE(clause) != LVAL_CONS) goto next;

    valk_lval_t *pattern = valk_lval_head(clause);
    valk_lval_t *body = valk_lval_tail(clause);
    lsp_scope_t *inner = scope_push(w->scope);

    if (pattern && LVAL_TYPE(pattern) == LVAL_CONS) {
      valk_lval_t *pat_head = valk_lval_head(pattern);
      if (pat_head && LVAL_TYPE(pat_head) == LVAL_SYM)
        emit_sym(w, pat_head->str, SEM_ENUM_MEMBER, 0);
      valk_lval_t *pat_args = valk_lval_tail(pattern);
      while (pat_args && LVAL_TYPE(pat_args) == LVAL_CONS) {
        valk_lval_t *pv = valk_lval_head(pat_args);
        if (pv && LVAL_TYPE(pv) == LVAL_SYM) {
          if (pv->str[0] == ':') {
            emit_sym(w, pv->str, SEM_PROPERTY, 0);
          } else {
            symset_add(&inner->locals, pv->str);
            emit_sym(w, pv->str, SEM_PARAMETER, SEM_MOD_DEFINITION);
          }
        }
        pat_args = valk_lval_tail(pat_args);
      }
    } else if (pattern && LVAL_TYPE(pattern) == LVAL_SYM) {
      emit_sym(w, pattern->str, SEM_VARIABLE, 0);
    }

    lsp_scope_t *saved = w->scope;
    w->scope = inner;
    walk_body(w, body);
    w->scope = saved;
    scope_pop(inner);

  next:
    clauses = valk_lval_tail(clauses);
  }
}

// ---------------------------------------------------------------------------
// Main walk dispatch
// ---------------------------------------------------------------------------

static void walk_expr(walk_ctx_t *w, valk_lval_t *expr) {
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    walk_sym(w, expr);
    return;
  }

  if (LVAL_TYPE(expr) == LVAL_NUM && w->emit_sem) {
    char num_str[64];
    snprintf(num_str, sizeof(num_str), "%li", expr->num);
    int off = find_sym_offset(w->text, num_str, *w->cursor);
    if (off >= 0) {
      *w->cursor = off + (int)strlen(num_str);
      lsp_pos_t p = offset_to_pos(w->text, off);
      doc_add_sem(w->doc, p.line, p.col, (int)strlen(num_str), SEM_NUMBER, 0);
    }
    return;
  }

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = valk_lval_head(expr);
  valk_lval_t *rest = valk_lval_tail(expr);
  if (!head) return;

  if (expr->flags & LVAL_FLAG_QUOTED) {
    if (LVAL_TYPE(head) != LVAL_SYM ||
        (!is_special_form(head->str) && !is_builtin(head->str) &&
         !symset_contains(w->globals, head->str) &&
         !scope_has(w->scope, head->str))) {
      walk_body(w, expr);
      return;
    }
  }

  if (LVAL_TYPE(head) != LVAL_SYM) {
    walk_expr(w, head);
    walk_body(w, rest);
    return;
  }

  const char *name = head->str;

  if (w->emit_sem) {
    if (is_special_form(name))
      emit_sym(w, name, SEM_KEYWORD, 0);
    else if (is_builtin(name))
      emit_sym(w, name, SEM_FUNCTION, SEM_MOD_DEFAULT_LIB);
    else
      emit_sym(w, name, SEM_FUNCTION, 0);
  }

  if (w->emit_diag && !is_special_form(name) && !is_builtin(name) &&
      !scope_has(w->scope, name) && !symset_contains(w->globals, name)) {
    bool is_accessor = (name[0] >= 'A' && name[0] <= 'Z');
    if (is_accessor) {
      const char *colon = strchr(name, ':');
      is_accessor = colon && colon != name && colon[1] != '\0' && colon[1] != ':';
    }
    if (!is_accessor) {
      char msg[256];
      snprintf(msg, sizeof(msg), "Function '%s' is not defined", name);
      diag_at_sym(w, name, msg, 1);
    }
  }

  check_arity(w, name, count_args(rest));

  if (strcmp(name, "\\") == 0)       { walk_lambda(w, rest); return; }
  if (strcmp(name, "fun") == 0)      { walk_fun(w, rest); return; }
  if (strcmp(name, "def") == 0)      { walk_binding(w, "def", rest); return; }
  if (strcmp(name, "=") == 0)        { walk_binding(w, "=", rest); return; }
  if (strcmp(name, "type") == 0)     { walk_type(w, rest); return; }
  if (strcmp(name, "sig") == 0)      { return; }
  if (strcmp(name, "match") == 0)    { walk_match(w, rest); return; }
  if (strcmp(name, "aio/do") == 0)   { walk_aio_do(w, rest); return; }

  walk_body(w, rest);
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

static int sem_token_cmp(const void *a, const void *b) {
  const lsp_sem_token_t *ta = a, *tb = b;
  if (ta->line != tb->line) return ta->line - tb->line;
  return ta->col - tb->col;
}

void check_and_sem_pass(lsp_document_t *doc, bool emit_sem) {
  lsp_symset_t globals;
  build_global_symset(doc, &globals);

  if (emit_sem)
    doc_sem_clear(doc);

  const char *text = doc->text;
  int pos = 0;
  int len = (int)doc->text_len;
  int cursor = 0;

  lsp_scope_t *top = scope_push(nullptr);

  walk_ctx_t w = {
    .globals = &globals,
    .scope = top,
    .doc = doc,
    .text = text,
    .cursor = &cursor,
    .emit_sem = emit_sem,
    .emit_diag = true,
  };

  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;

    if (text[pos] == ';') {
      int start = pos;
      while (pos < len && text[pos] != '\n') pos++;
      if (emit_sem) {
        lsp_pos_t p = offset_to_pos(text, start);
        doc_add_sem(doc, p.line, p.col, pos - start, SEM_COMMENT, 0);
      }
      continue;
    }

    cursor = pos;
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;

    walk_expr(&w, expr);
  }

  scope_pop(top);
  symset_free(&globals);

  if (emit_sem && doc->sem_token_count > 1) {
    qsort(doc->sem_tokens, doc->sem_token_count, sizeof(lsp_sem_token_t),
          sem_token_cmp);

    size_t w2 = 0;
    for (size_t r = 0; r < doc->sem_token_count; r++) {
      if (w2 > 0 && doc->sem_tokens[r].line == doc->sem_tokens[w2 - 1].line &&
          doc->sem_tokens[r].col == doc->sem_tokens[w2 - 1].col) {
        doc->sem_tokens[w2 - 1] = doc->sem_tokens[r];
        continue;
      }
      doc->sem_tokens[w2++] = doc->sem_tokens[r];
    }
    doc->sem_token_count = w2;
  }
}
