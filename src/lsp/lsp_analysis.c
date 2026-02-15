#include "lsp_doc.h"
#include "lsp_builtins_gen.h"
#include "lsp_types.h"

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
// Parse-loop helper: iterate top-level forms
// ---------------------------------------------------------------------------

typedef struct valk_lval_t valk_lval_t;

typedef void (*form_visitor_fn)(valk_lval_t *expr, void *ctx, int form_start);

static void parse_toplevel_forms(const char *text, int len, form_visitor_fn visitor, void *ctx) {
  int pos = 0;
  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;

    if (text[pos] == ';') {
      while (pos < len && text[pos] != '\n') pos++;
      continue;
    }

    int form_start = pos;
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;

    visitor(expr, ctx, form_start);
  }
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

static void extract_def_or_fun(valk_lval_t *head, valk_lval_t *tail, lsp_symset_t *globals) {
  if (strcmp(head->str, "def") != 0 && strcmp(head->str, "fun") != 0) return;
  if (LVAL_TYPE(tail) != LVAL_CONS) return;
  valk_lval_t *binding = valk_lval_head(tail);
  if (!binding) return;

  if (LVAL_TYPE(binding) == LVAL_CONS) {
    valk_lval_t *first = valk_lval_head(binding);
    if (first && LVAL_TYPE(first) == LVAL_SYM)
      symset_add(globals, first->str);
  } else if (LVAL_TYPE(binding) == LVAL_SYM) {
    symset_add(globals, binding->str);
  }
}

static void extract_type_ctors(valk_lval_t *tail, lsp_symset_t *globals) {
  if (LVAL_TYPE(tail) == LVAL_CONS)
    tail = valk_lval_tail(tail);
  while (tail && LVAL_TYPE(tail) == LVAL_CONS) {
    valk_lval_t *variant = valk_lval_head(tail);
    if (variant && LVAL_TYPE(variant) == LVAL_CONS) {
      valk_lval_t *ctor_name = valk_lval_head(variant);
      if (ctor_name && LVAL_TYPE(ctor_name) == LVAL_SYM)
        symset_add(globals, ctor_name->str);
    }
    tail = valk_lval_tail(tail);
  }
}

typedef struct {
  lsp_symset_t *globals;
} extract_syms_ctx_t;

static void extract_global_visitor(valk_lval_t *expr, void *ctx, int form_start) {
  (void)form_start;
  extract_syms_ctx_t *ec = ctx;
  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = valk_lval_head(expr);
  if (!head || LVAL_TYPE(head) != LVAL_SYM) return;
  valk_lval_t *tail = valk_lval_tail(expr);

  extract_def_or_fun(head, tail, ec->globals);
  if (strcmp(head->str, "type") == 0)
    extract_type_ctors(tail, ec->globals);
}

static void extract_global_symbols_from_text(const char *text, lsp_symset_t *globals) {
  extract_syms_ctx_t ctx = {.globals = globals};
  parse_toplevel_forms(text, (int)strlen(text), extract_global_visitor, &ctx);
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
    if (!head || LVAL_TYPE(head) != LVAL_SYM || strcmp(head->str, "load") != 0)
      continue;

    valk_lval_t *tail = valk_lval_tail(expr);
    if (LVAL_TYPE(tail) != LVAL_CONS) continue;
    valk_lval_t *arg = valk_lval_head(tail);
    if (!arg || LVAL_TYPE(arg) != LVAL_STR) continue;

    char resolved[PATH_MAX], real[PATH_MAX];
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
    if (!found || symset_contains(visited, real)) continue;
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

  for (int i = 0; LSP_BUILTINS[i].name; i++)
    symset_add(globals, LSP_BUILTINS[i].name);
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
// Unified AST walker — check_expr + sem_expr in a single pass.
//
// When `emit_sem` is true, emits semantic tokens.
// When `emit_diag` is true, emits undefined-symbol/arity diagnostics.
// Both can be true for a single combined pass.
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

static void diag_at_sym(walk_ctx_t *w, const char *sym, const char *msg, int severity) {
  if (!w->emit_diag) return;
  int off = find_sym_offset(w->text, sym, *w->cursor);
  if (off < 0) return;
  lsp_pos_t p = offset_to_pos(w->text, off);
  doc_add_diag_full(w->doc, msg, p.line, p.col, (int)strlen(sym), severity);
}

// --- Symbol resolution (diag + sem combined) ---

static void walk_sym(walk_ctx_t *w, valk_lval_t *expr) {
  const char *name = expr->str;

  if (name[0] == ':') {
    emit_sym(w, name, SEM_PROPERTY, 0);
    return;
  }

  if (strcmp(name, "true") == 0 || strcmp(name, "false") == 0 ||
      strcmp(name, "nil") == 0 || strcmp(name, "otherwise") == 0) {
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

  if (w->emit_diag) {
    char msg[256];
    snprintf(msg, sizeof(msg), "Symbol '%s' is not defined", name);
    diag_at_sym(w, name, msg, 2);
  }
  advance_cursor(w, name);
}

// --- Arity checking ---

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

// --- Form-specific handlers ---

static void walk_lambda(walk_ctx_t *w, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *formals = valk_lval_head(rest);
  valk_lval_t *body_rest = valk_lval_tail(rest);

  lsp_scope_t *inner = scope_push(w->scope);
  if (formals && LVAL_TYPE(formals) == LVAL_CONS) {
    valk_lval_t *cur = formals;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      valk_lval_t *h = valk_lval_head(cur);
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
  while (params && LVAL_TYPE(params) == LVAL_CONS) {
    valk_lval_t *h = valk_lval_head(params);
    if (h && LVAL_TYPE(h) == LVAL_SYM) {
      if (h->str[0] != '&') {
        symset_add(&inner->locals, h->str);
        emit_sym(w, h->str, SEM_PARAMETER, SEM_MOD_DECLARATION);
      } else {
        emit_sym(w, h->str, SEM_OPERATOR, 0);
      }
    }
    params = valk_lval_tail(params);
  }

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

  if (type_name_q && LVAL_TYPE(type_name_q) == LVAL_CONS) {
    valk_lval_t *tname = valk_lval_head(type_name_q);
    if (tname && LVAL_TYPE(tname) == LVAL_SYM)
      emit_sym(w, tname->str, SEM_TYPE, SEM_MOD_DEFINITION);
    valk_lval_t *tparams = valk_lval_tail(type_name_q);
    while (tparams && LVAL_TYPE(tparams) == LVAL_CONS) {
      valk_lval_t *tp = valk_lval_head(tparams);
      if (tp && LVAL_TYPE(tp) == LVAL_SYM)
        emit_sym(w, tp->str, SEM_TYPE_PARAM, 0);
      tparams = valk_lval_tail(tparams);
    }
  }

  valk_lval_t *variants = valk_lval_tail(rest);
  while (variants && LVAL_TYPE(variants) == LVAL_CONS) {
    valk_lval_t *variant = valk_lval_head(variants);
    if (variant && LVAL_TYPE(variant) == LVAL_CONS) {
      valk_lval_t *ctor = valk_lval_head(variant);
      if (ctor && LVAL_TYPE(ctor) == LVAL_SYM) {
        symset_add(w->globals, ctor->str);
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

// --- Main walk dispatch ---

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

  if (expr->flags & LVAL_FLAG_QUOTED) {
    if (w->emit_sem)
      walk_body(w, expr);
    return;
  }

  valk_lval_t *head = valk_lval_head(expr);
  valk_lval_t *rest = valk_lval_tail(expr);
  if (!head) return;

  if (LVAL_TYPE(head) != LVAL_SYM) {
    walk_expr(w, head);
    walk_body(w, rest);
    return;
  }

  const char *name = head->str;

  // Emit semantic token for head symbol
  if (w->emit_sem) {
    if (is_special_form(name))
      emit_sym(w, name, SEM_KEYWORD, 0);
    else if (is_builtin(name))
      emit_sym(w, name, SEM_FUNCTION, SEM_MOD_DEFAULT_LIB);
    else
      emit_sym(w, name, SEM_FUNCTION, 0);
  }

  // Arity checking
  check_arity(w, name, count_args(rest));

  // Dispatch special forms
  if (strcmp(name, "\\") == 0)       { walk_lambda(w, rest); return; }
  if (strcmp(name, "fun") == 0)      { walk_fun(w, rest); return; }
  if (strcmp(name, "def") == 0)      { walk_binding(w, "def", rest); return; }
  if (strcmp(name, "=") == 0)        { walk_binding(w, "=", rest); return; }
  if (strcmp(name, "type") == 0)     { walk_type(w, rest); return; }
  if (strcmp(name, "match") == 0)    { walk_match(w, rest); return; }

  // Forms that just recurse into children
  walk_body(w, rest);
}

// ---------------------------------------------------------------------------
// Combined check+sem pass
// ---------------------------------------------------------------------------

static int sem_token_cmp(const void *a, const void *b) {
  const lsp_sem_token_t *ta = a, *tb = b;
  if (ta->line != tb->line) return ta->line - tb->line;
  return ta->col - tb->col;
}

static void check_and_sem_pass(lsp_document_t *doc, bool emit_sem) {
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
    qsort(doc->sem_tokens, doc->sem_token_count, sizeof(lsp_sem_token_t), sem_token_cmp);

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

// ---------------------------------------------------------------------------
// Type checking pass
// ---------------------------------------------------------------------------

static void check_types(lsp_document_t *doc) {
  type_arena_t arena;
  type_arena_init(&arena);

  typed_scope_t *top = typed_scope_push(&arena, nullptr);
  lsp_builtin_schemes_init(&arena, top);

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
  };

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
  lsp_builtin_schemes_init(&arena, top);

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
  };

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

static void extract_symbols_visitor(valk_lval_t *expr, void *ctx, int form_start) {
  lsp_document_t *doc = ctx;
  const char *text = doc->text;
  int pos_end = form_start;

  // Find end by re-reading (form_start is before read, we need after)
  // The caller already read past, so we use the expression structure
  // to determine the end position. Since we can't easily get it,
  // store form_start and find the matching paren.

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = valk_lval_head(expr);
  if (!head || LVAL_TYPE(head) != LVAL_SYM) return;

  // We need the end position. Re-read to get it.
  int tmp = form_start;
  valk_lval_read(&tmp, text);
  pos_end = tmp;

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
        if (strcmp(head->str, "fun") == 0)
          arity = (int)valk_lval_list_count(binding) - 1;
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
      sp += snprintf(sp, se - sp, "(fun (%s", sym_name);
      valk_lval_t *param = valk_lval_tail(binding);
      while (param && LVAL_TYPE(param) == LVAL_CONS && sp < se) {
        valk_lval_t *ph = valk_lval_head(param);
        if (ph && LVAL_TYPE(ph) == LVAL_SYM)
          sp += snprintf(sp, se - sp, " %s", ph->str);
        param = valk_lval_tail(param);
      }
      snprintf(sp, se - sp, ") ...)");
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
          doc_add_symbol(doc, ctor->str, p.line, p.col, field_count, form_start, pos_end);
          lsp_symbol_t *sym = &doc->symbols[doc->symbol_count - 1];
          char sig[256];
          if (type_name)
            snprintf(sig, sizeof(sig), "(type %s) constructor", type_name);
          else
            snprintf(sig, sizeof(sig), "constructor");
          sym->doc = strdup(sig);
        }
      }
      variants = valk_lval_tail(variants);
    }
  }
}

// ---------------------------------------------------------------------------
// Main entry point: analyze_document
// ---------------------------------------------------------------------------

void analyze_document(lsp_document_t *doc) {
  doc_symbols_clear(doc);
  doc_diag_clear(doc);

  const char *text = doc->text;
  int pos = 0;
  int len = (int)doc->text_len;

  // First pass: extract symbols (for document outline)
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

    extract_symbols_visitor(expr, doc, form_start);
  }

  // Second pass: check undefined symbols + generate semantic tokens (combined)
  check_and_sem_pass(doc, true);

  // Third pass: type inference
  check_types(doc);
}
