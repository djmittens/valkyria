#include "diag.h"
#include "parser.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LSP_SYM_CHARS ("abcdefghijklmnopqrstuvwxyz" \
                       "ABCDEFGHIJKLMNOPQRSTUVWXYZ" \
                       "0123456789_+-*/\\=<>!&?:/")

typedef struct {
  char **names;
  size_t count;
  size_t cap;
} symset_t;

typedef struct scope {
  symset_t locals;
  struct scope *parent;
} scope_t;

static void symset_init(symset_t *s) {
  s->names = nullptr;
  s->count = 0;
  s->cap = 0;
}

static void symset_free(symset_t *s) {
  for (size_t i = 0; i < s->count; i++)
    free(s->names[i]);
  free(s->names);
  s->names = nullptr;
  s->count = s->cap = 0;
}

static bool symset_contains(symset_t *s, const char *name) {
  for (size_t i = 0; i < s->count; i++)
    if (strcmp(s->names[i], name) == 0) return true;
  return false;
}

static void symset_add(symset_t *s, const char *name) {
  if (symset_contains(s, name)) return;
  if (s->count >= s->cap) {
    s->cap = s->cap == 0 ? 64 : s->cap * 2;
    s->names = realloc(s->names, sizeof(char *) * s->cap);
  }
  s->names[s->count++] = strdup(name);
}

static scope_t *scope_push(scope_t *parent) {
  scope_t *s = calloc(1, sizeof(scope_t));
  symset_init(&s->locals);
  s->parent = parent;
  return s;
}

static void scope_pop(scope_t *s) {
  symset_free(&s->locals);
  free(s);
}

static bool scope_has(scope_t *s, const char *name) {
  while (s) {
    if (symset_contains(&s->locals, name)) return true;
    s = s->parent;
  }
  return false;
}

// LCOV_EXCL_BR_START - character-level dispatch and AST null/type guards
static bool *build_skip_map(const char *text, int len) {
  bool *skip = calloc(len, sizeof(bool));
  if (!skip) return nullptr; // LCOV_EXCL_LINE
  bool in_str = false;
  for (int i = 0; i < len; i++) {
    if (text[i] == '"' && !in_str) {
      in_str = true;
      skip[i] = true;
    } else if (text[i] == '"' && in_str) {
      skip[i] = true;
      in_str = false;
    } else if (text[i] == '\\' && in_str) {
      skip[i] = true;
      if (i + 1 < len) skip[++i] = true;
    } else if (text[i] == ';' && !in_str) {
      while (i < len && text[i] != '\n') skip[i++] = true;
      if (i < len) i--;
    } else if (in_str) {
      skip[i] = true;
    }
  }
  return skip;
}

static int find_sym_offset(const char *text, const char *sym,
                           int search_start, const bool *skip) {
  int slen = (int)strlen(sym);
  int tlen = (int)strlen(text);
  const char *chars = LSP_SYM_CHARS;
  for (int i = search_start; i <= tlen - slen; i++) {
    if (skip && skip[i]) continue;
    if (memcmp(text + i, sym, slen) != 0) continue;
    if (i > 0 && strchr(chars, text[i - 1])) continue;
    if (i + slen < tlen && strchr(chars, text[i + slen])) continue;
    return i;
  }
  return -1;
}

static const char *SPECIAL_FORMS[] = {
  "=", "\\", "def", "fun", "if", "do", "select", "case", "quote",
  "load", "load-raw", "eval", "read", "let", "aio/let", "aio/do", "<-",
  "type", "match", "sig", "ctx/with", "ctx/with-deadline", "with",
  nullptr
};

static bool is_special_form(const char *name) {
  for (const char **p = SPECIAL_FORMS; *p; p++)
    if (strcmp(*p, name) == 0) return true;
  return false;
}

static void extract_def_or_fun(valk_lval_t *head, valk_lval_t *tail,
                               symset_t *globals) {
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

static void extract_type_ctors(valk_lval_t *tail, symset_t *globals) {
  const char *type_name = NULL;
  if (LVAL_TYPE(tail) == LVAL_CONS) {
    valk_lval_t *name_q = valk_lval_head(tail);
    if (name_q && LVAL_TYPE(name_q) == LVAL_CONS) {
      valk_lval_t *tn = valk_lval_head(name_q);
      if (tn && LVAL_TYPE(tn) == LVAL_SYM) type_name = tn->str;
    }
    tail = valk_lval_tail(tail);
  }
  while (tail && LVAL_TYPE(tail) == LVAL_CONS) {
    valk_lval_t *variant = valk_lval_head(tail);
    if (variant && LVAL_TYPE(variant) == LVAL_CONS) {
      valk_lval_t *ctor_name = valk_lval_head(variant);
      if (ctor_name && LVAL_TYPE(ctor_name) == LVAL_SYM) {
        symset_add(globals, ctor_name->str);
        if (type_name && ctor_name->str[0] != ':') {
          char qname[256];
          snprintf(qname, sizeof(qname), "%s::%s", type_name, ctor_name->str);
          symset_add(globals, qname);
        }
      }
    }
    tail = valk_lval_tail(tail);
  }
}

static void extract_global_symbols_from_text(const char *text,
                                             symset_t *globals) {
  int pos = 0, len = (int)strlen(text);
  while (pos < len) {
    while (pos < len && strchr(" \t\r\n", text[pos])) pos++;
    if (pos >= len) break;
    if (text[pos] == ';') { while (pos < len && text[pos] != '\n') pos++; continue; }
    valk_lval_t *expr = valk_lval_read(&pos, text);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    if (LVAL_TYPE(expr) != LVAL_CONS) continue;

    valk_lval_t *head = valk_lval_head(expr);
    if (!head || LVAL_TYPE(head) != LVAL_SYM) continue;
    valk_lval_t *tail = valk_lval_tail(expr);

    extract_def_or_fun(head, tail, globals);
    if (strcmp(head->str, "type") == 0)
      extract_type_ctors(tail, globals);
    if (strcmp(head->str, "sig") == 0 && LVAL_TYPE(tail) == LVAL_CONS) {
      valk_lval_t *name_q = valk_lval_head(tail);
      valk_lval_t *sig_name = (name_q && LVAL_TYPE(name_q) == LVAL_CONS)
        ? valk_lval_head(name_q) : name_q;
      if (sig_name && LVAL_TYPE(sig_name) == LVAL_SYM)
        symset_add(globals, sig_name->str);
    }
  }
}

typedef struct {
  symset_t *globals;
  scope_t *scope;
  valk_diag_list_t *diags;
  valk_name_resolver_t *resolver;
  const char *text;
  const bool *skip_map;
  int *cursor;
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

static int find_sym(walk_ctx_t *w, const char *sym) {
  return find_sym_offset(w->text, sym, *w->cursor, w->skip_map);
}

static void advance_cursor(walk_ctx_t *w, const char *sym) {
  int off = find_sym(w, sym);
  if (off >= 0) *w->cursor = off + (int)strlen(sym);
}

static void diag_at_sym(walk_ctx_t *w, const char *sym, const char *msg,
                        int severity) {
  if (!w->diags) return;
  int off = find_sym(w, sym);
  if (off < 0) return;
  valk_diag_add(w->diags, msg, off, (int)strlen(sym), severity);
}

static void walk_sym(walk_ctx_t *w, valk_lval_t *expr) {
  const char *name = expr->str;

  if (name[0] == ':') { advance_cursor(w, name); return; }

  if (strcmp(name, "true") == 0 || strcmp(name, "false") == 0 ||
      strcmp(name, "nil") == 0 || strcmp(name, "otherwise") == 0 ||
      strcmp(name, "_") == 0) {
    advance_cursor(w, name);
    return;
  }

  if (scope_has(w->scope, name)) { advance_cursor(w, name); return; }
  if (is_special_form(name)) { advance_cursor(w, name); return; }
  if (symset_contains(w->globals, name)) { advance_cursor(w, name); return; }
  if (w->resolver && w->resolver->is_known(name, w->resolver->ctx)) {
    advance_cursor(w, name);
    return;
  }

  if (name[0] >= 'A' && name[0] <= 'Z') {
    const char *colon = strchr(name, ':');
    if (colon && colon != name && colon[1] != '\0' && colon[1] != ':') {
      advance_cursor(w, name);
      return;
    }
  }

  if (name[0] >= 'a' && name[0] <= 'z') {
    const char *colon = strchr(name, ':');
    if (colon && colon != name && colon[1] >= 'a' && colon[1] <= 'z' &&
        colon[1] != ':') {
      advance_cursor(w, name);
      return;
    }
  }

  char msg[256];
  snprintf(msg, sizeof(msg), "Symbol '%s' is not defined", name);
  diag_at_sym(w, name, msg, 1);
  advance_cursor(w, name);
}

static void walk_annotated_formals(walk_ctx_t *w, valk_lval_t *formals,
                                   scope_t *inner) {
  valk_lval_t *cur = formals;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *h = valk_lval_head(cur);

    if (h && LVAL_TYPE(h) == LVAL_SYM && strcmp(h->str, "->") == 0) {
      advance_cursor(w, h->str);
      cur = valk_lval_tail(cur);
      if (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        advance_cursor(w, valk_lval_head(cur)->str);
        cur = valk_lval_tail(cur);
      }
      continue;
    }

    if (h && LVAL_TYPE(h) == LVAL_SYM && strcmp(h->str, "::") == 0) {
      advance_cursor(w, h->str);
      cur = valk_lval_tail(cur);
      if (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        advance_cursor(w, valk_lval_head(cur)->str);
        cur = valk_lval_tail(cur);
      }
      continue;
    }

    if (h && LVAL_TYPE(h) == LVAL_SYM) {
      if (h->str[0] != '&')
        symset_add(&inner->locals, h->str);
      advance_cursor(w, h->str);
    }
    cur = valk_lval_tail(cur);
  }
}

static void walk_lambda(walk_ctx_t *w, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *formals = valk_lval_head(rest);
  valk_lval_t *body_rest = valk_lval_tail(rest);

  scope_t *inner = scope_push(w->scope);
  if (formals && LVAL_TYPE(formals) == LVAL_CONS)
    walk_annotated_formals(w, formals, inner);

  scope_t *saved = w->scope;
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
    advance_cursor(w, fname->str);
  }

  scope_t *inner = scope_push(w->scope);
  valk_lval_t *params = valk_lval_tail(name_formals);
  if (params && LVAL_TYPE(params) == LVAL_CONS)
    walk_annotated_formals(w, params, inner);

  scope_t *saved = w->scope;
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
        advance_cursor(w, s->str);
      }
      cur = valk_lval_tail(cur);
    }
  } else if (binding && LVAL_TYPE(binding) == LVAL_SYM) {
    if (is_global)
      symset_add(w->globals, binding->str);
    else
      symset_add(&w->scope->locals, binding->str);
    advance_cursor(w, binding->str);
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
      advance_cursor(w, tname->str);
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
        advance_cursor(w, ctor->str);
      }
      valk_lval_t *fields = valk_lval_tail(variant);
      while (fields && LVAL_TYPE(fields) == LVAL_CONS) {
        valk_lval_t *fld = valk_lval_head(fields);
        if (fld && LVAL_TYPE(fld) == LVAL_SYM)
          advance_cursor(w, fld->str);
        fields = valk_lval_tail(fields);
      }
    }
    variants = valk_lval_tail(variants);
  }
}

static void walk_aio_let(walk_ctx_t *w, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *bindings = valk_lval_head(rest);
  valk_lval_t *body_rest = valk_lval_tail(rest);
  if (!bindings || LVAL_TYPE(bindings) != LVAL_CONS) return;

  scope_t *inner = scope_push(w->scope);
  scope_t *saved = w->scope;
  w->scope = inner;

  uint32_t sf = bindings->flags;
  if (bindings->flags & LVAL_FLAG_QUOTED)
    bindings->flags &= ~LVAL_FLAG_QUOTED;

  valk_lval_t *cur = bindings;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *item = valk_lval_head(cur);
    if (item && LVAL_TYPE(item) == LVAL_SYM && item->str[0] == ':') {
      advance_cursor(w, item->str);
      cur = valk_lval_tail(cur);
      continue;
    }
    if (item && LVAL_TYPE(item) == LVAL_CONS) {
      valk_lval_t *var = valk_lval_head(item);
      valk_lval_t *val_rest = valk_lval_tail(item);
      if (var && LVAL_TYPE(var) == LVAL_SYM) {
        symset_add(&inner->locals, var->str);
        advance_cursor(w, var->str);
      }
      walk_body(w, val_rest);
    }
    cur = valk_lval_tail(cur);
  }

  bindings->flags = sf;
  walk_body(w, body_rest);

  w->scope = saved;
  scope_pop(inner);
}

static void walk_aio_do(walk_ctx_t *w, valk_lval_t *rest) {
  if (LVAL_TYPE(rest) != LVAL_CONS) return;
  valk_lval_t *body = valk_lval_head(rest);
  if (!body || LVAL_TYPE(body) != LVAL_CONS) return;

  scope_t *inner = scope_push(w->scope);
  scope_t *saved = w->scope;
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
        if (sh->str[0] != '_' || sh->str[1] != '\0')
          symset_add(&inner->locals, sh->str);
        advance_cursor(w, sh->str);
        advance_cursor(w, "<-");
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
    scope_t *inner = scope_push(w->scope);

    if (pattern && LVAL_TYPE(pattern) == LVAL_CONS) {
      valk_lval_t *pat_head = valk_lval_head(pattern);
      if (pat_head && LVAL_TYPE(pat_head) == LVAL_SYM)
        advance_cursor(w, pat_head->str);
      valk_lval_t *pat_args = valk_lval_tail(pattern);
      while (pat_args && LVAL_TYPE(pat_args) == LVAL_CONS) {
        valk_lval_t *pv = valk_lval_head(pat_args);
        if (pv && LVAL_TYPE(pv) == LVAL_SYM) {
          if (pv->str[0] != ':')
            symset_add(&inner->locals, pv->str);
          advance_cursor(w, pv->str);
        }
        pat_args = valk_lval_tail(pat_args);
      }
    } else if (pattern && LVAL_TYPE(pattern) == LVAL_SYM) {
      advance_cursor(w, pattern->str);
    }

    scope_t *saved = w->scope;
    w->scope = inner;
    walk_body(w, body);
    w->scope = saved;
    scope_pop(inner);

  next:
    clauses = valk_lval_tail(clauses);
  }
}

static void walk_expr(walk_ctx_t *w, valk_lval_t *expr) {
  if (!expr) return;

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    walk_sym(w, expr);
    return;
  }

  if (LVAL_TYPE(expr) == LVAL_NUM) {
    char num_str[64];
    snprintf(num_str, sizeof(num_str), "%li", expr->num);
    advance_cursor(w, num_str);
    return;
  }

  if (LVAL_TYPE(expr) != LVAL_CONS) return;

  valk_lval_t *head = valk_lval_head(expr);
  valk_lval_t *rest = valk_lval_tail(expr);
  if (!head) return;

  if (expr->flags & LVAL_FLAG_QUOTED) {
    if (LVAL_TYPE(head) != LVAL_SYM ||
        (!is_special_form(head->str) &&
         !symset_contains(w->globals, head->str) &&
         !scope_has(w->scope, head->str) &&
         !(w->resolver && w->resolver->is_known(head->str, w->resolver->ctx)))) {
      return;
    }
  }

  if (LVAL_TYPE(head) != LVAL_SYM) {
    walk_expr(w, head);
    walk_body(w, rest);
    return;
  }

  const char *name = head->str;

  if (!is_special_form(name) &&
      !scope_has(w->scope, name) && !symset_contains(w->globals, name) &&
      !(w->resolver && w->resolver->is_known(name, w->resolver->ctx))) {
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
  advance_cursor(w, name);

  (void)count_args;

  if (strcmp(name, "\\") == 0)       { walk_lambda(w, rest); return; }
  if (strcmp(name, "fun") == 0)      { walk_fun(w, rest); return; }
  if (strcmp(name, "def") == 0)      { walk_binding(w, "def", rest); return; }
  if (strcmp(name, "=") == 0)        { walk_binding(w, "=", rest); return; }
  if (strcmp(name, "type") == 0)     { walk_type(w, rest); return; }
  if (strcmp(name, "sig") == 0) {
    if (LVAL_TYPE(rest) != LVAL_CONS) return;
    valk_lval_t *name_q = valk_lval_head(rest);
    valk_lval_t *sig_name = (name_q && LVAL_TYPE(name_q) == LVAL_CONS)
      ? valk_lval_head(name_q) : name_q;
    if (sig_name && LVAL_TYPE(sig_name) == LVAL_SYM)
      advance_cursor(w, sig_name->str);
    return;
  }
  if (strcmp(name, "quote") == 0)    { return; }
  if (strcmp(name, "match") == 0)    { walk_match(w, rest); return; }
  if (strcmp(name, "aio/do") == 0)   { walk_aio_do(w, rest); return; }
  if (strcmp(name, "aio/let") == 0)  { walk_aio_let(w, rest); return; }

  walk_body(w, rest);
}
// LCOV_EXCL_BR_STOP

valk_diag_list_t valk_validate_ast(valk_lval_t *ast, const char *text,
                                    valk_name_resolver_t resolver) {
  symset_t file_defs;
  symset_init(&file_defs);
  extract_global_symbols_from_text(text, &file_defs);

  valk_diag_list_t diags;
  valk_diag_init(&diags);

  int cursor = 0;
  int tlen = (int)strlen(text);
  bool *skip_map = build_skip_map(text, tlen);

  scope_t *top = scope_push(nullptr);

  walk_ctx_t w = {
    .globals = &file_defs,
    .scope = top,
    .diags = &diags,
    .resolver = &resolver,
    .text = text,
    .skip_map = skip_map,
    .cursor = &cursor,
  };

  // LCOV_EXCL_BR_START - AST iteration null/type guards
  valk_lval_t *rest = ast;
  while (rest && LVAL_TYPE(rest) == LVAL_CONS) {
    valk_lval_t *expr = valk_lval_head(rest);
    if (LVAL_TYPE(expr) == LVAL_ERR) break;
    if (LVAL_SRC_POS(expr) >= 0) cursor = LVAL_SRC_POS(expr);
    walk_expr(&w, expr);
    rest = valk_lval_tail(rest);
  }
  // LCOV_EXCL_BR_STOP

  scope_pop(top);
  free(skip_map);
  symset_free(&file_defs);

  return diags;
}
