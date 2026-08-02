#include "lsp_index_internal.h"

#include <string.h>

#define SQLITE_REF_TYPE "sqlite_db"

// Keyword/operator sets (simple linear scan — sets are small)
static const char *KEYWORDS[] = {
  "fun", "\\", "def", "=", "if", "select", "case",
  "do", "let", "type", "sig", "load", "and", "or", "not",
  "quote", "quasiquote", "unquote", "unquote-splicing", NULL
};

static const char *OPERATORS[] = {
  "+", "-", "*", "/", ">", "<", ">=", "<=", "==", "!=", "%", "ord", NULL
};

static bool in_set(const char *name, const char **set) {
  for (int i = 0; set[i]; i++)
    if (strcmp(name, set[i]) == 0) return true;
  return false;
}

static int source_len(const char *name) {
  if (strcmp(name, "quote") == 0) return 1;
  if (strcmp(name, "quasiquote") == 0) return 1;
  if (strcmp(name, "unquote") == 0) return 1;
  if (strcmp(name, "unquote-splicing") == 0) return 2;
  return (int)strlen(name);
}

// ---------------------------------------------------------------------------
// AST walker — single pass
// ---------------------------------------------------------------------------

static void walk_expr(index_ctx_t *ctx, valk_lval_t *expr);
static void walk_do(index_ctx_t *ctx, valk_lval_t *tl);
static void walk_list_head(index_ctx_t *ctx, valk_lval_t *expr, valk_lval_t *hd, valk_lval_t *tl);
static void walk_qexpr_body(index_ctx_t *ctx, valk_lval_t *qexpr);
static void walk_each(index_ctx_t *ctx, valk_lval_t *exprs);
static void walk_match(index_ctx_t *ctx, valk_lval_t *tl) {
  if (!tl || LVAL_TYPE(tl) != LVAL_CONS) return;

  // First arg is the value being matched
  walk_expr(ctx, tl->cons.head);
  tl = tl->cons.tail;

  // Rest are clauses: {(Pattern var1 var2) body}
  while (tl && LVAL_TYPE(tl) == LVAL_CONS) {
    valk_lval_t *clause = tl->cons.head;
    if (clause && LVAL_TYPE(clause) == LVAL_CONS && (clause->flags & LVAL_FLAG_QUOTED)) {
      valk_lval_t *pattern = clause->cons.head;
      valk_lval_t *body_list = clause->cons.tail;

      // Create scope for this match arm
      int clause_pos = (int)LVAL_SRC_POS(clause);
      if (clause_pos < 0 && pattern) clause_pos = (int)LVAL_SRC_POS(pattern);
      valk_lspi_push_scope(ctx, clause_pos);

      // Walk pattern — first element is constructor, rest are bound variables
      if (pattern && LVAL_TYPE(pattern) == LVAL_CONS) {
        valk_lval_t *ctor = pattern->cons.head;
        if (ctor && LVAL_TYPE(ctor) == LVAL_SYM) {
          int cp = (int)LVAL_SRC_POS(ctor);
          int cl = (int)strlen(ctor->str);
          if (cp >= 0) {
            valk_lspi_emit_semtok(ctx, cp, cl, TOK_TYPE, 0);
            valk_lspi_emit_node(ctx, cp, cp + cl, "sym", ctor->str);
          }
        }
        // Bind pattern variables
        valk_lval_t *vars = pattern->cons.tail;
        while (vars && LVAL_TYPE(vars) == LVAL_CONS) {
          valk_lval_t *v = vars->cons.head;
          if (v && LVAL_TYPE(v) == LVAL_SYM) {
            const char *vname = v->str;
            int vp = (int)LVAL_SRC_POS(v);
            int vl = (int)strlen(vname);
            valk_lspi_add_scope_name(ctx, vname, true);
            if (vp >= 0) {
              valk_lspi_emit_semtok(ctx, vp, vl, TOK_PARAMETER, 1);
              valk_lspi_emit_ref(ctx, vname, vp, vl, clause_pos, 1);
              valk_lspi_emit_node(ctx, vp, vp + vl, "sym", vname);
            }
          }
          vars = vars->cons.tail;
        }
      } else if (pattern && LVAL_TYPE(pattern) == LVAL_SYM) {
        // Simple pattern: just a symbol (wildcard or var)
        const char *pname = pattern->str;
        int pp = (int)LVAL_SRC_POS(pattern);
        int pl = (int)strlen(pname);
        if (pp >= 0 && strcmp(pname, "_") != 0) {
          valk_lspi_add_scope_name(ctx, pname, true);
          valk_lspi_emit_semtok(ctx, pp, pl, TOK_PARAMETER, 1);
          valk_lspi_emit_ref(ctx, pname, pp, pl, clause_pos, 1);
          valk_lspi_emit_node(ctx, pp, pp + pl, "sym", pname);
        }
      }

      // Walk body expressions
      while (body_list && LVAL_TYPE(body_list) == LVAL_CONS) {
        valk_lval_t *be = body_list->cons.head;
        if (be && LVAL_TYPE(be) == LVAL_CONS && (be->flags & LVAL_FLAG_QUOTED)) {
          walk_qexpr_body(ctx, be);
        } else {
          walk_expr(ctx, be);
        }
        body_list = body_list->cons.tail;
      }
      valk_lspi_pop_scope(ctx);
    }
    tl = tl->cons.tail;
  }
}



static void walk_each(index_ctx_t *ctx, valk_lval_t *exprs) {
  while (exprs && LVAL_TYPE(exprs) == LVAL_CONS) {
    valk_lval_t *e = exprs->cons.head;
    if (e && LVAL_TYPE(e) == LVAL_CONS && (e->flags & LVAL_FLAG_QUOTED)) {
      walk_qexpr_body(ctx, e);
    } else {
      walk_expr(ctx, e);
    }
    exprs = exprs->cons.tail;
  }
}

static void walk_qexpr_body(index_ctx_t *ctx, valk_lval_t *qexpr) {
  if (!qexpr || LVAL_TYPE(qexpr) != LVAL_CONS) return;
  valk_lval_t *hd = qexpr->cons.head;
  if (hd && LVAL_TYPE(hd) == LVAL_SYM) {
    const char *name = hd->str;
    if (strcmp(name, "do") == 0) {
      int dp = (int)LVAL_SRC_POS(hd);
      if (dp >= 0) valk_lspi_emit_semtok(ctx, dp, 2, TOK_KEYWORD, 0);
      walk_do(ctx, qexpr->cons.tail);
      return;
    }
  }
  // Treat qexpr as a single expression (e.g. {+ x 1}, {print msg})
  if (hd && LVAL_TYPE(hd) == LVAL_SYM && qexpr->cons.tail &&
      LVAL_TYPE(qexpr->cons.tail) == LVAL_CONS) {
    walk_list_head(ctx, qexpr, hd, qexpr->cons.tail);
  } else {
    walk_each(ctx, qexpr);
  }
}

static bool is_qexpr(valk_lval_t *v) {
  return v && LVAL_TYPE(v) == LVAL_CONS && (v->flags & LVAL_FLAG_QUOTED);
}

static bool is_keyword_str(const char *s) {
  return s[0] == ':';
}

static void collect_param_names(index_ctx_t *ctx, valk_lval_t *formals, int scope_pos) {
  while (formals && LVAL_TYPE(formals) == LVAL_CONS) {
    valk_lval_t *p = formals->cons.head;
    if (LVAL_TYPE(p) == LVAL_SYM) {
      const char *name = p->str;
      if (strcmp(name, "&") == 0) break;
      if (strcmp(name, "::") == 0 || strcmp(name, "->") == 0) {
        formals = formals->cons.tail; // skip annotation value
        if (formals && LVAL_TYPE(formals) == LVAL_CONS)
          formals = formals->cons.tail;
        continue;
      }
      valk_lspi_add_scope_name(ctx, name, true);
      int pos = (int)LVAL_SRC_POS(p);
      int len = (int)strlen(name);
      if (pos >= 0) {
        valk_lspi_emit_semtok(ctx, pos, len, TOK_PARAMETER, 1);
        valk_lspi_emit_ref(ctx, name, pos, len, scope_pos, 1);
        valk_lspi_emit_node(ctx, pos, pos + len, "sym", name);
      }
    }
    formals = formals->cons.tail;
  }
}

static void walk_fun(index_ctx_t *ctx, valk_lval_t *kw, valk_lval_t *tl, bool is_lambda) {
  int kw_pos = (int)LVAL_SRC_POS(kw);
  int kw_len = is_lambda ? 1 : 3;
  if (kw_pos >= 0) valk_lspi_emit_semtok(ctx, kw_pos, kw_len, TOK_KEYWORD, 0);

  u64 tl_len = valk_lval_list_count(tl);
  if (tl_len < 2) { walk_each(ctx, tl); return; }

  valk_lval_t *formals = tl->cons.head;
  valk_lval_t *body = valk_lval_list_nth(tl, 1);

  // For fun: first element of formals is the function name
  valk_lval_t *fname = NULL;
  valk_lval_t *params = formals;
  int param_count = 0;
  if (!is_lambda && formals && LVAL_TYPE(formals) == LVAL_CONS) {
    fname = formals->cons.head;
    params = formals->cons.tail;
    // Count params for arity (stop at &, ::, ->). A varargs function has
    // no fixed arity: store -1 so the validator's exact-count check does
    // not fire on calls with extra args ((fun {f a & as}) called (f 1 2 3)
    // used to be flagged "expects 1 arguments, got 3").
    bool varargs = false;
    valk_lval_t *pc = params;
    while (pc && LVAL_TYPE(pc) == LVAL_CONS) {
      if (LVAL_TYPE(pc->cons.head) == LVAL_SYM) {
        const char *pname = pc->cons.head->str;
        if (strcmp(pname, "&") == 0) { varargs = true; break; }
        if (strcmp(pname, "::") == 0 || strcmp(pname, "->") == 0) break;
      }
      param_count++;
      pc = pc->cons.tail;
    }
    if (varargs) param_count = -1;
    if (fname && LVAL_TYPE(fname) == LVAL_SYM) {
      int fp = (int)LVAL_SRC_POS(fname);
      int fl = (int)strlen(fname->str);
      char qbuf[QUAL_NAME_MAX];
      const char *qname = ctx->is_top_level
        ? valk_lspi_qualify(ctx, fname->str, qbuf, sizeof qbuf) : fname->str;
      if (fp >= 0) {
        valk_lspi_emit_semtok(ctx, fp, fl, TOK_FUNCTION, 1);
        valk_lspi_emit_ref(ctx, qname, fp, fl, -1, 1);
        valk_lspi_emit_node(ctx, fp, fp + fl, "sym", fname->str);
      }
      if (ctx->is_top_level && kw_pos >= 0) {
        const char *doc = valk_lspi_extract_doc_comment(ctx, kw_pos);
        char formals_buf[600];
        snprintf(formals_buf, sizeof formals_buf, "(fun %s ...)",
                 valk_lspi_sig_to_string(ctx, formals));
        valk_lspi_emit_symbol(ctx, qname, kw_pos, SYMKIND_FUNCTION, param_count, doc,
                    formals_buf);
      }
    }
  }

  // Create scope at the position of the full expression
  int scope_pos = kw_pos > 0 ? kw_pos - 1 : kw_pos;
  valk_lspi_push_scope(ctx, scope_pos);
  collect_param_names(ctx, params, scope_pos);
  bool was_top = ctx->is_top_level;
  ctx->is_top_level = false;

  // Body is a qexpr {do ...} — unwrap and walk contents as code
  if (body && LVAL_TYPE(body) == LVAL_CONS && (body->flags & LVAL_FLAG_QUOTED)) {
    // Walk qexpr contents as code
    valk_lval_t *inner = body;
    if (inner->cons.head && LVAL_TYPE(inner->cons.head) == LVAL_SYM &&
        strcmp(inner->cons.head->str, "do") == 0) {
      int dp = (int)LVAL_SRC_POS(inner->cons.head);
      if (dp >= 0) valk_lspi_emit_semtok(ctx, dp, 2, TOK_KEYWORD, 0);
      walk_do(ctx, inner->cons.tail);
    } else {
      walk_qexpr_body(ctx, inner);
    }
  } else {
    walk_expr(ctx, body);
  }
  ctx->is_top_level = was_top;
  valk_lspi_pop_scope(ctx);
}

static void walk_binding(index_ctx_t *ctx, valk_lval_t *kw, valk_lval_t *tl) {
  int kw_pos = (int)LVAL_SRC_POS(kw);
  int kw_len = (int)strlen(kw->str);
  if (kw_pos >= 0) valk_lspi_emit_semtok(ctx, kw_pos, kw_len, TOK_KEYWORD, 0);

  if (!tl || LVAL_TYPE(tl) != LVAL_CONS) return;
  valk_lval_t *binding = tl->cons.head;
  valk_lval_t *vals = tl->cons.tail;

  bool is_global = strcmp(kw->str, "def") == 0;
  int scope_id = is_global ? -1 : valk_lspi_current_scope_pos(ctx);

  // Emit variable declarations from binding
  if (binding && is_qexpr(binding)) {
    valk_lval_t *cur = binding;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      valk_lval_t *v = cur->cons.head;
      if (LVAL_TYPE(v) == LVAL_SYM) {
        char qbuf[QUAL_NAME_MAX];
        const char *qname = (is_global && ctx->is_top_level)
          ? valk_lspi_qualify(ctx, v->str, qbuf, sizeof qbuf) : v->str;
        if (is_global && ctx->is_top_level && kw_pos >= 0) {
          const char *doc = valk_lspi_extract_doc_comment(ctx, kw_pos);
          valk_lspi_emit_symbol(ctx, qname, kw_pos, SYMKIND_VARIABLE, -1, doc, NULL);
        }
        int vp = (int)LVAL_SRC_POS(v);
        int vl = (int)strlen(v->str);
        if (vp >= 0) {
          valk_lspi_emit_semtok(ctx, vp, vl, TOK_VARIABLE, 1);
          valk_lspi_emit_ref(ctx, qname, vp, vl, scope_id, 1);
          valk_lspi_emit_node(ctx, vp, vp + vl, "sym", v->str);
        }
      }
      cur = cur->cons.tail;
    }
  }

  walk_each(ctx, vals);
}

static void walk_do(index_ctx_t *ctx, valk_lval_t *tl) {
  // do blocks: walk children sequentially, adding = bindings to current scope
  while (tl && LVAL_TYPE(tl) == LVAL_CONS) {
    valk_lval_t *child = tl->cons.head;
    // Check if this is (= {var} ...) — add var to current scope names
    if (child && LVAL_TYPE(child) == LVAL_CONS) {
      valk_lval_t *ch = child->cons.head;
      if (ch && LVAL_TYPE(ch) == LVAL_SYM && strcmp(ch->str, "=") == 0) {
        valk_lval_t *binding = valk_lval_list_nth(child, 1);
        if (binding && is_qexpr(binding) && LVAL_TYPE(binding->cons.head) == LVAL_SYM) {
          valk_lspi_add_scope_name(ctx, binding->cons.head->str, false);
        }
      }
    }
    walk_expr(ctx, child);
    tl = tl->cons.tail;
  }
}

static void walk_sym(index_ctx_t *ctx, valk_lval_t *sym) {
  const char *name = sym->str;
  int pos = (int)LVAL_SRC_POS(sym);
  int len = (int)strlen(name);

  if (pos < 0) return;

  if (is_keyword_str(name)) {
    valk_lspi_emit_node_ctx(ctx, pos, pos + len, "sym", name, ctx->current_call);
    valk_lspi_emit_semtok(ctx, pos, len, TOK_PROPERTY, 0);
    return;
  }

  // Check for var:field pattern (lowercase:anything)
  const char *colon = strchr(name, ':');
  if (colon && colon != name) {
    // Split: var part + field parts
    int var_len = (int)(colon - name);
    char var_name[256];
    if (var_len >= (int)sizeof(var_name)) var_len = (int)sizeof(var_name) - 1;
    memcpy(var_name, name, var_len);
    var_name[var_len] = 0;

    // Emit var as scoped ref
    int scope_id = valk_lspi_resolve_scope(ctx, var_name);
    int tok = (scope_id >= 0 && valk_lspi_is_scope_param(ctx, var_name)) ? TOK_PARAMETER : TOK_VARIABLE;
    valk_lspi_emit_semtok(ctx, pos, var_len, tok, 0);
    valk_lspi_emit_ref(ctx, var_name, pos, var_len, scope_id, 0);
    valk_lspi_emit_node(ctx, pos, pos + var_len, "sym", var_name);

    // Emit each :field segment as property
    const char *p = colon;
    int field_pos = pos + var_len;
    while (*p == ':') {
      const char *next = strchr(p + 1, ':');
      int flen = next ? (int)(next - p) : (int)strlen(p);
      valk_lspi_emit_semtok(ctx, field_pos, flen, TOK_PROPERTY, 0);
      valk_lspi_emit_node_ctx(ctx, field_pos, field_pos + flen, "sym", p, var_name);
      field_pos += flen;
      p = next ? next : p + flen;
    }
    return;
  }

  // Check for Type:accessor (uppercase first char + colon)
  if (name[0] >= 'A' && name[0] <= 'Z' && colon) {
    valk_lspi_emit_node(ctx, pos, pos + len, "sym", name);
    valk_lspi_emit_semtok(ctx, pos, len, TOK_TYPE, 0);
    return;
  }

  valk_lspi_emit_node(ctx, pos, pos + len, "sym", name);
  int scope_id = valk_lspi_resolve_scope(ctx, name);
  char qbuf[QUAL_NAME_MAX];
  // Only globals get the module prefix — a lexical binding shadows the
  // module-level name (macro.c rewrite_node consults `shadows` first).
  const char *qname = scope_id < 0 ? valk_lspi_qualify(ctx, name, qbuf, sizeof qbuf) : name;
  if (scope_id >= 0) {
    int tok = valk_lspi_is_scope_param(ctx, name) ? TOK_PARAMETER : TOK_VARIABLE;
    valk_lspi_emit_semtok(ctx, pos, len, tok, 0);
  } else {
    valk_lspi_emit_semtok(ctx, pos, len, TOK_VARIABLE, 0);
    valk_lspi_emit_global_ref(ctx, qname, pos);
  }
  valk_lspi_emit_ref(ctx, qname, pos, len, scope_id, 0);
}

static void walk_list_head(index_ctx_t *ctx, valk_lval_t *expr, valk_lval_t *hd,
                           valk_lval_t *tl) {
  if (LVAL_TYPE(hd) != LVAL_SYM) {
    walk_each(ctx, expr);
    return;
  }

  const char *name = hd->str;

  if (strcmp(name, "fun") == 0)   { walk_fun(ctx, hd, tl, false); return; }
  if (strcmp(name, "\\") == 0)    { walk_fun(ctx, hd, tl, true); return; }
  if (strcmp(name, "def") == 0)   { walk_binding(ctx, hd, tl); return; }
  if (strcmp(name, "=") == 0)     { walk_binding(ctx, hd, tl); return; }
  if (strcmp(name, "type") == 0 && ctx->is_top_level && tl && LVAL_TYPE(tl) == LVAL_CONS) {
    int kp = (int)LVAL_SRC_POS(hd);
    if (kp >= 0) valk_lspi_emit_semtok(ctx, kp, 4, TOK_KEYWORD, 0);
    valk_lval_t *type_name = tl->cons.head;
    if (type_name && LVAL_TYPE(type_name) == LVAL_CONS &&
        (type_name->flags & LVAL_FLAG_QUOTED) &&
        LVAL_TYPE(type_name->cons.head) == LVAL_SYM) {
      const char *tname = type_name->cons.head->str;
      const char *doc = valk_lspi_extract_doc_comment(ctx, kp);
      valk_lspi_emit_symbol(ctx, tname, kp, SYMKIND_TYPE, -1, doc, NULL);
      // Also emit constructor
      valk_lval_t *fields = valk_lval_list_nth(tl, 1);
      int ctor_arity = 0;
      if (fields && LVAL_TYPE(fields) == LVAL_CONS) {
        valk_lval_t *fc = fields;
        while (fc && LVAL_TYPE(fc) == LVAL_CONS) { ctor_arity++; fc = fc->cons.tail; }
        ctor_arity /= 2; // fields are :name Type pairs
      }
      valk_lspi_emit_symbol(ctx, tname, kp, SYMKIND_CONSTRUCTOR, ctor_arity, doc, NULL);
    }
    walk_each(ctx, tl);
    return;
  }
  if (strcmp(name, "sig") == 0 && ctx->is_top_level && tl && LVAL_TYPE(tl) == LVAL_CONS) {
    int kp = (int)LVAL_SRC_POS(hd);
    if (kp >= 0) valk_lspi_emit_semtok(ctx, kp, 3, TOK_KEYWORD, 0);
    // (sig 'name {-> ...}) — extract sig text
    valk_lval_t *sig_name_q = tl->cons.head;
    if (sig_name_q && LVAL_TYPE(sig_name_q) == LVAL_CONS &&
        (sig_name_q->flags & LVAL_FLAG_QUOTED) &&
        LVAL_TYPE(sig_name_q->cons.head) == LVAL_SYM) {
      const char *sname_raw = sig_name_q->cons.head->str;
      // A sig pairs with a local bare def, so it is qualified alongside it
      // at runtime (qualify_sig_if_local in macro.c).
      char sig_qbuf[QUAL_NAME_MAX];
      const char *sname = valk_lspi_qualify(ctx, sname_raw, sig_qbuf, sizeof sig_qbuf);
      valk_lval_t *sig_type = (tl->cons.tail && LVAL_TYPE(tl->cons.tail) == LVAL_CONS)
        ? tl->cons.tail->cons.head : NULL;
      const char *sig_str = sig_type ? valk_lspi_sig_to_string(ctx, sig_type) : "(sig)";
      // Update a sig-less row if one exists; never clobber a fun row's
      // formals string — insert a separate row instead
      sqlite3_stmt *check;
      sqlite3_prepare_v2(ctx->db,
        "SELECT id FROM symbols WHERE file_id=?1 AND name=?2 AND (sig IS NULL OR sig='')",
        -1, &check, NULL);
      sqlite3_bind_int(check, 1, ctx->file_id);
      sqlite3_bind_text(check, 2, sname, -1, SQLITE_STATIC);
      if (sqlite3_step(check) == SQLITE_ROW) {
        int sym_id = sqlite3_column_int(check, 0);
        sqlite3_finalize(check);
        sqlite3_stmt *upd;
        sqlite3_prepare_v2(ctx->db,
          "UPDATE symbols SET sig=?1 WHERE id=?2", -1, &upd, NULL);
        sqlite3_bind_text(upd, 1, sig_str, -1, SQLITE_STATIC);
        sqlite3_bind_int(upd, 2, sym_id);
        sqlite3_step(upd);
        sqlite3_finalize(upd);
      } else {
        sqlite3_finalize(check);
        valk_lspi_emit_symbol(ctx, sname, kp, SYMKIND_FUNCTION, -1, NULL, sig_str);
      }
    }
    walk_each(ctx, tl);
    return;
  }
  if (strcmp(name, "match") == 0) {
    int kp = (int)LVAL_SRC_POS(hd);
    if (kp >= 0) valk_lspi_emit_semtok(ctx, kp, 5, TOK_KEYWORD, 0);
    walk_match(ctx, tl);
    return;
  }
  // quote falls through — walk_expr handles Q-exprs via walk_qexpr_tokens

  if (strcmp(name, "do") == 0) {
    int kp = (int)LVAL_SRC_POS(hd);
    if (kp >= 0) valk_lspi_emit_semtok(ctx, kp, 2, TOK_KEYWORD, 0);
    walk_do(ctx, tl);
    return;
  }

  int pos = (int)LVAL_SRC_POS(hd);
  int slen = source_len(name);

  char qbuf[QUAL_NAME_MAX];

  if (in_set(name, KEYWORDS)) {
    if (pos >= 0) valk_lspi_emit_semtok(ctx, pos, slen, TOK_KEYWORD, 0);
    walk_each(ctx, tl);
  } else if (in_set(name, OPERATORS)) {
    if (pos >= 0) {
      valk_lspi_emit_semtok(ctx, pos, slen, TOK_OPERATOR, 0);
      valk_lspi_emit_node(ctx, pos, pos + slen, "sym", name);
    }
    int scope_id = valk_lspi_resolve_scope(ctx, name);
    const char *qname = scope_id < 0 ? valk_lspi_qualify(ctx, name, qbuf, sizeof qbuf) : name;
    valk_lspi_emit_ref(ctx, qname, pos, slen, scope_id, 0);
    if (scope_id < 0 && pos >= 0) valk_lspi_emit_global_ref(ctx, qname, pos);
    walk_each(ctx, tl);
  } else {
    if (pos >= 0) {
      valk_lspi_emit_semtok(ctx, pos, slen, TOK_FUNCTION, 0);
      valk_lspi_emit_node(ctx, pos, pos + slen, "sym", name);
    }
    int scope_id = valk_lspi_resolve_scope(ctx, name);
    const char *qname = scope_id < 0 ? valk_lspi_qualify(ctx, name, qbuf, sizeof qbuf) : name;
    valk_lspi_emit_ref(ctx, qname, pos, slen, scope_id, 0);
    if (scope_id < 0 && pos >= 0) valk_lspi_emit_global_ref(ctx, qname, pos);
    const char *prev_call = ctx->current_call;
    ctx->current_call = name;
    walk_each(ctx, tl);
    ctx->current_call = prev_call;
  }
}

static void walk_qexpr_tokens(index_ctx_t *ctx, valk_lval_t *qexpr) {
  valk_lval_t *cur = qexpr;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *elem = cur->cons.head;
    if (LVAL_TYPE(elem) == LVAL_SYM) {
      int pos = (int)LVAL_SRC_POS(elem);
      int len = (int)strlen(elem->str);
      if (pos >= 0) {
        valk_lspi_emit_semtok(ctx, pos, len, TOK_VARIABLE, 0);
        valk_lspi_emit_node(ctx, pos, pos + len, "sym", elem->str);
      }
    } else if (LVAL_TYPE(elem) == LVAL_NUM) {
      int pos = (int)LVAL_SRC_POS(elem);
      if (pos >= 0) {
        char buf[32];
        snprintf(buf, sizeof(buf), "%ld", (long)elem->num);
        valk_lspi_emit_semtok(ctx, pos, (int)strlen(buf), TOK_NUMBER, 0);
      }
    } else if (LVAL_TYPE(elem) == LVAL_STR) {
      int pos = (int)LVAL_SRC_POS(elem);
      if (pos >= 0)
        valk_lspi_emit_semtok(ctx, pos, (int)strlen(elem->str) + 2, TOK_STRING, 0);
    } else if (LVAL_TYPE(elem) == LVAL_CONS) {
      walk_qexpr_tokens(ctx, elem);
    }
    cur = cur->cons.tail;
  }
}

static void walk_expr(index_ctx_t *ctx, valk_lval_t *expr) {
  if (!expr || LVAL_TYPE(expr) == LVAL_NIL) return;

  if (LVAL_TYPE(expr) == LVAL_NUM) {
    int pos = (int)LVAL_SRC_POS(expr);
    if (pos >= 0) {
      char buf[32];
      snprintf(buf, sizeof(buf), "%ld", (long)expr->num);
      int len = (int)strlen(buf);
      valk_lspi_emit_semtok(ctx, pos, len, TOK_NUMBER, 0);
      valk_lspi_emit_node(ctx, pos, pos + len, "num", buf);
    }
    return;
  }

  if (LVAL_TYPE(expr) == LVAL_STR) {
    int pos = (int)LVAL_SRC_POS(expr);
    if (pos >= 0) {
      int len = (int)strlen(expr->str);
      valk_lspi_emit_semtok(ctx, pos, len + 2, TOK_STRING, 0);
      valk_lspi_emit_node(ctx, pos, pos + len + 2, "str", expr->str);
    }
    return;
  }

  if (LVAL_TYPE(expr) == LVAL_SYM) {
    walk_sym(ctx, expr);
    return;
  }

  if (LVAL_TYPE(expr) == LVAL_CONS) {
    if (expr->flags & LVAL_FLAG_QUOTED) {
      walk_qexpr_tokens(ctx, expr);
      return;
    }
    valk_lval_t *hd = expr->cons.head;
    valk_lval_t *tl = expr->cons.tail;
    if (!tl || LVAL_TYPE(tl) == LVAL_NIL) {
      walk_expr(ctx, hd);
    } else {
      walk_list_head(ctx, expr, hd, tl);
    }
  }
}

// ---------------------------------------------------------------------------
// Public API — called from Valk as (lsp/index-file db file-id ast text)
// ---------------------------------------------------------------------------

static const char *SQL_DELETE_ALL[] = {
  "DELETE FROM nodes WHERE file_id=?1",
  "DELETE FROM semantic_tokens WHERE file_id=?1",
  "DELETE FROM scoped_refs WHERE file_id=?1",
  "DELETE FROM scopes WHERE file_id=?1",
  "DELETE FROM inlay_hints WHERE file_id=?1",
  "DELETE FROM symbols WHERE file_id=?1",
  "DELETE FROM refs WHERE file_id=?1",
  NULL
};

static const char *SQL_INSERT_NODE =
    "INSERT INTO nodes (file_id,pos,end_pos,type,name,context) VALUES (?1,?2,?3,?4,?5,?6)";
static const char *SQL_INSERT_SEMTOK =
    "INSERT INTO semantic_tokens (file_id,pos,length,token_type,modifiers) VALUES (?1,?2,?3,?4,?5)";
static const char *SQL_INSERT_REF =
    "INSERT INTO scoped_refs (file_id,name,pos,len,scope_id,is_def) VALUES (?1,?2,?3,?4,?5,?6)";
static const char *SQL_INSERT_SCOPE =
    "INSERT INTO scopes (file_id,pos,parent_pos) VALUES (?1,?2,?3)";
static const char *SQL_INSERT_SYMBOL =
    "INSERT INTO symbols (name,file_id,line,col,kind,arity,doc,sig,module) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9)";
static const char *SQL_INSERT_GLOBAL_REF =
    "INSERT INTO refs (name,file_id,line,col) VALUES (?1,?2,?3,?4)";

valk_lval_t *valk_builtin_lsp_index_file(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  u64 argc = valk_lval_list_count(a);
  if (argc < 4) return valk_lval_err("lsp/index-ast: need at least 4 args");

  valk_lval_t *db_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *fid_v = valk_lval_list_nth(a, 1);
  valk_lval_t *ast = valk_lval_list_nth(a, 2);
  valk_lval_t *text_v = valk_lval_list_nth(a, 3);
  bool fast = (argc > 4 && LVAL_TYPE(valk_lval_list_nth(a, 4)) == LVAL_NUM &&
               valk_lval_list_nth(a, 4)->num != 0);

  if (LVAL_TYPE(db_ref) != LVAL_REF || strcmp(db_ref->ref.type, SQLITE_REF_TYPE) != 0)
    return valk_lval_nil(); // LCOV_EXCL_LINE

  sqlite3 *db = db_ref->ref.ptr;
  int file_id = (int)fid_v->num;

  index_ctx_t ctx = {
    .db = db,
    .file_id = file_id,
    .text = text_v->str,
    .text_len = (int)strlen(text_v->str),
    .scope_depth = 0,
    .is_top_level = true,
    .fast_mode = fast,
  };

  // Skip reindex if AST is empty (preserves existing data on parse error)
  if (!ast || LVAL_TYPE(ast) == LVAL_NIL || LVAL_TYPE(ast) == LVAL_ERR) {
    return valk_lval_nil();
  }

  // Delete old data — only relevant tables
  if (fast) {
    sqlite3_stmt *del;
    const char *fast_dels[] = {
      "DELETE FROM symbols WHERE file_id=?1",
      "DELETE FROM refs WHERE file_id=?1",
      NULL
    };
    for (int i = 0; fast_dels[i]; i++) {
      sqlite3_prepare_v2(db, fast_dels[i], -1, &del, NULL);
      sqlite3_bind_int(del, 1, file_id);
      sqlite3_step(del);
      sqlite3_finalize(del);
    }
  } else {
    sqlite3_stmt *del;
    for (int i = 0; SQL_DELETE_ALL[i]; i++) {
      sqlite3_prepare_v2(db, SQL_DELETE_ALL[i], -1, &del, NULL);
      sqlite3_bind_int(del, 1, file_id);
      sqlite3_step(del);
      sqlite3_finalize(del);
    }
  }

  // Prepare insert statements (skip unused in fast mode)
  if (!fast) {
    sqlite3_prepare_v2(db, SQL_INSERT_NODE, -1, &ctx.stmt_node, NULL);
    sqlite3_prepare_v2(db, SQL_INSERT_SEMTOK, -1, &ctx.stmt_semtok, NULL);
    sqlite3_prepare_v2(db, SQL_INSERT_REF, -1, &ctx.stmt_ref, NULL);
    sqlite3_prepare_v2(db, SQL_INSERT_SCOPE, -1, &ctx.stmt_scope, NULL);
  }
  sqlite3_prepare_v2(db, SQL_INSERT_SYMBOL, -1, &ctx.stmt_symbol, NULL);
  sqlite3_prepare_v2(db, SQL_INSERT_GLOBAL_REF, -1, &ctx.stmt_global_ref, NULL);

  // Resolve the file's module prefix and local def set before walking, so
  // forward references inside the file qualify the same way the runtime
  // rewrite does.
  valk_lspi_collect_module_and_defs(&ctx, ast);

  // Single pass
  walk_each(&ctx, ast);

  // Cleanup
  if (!fast) {
    sqlite3_finalize(ctx.stmt_node);
    sqlite3_finalize(ctx.stmt_semtok);
    sqlite3_finalize(ctx.stmt_ref);
    sqlite3_finalize(ctx.stmt_scope);
  }
  sqlite3_finalize(ctx.stmt_symbol);
  sqlite3_finalize(ctx.stmt_global_ref);

  return valk_lval_nil();
}
