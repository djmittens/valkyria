#include "builtins_internal.h"
#include <string.h>

// Generic AST visitor — walks the tree, calls Valk callbacks.
// The traversal and pattern recognition are in C (fast).
// The actions (what to do with each node) are Valk lambdas (extensible).

#define MAX_SCOPE_DEPTH 128

typedef struct {
  valk_lval_t *on_sym;    // (fn name pos len)
  valk_lval_t *on_num;    // (fn name pos)
  valk_lval_t *on_str;    // (fn name pos len)
  valk_lval_t *on_call;   // (fn name pos len)
  valk_lval_t *on_def;    // (fn name pos is_global)
  valk_lval_t *on_fun;    // (fn name params_node pos)
  valk_lval_t *on_type;   // (fn name fields_node pos)
  valk_lval_t *on_sig;    // (fn name sig_node pos)
  valk_lval_t *on_param;  // (fn name pos)
  valk_lval_t *on_ref;    // (fn name pos len scope_pos)

  const char *scope_names[MAX_SCOPE_DEPTH][64];
  int scope_name_count[MAX_SCOPE_DEPTH];
  int scope_pos[MAX_SCOPE_DEPTH];
  int scope_depth;
  int top_level;
} visit_ctx_t;

static void visit_each(visit_ctx_t *ctx, valk_lval_t *exprs);
static void visit_expr(visit_ctx_t *ctx, valk_lval_t *expr);
static void visit_qbody(visit_ctx_t *ctx, valk_lval_t *qexpr);

// --- Callback dispatch ---

static void __attribute__((unused)) fire1(valk_lval_t *handler, valk_lval_t *a) {
  if (!handler) return;
  valk_lval_t *args = valk_lval_cons(a, valk_lval_nil());
  valk_lval_eval_call(handler->fun.env, handler, args);
}

static void fire2(valk_lval_t *handler, valk_lval_t *a, valk_lval_t *b) {
  if (!handler) return;
  valk_lval_t *args = valk_lval_cons(a, valk_lval_cons(b, valk_lval_nil()));
  valk_lval_eval_call(handler->fun.env, handler, args);
}

static void fire3(valk_lval_t *handler, valk_lval_t *a, valk_lval_t *b, valk_lval_t *c) {
  if (!handler) return;
  valk_lval_t *args = valk_lval_cons(a, valk_lval_cons(b, valk_lval_cons(c, valk_lval_nil())));
  valk_lval_eval_call(handler->fun.env, handler, args);
}

static void fire4(valk_lval_t *handler, valk_lval_t *a, valk_lval_t *b,
                   valk_lval_t *c, valk_lval_t *d) {
  if (!handler) return;
  valk_lval_t *args = valk_lval_cons(a, valk_lval_cons(b, valk_lval_cons(c,
    valk_lval_cons(d, valk_lval_nil()))));
  valk_lval_eval_call(handler->fun.env, handler, args);
}

// --- Scope tracking ---

static int current_scope(visit_ctx_t *ctx) {
  return ctx->scope_depth > 0 ? ctx->scope_pos[ctx->scope_depth - 1] : -1;
}

static void push_scope(visit_ctx_t *ctx, int pos) {
  if (ctx->scope_depth >= MAX_SCOPE_DEPTH) return;
  ctx->scope_pos[ctx->scope_depth] = pos;
  ctx->scope_name_count[ctx->scope_depth] = 0;
  ctx->scope_depth++;
}

static void pop_scope(visit_ctx_t *ctx) {
  if (ctx->scope_depth > 0) ctx->scope_depth--;
}

static void add_scope_name(visit_ctx_t *ctx, const char *name) {
  if (ctx->scope_depth <= 0) return;
  int idx = ctx->scope_depth - 1;
  if (ctx->scope_name_count[idx] < 64)
    ctx->scope_names[idx][ctx->scope_name_count[idx]++] = name;
}

static bool in_scope(visit_ctx_t *ctx, const char *name) {
  for (int i = ctx->scope_depth - 1; i >= 0; i--)
    for (int j = 0; j < ctx->scope_name_count[i]; j++)
      if (strcmp(ctx->scope_names[i][j], name) == 0) return true;
  return false;
}

// --- Helpers ---

static bool is_qexpr(valk_lval_t *v) {
  return v && LVAL_TYPE(v) == LVAL_CONS && (v->flags & LVAL_FLAG_QUOTED);
}

// --- Form walkers ---

static void visit_params(visit_ctx_t *ctx, valk_lval_t *params, int scope_pos) {
  (void)scope_pos;
  while (params && LVAL_TYPE(params) == LVAL_CONS) {
    valk_lval_t *p = params->cons.head;
    if (LVAL_TYPE(p) == LVAL_SYM) {
      if (strcmp(p->str, "&") == 0) break;
      add_scope_name(ctx, p->str);
      int pos = (int)LVAL_SRC_POS(p);
      if (pos >= 0)
        fire2(ctx->on_param, valk_lval_str(p->str), valk_lval_num(pos));
    }
    params = params->cons.tail;
  }
}

static void visit_fun(visit_ctx_t *ctx, valk_lval_t *tl, bool is_lambda) {
  u64 tl_len = valk_lval_list_count(tl);
  if (tl_len < 2) { visit_each(ctx, tl); return; }

  valk_lval_t *formals = tl->cons.head;
  valk_lval_t *body = valk_lval_list_nth(tl, 1);
  valk_lval_t *params = formals;

  if (!is_lambda && formals && LVAL_TYPE(formals) == LVAL_CONS) {
    valk_lval_t *fname = formals->cons.head;
    params = formals->cons.tail;
    if (fname && LVAL_TYPE(fname) == LVAL_SYM) {
      int fp = (int)LVAL_SRC_POS(fname);
      int kp = (int)LVAL_SRC_POS(formals);
      fire3(ctx->on_fun, valk_lval_str(fname->str), params, valk_lval_num(kp));
      fire3(ctx->on_def, valk_lval_str(fname->str), valk_lval_num(fp), valk_lval_num(1));
    }
  }

  int kp = formals ? (int)LVAL_SRC_POS(formals) : 0;
  int sp = kp > 0 ? kp - 1 : kp;
  push_scope(ctx, sp);
  visit_params(ctx, params, sp);
  int was_top = ctx->top_level;
  ctx->top_level = 0;
  if (body && is_qexpr(body)) visit_qbody(ctx, body);
  else visit_expr(ctx, body);
  ctx->top_level = was_top;
  pop_scope(ctx);
}

static void visit_binding(visit_ctx_t *ctx, valk_lval_t *kw, valk_lval_t *tl) {
  if (!tl || LVAL_TYPE(tl) != LVAL_CONS) return;
  valk_lval_t *binding = tl->cons.head;
  valk_lval_t *vals = tl->cons.tail;
  bool is_global = strcmp(kw->str, "def") == 0;

  if (binding && is_qexpr(binding)) {
    valk_lval_t *cur = binding;
    while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
      valk_lval_t *v = cur->cons.head;
      if (LVAL_TYPE(v) == LVAL_SYM) {
        int vp = (int)LVAL_SRC_POS(v);
        fire3(ctx->on_def, valk_lval_str(v->str), valk_lval_num(vp),
              valk_lval_num(is_global ? 1 : 0));
        if (!is_global) add_scope_name(ctx, v->str);
      }
      cur = cur->cons.tail;
    }
  }
  visit_each(ctx, vals);
}

static void visit_do(visit_ctx_t *ctx, valk_lval_t *tl) {
  while (tl && LVAL_TYPE(tl) == LVAL_CONS) {
    valk_lval_t *child = tl->cons.head;
    if (child && LVAL_TYPE(child) == LVAL_CONS && !(child->flags & LVAL_FLAG_QUOTED)) {
      valk_lval_t *ch = child->cons.head;
      if (ch && LVAL_TYPE(ch) == LVAL_SYM && strcmp(ch->str, "=") == 0) {
        valk_lval_t *b = valk_lval_list_nth(child, 1);
        if (b && is_qexpr(b) && LVAL_TYPE(b->cons.head) == LVAL_SYM)
          add_scope_name(ctx, b->cons.head->str);
      }
    }
    visit_expr(ctx, child);
    tl = tl->cons.tail;
  }
}

static void visit_match(visit_ctx_t *ctx, valk_lval_t *tl) {
  if (!tl || LVAL_TYPE(tl) != LVAL_CONS) return;
  visit_expr(ctx, tl->cons.head);
  tl = tl->cons.tail;
  while (tl && LVAL_TYPE(tl) == LVAL_CONS) {
    valk_lval_t *clause = tl->cons.head;
    if (clause && is_qexpr(clause)) {
      valk_lval_t *pattern = clause->cons.head;
      int cp = (int)LVAL_SRC_POS(clause);
      push_scope(ctx, cp);
      if (pattern && LVAL_TYPE(pattern) == LVAL_CONS) {
        valk_lval_t *vars = pattern->cons.tail;
        while (vars && LVAL_TYPE(vars) == LVAL_CONS) {
          valk_lval_t *v = vars->cons.head;
          if (v && LVAL_TYPE(v) == LVAL_SYM) {
            add_scope_name(ctx, v->str);
            fire2(ctx->on_param, valk_lval_str(v->str), valk_lval_num((int)LVAL_SRC_POS(v)));
          }
          vars = vars->cons.tail;
        }
      }
      valk_lval_t *body = clause->cons.tail;
      while (body && LVAL_TYPE(body) == LVAL_CONS) {
        valk_lval_t *be = body->cons.head;
        if (be && is_qexpr(be)) visit_qbody(ctx, be);
        else visit_expr(ctx, be);
        body = body->cons.tail;
      }
      pop_scope(ctx);
    }
    tl = tl->cons.tail;
  }
}

static void visit_sym(visit_ctx_t *ctx, valk_lval_t *sym) {
  const char *name = sym->str;
  int pos = (int)LVAL_SRC_POS(sym);
  int slen = (int)strlen(name);
  if (pos < 0) return;
  fire3(ctx->on_sym, valk_lval_str(name), valk_lval_num(pos), valk_lval_num(slen));
  int sp = in_scope(ctx, name) ? current_scope(ctx) : -1;
  fire4(ctx->on_ref, valk_lval_str(name), valk_lval_num(pos),
        valk_lval_num(slen), valk_lval_num(sp));
}

static void visit_head(visit_ctx_t *ctx, valk_lval_t *expr, valk_lval_t *hd, valk_lval_t *tl) {
  if (LVAL_TYPE(hd) != LVAL_SYM) { visit_each(ctx, expr); return; }
  const char *name = hd->str;
  if (strcmp(name, "fun") == 0) { visit_fun(ctx, tl, false); return; }
  if (strcmp(name, "\\") == 0)  { visit_fun(ctx, tl, true); return; }
  if (strcmp(name, "def") == 0 || strcmp(name, "=") == 0)
    { visit_binding(ctx, hd, tl); return; }
  if (strcmp(name, "do") == 0)    { visit_do(ctx, tl); return; }
  if (strcmp(name, "match") == 0) { visit_match(ctx, tl); return; }
  if (strcmp(name, "type") == 0 && ctx->top_level) {
    if (tl && LVAL_TYPE(tl) == LVAL_CONS) {
      valk_lval_t *name_q = tl->cons.head;
      if (name_q && is_qexpr(name_q) && LVAL_TYPE(name_q->cons.head) == LVAL_SYM) {
        valk_lval_t *fields = valk_lval_list_nth(tl, 1);
        int pos = (int)LVAL_SRC_POS(hd);
        fire3(ctx->on_type, valk_lval_str(name_q->cons.head->str),
              fields ? fields : valk_lval_nil(), valk_lval_num(pos));
      }
    }
    visit_each(ctx, tl); return;
  }
  if (strcmp(name, "sig") == 0 && ctx->top_level) {
    if (tl && LVAL_TYPE(tl) == LVAL_CONS) {
      valk_lval_t *name_q = tl->cons.head;
      if (name_q && is_qexpr(name_q) && LVAL_TYPE(name_q->cons.head) == LVAL_SYM) {
        valk_lval_t *sig_body = valk_lval_list_nth(tl, 1);
        int pos = (int)LVAL_SRC_POS(hd);
        fire3(ctx->on_sig, valk_lval_str(name_q->cons.head->str),
              sig_body ? sig_body : valk_lval_nil(), valk_lval_num(pos));
      }
    }
    visit_each(ctx, tl); return;
  }
  // Function call
  int pos = (int)LVAL_SRC_POS(hd);
  int slen = (int)strlen(name);
  if (pos >= 0)
    fire3(ctx->on_call, valk_lval_str(name), valk_lval_num(pos), valk_lval_num(slen));
  int sp = in_scope(ctx, name) ? current_scope(ctx) : -1;
  if (pos >= 0)
    fire4(ctx->on_ref, valk_lval_str(name), valk_lval_num(pos),
          valk_lval_num(slen), valk_lval_num(sp));
  visit_each(ctx, tl);
}

static void visit_qexpr_tokens(visit_ctx_t *ctx, valk_lval_t *qexpr) {
  valk_lval_t *cur = qexpr;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *elem = cur->cons.head;
    if (LVAL_TYPE(elem) == LVAL_SYM) visit_sym(ctx, elem);
    else if (LVAL_TYPE(elem) == LVAL_NUM) {
      int pos = (int)LVAL_SRC_POS(elem);
      if (pos >= 0) {
        char buf[32]; snprintf(buf, sizeof(buf), "%ld", (long)elem->num);
        fire2(ctx->on_num, valk_lval_str(buf), valk_lval_num(pos));
      }
    } else if (LVAL_TYPE(elem) == LVAL_STR) {
      int pos = (int)LVAL_SRC_POS(elem);
      if (pos >= 0)
        fire3(ctx->on_str, valk_lval_str(elem->str), valk_lval_num(pos),
              valk_lval_num((int)strlen(elem->str) + 2));
    } else if (LVAL_TYPE(elem) == LVAL_CONS) {
      visit_qexpr_tokens(ctx, elem);
    }
    cur = cur->cons.tail;
  }
}

static void visit_qbody(visit_ctx_t *ctx, valk_lval_t *qexpr) {
  if (!qexpr || LVAL_TYPE(qexpr) != LVAL_CONS) return;
  valk_lval_t *hd = qexpr->cons.head;
  if (hd && LVAL_TYPE(hd) == LVAL_SYM) {
    if (strcmp(hd->str, "do") == 0) { visit_do(ctx, qexpr->cons.tail); return; }
    if (qexpr->cons.tail && LVAL_TYPE(qexpr->cons.tail) == LVAL_CONS) {
      visit_head(ctx, qexpr, hd, qexpr->cons.tail); return;
    }
  }
  visit_each(ctx, qexpr);
}

static void visit_expr(visit_ctx_t *ctx, valk_lval_t *expr) {
  if (!expr || LVAL_TYPE(expr) == LVAL_NIL) return;
  if (LVAL_TYPE(expr) == LVAL_NUM) {
    int pos = (int)LVAL_SRC_POS(expr);
    if (pos >= 0) {
      char buf[32]; snprintf(buf, sizeof(buf), "%ld", (long)expr->num);
      fire2(ctx->on_num, valk_lval_str(buf), valk_lval_num(pos));
    }
    return;
  }
  if (LVAL_TYPE(expr) == LVAL_STR) {
    int pos = (int)LVAL_SRC_POS(expr);
    if (pos >= 0)
      fire3(ctx->on_str, valk_lval_str(expr->str), valk_lval_num(pos),
            valk_lval_num((int)strlen(expr->str) + 2));
    return;
  }
  if (LVAL_TYPE(expr) == LVAL_SYM) { visit_sym(ctx, expr); return; }
  if (LVAL_TYPE(expr) == LVAL_CONS) {
    if (expr->flags & LVAL_FLAG_QUOTED) { visit_qexpr_tokens(ctx, expr); return; }
    valk_lval_t *hd = expr->cons.head;
    valk_lval_t *tl = expr->cons.tail;
    if (!tl || LVAL_TYPE(tl) == LVAL_NIL) visit_expr(ctx, hd);
    else visit_head(ctx, expr, hd, tl);
  }
}

static void visit_each(visit_ctx_t *ctx, valk_lval_t *exprs) {
  while (exprs && LVAL_TYPE(exprs) == LVAL_CONS) {
    valk_lval_t *e = exprs->cons.head;
    if (e && is_qexpr(e)) visit_qbody(ctx, e);
    else visit_expr(ctx, e);
    exprs = exprs->cons.tail;
  }
}

// --- Resolve handler from ops list ---

static valk_lval_t *resolve_handler(valk_lval_t *ops, const char *key) {
  while (ops && LVAL_TYPE(ops) == LVAL_CONS) {
    valk_lval_t *op = ops->cons.head;
    valk_lval_t *val = valk_plist_get(op, key);
    if (val && LVAL_TYPE(val) == LVAL_FUN) return val;
    ops = ops->cons.tail;
  }
  return NULL;
}

// --- Public API: (ast/visit ast ops) ---

valk_lval_t *valk_builtin_ast_visit(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *ast = valk_lval_list_nth(a, 0);
  valk_lval_t *ops = valk_lval_list_nth(a, 1);

  visit_ctx_t ctx = { .scope_depth = 0, .top_level = 1 };

  ctx.on_sym   = resolve_handler(ops, ":on-sym");
  ctx.on_num   = resolve_handler(ops, ":on-num");
  ctx.on_str   = resolve_handler(ops, ":on-str");
  ctx.on_call  = resolve_handler(ops, ":on-call");
  ctx.on_def   = resolve_handler(ops, ":on-def");
  ctx.on_fun   = resolve_handler(ops, ":on-fun");
  ctx.on_type  = resolve_handler(ops, ":on-type");
  ctx.on_sig   = resolve_handler(ops, ":on-sig");
  ctx.on_param = resolve_handler(ops, ":on-param");
  ctx.on_ref   = resolve_handler(ops, ":on-ref");

  visit_each(&ctx, ast);
  return valk_lval_nil();
}
