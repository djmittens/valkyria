#include "type_infer_internal.h"

#include <stdio.h>
#include <string.h>

#include "common.h"

static void skip_ws(const char *s, int *pos) {
  while (s[*pos] == ' ' || s[*pos] == '\t') (*pos)++;
}

static valk_type_t *parse_type_str_vm(valk_ti_ctx_t *ctx, const char *s,
                                       int *pos, ti_var_map_t *vm);

static valk_type_t *parse_type_atom_vm(valk_ti_ctx_t *ctx, const char *s,
                                        int *pos, ti_var_map_t *vm) {
  skip_ws(s, pos);
  if (s[*pos] == '(') {
    (*pos)++;
    skip_ws(s, pos);
    char name[128];
    int ni = 0;
    while (s[*pos] && s[*pos] != ' ' && s[*pos] != ')' && ni < 126)
      name[ni++] = s[(*pos)++];
    name[ni] = 0;
    bool is_arrow = (strcmp(name, "->") == 0);
    valk_type_t *parts[VALK_TI_MAX_TYPE_ARITY];
    u32 count = 0;
    bool overflowed = false;
    while (true) {
      skip_ws(s, pos);
      if (!s[*pos] || s[*pos] == ')') break;
      if (count >= VALK_TI_MAX_TYPE_ARITY) {
        if (!overflowed) {
          fprintf(stderr, "[type-infer] warning: parsed type '%s' has more than %d parts, truncating\n",
                  name, VALK_TI_MAX_TYPE_ARITY);
          overflowed = true;
        }
        // Skip remaining by parsing and discarding
        parse_type_str_vm(ctx, s, pos, vm);
        continue;
      }
      parts[count] = parse_type_str_vm(ctx, s, pos, vm);
      if (parts[count]) count++;
    }
    if (s[*pos] == ')') (*pos)++;
    if (is_arrow && count >= 1) {
      valk_type_t *ret = parts[count - 1];
      return valk_ti_fun(ctx, parts, count - 1, ret);
    }
    return valk_ti_con(ctx, ti_strdup(ctx, name), parts, count);
  }
  char name[128];
  int ni = 0;
  while (s[*pos] && s[*pos] != ' ' && s[*pos] != ')' && ni < 126)
    name[ni++] = s[(*pos)++];
  name[ni] = 0;
  if (!ni) return valk_ti_fresh_var(ctx);
  if (name[0] >= 'a' && name[0] <= 'z')
    return get_or_create_var(ctx, vm, name[0]);
  if (name[1] == 0 && name[0] >= 'A' && name[0] <= 'Z')
    return get_or_create_var(ctx, vm, name[0]);
  if (strcmp(name, "Num") == 0) return ctx->t_num;
  if (strcmp(name, "Str") == 0) return ctx->t_str;
  if (strcmp(name, "Any") == 0) return valk_ti_fresh_var(ctx);
  return valk_ti_con(ctx, ti_strdup(ctx, name), nullptr, 0);
}

static valk_type_t *parse_type_str_vm(valk_ti_ctx_t *ctx, const char *s,
                                       int *pos, ti_var_map_t *vm) {
  return parse_type_atom_vm(ctx, s, pos, vm);
}

valk_type_t *valk_ti_parse_sig_str(valk_ti_ctx_t *ctx, const char *s) {
  if (!s || !*s) return valk_ti_fresh_var(ctx);
  int pos = 0;
  ti_var_map_t vm = {0};
  return parse_type_str_vm(ctx, s, &pos, &vm);
}

valk_type_scheme_t ti_scheme_from_type(valk_ti_ctx_t *ctx, valk_type_t *ft) {
  u32 vars[128]; u32 vc = 0;
  collect_free_vars(ft, vars, &vc, 128);
  u32 *bv = NULL;
  if (vc > 0) { bv = ti_alloc(ctx, sizeof(u32) * vc); if (bv) memcpy(bv, vars, sizeof(u32) * vc); }
  return (valk_type_scheme_t){.type = ft, .bound_vars = bv, .bound_count = vc};
}

void valk_ti_promote_to_base(valk_ti_ctx_t *ctx) {
  if (!ctx->scope || ctx->scope == ctx->base_scope) return;
  bool was_expr = ctx->use_expr;
  ctx->use_expr = false;
  for (u32 i = 0; i < ctx->scope->count; i++) {
    const char *name = ctx->scope->entries[i].name;
    valk_type_t *t = valk_type_find(ctx->scope->entries[i].scheme.type);
    if (!t || t->kind == VALK_TY_VAR) continue;
    if (valk_ti_scope_lookup(ctx->base_scope, name)) continue;
    char buf[256];
    valk_type_to_str(t, buf, sizeof(buf));
    valk_type_t *pt = valk_ti_parse_sig_str(ctx, buf);
    if (pt) {
      valk_type_scheme_t s = {.type = pt};
      valk_ti_scope_bind(ctx, ctx->base_scope, ti_strdup(ctx, name), s);
    }
  }
  ctx->use_expr = was_expr;
}

void valk_ti_import_new(valk_ti_ctx_t *ctx) {
  if (!ctx->type_env) return;
  bool was_expr = ctx->use_expr;
  ctx->use_expr = false;
  for (u64 i = ctx->imported_sig_count; i < ctx->type_env->sig_count; i++) {
    valk_type_sig_t *sig = ctx->type_env->sigs[i];
    if (valk_ti_scope_lookup(ctx->scope, sig->name)) continue;
    ti_var_map_t vm = {0};
    valk_type_t *params[32];
    for (u64 p = 0; p < sig->param_count && p < 32; p++) {
      int pos = 0;
      params[p] = parse_type_str_vm(ctx, sig->param_types[p], &pos, &vm);
    }
    { int pos = 0;
      valk_type_t *ret = parse_type_str_vm(ctx, sig->return_type, &pos, &vm);
      valk_type_t *ft = valk_ti_fun(ctx, params, (u32)sig->param_count, ret);
      valk_ti_scope_bind(ctx, ctx->scope, ti_strdup(ctx, sig->name), ti_scheme_from_type(ctx, ft));
    }
  }
  ctx->imported_sig_count = ctx->type_env->sig_count;
  for (u64 i = ctx->imported_type_count; i < ctx->type_env->type_count; i++) {
    valk_type_decl_t *decl = ctx->type_env->types[i];
    valk_type_t *parent_type = valk_ti_con(ctx, ti_strdup(ctx, decl->name), nullptr, 0);
    for (u64 c = 0; c < decl->constructor_count; c++) {
      valk_constructor_t *ctor = decl->constructors[c];
      if (valk_ti_scope_lookup(ctx->scope, ctor->name)) continue;
      const char *short_name = strrchr(ctor->name, ':');
      short_name = short_name ? short_name + 1 : ctor->name;
      if (ctor->field_count == 0) {
        valk_type_scheme_t s = {.type = parent_type};
        valk_ti_scope_bind(ctx, ctx->scope, ti_strdup(ctx, ctor->name), s);
        if (short_name != ctor->name)
          valk_ti_scope_bind(ctx, ctx->scope, ti_strdup(ctx, short_name), s);
      } else {
        valk_type_t *field_types[32];
        for (u64 f = 0; f < ctor->field_count && f < 32; f++)
          field_types[f] = valk_ti_parse_sig_str(ctx, ctor->fields[f].type_name);
        valk_type_t *ct = valk_ti_fun(ctx, field_types, (u32)ctor->field_count, parent_type);
        valk_type_scheme_t s = ti_scheme_from_type(ctx, ct);
        valk_ti_scope_bind(ctx, ctx->scope, ti_strdup(ctx, ctor->name), s);
        if (short_name != ctor->name)
          valk_ti_scope_bind(ctx, ctx->scope, ti_strdup(ctx, short_name), s);
      }
    }
  }
  ctx->imported_type_count = ctx->type_env->type_count;
  ctx->base_scope = ctx->scope;
  ctx->use_expr = was_expr;
}

void valk_ti_resolve_scopes(valk_ti_ctx_t *ctx, valk_ti_scope_t *scope) {
  if (!scope) return;
  bool was_expr = ctx->use_expr;
  ctx->use_expr = false;
  for (u32 i = 0; i < scope->count; i++) {
    valk_type_t *t = valk_type_find(scope->entries[i].scheme.type);
    if (t && t->kind == VALK_TY_CON && t->con.arity == 0) {
      scope->entries[i].resolved_type = t->con.name;
    } else if (t && t->kind == VALK_TY_CON) {
      char buf[256];
      valk_type_to_str(t, buf, sizeof(buf));
      scope->entries[i].resolved_type = ti_strdup(ctx, buf);
    } else if (t && t->kind == VALK_TY_FUN && t->fun.ret) {
      valk_type_t *ret = valk_type_find(t->fun.ret);
      if (ret && ret->kind == VALK_TY_CON && ret->con.arity == 0)
        scope->entries[i].resolved_type = ret->con.name;
      else
        scope->entries[i].resolved_type = NULL;
    } else {
      scope->entries[i].resolved_type = NULL;
    }
  }
  for (u32 c = 0; c < scope->child_count; c++)
    valk_ti_resolve_scopes(ctx, scope->children[c]);
  ctx->use_expr = was_expr;
}

valk_ti_scope_t *valk_ti_scope_at_pos(valk_ti_scope_t *scope, i32 pos) {
  if (!scope || pos < 0) return scope;
  for (u32 i = 0; i < scope->child_count; i++) {
    valk_ti_scope_t *c = scope->children[i];
    if (c->start_pos >= 0 && c->start_pos <= pos &&
        (c->end_pos < 0 || c->end_pos >= pos)) {
      valk_ti_scope_t *inner = valk_ti_scope_at_pos(c, pos);
      return inner ? inner : c;
    }
  }
  return scope;
}

const char *valk_ti_scope_resolve(valk_ti_scope_t *scope, const char *name) {
  for (valk_ti_scope_t *s = scope; s; s = s->parent) {
    for (u32 i = s->count; i > 0; i--) {
      if (strcmp(s->entries[i - 1].name, name) == 0) {
        if (s->entries[i - 1].resolved_type)
          return s->entries[i - 1].resolved_type;
        valk_type_t *t = valk_type_find(s->entries[i - 1].scheme.type);
        if (t && t->kind == VALK_TY_CON && t->con.arity == 0)
          return t->con.name;
        return NULL;
      }
    }
  }
  return NULL;
}

const char *valk_ti_lookup_type_name(valk_ti_ctx_t *ctx, const char *name) {
  if (!ctx || !name) return NULL;
  valk_type_t *t = valk_ti_lookup_binding(ctx, name);
  if (!t) {
    valk_type_scheme_t *s = valk_ti_scope_lookup(ctx->scope, name);
    if (!s) return NULL;
    t = valk_type_find(s->type);
  }
  if (!t || t->kind != VALK_TY_CON) return NULL;
  if (t->con.arity == 0) return t->con.name;
  valk_type_to_str(t, ctx->lookup_buf, sizeof(ctx->lookup_buf));
  return ctx->lookup_buf;
}

sz valk_type_to_str(valk_type_t *t, char *buf, sz buf_size) {
  t = valk_type_find(t);
  if (!t) return snprintf(buf, buf_size, "?");
  if (t->kind == VALK_TY_VAR)
    return snprintf(buf, buf_size, "?%u", t->var.id);
  if (t->kind == VALK_TY_CON) {
    if (t->con.arity == 0) return snprintf(buf, buf_size, "%s", t->con.name);
    sz off = snprintf(buf, buf_size, "(%s", t->con.name);
    for (u32 i = 0; i < t->con.arity && off < buf_size; i++) {
      off += snprintf(buf + off, buf_size - off, " ");
      off += valk_type_to_str(t->con.args[i], buf + off, buf_size - off);
    }
    if (off < buf_size) off += snprintf(buf + off, buf_size - off, ")");
    return off;
  }
  if (t->kind == VALK_TY_FUN) {
    sz off = snprintf(buf, buf_size, "(-> ");
    for (u32 i = 0; i < t->fun.param_count && off < buf_size; i++) {
      off += valk_type_to_str(t->fun.params[i], buf + off, buf_size - off);
      if (off < buf_size) off += snprintf(buf + off, buf_size - off, " ");
    }
    off += valk_type_to_str(t->fun.ret, buf + off, buf_size - off);
    if (off < buf_size) off += snprintf(buf + off, buf_size - off, ")");
    return off;
  }
  return snprintf(buf, buf_size, "???");
}
