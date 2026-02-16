#pragma once
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

// ---------------------------------------------------------------------------
// Hindley-Milner type system for Valkyria.
//
// Type constructors: List(a), Handle(a), Ref(tag), Fun(a1..an -> r)
// Type variables with unification (Algorithm W).
// Let-polymorphism via type schemes (forall a b. ...).
// Type narrowing via predicates (num?, str?, error?, list?, ref?).
// ---------------------------------------------------------------------------

typedef enum {
  TY_NUM = 0,
  TY_STR,
  TY_SYM,
  TY_NIL,
  TY_ERR,
  TY_LIST,
  TY_HANDLE,
  TY_REF,
  TY_FUN,
  TY_VAR,
  TY_ANY,
  TY_UNION,
  TY_NEVER,
  TY_NAMED,
  TY_PLIST,
  TY_TUPLE,
  TY__COUNT,
} valk_type_kind_e;

#define TY_MAX_UNION   4
#define TY_MAX_PARAMS  8

typedef struct valk_type valk_type_t;

struct valk_type {
  valk_type_kind_e kind;
  union {
    struct { valk_type_t *elem; } list;

    struct { valk_type_t *inner; } handle;

    struct { const char *tag; } ref;

    struct {
      valk_type_t *params[TY_MAX_PARAMS];
      const char *param_names[TY_MAX_PARAMS];
      int param_count;
      valk_type_t *ret;
      bool variadic;
    } fun;

    struct {
      int id;
      valk_type_t *link;
    } var;

    struct {
      valk_type_t *members[TY_MAX_UNION];
      int count;
    } onion;

    struct {
      const char *name;
      valk_type_t *params[TY_MAX_PARAMS];
      int param_count;
    } named;

    struct {
      const char *keys[TY_MAX_PARAMS];
      valk_type_t *vals[TY_MAX_PARAMS];
      int count;
    } plist;

    struct {
      valk_type_t *elems[TY_MAX_PARAMS];
      int count;
    } tuple;
  };
};

// ---------------------------------------------------------------------------
// Type arena — bump allocator for types within a single analysis pass.
// ---------------------------------------------------------------------------

#define TYPE_ARENA_BLOCK_SIZE (8192)

typedef struct type_arena_block {
  struct type_arena_block *next;
  size_t used;
  char data[TYPE_ARENA_BLOCK_SIZE];
} type_arena_block_t;

typedef struct {
  type_arena_block_t *head;
  int next_var_id;
} type_arena_t;

void type_arena_init(type_arena_t *a);
void type_arena_free(type_arena_t *a);
valk_type_t *type_arena_alloc(type_arena_t *a);
char *type_arena_strdup(type_arena_t *a, const char *s);

// ---------------------------------------------------------------------------
// Type constructors (arena-allocated)
// ---------------------------------------------------------------------------

valk_type_t *ty_num(type_arena_t *a);
valk_type_t *ty_str(type_arena_t *a);
valk_type_t *ty_sym(type_arena_t *a);
valk_type_t *ty_nil(type_arena_t *a);
valk_type_t *ty_err(type_arena_t *a);
valk_type_t *ty_any(type_arena_t *a);
valk_type_t *ty_never(type_arena_t *a);

valk_type_t *ty_ground(type_arena_t *a, valk_type_kind_e kind);
valk_type_t *ty_list(type_arena_t *a, valk_type_t *elem);
valk_type_t *ty_handle(type_arena_t *a, valk_type_t *inner);
valk_type_t *ty_ref(type_arena_t *a, const char *tag);
valk_type_t *ty_fun(type_arena_t *a, valk_type_t **params, int n, valk_type_t *ret, bool variadic);
valk_type_t *ty_fun_named(type_arena_t *a, valk_type_t **params, const char **names, int n, valk_type_t *ret, bool variadic);
valk_type_t *ty_var(type_arena_t *a);

valk_type_t *ty_named(type_arena_t *a, const char *name, valk_type_t **params, int n);

valk_type_t *ty_plist(type_arena_t *a, const char **keys, valk_type_t **vals, int n);
valk_type_t *ty_plist_get(const valk_type_t *plist, const char *key);

valk_type_t *ty_tuple(type_arena_t *a, valk_type_t **elems, int n);

valk_type_t *ty_union2(type_arena_t *a, valk_type_t *t1, valk_type_t *t2);
valk_type_t *ty_union3(type_arena_t *a, valk_type_t *t1, valk_type_t *t2, valk_type_t *t3);
valk_type_t *ty_join(type_arena_t *a, const valk_type_t *t1, const valk_type_t *t2);

// ---------------------------------------------------------------------------
// Type operations
// ---------------------------------------------------------------------------

valk_type_t *ty_resolve(valk_type_t *ty);
bool ty_equal(const valk_type_t *a, const valk_type_t *b);
bool ty_compatible(const valk_type_t *expected, const valk_type_t *actual);
bool ty_unify(type_arena_t *a, valk_type_t *t1, valk_type_t *t2);
bool ty_occurs(int var_id, valk_type_t *ty);
bool ty_has_unresolved_var(const valk_type_t *ty);
bool ty_contains_any(const valk_type_t *ty);
bool ty_has_inference_failure(const valk_type_t *ty);

const char *valk_type_name(const valk_type_t *ty);
char *valk_type_display(const valk_type_t *ty);
char *valk_type_display_pretty(const valk_type_t *ty);

// ---------------------------------------------------------------------------
// Type schemes — polymorphic types with bound variables.
// forall a1 a2 ... an. body
// ---------------------------------------------------------------------------

#define SCHEME_MAX_VARS 8

typedef struct {
  int var_ids[SCHEME_MAX_VARS];
  int var_count;
  valk_type_t *body;
} type_scheme_t;

type_scheme_t *scheme_mono(type_arena_t *a, valk_type_t *ty);
type_scheme_t *scheme_poly(type_arena_t *a, int *var_ids, int var_count, valk_type_t *body);
valk_type_t *scheme_instantiate(type_arena_t *a, const type_scheme_t *scheme);
type_scheme_t *scheme_generalize(type_arena_t *a, valk_type_t *ty, int floor_var_id);

// ---------------------------------------------------------------------------
// Typed scope — name→scheme bindings with parent chain (lexical scoping).
// ---------------------------------------------------------------------------

typedef struct {
  char *name;
  type_scheme_t *scheme;
} typed_binding_t;

typedef struct typed_scope {
  typed_binding_t *bindings;
  size_t count;
  size_t cap;
  struct typed_scope *parent;
} typed_scope_t;

typed_scope_t *typed_scope_push(type_arena_t *a, typed_scope_t *parent);
void typed_scope_pop(typed_scope_t *s);
void typed_scope_add(typed_scope_t *s, const char *name, type_scheme_t *scheme);
void typed_scope_add_mono(typed_scope_t *s, const char *name, valk_type_t *ty);
type_scheme_t *typed_scope_lookup(typed_scope_t *s, const char *name);

// ---------------------------------------------------------------------------
// Inference context
// ---------------------------------------------------------------------------

#include "lsp_doc.h"

// ---------------------------------------------------------------------------
// Inlay hints — type annotations shown inline by the editor.
// ---------------------------------------------------------------------------

typedef enum {
  INLAY_TYPE = 1,
  INLAY_PARAM = 2,
} inlay_hint_kind_e;

typedef struct {
  int offset;
  inlay_hint_kind_e kind;
  char *label;
  valk_type_t *type;
  bool is_return;
} lsp_inlay_hint_t;

#define MAX_PLIST_TYPES 32

typedef struct {
  const char *name;
  const char *keys[TY_MAX_PARAMS];
  int key_count;
  type_scheme_t *ctor_scheme;
} plist_type_reg_t;

typedef struct {
  type_arena_t *arena;
  typed_scope_t *scope;
  lsp_document_t *doc;
  const char *text;
  int *cursor;
  int floor_var_id;
  int hover_offset;
  valk_type_t *hover_result;
  lsp_inlay_hint_t *hints;
  size_t hint_count;
  size_t hint_cap;
  bool collect_hints;
  plist_type_reg_t plist_types[MAX_PLIST_TYPES];
  int plist_type_count;
} infer_ctx_t;

void infer_ctx_add_hint(infer_ctx_t *ctx, int offset, inlay_hint_kind_e kind,
                        const char *label);

// ---------------------------------------------------------------------------
// Annotation parsing (lsp_infer_ann.c)
// ---------------------------------------------------------------------------

#define ANN_MAX_VARS 16

typedef struct {
  char *names[ANN_MAX_VARS];
  valk_type_t *vars[ANN_MAX_VARS];
  int count;
  type_arena_t *arena;
} ann_var_map_t;

typedef struct valk_lval_t valk_lval_t;

valk_type_t *ann_var(ann_var_map_t *m, const char *name);
valk_type_t *parse_type_ann(ann_var_map_t *m, valk_lval_t *node);
bool is_ann_sym(valk_lval_t *node, const char *s);

typedef struct {
  valk_type_t *param_types[TY_MAX_PARAMS];
  valk_lval_t *param_nodes[TY_MAX_PARAMS];
  int param_count;
  bool variadic;
  valk_type_t *ret_ann;
} parsed_formals_t;

void parse_formals(infer_ctx_t *ctx, valk_lval_t *formals,
                   typed_scope_t *inner, parsed_formals_t *out);

// ---------------------------------------------------------------------------
// PList inference (lsp_infer_plist.c)
// ---------------------------------------------------------------------------

valk_type_t *infer_plist_from_list_call(infer_ctx_t *ctx, valk_lval_t *rest);
valk_type_t *infer_plist_get(infer_ctx_t *ctx, valk_lval_t *rest);
valk_type_t *infer_plist_set(infer_ctx_t *ctx, valk_lval_t *rest);
valk_type_t *infer_plist_has(infer_ctx_t *ctx, valk_lval_t *rest);
valk_type_t *infer_plist_keys_vals(infer_ctx_t *ctx, const char *name, valk_lval_t *rest);

// ---------------------------------------------------------------------------
// Type inference entry point
// ---------------------------------------------------------------------------

int infer_count_list(valk_lval_t *rest);
valk_type_t *infer_expr(infer_ctx_t *ctx, valk_lval_t *expr);

// ---------------------------------------------------------------------------
// Builtin type scheme table (populated by init)
// ---------------------------------------------------------------------------

void lsp_builtin_schemes_init(type_arena_t *a, typed_scope_t *scope);

// Cross-file type inference (lsp_loads.c)
#include "lsp_doc.h"
void init_typed_scope_with_loads(type_arena_t *arena, typed_scope_t *scope,
                                lsp_document_t *doc);
void init_typed_scope_with_plist_reg(type_arena_t *arena, typed_scope_t *scope,
                                    lsp_document_t *doc,
                                    plist_type_reg_t *out_regs, int *out_count);

// Inlay hint collection (lsp_analysis.c)
void lsp_collect_inlay_hints(lsp_document_t *doc,
                             lsp_inlay_hint_t **out_hints, size_t *out_count);
