#include "lsp_types.h"

#include <string.h>

// ---------------------------------------------------------------------------
// Register all builtins with their polymorphic type schemes.
// ---------------------------------------------------------------------------

#define ADD_MONO(name, ty) typed_scope_add(scope, name, scheme_mono(a, ty))
#define ADD_SCHEME(name, sch) typed_scope_add(scope, name, sch)
#define ADD_NAMED(name, params, names, n, ret, var) \
  typed_scope_add(scope, name, scheme_mono(a, ty_fun_named(a, params, names, n, ret, var)))

static void add_variadic_num_op(type_arena_t *a, typed_scope_t *scope, const char *name) {
  valk_type_t *p = ty_num(a);
  ADD_MONO(name, ty_fun(a, &p, 1, ty_num(a), true));
}

static void add_cmp_op(type_arena_t *a, typed_scope_t *scope, const char *name) {
  valk_type_t *ps[2] = {ty_num(a), ty_num(a)};
  ADD_MONO(name, ty_fun(a, ps, 2, ty_num(a), false));
}

static void add_poly_predicate(type_arena_t *a, typed_scope_t *scope, const char *name) {
  valk_type_t *v = ty_var(a);
  valk_type_t *ps[1] = {v};
  valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
  int ids[1] = {v->var.id};
  ADD_SCHEME(name, scheme_poly(a, ids, 1, fn));
}

void lsp_builtin_schemes_init(type_arena_t *a, typed_scope_t *scope) {

  // === Arithmetic ===
  add_variadic_num_op(a, scope, "+");
  add_variadic_num_op(a, scope, "-");
  add_variadic_num_op(a, scope, "*");
  add_variadic_num_op(a, scope, "/");

  // === Comparison ===
  add_cmp_op(a, scope, "<");
  add_cmp_op(a, scope, ">");
  add_cmp_op(a, scope, "<=");
  add_cmp_op(a, scope, ">=");
  {
    // == and != : Any -> Any -> Num  (dynamic equality, any types allowed)
    valk_type_t *ps[2] = {ty_any(a), ty_any(a)};
    ADD_MONO("==", ty_fun(a, ps, 2, ty_num(a), false));
    ADD_MONO("!=", ty_fun(a, ps, 2, ty_num(a), false));
  }

  // === Ordering ===
  {
    // ord : Any -> Any -> Num
    valk_type_t *ps[2] = {ty_any(a), ty_any(a)};
    ADD_MONO("ord", ty_fun(a, ps, 2, ty_num(a), false));
  }

  // === List operations ===
  {
    // head : forall a. List(a) -> a
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {ty_list(a, v)};
    valk_type_t *fn = ty_fun(a, ps, 1, v, false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("head", scheme_poly(a, ids, 1, fn));
  }
  {
    // tail : forall a. List(a) -> List(a)
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {ty_list(a, v)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_list(a, v), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("tail", scheme_poly(a, ids, 1, fn));
  }
  {
    // cons : forall a. a -> List(a) -> List(a)
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[2] = {v, ty_list(a, v)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_list(a, v), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("cons", scheme_poly(a, ids, 1, fn));
  }
  {
    // init : forall a. List(a) -> List(a)
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {ty_list(a, v)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_list(a, v), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("init", scheme_poly(a, ids, 1, fn));
  }
  {
    // join : forall a. List(a)... -> List(a)
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {ty_list(a, v)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_list(a, v), true);
    int ids[1] = {v->var.id};
    ADD_SCHEME("join", scheme_poly(a, ids, 1, fn));
  }
  {
    // list : Any... -> List(Any)  (heterogeneous, can't be polymorphic)
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("list", ty_fun(a, ps, 1, ty_list(a, ty_any(a)), true));
  }
  {
    // len : forall a. List(a) -> Num
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("len", scheme_poly(a, ids, 1, fn));
  }
  {
    // range : Num -> Num -> List(Num)
    valk_type_t *ps[2] = {ty_num(a), ty_num(a)};
    ADD_MONO("range", ty_fun(a, ps, 2, ty_list(a, ty_num(a)), false));
  }
  {
    // repeat : forall a. (Num -> a) -> Num -> List(a)
    valk_type_t *v = ty_var(a);
    valk_type_t *cb_p[1] = {ty_num(a)};
    valk_type_t *ps[2] = {ty_fun(a, cb_p, 1, v, false), ty_num(a)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_list(a, v), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("repeat", scheme_poly(a, ids, 1, fn));
  }

  // === Higher-order functions (prelude overrides) ===
  {
    // map : forall a b. (a -> b) -> List(a) -> List(b)
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[1] = {va};
    valk_type_t *ps[2] = {ty_fun(a, cb_p, 1, vb, false), ty_list(a, va)};
    const char *ns[2] = {"f", "l"};
    valk_type_t *fn = ty_fun_named(a, ps, ns, 2, ty_list(a, vb), false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("map", scheme_poly(a, ids, 2, fn));
  }
  {
    // filter : forall a. (a -> Num) -> List(a) -> List(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *cb_p[1] = {va};
    valk_type_t *ps[2] = {ty_fun(a, cb_p, 1, ty_num(a), false), ty_list(a, va)};
    const char *ns[2] = {"f", "l"};
    valk_type_t *fn = ty_fun_named(a, ps, ns, 2, ty_list(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("filter", scheme_poly(a, ids, 1, fn));
  }
  {
    // foldl : forall a b. (a -> b -> a) -> a -> List(b) -> a
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[2] = {va, vb};
    valk_type_t *ps[3] = {ty_fun(a, cb_p, 2, va, false), va, ty_list(a, vb)};
    const char *ns[3] = {"f", "z", "l"};
    valk_type_t *fn = ty_fun_named(a, ps, ns, 3, va, false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("foldl", scheme_poly(a, ids, 2, fn));
  }
  {
    // list/flat-map : forall a b. List(a) -> (a -> List(b)) -> List(b)
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[1] = {va};
    valk_type_t *ps[2] = {ty_list(a, va), ty_fun(a, cb_p, 1, ty_list(a, vb), false)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_list(a, vb), false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("list/flat-map", scheme_poly(a, ids, 2, fn));
  }
  {
    // list/ap : forall a b. List(a -> b) -> List(a) -> List(b)
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[1] = {va};
    valk_type_t *ps[2] = {ty_list(a, ty_fun(a, cb_p, 1, vb, false)), ty_list(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_list(a, vb), false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("list/ap", scheme_poly(a, ids, 2, fn));
  }
  {
    // exists : forall a. a -> List(a) -> Num
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[2] = {va, ty_list(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_num(a), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("exists", scheme_poly(a, ids, 1, fn));
  }

  // === Dynamic eval and apply ===
  {
    // eval : forall a. a -> a
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {va};
    valk_type_t *fn = ty_fun(a, ps, 1, va, false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("eval", scheme_poly(a, ids, 1, fn));
  }
  {
    // unpack/curry : forall a b. (a -> b) -> List(a) -> b
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[1] = {va};
    valk_type_t *ps[2] = {ty_fun(a, cb_p, 1, vb, false), ty_list(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 2, vb, false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("unpack", scheme_poly(a, ids, 2, fn));
    ADD_SCHEME("curry", scheme_poly(a, ids, 2, fn));
  }
  {
    // pack/uncurry : forall a b. (List(a) -> b) -> a... -> b
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[1] = {ty_list(a, va)};
    valk_type_t *ps[2] = {ty_fun(a, cb_p, 1, vb, false), va};
    valk_type_t *fn = ty_fun(a, ps, 2, vb, true);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("pack", scheme_poly(a, ids, 2, fn));
    ADD_SCHEME("uncurry", scheme_poly(a, ids, 2, fn));
  }

  // === More prelude overrides ===
  {
    // reverse : forall a. List(a) -> List(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_list(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_list(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("reverse", scheme_poly(a, ids, 1, fn));
  }
  {
    // nth : forall a. List(a) -> Num -> a
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[2] = {ty_list(a, va), ty_num(a)};
    valk_type_t *fn = ty_fun(a, ps, 2, va, false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("nth", scheme_poly(a, ids, 1, fn));
  }
  {
    // take/drop/split : forall a. Num -> List(a) -> List(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[2] = {ty_num(a), ty_list(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_list(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("take", scheme_poly(a, ids, 1, fn));
    ADD_SCHEME("drop", scheme_poly(a, ids, 1, fn));
  }
  {
    // sum/product : List(Num) -> Num
    valk_type_t *ps[1] = {ty_list(a, ty_num(a))};
    ADD_MONO("sum", ty_fun(a, ps, 1, ty_num(a), false));
    ADD_MONO("product", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    // do : forall a. a... -> a  (returns last expression)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {va};
    valk_type_t *fn = ty_fun(a, ps, 1, va, true);
    int ids[1] = {va->var.id};
    ADD_SCHEME("do", scheme_poly(a, ids, 1, fn));
  }

  // === PList accessors (prelude) ===
  {
    // get : forall a b. a -> Sym -> b -> b  (plist get with default)
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *ps[3] = {va, ty_sym(a), vb};
    const char *ns[3] = {"pl", "key", "default"};
    valk_type_t *fn = ty_fun_named(a, ps, ns, 3, vb, false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("get", scheme_poly(a, ids, 2, fn));
  }

  // === Type predicates ===
  add_poly_predicate(a, scope, "list?");
  add_poly_predicate(a, scope, "error?");
  add_poly_predicate(a, scope, "ref?");
  add_poly_predicate(a, scope, "num?");
  add_poly_predicate(a, scope, "str?");
  add_poly_predicate(a, scope, "nil?");
  add_poly_predicate(a, scope, "handle?");
  add_poly_predicate(a, scope, "fun?");

  // === I/O ===
  {
    // print/println : Any... -> Nil
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("print", ty_fun(a, ps, 1, ty_nil(a), true));
    ADD_MONO("println", ty_fun(a, ps, 1, ty_nil(a), true));
  }
  {
    // printf : Str -> Any... -> Nil
    valk_type_t *ps[2] = {ty_str(a), ty_any(a)};
    ADD_MONO("printf", ty_fun(a, ps, 2, ty_nil(a), true));
  }
  {
    // error : Str -> Err
    valk_type_t *ps[1] = {ty_str(a)};
    ADD_MONO("error", ty_fun(a, ps, 1, ty_err(a), false));
  }

  // === String operations ===
  {
    valk_type_t *ps[3] = {ty_str(a), ty_str(a), ty_str(a)};
    ADD_MONO("str/replace", ty_fun(a, ps, 3, ty_str(a), false));
  }
  {
    valk_type_t *ps[3] = {ty_str(a), ty_num(a), ty_num(a)};
    ADD_MONO("str/slice", ty_fun(a, ps, 3, ty_str(a), false));
  }
  {
    valk_type_t *ps[2] = {ty_str(a), ty_str(a)};
    ADD_MONO("str/split", ty_fun(a, ps, 2, ty_list(a, ty_str(a)), false));
  }
  {
    valk_type_t *ps[1] = {ty_str(a)};
    ADD_MONO("str->num", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    // str : Any... -> Str
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("str", ty_fun(a, ps, 1, ty_str(a), true));
  }
  {
    // make-string : Any -> Any -> Str
    valk_type_t *ps[2] = {ty_any(a), ty_any(a)};
    ADD_MONO("make-string", ty_fun(a, ps, 2, ty_str(a), false));
  }

  // === File I/O ===
  {
    valk_type_t *ps[1] = {ty_str(a)};
    ADD_MONO("read-file", ty_fun(a, ps, 1, ty_str(a), false));
  }

  // === Async core ===
  {
    // aio/start : () -> Handle(Ref(aio))
    ADD_MONO("aio/start", ty_fun(a, nullptr, 0, ty_handle(a, ty_ref(a, "aio")), false));
  }
  {
    // aio/await : forall a. Handle(a) -> a
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, v)};
    valk_type_t *fn = ty_fun(a, ps, 1, v, false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("aio/await", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/run : Ref(aio) -> Nil
    valk_type_t *ps[1] = {ty_ref(a, "aio")};
    const char *ns[1] = {"sys"};
    ADD_NAMED("aio/run", ps, ns, 1, ty_nil(a), false);
  }
  {
    // aio/stop : Ref(aio) -> Nil
    valk_type_t *ps[1] = {ty_ref(a, "aio")};
    const char *ns[1] = {"sys"};
    ADD_NAMED("aio/stop", ps, ns, 1, ty_nil(a), false);
  }
  {
    // aio/sleep : Ref(aio) -> Num -> Handle(Nil)
    valk_type_t *ps[2] = {ty_ref(a, "aio"), ty_num(a)};
    const char *ns[2] = {"sys", "ms"};
    ADD_NAMED("aio/sleep", ps, ns, 2, ty_handle(a, ty_nil(a)), false);
  }
  {
    // aio/then : forall a b. Handle(a) -> (a -> b) -> Handle(b)
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[1] = {va};
    valk_type_t *ps[2] = {ty_handle(a, va), ty_fun(a, cb_p, 1, vb, false)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, vb), false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("aio/then", scheme_poly(a, ids, 2, fn));
  }
  {
    // aio/catch : forall a. Handle(a) -> (Err -> a) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *cb_p[1] = {ty_err(a)};
    valk_type_t *ps[2] = {ty_handle(a, va), ty_fun(a, cb_p, 1, va, false)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/catch", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/finally : forall a. Handle(a) -> (-> Nil) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[2] = {ty_handle(a, va), ty_fun(a, nullptr, 0, ty_nil(a), false)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/finally", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/pure : forall a. a -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {va};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/pure", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/fail : forall a. Any -> Handle(a)  (accepts Str, Sym, Err, etc.)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_any(a)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/fail", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/result : forall a. Handle(a) -> a
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 1, va, false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/result", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/error : forall a. Handle(a) -> Err
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_err(a), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/error", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/cancel : forall a. Handle(a) -> Sym
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_sym(a), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/cancel", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/cancelled? : forall a. Handle(a) -> Num
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/cancelled?", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/status : forall a. Handle(a) -> Sym
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_sym(a), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/status", scheme_poly(a, ids, 1, fn));
  }

  // === Async combinators ===
  {
    // aio/all : forall a. List(Handle(a)) -> Handle(List(a))
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_list(a, ty_handle(a, va))};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_handle(a, ty_list(a, va)), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/all", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/all-settled : forall a. List(Handle(a)) -> Handle(List(a))
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_list(a, ty_handle(a, va))};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_handle(a, ty_list(a, va)), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/all-settled", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/race : forall a. List(Handle(a)) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_list(a, ty_handle(a, va))};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/race", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/any : forall a. List(Handle(a)) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_list(a, ty_handle(a, va))};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/any", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/within : forall a. Handle(a) -> Num -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[2] = {ty_handle(a, va), ty_num(a)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/within", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/on-cancel : forall a. Handle(a) -> (-> Nil) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[2] = {ty_handle(a, va), ty_fun(a, nullptr, 0, ty_nil(a), false)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/on-cancel", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/scope : forall a. (-> Handle(a)) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *cb_p[1] = {ty_ref(a, "aio")};
    valk_type_t *ps[1] = {ty_fun(a, cb_p, 1, ty_handle(a, va), false)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/scope", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/bracket : forall a b. Handle(a) -> (a -> Nil) -> (a -> b) -> Handle(b)
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *rel_p[1] = {va};
    valk_type_t *use_p[1] = {va};
    valk_type_t *ps[3] = {ty_handle(a, va),
                          ty_fun(a, rel_p, 1, ty_nil(a), false),
                          ty_fun(a, use_p, 1, vb, false)};
    valk_type_t *fn = ty_fun(a, ps, 3, ty_handle(a, vb), false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("aio/bracket", scheme_poly(a, ids, 2, fn));
  }
  {
    // aio/traverse : forall a b. List(a) -> (a -> Handle(b)) -> Handle(List(b))
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[1] = {va};
    valk_type_t *ps[2] = {ty_list(a, va), ty_fun(a, cb_p, 1, ty_handle(a, vb), false)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, ty_list(a, vb)), false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("aio/traverse", scheme_poly(a, ids, 2, fn));
  }

  // === Async scheduling ===
  {
    // aio/schedule : forall a. Ref(aio) -> Num -> (-> a) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_num(a),
                          ty_fun(a, nullptr, 0, va, false)};
    valk_type_t *fn = ty_fun(a, ps, 3, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/schedule", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/interval : forall a. Ref(aio) -> Num -> (-> a) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_num(a),
                          ty_fun(a, nullptr, 0, va, false)};
    valk_type_t *fn = ty_fun(a, ps, 3, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/interval", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/retry : forall a. Ref(aio) -> (-> Handle(a)) -> List(Num) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[3] = {ty_ref(a, "aio"),
                          ty_fun(a, nullptr, 0, ty_handle(a, va), false),
                          ty_list(a, ty_any(a))};
    valk_type_t *fn = ty_fun(a, ps, 3, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/retry", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/never : Ref(aio) -> Handle(Never)
    valk_type_t *ps[1] = {ty_ref(a, "aio")};
    ADD_MONO("aio/never", ty_fun(a, ps, 1, ty_handle(a, ty_never(a)), false));
  }

  // === Async diagnostics ===
  {
    valk_type_t *ps[1] = {ty_ref(a, "aio")};
    ADD_MONO("aio/metrics-json", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/metrics-json-compact", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/metrics-prometheus", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/system-stats-prometheus", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/diagnostics-state-json", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/diagnostics-state-json-compact", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/systems-json", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/on-loop-thread?", ty_fun(a, ps, 1, ty_num(a), false));
    ADD_MONO("aio/pool-stats", ty_fun(a, ps, 1, ty_list(a, ty_num(a)), false));
  }
  {
    // aio/slab-buckets : Ref(aio) -> Str -> Num -> Num -> Num -> Str
    valk_type_t *ps[5] = {ty_ref(a, "aio"), ty_str(a), ty_num(a), ty_num(a), ty_num(a)};
    const char *ns[5] = {"sys", "slab-name", "start", "end", "num-buckets"};
    ADD_NAMED("aio/slab-buckets", ps, ns, 5, ty_str(a), false);
  }

  // === HTTP/2 ===
  {
    // http2/client-request : Ref(aio) -> Str -> Num -> Str -> Handle(Ref(http_response))
    valk_type_t *ps[4] = {ty_ref(a, "aio"), ty_str(a), ty_num(a), ty_str(a)};
    ADD_MONO("http2/client-request",
             ty_fun(a, ps, 4, ty_handle(a, ty_ref(a, "http_response")), false));
  }
  {
    // http2/client-request-with-headers : Ref(aio) -> Str -> Num -> Str -> List(List(Str)) -> Handle(Ref(http_response))
    valk_type_t *ps[5] = {ty_ref(a, "aio"), ty_str(a), ty_num(a), ty_str(a),
                          ty_list(a, ty_list(a, ty_str(a)))};
    ADD_MONO("http2/client-request-with-headers",
             ty_fun(a, ps, 5, ty_handle(a, ty_ref(a, "http_response")), false));
  }
  {
    // http2/response-* : Ref(http_response) -> Str/List
    valk_type_t *ps[1] = {ty_ref(a, "http_response")};
    ADD_MONO("http2/response-body", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("http2/response-status", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("http2/response-headers", ty_fun(a, ps, 1, ty_list(a, ty_str(a)), false));
  }
  {
    // http2/request : Str -> Str -> Str -> Str -> Ref(http_request)
    valk_type_t *ps[4] = {ty_str(a), ty_str(a), ty_str(a), ty_str(a)};
    ADD_MONO("http2/request", ty_fun(a, ps, 4, ty_ref(a, "http_request"), false));
  }
  {
    // http2/request-add-header : Ref(http_request) -> Str -> Str -> Nil
    valk_type_t *ps[3] = {ty_ref(a, "http_request"), ty_str(a), ty_str(a)};
    ADD_MONO("http2/request-add-header", ty_fun(a, ps, 3, ty_nil(a), false));
  }
  {
    // http2/mock-response : Str -> Str -> Str -> Ref(http_response)
    valk_type_t *ps[3] = {ty_str(a), ty_str(a), ty_str(a)};
    ADD_MONO("http2/mock-response", ty_fun(a, ps, 3, ty_ref(a, "http_response"), false));
  }
  {
    // http2/connect : Ref(aio) -> Str -> Num -> (Ref(http_request) -> Nil) -> Nil
    valk_type_t *cb_p[1] = {ty_ref(a, "http_request")};
    valk_type_t *ps[4] = {ty_ref(a, "aio"), ty_str(a), ty_num(a),
                          ty_fun(a, cb_p, 1, ty_nil(a), false)};
    ADD_MONO("http2/connect", ty_fun(a, ps, 4, ty_nil(a), false));
  }
  {
    // http2/server-listen : Ref(aio) -> Num -> (Ref(http_request) -> Any) -> Handle(Ref(http_server))
    valk_type_t *cb_p[1] = {ty_ref(a, "http_request")};
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_num(a),
                          ty_fun(a, cb_p, 1, ty_any(a), false)};
    const char *ns[3] = {"sys", "port", "handler"};
    ADD_NAMED("http2/server-listen", ps, ns, 3,
              ty_handle(a, ty_ref(a, "http_server")), true);
  }
  {
    // http2/server-handle : Ref(http_server) -> (Ref(http_request) -> Nil) -> Nil
    valk_type_t *cb_p[1] = {ty_ref(a, "http_request")};
    valk_type_t *ps[2] = {ty_ref(a, "http_server"),
                          ty_fun(a, cb_p, 1, ty_nil(a), false)};
    ADD_MONO("http2/server-handle", ty_fun(a, ps, 2, ty_nil(a), false));
  }
  {
    // http2/server-port : Handle(Ref(http_server)) -> Num  (also accepts Ref directly)
    valk_type_t *ps[1] = {ty_handle(a, ty_ref(a, "http_server"))};
    ADD_MONO("http2/server-port", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    // http2/server-stop : Handle(Ref(http_server)) -> Handle(Nil)
    valk_type_t *ps[1] = {ty_handle(a, ty_ref(a, "http_server"))};
    ADD_MONO("http2/server-stop", ty_fun(a, ps, 1, ty_handle(a, ty_nil(a)), false));
  }
  {
    // http2/fetch : Ref(aio) -> Str -> Handle(Ref(http_response))
    valk_type_t *ps[2] = {ty_ref(a, "aio"), ty_str(a)};
    ADD_MONO("http2/fetch", ty_fun(a, ps, 2, ty_handle(a, ty_ref(a, "http_response")), false));
    ADD_MONO("http2/fetch-text", ty_fun(a, ps, 2, ty_handle(a, ty_str(a)), false));
    ADD_MONO("http2/fetch-ok?", ty_fun(a, ps, 2, ty_handle(a, ty_num(a)), false));
  }
  {
    // http2/fetch-all : Ref(aio) -> List(Str) -> Handle(List(Ref(http_response)))
    valk_type_t *ps[2] = {ty_ref(a, "aio"), ty_list(a, ty_str(a))};
    ADD_MONO("http2/fetch-all", ty_fun(a, ps, 2,
             ty_handle(a, ty_list(a, ty_ref(a, "http_response"))), false));
    ADD_MONO("http2/fetch-all-text", ty_fun(a, ps, 2,
             ty_handle(a, ty_list(a, ty_str(a))), false));
  }
  {
    // http2/fetch-retry : Ref(aio) -> Str -> Num -> Handle(Ref(http_response))
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_str(a), ty_num(a)};
    ADD_MONO("http2/fetch-retry", ty_fun(a, ps, 3,
             ty_handle(a, ty_ref(a, "http_response")), false));
  }
  {
    // http2/aggregate : Ref(aio) -> List(Str) -> (List(Str) -> Str) -> Handle(Str)
    valk_type_t *cb_p[1] = {ty_list(a, ty_str(a))};
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_list(a, ty_str(a)),
                          ty_fun(a, cb_p, 1, ty_str(a), false)};
    ADD_MONO("http2/aggregate", ty_fun(a, ps, 3, ty_handle(a, ty_str(a)), false));
  }
  {
    // http2/fan-out : Ref(aio) -> Str -> List(Num) -> Handle(List(Str))
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_str(a), ty_list(a, ty_num(a))};
    ADD_MONO("http2/fan-out", ty_fun(a, ps, 3, ty_handle(a, ty_list(a, ty_str(a))), false));
  }
  {
    // http2/health-check : Ref(aio) -> Str -> Handle(Num)
    valk_type_t *ps[2] = {ty_ref(a, "aio"), ty_str(a)};
    ADD_MONO("http2/health-check", ty_fun(a, ps, 2, ty_handle(a, ty_num(a)), false));
  }
  {
    // http2/health-check-all : Ref(aio) -> List(Str) -> Handle(List(Num))
    valk_type_t *ps[2] = {ty_ref(a, "aio"), ty_list(a, ty_str(a))};
    ADD_MONO("http2/health-check-all", ty_fun(a, ps, 2,
             ty_handle(a, ty_list(a, ty_num(a))), false));
  }

  // === Request accessors ===
  {
    valk_type_t *ps[1] = {ty_ref(a, "http_request")};
    ADD_MONO("req/method", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/path", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/scheme", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/authority", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/body", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/headers", ty_fun(a, ps, 1, ty_list(a, ty_str(a)), false));
    ADD_MONO("req/stream-id", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    valk_type_t *ps[2] = {ty_ref(a, "http_request"), ty_str(a)};
    ADD_MONO("req/header", ty_fun(a, ps, 2, ty_str(a), false));
  }

  // === Stream ===
  {
    // stream/open : Ref(http_request) -> Ref(stream)... -> Ref(stream)
    valk_type_t *ps[1] = {ty_ref(a, "http_request")};
    ADD_MONO("stream/open", ty_fun(a, ps, 1, ty_ref(a, "stream"), true));
  }
  {
    valk_type_t *ps[1] = {ty_ref(a, "stream")};
    ADD_MONO("stream/close", ty_fun(a, ps, 1, ty_handle(a, ty_sym(a)), false));
    ADD_MONO("stream/cancel", ty_fun(a, ps, 1, ty_handle(a, ty_sym(a)), false));
    ADD_MONO("stream/closed", ty_fun(a, ps, 1, ty_handle(a, ty_sym(a)), false));
    ADD_MONO("stream/id", ty_fun(a, ps, 1, ty_num(a), false));
    ADD_MONO("stream/writable?", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    // stream/write : Ref(stream) -> Str -> Num
    valk_type_t *ps[2] = {ty_ref(a, "stream"), ty_str(a)};
    ADD_MONO("stream/write", ty_fun(a, ps, 2, ty_num(a), false));
  }
  {
    // stream callbacks return the stream ref for chaining
    valk_type_t *ps[2] = {ty_ref(a, "stream"), ty_fun(a, nullptr, 0, ty_nil(a), false)};
    ADD_MONO("stream/on-close", ty_fun(a, ps, 2, ty_ref(a, "stream"), false));
    ADD_MONO("stream/on-drain", ty_fun(a, ps, 2, ty_ref(a, "stream"), false));
  }
  {
    // stream/set-* : Ref(stream) -> Num -> Ref(stream)
    valk_type_t *ps[2] = {ty_ref(a, "stream"), ty_num(a)};
    ADD_MONO("stream/set-max-session", ty_fun(a, ps, 2, ty_ref(a, "stream"), false));
    ADD_MONO("stream/set-timeout", ty_fun(a, ps, 2, ty_ref(a, "stream"), false));
  }

  // === Memory/GC ===
  ADD_MONO("mem/arena/capacity", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("mem/arena/high-water", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("mem/arena/usage", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("mem/heap/usage", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("mem/heap/hard-limit", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("mem/gc/usage", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("mem/gc/threshold", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("mem/gc/min-interval", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("mem/gc/collect", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("mem/gc/stats", ty_fun(a, nullptr, 0, ty_nil(a), false));
  ADD_MONO("mem/stats", ty_fun(a, nullptr, 0, ty_nil(a), false));
  ADD_MONO("mem/checkpoint/stats", ty_fun(a, nullptr, 0, ty_list(a, ty_num(a)), false));
  {
    valk_type_t *ps[1] = {ty_num(a)};
    ADD_MONO("mem/gc/set-threshold", ty_fun(a, ps, 1, ty_num(a), false));
    ADD_MONO("mem/gc/set-min-interval", ty_fun(a, ps, 1, ty_num(a), false));
    ADD_MONO("mem/heap/set-hard-limit", ty_fun(a, ps, 1, ty_num(a), false));
  }

  // === Metrics ===
  ADD_MONO("metrics/json", ty_fun(a, nullptr, 0, ty_str(a), false));
  ADD_MONO("metrics/prometheus", ty_fun(a, nullptr, 0, ty_str(a), false));
  ADD_MONO("metrics/registry-json", ty_fun(a, nullptr, 0, ty_str(a), false));
  ADD_MONO("metrics/baseline", ty_fun(a, nullptr, 0, ty_ref(a, "metrics"), false));
  ADD_MONO("metrics/collect-delta", ty_fun(a, nullptr, 0, ty_ref(a, "metrics"), false));
  {
    valk_type_t *ps[1] = {ty_ref(a, "metrics")};
    ADD_MONO("metrics/collect-delta-stateless", ty_fun(a, ps, 1, ty_ref(a, "metrics"), false));
    ADD_MONO("metrics/delta-json", ty_fun(a, ps, 1, ty_str(a), false));
  }
  {
    // metrics/counter : Str -> Str... -> Ref(metrics)
    valk_type_t *ps[1] = {ty_str(a)};
    ADD_MONO("metrics/counter", ty_fun(a, ps, 1, ty_ref(a, "metrics"), true));
    ADD_MONO("metrics/gauge", ty_fun(a, ps, 1, ty_ref(a, "metrics"), true));
    ADD_MONO("metrics/histogram", ty_fun(a, ps, 1, ty_ref(a, "metrics"), true));
  }
  {
    // metrics/counter-inc : Ref(metrics) -> Num -> Nil  (optional amount)
    valk_type_t *ps2[2] = {ty_ref(a, "metrics"), ty_num(a)};
    ADD_MONO("metrics/counter-inc", ty_fun(a, ps2, 2, ty_nil(a), false));
  }
  {
    // metrics/histogram-observe : Ref(metrics) -> Num -> Nil
    valk_type_t *ps[2] = {ty_ref(a, "metrics"), ty_num(a)};
    ADD_MONO("metrics/histogram-observe", ty_fun(a, ps, 2, ty_nil(a), false));
  }
  {
    // metrics/gauge-set : Ref(metrics) -> Num -> Nil
    valk_type_t *ps[2] = {ty_ref(a, "metrics"), ty_num(a)};
    ADD_MONO("metrics/gauge-set", ty_fun(a, ps, 2, ty_nil(a), false));
  }
  {
    // metrics/gauge-inc/dec : Ref(metrics) -> Nil
    valk_type_t *ps[1] = {ty_ref(a, "metrics")};
    ADD_MONO("metrics/gauge-inc", ty_fun(a, ps, 1, ty_nil(a), false));
    ADD_MONO("metrics/gauge-dec", ty_fun(a, ps, 1, ty_nil(a), false));
  }

  // === Random ===
  {
    valk_type_t *ps[2] = {ty_num(a), ty_num(a)};
    ADD_MONO("rand", ty_fun(a, ps, 2, ty_num(a), false));
  }
  {
    valk_type_t *ps[1] = {ty_num(a)};
    ADD_MONO("rand-seed", ty_fun(a, ps, 1, ty_nil(a), false));
  }

  // === Misc ===
  ADD_MONO("time-us", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("stack-depth", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("penv", ty_fun(a, nullptr, 0, ty_list(a, ty_str(a)), false));
  {
    // exit/shutdown : Num -> Num  (optional arg, but Num -> Num is the typed sig)
    valk_type_t *ps[1] = {ty_num(a)};
    ADD_MONO("exit", ty_fun(a, ps, 1, ty_num(a), false));
    ADD_MONO("shutdown", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    valk_type_t *ps[1] = {ty_num(a)};
    ADD_MONO("sleep", ty_fun(a, ps, 1, ty_nil(a), false));
  }

  // === Coverage ===
  {
    valk_type_t *ps[2] = {ty_num(a), ty_num(a)};
    ADD_MONO("coverage-branch", ty_fun(a, ps, 2, ty_num(a), false));
  }
  {
    // coverage-mark/record : forall a. a -> a  (identity with side effect)
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, v, false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("coverage-mark", scheme_poly(a, ids, 1, fn));
  }
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, v, false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("coverage-record", scheme_poly(a, ids, 1, fn));
  }

  // === Source location ===
  {
    // source-* : forall a. a -> Num/Str
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    int ids[1] = {v->var.id};
    ADD_SCHEME("source-line", scheme_poly(a, ids, 1, ty_fun(a, ps, 1, ty_num(a), false)));
  }
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    int ids[1] = {v->var.id};
    ADD_SCHEME("source-column", scheme_poly(a, ids, 1, ty_fun(a, ps, 1, ty_num(a), false)));
  }
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    int ids[1] = {v->var.id};
    ADD_SCHEME("source-file", scheme_poly(a, ids, 1, ty_fun(a, ps, 1, ty_str(a), false)));
  }

  // === Context ===
  ADD_MONO("ctx/deadline", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("ctx/deadline-exceeded?", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("ctx/locals", ty_fun(a, nullptr, 0, ty_list(a, ty_any(a)), false));
  {
    // ctx/get : Sym -> Any  (key lookup, can't be more precise)
    valk_type_t *ps[1] = {ty_sym(a)};
    ADD_MONO("ctx/get", ty_fun(a, ps, 1, ty_any(a), false));
  }

  // === Trace ===
  ADD_MONO("trace/id", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("trace/span", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("trace/parent-span", ty_fun(a, nullptr, 0, ty_num(a), false));

  // === VM ===
  ADD_MONO("vm/metrics-json", ty_fun(a, nullptr, 0, ty_str(a), true));
  ADD_MONO("vm/metrics-json-compact", ty_fun(a, nullptr, 0, ty_str(a), true));
  ADD_MONO("vm/metrics-prometheus", ty_fun(a, nullptr, 0, ty_str(a), true));

  // === Test ===
  ADD_MONO("test/capture-start", ty_fun(a, nullptr, 0, ty_ref(a, "capture"), false));
  {
    valk_type_t *ps[1] = {ty_ref(a, "capture")};
    ADD_MONO("test/capture-stop", ty_fun(a, ps, 1, ty_str(a), false));
  }

  // === Logging ===
  {
    valk_type_t *ps[1] = {ty_str(a)};
    ADD_MONO("sys/log/set-level", ty_fun(a, ps, 1, ty_str(a), false));
  }
}
