#include "lsp_types.h"

#include <string.h>

// ---------------------------------------------------------------------------
// Register all builtins with their polymorphic type schemes.
//
// Key type schemes:
//   head       : forall a. List(a) -> a
//   tail       : forall a. List(a) -> List(a)|Nil
//   cons       : forall a. a -> List(a) -> List(a)
//   aio/start  : () -> Handle(Ref(aio))
//   aio/await  : forall a. Handle(a) -> a
//   aio/then   : forall a b. Handle(a) -> (a -> Handle(b)) -> Handle(b)
//   aio/sleep  : Ref(aio) -> Num -> Handle(Nil)
//   http2/client-request : Ref(aio) -> Str -> Num -> Str -> Handle(Ref(http_response))
//   http2/response-body  : Ref(http_response) -> Str
//   http2/response-status: Ref(http_response) -> Str
// ---------------------------------------------------------------------------

#define ADD_MONO(name, ty) typed_scope_add(scope, name, scheme_mono(a, ty))
#define ADD_SCHEME(name, sch) typed_scope_add(scope, name, sch)

static void add_variadic_num_op(type_arena_t *a, typed_scope_t *scope, const char *name) {
  valk_type_t *p = ty_num(a);
  ADD_MONO(name, ty_fun(a, &p, 1, ty_num(a), true));
}

static void add_cmp_op(type_arena_t *a, typed_scope_t *scope, const char *name) {
  valk_type_t *ps[2] = {ty_num(a), ty_num(a)};
  ADD_MONO(name, ty_fun(a, ps, 2, ty_num(a), false));
}

static void add_eq_op(type_arena_t *a, typed_scope_t *scope, const char *name) {
  valk_type_t *ps[2] = {ty_any(a), ty_any(a)};
  ADD_MONO(name, ty_fun(a, ps, 2, ty_num(a), false));
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
  add_eq_op(a, scope, "==");
  add_eq_op(a, scope, "!=");

  // === Ordering ===
  {
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
    // cons : Any -> Any -> List(Any)
    valk_type_t *ps[2] = {ty_any(a), ty_any(a)};
    ADD_MONO("cons", ty_fun(a, ps, 2, ty_list(a, ty_any(a)), false));
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
    // list : Any... -> List(Any)
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("list", ty_fun(a, ps, 1, ty_list(a, ty_any(a)), true));
  }
  {
    // len : Any -> Num  (works on List, Str, plist, etc.)
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("len", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    // range : Num -> Num -> List(Num)
    valk_type_t *ps[2] = {ty_num(a), ty_num(a)};
    ADD_MONO("range", ty_fun(a, ps, 2, ty_list(a, ty_num(a)), false));
  }
  {
    // repeat : forall a. (Any -> a) -> Num -> List(a)
    valk_type_t *v = ty_var(a);
    valk_type_t *cb_p[1] = {ty_any(a)};
    valk_type_t *ps[2] = {ty_fun(a, cb_p, 1, v, false), ty_num(a)};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_list(a, v), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("repeat", scheme_poly(a, ids, 1, fn));
  }
  {
    // list? : forall a. a -> Num
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("list?", scheme_poly(a, ids, 1, fn));
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
    valk_type_t *ps[2] = {ty_any(a), ty_any(a)};
    ADD_MONO("make-string", ty_fun(a, ps, 2, ty_str(a), false));
  }

  // === Type predicates ===
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("error?", scheme_poly(a, ids, 1, fn));
  }
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("ref?", scheme_poly(a, ids, 1, fn));
  }
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("num?", scheme_poly(a, ids, 1, fn));
  }
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("str?", scheme_poly(a, ids, 1, fn));
  }
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("nil?", scheme_poly(a, ids, 1, fn));
  }
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("handle?", scheme_poly(a, ids, 1, fn));
  }
  {
    valk_type_t *v = ty_var(a);
    valk_type_t *ps[1] = {v};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_num(a), false);
    int ids[1] = {v->var.id};
    ADD_SCHEME("fun?", scheme_poly(a, ids, 1, fn));
  }

  // === I/O ===
  {
    // print : Any... -> Nil
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("print", ty_fun(a, ps, 1, ty_nil(a), true));
  }
  {
    // println : Any... -> Nil
    valk_type_t *ps[1] = {ty_any(a)};
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

  // === File I/O ===
  {
    valk_type_t *ps[1] = {ty_str(a)};
    ADD_MONO("read-file", ty_fun(a, ps, 1, ty_str(a), false));
  }

  // === Async core ===
  {
    // aio/start : () -> Handle(Ref(aio))
    valk_type_t *ret = ty_handle(a, ty_ref(a, "aio"));
    ADD_MONO("aio/start", ty_fun(a, nullptr, 0, ret, false));
  }
  {
    // aio/await : Handle(A) -> A  (polymorphic)
    int floor = a->next_var_id;
    valk_type_t *inner = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, inner)};
    valk_type_t *fn = ty_fun(a, ps, 1, inner, false);
    typed_scope_add(scope, "aio/await", scheme_generalize(a, fn, floor));
  }
  {
    // aio/run : Ref(aio) -> Nil
    valk_type_t *ps[1] = {ty_ref(a, "aio")};
    ADD_MONO("aio/run", ty_fun(a, ps, 1, ty_nil(a), false));
  }
  {
    // aio/stop : Ref(aio) -> Nil
    valk_type_t *ps[1] = {ty_ref(a, "aio")};
    ADD_MONO("aio/stop", ty_fun(a, ps, 1, ty_nil(a), false));
  }
  {
    // aio/sleep : Ref(aio) -> Num -> Handle(Nil)
    valk_type_t *ps[2] = {ty_ref(a, "aio"), ty_num(a)};
    ADD_MONO("aio/sleep", ty_fun(a, ps, 2, ty_handle(a, ty_nil(a)), false));
  }
  {
    // aio/then : forall a b. Handle(a) -> (a -> b) -> Handle(b)
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[1] = {va};
    valk_type_t *cb = ty_fun(a, cb_p, 1, vb, false);
    valk_type_t *ps[2] = {ty_handle(a, va), cb};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, vb), false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("aio/then", scheme_poly(a, ids, 2, fn));
  }
  {
    // aio/catch : forall a. Handle(a) -> (Any -> a) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *cb_p[1] = {ty_any(a)};
    valk_type_t *cb = ty_fun(a, cb_p, 1, va, false);
    valk_type_t *ps[2] = {ty_handle(a, va), cb};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/catch", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/finally : forall a. Handle(a) -> (-> Any) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *cb = ty_fun(a, nullptr, 0, ty_any(a), false);
    valk_type_t *ps[2] = {ty_handle(a, va), cb};
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
    // aio/fail : forall a. Any -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_any(a)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/fail", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/result : Any -> Any
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("aio/result", ty_fun(a, ps, 1, ty_any(a), false));
  }
  {
    // aio/error : forall a. Handle(a) -> Any
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_any(a), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/error", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/cancel : forall a. Handle(a) -> Any
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_any(a), false);
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
    // aio/status : forall a. Handle(a) -> Any
    valk_type_t *va = ty_var(a);
    valk_type_t *ps[1] = {ty_handle(a, va)};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_any(a), false);
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
    // aio/on-cancel : forall a. Handle(a) -> (-> Any) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *cb = ty_fun(a, nullptr, 0, ty_any(a), false);
    valk_type_t *ps[2] = {ty_handle(a, va), cb};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/on-cancel", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/scope : forall a. (Any... -> a) -> Handle(a)
    valk_type_t *va = ty_var(a);
    valk_type_t *cb_p[1] = {ty_any(a)};
    valk_type_t *cb = ty_fun(a, cb_p, 1, va, true);
    valk_type_t *ps[1] = {cb};
    valk_type_t *fn = ty_fun(a, ps, 1, ty_handle(a, va), false);
    int ids[1] = {va->var.id};
    ADD_SCHEME("aio/scope", scheme_poly(a, ids, 1, fn));
  }
  {
    // aio/bracket : forall a b. Handle(a) -> (a -> Any) -> (a -> b) -> Handle(b)
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *rel_p[1] = {va};
    valk_type_t *rel = ty_fun(a, rel_p, 1, ty_any(a), false);
    valk_type_t *use_p[1] = {va};
    valk_type_t *use = ty_fun(a, use_p, 1, vb, false);
    valk_type_t *ps[3] = {ty_handle(a, va), rel, use};
    valk_type_t *fn = ty_fun(a, ps, 3, ty_handle(a, vb), false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("aio/bracket", scheme_poly(a, ids, 2, fn));
  }
  {
    // aio/traverse : forall a b. List(a) -> (a -> b) -> Handle(List(b))
    valk_type_t *va = ty_var(a);
    valk_type_t *vb = ty_var(a);
    valk_type_t *cb_p[1] = {va};
    valk_type_t *cb = ty_fun(a, cb_p, 1, vb, false);
    valk_type_t *ps[2] = {ty_list(a, va), cb};
    valk_type_t *fn = ty_fun(a, ps, 2, ty_handle(a, ty_list(a, vb)), false);
    int ids[2] = {va->var.id, vb->var.id};
    ADD_SCHEME("aio/traverse", scheme_poly(a, ids, 2, fn));
  }

  // === Async scheduling ===
  {
    // aio/schedule : Ref(aio) -> Num -> (Any... -> Any) -> Handle(Any)
    valk_type_t *cb_p[1] = {ty_any(a)};
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_num(a), ty_fun(a, cb_p, 1, ty_any(a), true)};
    ADD_MONO("aio/schedule", ty_fun(a, ps, 3, ty_handle(a, ty_any(a)), false));
  }
  {
    // aio/interval : Ref(aio) -> Num -> (Any... -> Any) -> Handle(Any)
    valk_type_t *cb_p[1] = {ty_any(a)};
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_num(a), ty_fun(a, cb_p, 1, ty_any(a), true)};
    ADD_MONO("aio/interval", ty_fun(a, ps, 3, ty_handle(a, ty_any(a)), false));
  }
  {
    // aio/retry : Ref(aio) -> (-> Handle(Any)) -> Any -> Handle(Any)
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_any(a), ty_any(a)};
    ADD_MONO("aio/retry", ty_fun(a, ps, 3, ty_handle(a, ty_any(a)), false));
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
    ADD_MONO("aio/diagnostics-state-json", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/diagnostics-state-json-compact", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/systems-json", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("aio/on-loop-thread?", ty_fun(a, ps, 1, ty_num(a), false));
    ADD_MONO("aio/pool-stats", ty_fun(a, ps, 1, ty_any(a), false));
  }
  {
    // aio/slab-buckets : Ref(aio) -> Any... -> Any
    valk_type_t *ps[1] = {ty_ref(a, "aio")};
    ADD_MONO("aio/slab-buckets", ty_fun(a, ps, 1, ty_any(a), true));
  }

  // === HTTP/2 ===
  {
    // http2/client-request : Ref(aio) -> Str -> Num -> Str -> Handle(Ref(http_response))
    valk_type_t *ps[4] = {ty_ref(a, "aio"), ty_str(a), ty_num(a), ty_str(a)};
    ADD_MONO("http2/client-request",
             ty_fun(a, ps, 4, ty_handle(a, ty_ref(a, "http_response")), false));
  }
  {
    // http2/client-request-with-headers : Ref(aio) -> Str -> Num -> Str -> List(Any) -> Handle(Ref(http_response))
    valk_type_t *ps[5] = {ty_ref(a, "aio"), ty_str(a), ty_num(a), ty_str(a),
                          ty_list(a, ty_any(a))};
    ADD_MONO("http2/client-request-with-headers",
             ty_fun(a, ps, 5, ty_handle(a, ty_ref(a, "http_response")), false));
  }
  {
    // http2/response-* : Any -> Str/List
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("http2/response-body", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("http2/response-status", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("http2/response-headers", ty_fun(a, ps, 1, ty_list(a, ty_any(a)), false));
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
    // http2/mock-response : Str -> Str -> Any -> Ref(http_response)
    valk_type_t *ps[3] = {ty_str(a), ty_str(a), ty_any(a)};
    ADD_MONO("http2/mock-response", ty_fun(a, ps, 3, ty_ref(a, "http_response"), false));
  }
  {
    // http2/connect : Ref(aio) -> Str -> Num -> (Any -> Any) -> Nil
    valk_type_t *cb_p[1] = {ty_any(a)};
    valk_type_t *ps[4] = {ty_ref(a, "aio"), ty_str(a), ty_num(a), ty_fun(a, cb_p, 1, ty_any(a), false)};
    ADD_MONO("http2/connect", ty_fun(a, ps, 4, ty_nil(a), false));
  }
  {
    // http2/server-listen : Ref(aio) -> Num -> Any... -> Handle(Any)
    valk_type_t *ps[3] = {ty_ref(a, "aio"), ty_num(a), ty_any(a)};
    ADD_MONO("http2/server-listen", ty_fun(a, ps, 3, ty_handle(a, ty_any(a)), true));
  }
  {
    // http2/server-handle : Ref -> (Any -> Any) -> Nil
    valk_type_t *cb_p[1] = {ty_any(a)};
    valk_type_t *ps[2] = {ty_ref(a, nullptr), ty_fun(a, cb_p, 1, ty_any(a), false)};
    ADD_MONO("http2/server-handle", ty_fun(a, ps, 2, ty_nil(a), false));
  }
  {
    // http2/server-port : Any -> Num
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("http2/server-port", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    // http2/server-stop : Any -> Handle(Any)
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("http2/server-stop", ty_fun(a, ps, 1, ty_handle(a, ty_any(a)), false));
  }

  // === Request accessors ===
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("req/method", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/path", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/scheme", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/authority", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/body", ty_fun(a, ps, 1, ty_str(a), false));
    ADD_MONO("req/headers", ty_fun(a, ps, 1, ty_list(a, ty_any(a)), false));
    ADD_MONO("req/stream-id", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    valk_type_t *ps[2] = {ty_any(a), ty_str(a)};
    ADD_MONO("req/header", ty_fun(a, ps, 2, ty_str(a), false));
  }

  // === Stream ===
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("stream/close", ty_fun(a, ps, 1, ty_any(a), false));
    ADD_MONO("stream/cancel", ty_fun(a, ps, 1, ty_any(a), false));
    ADD_MONO("stream/closed", ty_fun(a, ps, 1, ty_handle(a, ty_any(a)), false));
    ADD_MONO("stream/id", ty_fun(a, ps, 1, ty_any(a), false));
    ADD_MONO("stream/writable?", ty_fun(a, ps, 1, ty_num(a), false));
  }
  {
    valk_type_t *ps[2] = {ty_any(a), ty_any(a)};
    ADD_MONO("stream/write", ty_fun(a, ps, 2, ty_any(a), false));
    ADD_MONO("stream/on-close", ty_fun(a, ps, 2, ty_any(a), false));
    ADD_MONO("stream/on-drain", ty_fun(a, ps, 2, ty_any(a), false));
    ADD_MONO("stream/set-max-session", ty_fun(a, ps, 2, ty_any(a), false));
    ADD_MONO("stream/set-timeout", ty_fun(a, ps, 2, ty_any(a), false));
  }
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("stream/open", ty_fun(a, ps, 1, ty_any(a), true));
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
  ADD_MONO("mem/checkpoint/stats", ty_fun(a, nullptr, 0, ty_list(a, ty_any(a)), false));
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
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("metrics/collect-delta-stateless", ty_fun(a, ps, 1, ty_ref(a, "metrics"), false));
    ADD_MONO("metrics/delta-json", ty_fun(a, ps, 1, ty_str(a), false));
  }
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("metrics/counter", ty_fun(a, ps, 1, ty_ref(a, "metrics"), true));
    ADD_MONO("metrics/gauge", ty_fun(a, ps, 1, ty_ref(a, "metrics"), true));
    ADD_MONO("metrics/histogram", ty_fun(a, ps, 1, ty_ref(a, "metrics"), true));
  }
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("metrics/counter-inc", ty_fun(a, ps, 1, ty_nil(a), true));
    ADD_MONO("metrics/histogram-observe", ty_fun(a, ps, 1, ty_nil(a), true));
  }
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("metrics/gauge-inc", ty_fun(a, ps, 1, ty_nil(a), true));
    ADD_MONO("metrics/gauge-dec", ty_fun(a, ps, 1, ty_nil(a), true));
  }
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("metrics/gauge-set", ty_fun(a, ps, 1, ty_nil(a), true));
  }

  // === Misc ===
  ADD_MONO("time-us", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("stack-depth", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("penv", ty_fun(a, nullptr, 0, ty_list(a, ty_any(a)), false));
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("exit", ty_fun(a, ps, 1, ty_any(a), false));
    ADD_MONO("shutdown", ty_fun(a, ps, 1, ty_any(a), false));
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
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("coverage-mark", ty_fun(a, ps, 1, ty_any(a), false));
    ADD_MONO("coverage-record", ty_fun(a, ps, 1, ty_any(a), false));
  }

  // === Source location ===
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("source-line", ty_fun(a, ps, 1, ty_num(a), false));
    ADD_MONO("source-column", ty_fun(a, ps, 1, ty_num(a), false));
    ADD_MONO("source-file", ty_fun(a, ps, 1, ty_str(a), false));
  }

  // === Context ===
  ADD_MONO("ctx/deadline", ty_fun(a, nullptr, 0, ty_any(a), false));
  ADD_MONO("ctx/deadline-exceeded?", ty_fun(a, nullptr, 0, ty_num(a), false));
  ADD_MONO("ctx/locals", ty_fun(a, nullptr, 0, ty_any(a), false));
  {
    valk_type_t *ps[1] = {ty_any(a)};
    ADD_MONO("ctx/get", ty_fun(a, ps, 1, ty_any(a), false));
  }

  // === Trace ===
  ADD_MONO("trace/id", ty_fun(a, nullptr, 0, ty_any(a), false));
  ADD_MONO("trace/span", ty_fun(a, nullptr, 0, ty_any(a), false));
  ADD_MONO("trace/parent-span", ty_fun(a, nullptr, 0, ty_any(a), false));

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
