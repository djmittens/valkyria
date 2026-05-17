#include "vir.h"
#include "../common.h"
#include <stdlib.h>
#include <string.h>

const char *vir_opcode_name(vir_opcode_e op) {
  switch (op) {
    case VIR_CONST_NUM: return "const.num";
    case VIR_CONST_STR: return "const.str";
    case VIR_CONST_NIL: return "const.nil";
    case VIR_CONST_SYM: return "const.sym";
    case VIR_ADD: return "add";
    case VIR_SUB: return "sub";
    case VIR_MUL: return "mul";
    case VIR_DIV: return "div";
    case VIR_MOD: return "mod";
    case VIR_EQ: return "eq";
    case VIR_NE: return "ne";
    case VIR_LT: return "lt";
    case VIR_LE: return "le";
    case VIR_GT: return "gt";
    case VIR_GE: return "ge";
    case VIR_TRUTHY: return "truthy";
    case VIR_UNBOX_NUM: return "unbox.num";
    case VIR_BOX_NUM: return "box.num";
    case VIR_BR: return "br";
    case VIR_BR_IF: return "br.if";
    case VIR_RET: return "ret";
    case VIR_CALL: return "call";
    case VIR_TAIL_CALL: return "tail_call";
    case VIR_ENV_GET: return "env.get";
    case VIR_ENV_PUT: return "env.put";
    case VIR_ENV_DEF: return "env.def";
    case VIR_CONS: return "cons";
    case VIR_QCONS: return "qcons";
    case VIR_LAMBDA: return "lambda";
    case VIR_LITERAL: return "literal";
    case VIR_DIRECT_CALL: return "direct_call";
    case VIR_GC_SAFEPOINT: return "gc.safepoint";
    case VIR_PHI: return "phi";
    case VIR_COPY: return "copy";
  }
  return "?";
}

const char *vir_type_name(vir_type_e ty) {
  switch (ty) {
    case VIR_TYPE_PTR: return "ptr";
    case VIR_TYPE_I64: return "i64";
    case VIR_TYPE_I1: return "i1";
    case VIR_TYPE_VOID: return "void";
  }
  return "?";
}

static char *str_dup(const char *s) {
  if (!s) return NULL;
  size_t len = strlen(s) + 1;
  char *copy = malloc(len);
  memcpy(copy, s, len);
  return copy;
}

vir_module_t *vir_module_new(const char *name) {
  vir_module_t *m = calloc(1, sizeof(vir_module_t));
  VALK_OOM_ASSERT(m);
  m->name = str_dup(name);
  return m;
}

static void free_value(vir_value_t *v) {
  if (!v) return;
  if (v->operands) free(v->operands);
  if (v->opcode == VIR_CONST_STR || v->opcode == VIR_CONST_SYM)
    free(v->str_val);
  if (v->opcode == VIR_CALL || v->opcode == VIR_TAIL_CALL)
    free(v->call.args);
  if (v->opcode == VIR_DIRECT_CALL) {
    free(v->direct_call.native_name);
    if (v->direct_call.formal_names) {
      for (u32 i = 0; i < v->direct_call.nargs; i++)
        free(v->direct_call.formal_names[i]);
      free(v->direct_call.formal_names);
    }
    free(v->direct_call.arg_vals);
  }
  if (v->opcode == VIR_PHI) {
    free(v->phi.incoming_vals);
    free(v->phi.incoming_blocks);
  }
  free(v);
}

static void free_block(vir_block_t *bb) {
  if (!bb) return;
  vir_value_t *v = bb->first;
  while (v) {
    vir_value_t *next = v->next;
    free_value(v);
    v = next;
  }
  free(bb->name);
  free(bb->preds);
  free(bb->succs);
  free(bb);
}

static void free_func(vir_func_t *fn) {
  if (!fn) return;
  vir_block_t *bb = fn->block_list;
  while (bb) {
    vir_block_t *next = bb->next;
    free_block(bb);
    bb = next;
  }
  if (fn->params) free(fn->params);
  free(fn->name);
  free(fn);
}

void vir_module_free(vir_module_t *mod) {
  if (!mod) return;
  vir_func_t *fn = mod->func_list;
  while (fn) {
    vir_func_t *next = fn->next;
    free_func(fn);
    fn = next;
  }
  free(mod->name);
  free(mod);
}

vir_builder_t *vir_builder_new(vir_module_t *mod) {
  vir_builder_t *b = calloc(1, sizeof(vir_builder_t));
  VALK_OOM_ASSERT(b);
  b->module = mod;
  return b;
}

void vir_builder_free(vir_builder_t *b) {
  free(b);
}

vir_func_t *vir_builder_add_func(vir_builder_t *b, const char *name,
                                 u32 num_params) {
  vir_func_t *fn = calloc(1, sizeof(vir_func_t));
  VALK_OOM_ASSERT(fn);
  fn->name = str_dup(name);
  fn->num_params = num_params;
  fn->parent = b->module;

  if (num_params > 0) {
    fn->params = calloc(num_params, sizeof(vir_value_t *));
    VALK_OOM_ASSERT(fn->params);
    for (u32 i = 0; i < num_params; i++) {
      vir_value_t *p = calloc(1, sizeof(vir_value_t));
      VALK_OOM_ASSERT(p);
      p->opcode = VIR_COPY;
      p->type = VIR_TYPE_PTR;
      p->id = b->next_val_id++;
      fn->params[i] = p;
    }
  }

  fn->next = b->module->func_list;
  b->module->func_list = fn;
  b->module->num_funcs++;
  b->cur_fn = fn;
  b->cur_bb = NULL;
  return fn;
}

vir_block_t *vir_builder_add_block(vir_builder_t *b, const char *name) {
  vir_block_t *bb = calloc(1, sizeof(vir_block_t));
  VALK_OOM_ASSERT(bb);
  bb->name = str_dup(name);
  bb->id = b->next_bb_id++;
  bb->parent = b->cur_fn;

  if (!b->cur_fn->entry)
    b->cur_fn->entry = bb;

  // Append to block_list so iteration order matches addition order.
  // Critical for vir_to_llvm_func: it visits blocks head-first and
  // expects an entry-block value to be lowered (and added to val_map)
  // before any later block references it. Prepending would visit
  // dominator blocks AFTER their dominees, leaving operands unset and
  // crashing in LLVMTypeOf at the first cross-block use.
  bb->next = NULL;
  if (!b->cur_fn->block_list) {
    b->cur_fn->block_list = bb;
  } else {
    vir_block_t *tail = b->cur_fn->block_list;
    while (tail->next) tail = tail->next;
    tail->next = bb;
  }
  b->cur_fn->num_blocks++;
  return bb;
}

void vir_builder_set_block(vir_builder_t *b, vir_block_t *bb) {
  b->cur_bb = bb;
}

static vir_value_t *emit(vir_builder_t *b, vir_value_t *v) {
  v->parent = b->cur_bb;
  if (!b->cur_bb->first) {
    b->cur_bb->first = v;
    b->cur_bb->last = v;
  } else {
    b->cur_bb->last->next = v;
    b->cur_bb->last = v;
  }
  b->cur_bb->num_instrs++;
  return v;
}

static vir_value_t *new_val(vir_builder_t *b, vir_opcode_e op, vir_type_e ty) {
  vir_value_t *v = calloc(1, sizeof(vir_value_t));
  VALK_OOM_ASSERT(v);
  v->opcode = op;
  v->type = ty;
  v->id = b->next_val_id++;
  return v;
}

vir_value_t *vir_build_const_num(vir_builder_t *b, long val) {
  vir_value_t *v = new_val(b, VIR_CONST_NUM, VIR_TYPE_PTR);
  v->num_val = val;
  return emit(b, v);
}

vir_value_t *vir_build_const_str(vir_builder_t *b, const char *val) {
  vir_value_t *v = new_val(b, VIR_CONST_STR, VIR_TYPE_PTR);
  v->str_val = str_dup(val);
  return emit(b, v);
}

vir_value_t *vir_build_const_nil(vir_builder_t *b) {
  return emit(b, new_val(b, VIR_CONST_NIL, VIR_TYPE_PTR));
}

vir_value_t *vir_build_const_sym(vir_builder_t *b, const char *name) {
  vir_value_t *v = new_val(b, VIR_CONST_SYM, VIR_TYPE_PTR);
  v->str_val = str_dup(name);
  return emit(b, v);
}

static void set_operands(vir_value_t *v, vir_value_t **ops, u32 n) {
  v->operands = calloc(n, sizeof(vir_value_t *));
  VALK_OOM_ASSERT(v->operands);
  memcpy(v->operands, ops, n * sizeof(vir_value_t *));
  v->num_operands = n;
}

vir_value_t *vir_build_binop(vir_builder_t *b, vir_opcode_e op,
                             vir_value_t *lhs, vir_value_t *rhs) {
  vir_type_e ty = (op >= VIR_EQ && op <= VIR_GE) ? VIR_TYPE_I1 : VIR_TYPE_I64;
  vir_value_t *v = new_val(b, op, ty);
  vir_value_t *ops[] = {lhs, rhs};
  set_operands(v, ops, 2);
  return emit(b, v);
}

vir_value_t *vir_build_truthy(vir_builder_t *b, vir_value_t *val) {
  vir_value_t *v = new_val(b, VIR_TRUTHY, VIR_TYPE_I1);
  set_operands(v, &val, 1);
  return emit(b, v);
}

vir_value_t *vir_build_unbox_num(vir_builder_t *b, vir_value_t *val) {
  vir_value_t *v = new_val(b, VIR_UNBOX_NUM, VIR_TYPE_I64);
  set_operands(v, &val, 1);
  return emit(b, v);
}

vir_value_t *vir_build_box_num(vir_builder_t *b, vir_value_t *val) {
  vir_value_t *v = new_val(b, VIR_BOX_NUM, VIR_TYPE_PTR);
  set_operands(v, &val, 1);
  return emit(b, v);
}

void vir_build_br(vir_builder_t *b, vir_block_t *target) {
  vir_value_t *v = new_val(b, VIR_BR, VIR_TYPE_VOID);
  v->br.target = target;
  emit(b, v);
  vir_block_add_succ(b->cur_bb, target);
  vir_block_add_pred(target, b->cur_bb);
}

void vir_build_br_if(vir_builder_t *b, vir_value_t *cond,
                     vir_block_t *true_bb, vir_block_t *false_bb) {
  vir_value_t *v = new_val(b, VIR_BR_IF, VIR_TYPE_VOID);
  v->br_if.true_bb = true_bb;
  v->br_if.false_bb = false_bb;
  set_operands(v, &cond, 1);
  emit(b, v);
  vir_block_add_succ(b->cur_bb, true_bb);
  vir_block_add_succ(b->cur_bb, false_bb);
  vir_block_add_pred(true_bb, b->cur_bb);
  vir_block_add_pred(false_bb, b->cur_bb);
}

void vir_build_ret(vir_builder_t *b, vir_value_t *val) {
  vir_value_t *v = new_val(b, VIR_RET, VIR_TYPE_VOID);
  set_operands(v, &val, 1);
  emit(b, v);
}

static vir_value_t *build_call_impl(vir_builder_t *b, vir_opcode_e op,
                                    vir_value_t *fn,
                                    vir_value_t **args, u32 num_args) {
  vir_value_t *v = new_val(b, op, VIR_TYPE_PTR);
  set_operands(v, &fn, 1);
  v->call.num_args = num_args;
  if (num_args > 0) {
    v->call.args = calloc(num_args, sizeof(vir_value_t *));
    VALK_OOM_ASSERT(v->call.args);
    memcpy(v->call.args, args, num_args * sizeof(vir_value_t *));
  }
  if (op == VIR_TAIL_CALL && b->cur_fn)
    b->cur_fn->has_tail_calls = true;
  return emit(b, v);
}

vir_value_t *vir_build_call(vir_builder_t *b, vir_value_t *fn,
                            vir_value_t **args, u32 num_args) {
  return build_call_impl(b, VIR_CALL, fn, args, num_args);
}

vir_value_t *vir_build_tail_call(vir_builder_t *b, vir_value_t *fn,
                                 vir_value_t **args, u32 num_args) {
  return build_call_impl(b, VIR_TAIL_CALL, fn, args, num_args);
}

vir_value_t *vir_build_direct_call(vir_builder_t *b, const char *native_name,
                                   const char **formal_names,
                                   vir_value_t **arg_vals, u32 nargs) {
  vir_value_t *v = new_val(b, VIR_DIRECT_CALL, VIR_TYPE_PTR);
  v->direct_call.native_name = str_dup(native_name);
  v->direct_call.nargs = nargs;
  if (nargs > 0) {
    v->direct_call.formal_names = calloc(nargs, sizeof(char *));
    v->direct_call.arg_vals = calloc(nargs, sizeof(vir_value_t *));
    VALK_OOM_ASSERT(v->direct_call.formal_names);
    VALK_OOM_ASSERT(v->direct_call.arg_vals);
    for (u32 i = 0; i < nargs; i++) {
      v->direct_call.formal_names[i] = str_dup(formal_names[i]);
      v->direct_call.arg_vals[i] = arg_vals[i];
    }
  }
  return emit(b, v);
}

vir_value_t *vir_build_env_get(vir_builder_t *b, vir_value_t *env,
                               const char *sym) {
  vir_value_t *v = new_val(b, VIR_ENV_GET, VIR_TYPE_PTR);
  v->str_val = str_dup(sym);
  set_operands(v, &env, 1);
  return emit(b, v);
}

void vir_build_env_put(vir_builder_t *b, vir_value_t *env,
                       const char *sym, vir_value_t *val) {
  vir_value_t *v = new_val(b, VIR_ENV_PUT, VIR_TYPE_VOID);
  v->str_val = str_dup(sym);
  vir_value_t *ops[] = {env, val};
  set_operands(v, ops, 2);
  emit(b, v);
}

void vir_build_env_def(vir_builder_t *b, vir_value_t *env,
                       const char *sym, vir_value_t *val) {
  vir_value_t *v = new_val(b, VIR_ENV_DEF, VIR_TYPE_VOID);
  v->str_val = str_dup(sym);
  vir_value_t *ops[] = {env, val};
  set_operands(v, ops, 2);
  emit(b, v);
}

vir_value_t *vir_build_cons(vir_builder_t *b, vir_value_t *head,
                            vir_value_t *tail) {
  vir_value_t *v = new_val(b, VIR_CONS, VIR_TYPE_PTR);
  vir_value_t *ops[] = {head, tail};
  set_operands(v, ops, 2);
  return emit(b, v);
}

vir_value_t *vir_build_qcons(vir_builder_t *b, vir_value_t *head,
                             vir_value_t *tail) {
  vir_value_t *v = new_val(b, VIR_QCONS, VIR_TYPE_PTR);
  vir_value_t *ops[] = {head, tail};
  set_operands(v, ops, 2);
  return emit(b, v);
}

vir_value_t *vir_build_lambda(vir_builder_t *b, vir_value_t *env,
                              vir_value_t *formals, vir_value_t *body) {
  vir_value_t *v = new_val(b, VIR_LAMBDA, VIR_TYPE_PTR);
  vir_value_t *ops[] = {env, formals, body};
  set_operands(v, ops, 3);
  return emit(b, v);
}

vir_value_t *vir_build_literal(vir_builder_t *b, void *ast_node) {
  vir_value_t *v = new_val(b, VIR_LITERAL, VIR_TYPE_PTR);
  v->ast_node = ast_node;
  return emit(b, v);
}

// vir_build_gc_root / vir_build_gc_unroot retired with the wider
// root_stack delete. The compiler emits safepoint polls only;
// conservative native-stack scanning at safepoint discovers all roots.
void vir_build_gc_safepoint(vir_builder_t *b) {
  emit(b, new_val(b, VIR_GC_SAFEPOINT, VIR_TYPE_VOID));
}

vir_value_t *vir_build_phi(vir_builder_t *b, vir_type_e type) {
  vir_value_t *v = new_val(b, VIR_PHI, type);
  return emit(b, v);
}

void vir_phi_add_incoming(vir_value_t *phi, vir_value_t *val,
                          vir_block_t *from) {
  u32 n = phi->phi.num_incoming;
  phi->phi.incoming_vals = realloc(phi->phi.incoming_vals,
    (n + 1) * sizeof(vir_value_t *));
  VALK_OOM_ASSERT(phi->phi.incoming_vals);
  phi->phi.incoming_blocks = realloc(phi->phi.incoming_blocks,
    (n + 1) * sizeof(vir_block_t *));
  VALK_OOM_ASSERT(phi->phi.incoming_blocks);
  phi->phi.incoming_vals[n] = val;
  phi->phi.incoming_blocks[n] = from;
  phi->phi.num_incoming = n + 1;
}

void vir_block_add_pred(vir_block_t *bb, vir_block_t *pred) {
  if (bb->num_preds >= bb->pred_cap) {
    bb->pred_cap = bb->pred_cap ? bb->pred_cap * 2 : 4;
    bb->preds = realloc(bb->preds, bb->pred_cap * sizeof(vir_block_t *));
    VALK_OOM_ASSERT(bb->preds);
  }
  bb->preds[bb->num_preds++] = pred;
}

void vir_block_add_succ(vir_block_t *bb, vir_block_t *succ) {
  if (bb->num_succs >= bb->succ_cap) {
    bb->succ_cap = bb->succ_cap ? bb->succ_cap * 2 : 4;
    bb->succs = realloc(bb->succs, bb->succ_cap * sizeof(vir_block_t *));
    VALK_OOM_ASSERT(bb->succs);
  }
  bb->succs[bb->num_succs++] = succ;
}
