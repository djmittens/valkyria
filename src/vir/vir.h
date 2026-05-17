#pragma once
#include <stdbool.h>
#include <stdio.h>
#include "../types.h"

typedef enum {
  VIR_CONST_NUM,
  VIR_CONST_STR,
  VIR_CONST_NIL,
  VIR_CONST_SYM,

  VIR_ADD,
  VIR_SUB,
  VIR_MUL,
  VIR_DIV,
  VIR_MOD,

  VIR_EQ,
  VIR_NE,
  VIR_LT,
  VIR_LE,
  VIR_GT,
  VIR_GE,

  VIR_TRUTHY,
  VIR_UNBOX_NUM,
  VIR_BOX_NUM,

  VIR_BR,
  VIR_BR_IF,
  VIR_RET,

  VIR_CALL,
  VIR_TAIL_CALL,
  // Direct AOT-to-AOT call. The target is a known compiled lambda;
  // ast_to_vir embeds the target's native_name + formal names so
  // vir_to_llvm can build a call_env + lenv_put each formal + call
  // native_fn(call_env), bypassing valk_lval_eval_call. Mirrors the
  // codegen_try_direct_call slow fallback in llvm_codegen_call.c.
  VIR_DIRECT_CALL,

  VIR_ENV_GET,
  VIR_ENV_PUT,
  VIR_ENV_DEF,

  VIR_CONS,
  VIR_QCONS,
  VIR_LAMBDA,
  VIR_LITERAL,

  // VIR_GC_ROOT/UNROOT removed: GC roots are discovered automatically
  // via conservative native-stack scanning (see scan_thread_native_stack
  // in src/gc_mark.c). The compiler emits safepoint polls only —
  // everything else is the runtime's job.
  VIR_GC_SAFEPOINT,

  VIR_PHI,
  VIR_COPY,
} vir_opcode_e;

typedef enum {
  VIR_TYPE_PTR,
  VIR_TYPE_I64,
  VIR_TYPE_I1,
  VIR_TYPE_VOID,
} vir_type_e;

typedef struct vir_value vir_value_t;
typedef struct vir_block vir_block_t;
typedef struct vir_func vir_func_t;
typedef struct vir_module vir_module_t;

struct vir_value {
  vir_opcode_e opcode;
  vir_type_e type;
  u32 id;

  vir_value_t **operands;
  u32 num_operands;

  union {
    long num_val;
    char *str_val;
    struct {
      vir_block_t *target;
    } br;
    struct {
      vir_block_t *true_bb;
      vir_block_t *false_bb;
    } br_if;
    struct {
      vir_value_t **args;
      u32 num_args;
      // When true, vir_to_llvm emits this call with musttail and an
      // immediate ret. Set by ast_to_vir when the call appears in
      // tail position (last expr of body / if branch / do block).
      // Required to prevent slow-body recursion from blowing the C
      // stack — see test_recursion_stress.valk.
      bool is_tail;
    } call;
    struct {
      char *native_name;     // strdup'd; target's compiled fn symbol
      char **formal_names;   // strdup'd array of N formal names
      vir_value_t **arg_vals;// N evaluated arg SSA values
      u32 nargs;
      bool is_tail;          // see VIR_CALL.is_tail above
    } direct_call;
    struct {
      vir_value_t **incoming_vals;
      vir_block_t **incoming_blocks;
      u32 num_incoming;
    } phi;
    void *ast_node;
  };

  vir_value_t *next;
  vir_block_t *parent;
};

struct vir_block {
  char *name;
  u32 id;
  vir_value_t *first;
  vir_value_t *last;
  u32 num_instrs;

  vir_block_t **preds;
  u32 num_preds;
  u32 pred_cap;

  vir_block_t **succs;
  u32 num_succs;
  u32 succ_cap;

  vir_block_t *next;
  vir_func_t *parent;
};

struct vir_func {
  char *name;
  vir_block_t *entry;
  vir_block_t *block_list;
  u32 num_blocks;

  vir_value_t **params;
  u32 num_params;
  bool has_tail_calls;

  vir_func_t *next;
  vir_module_t *parent;
};

struct vir_module {
  char *name;
  vir_func_t *func_list;
  u32 num_funcs;
};

typedef struct {
  vir_module_t *module;
  vir_func_t *cur_fn;
  vir_block_t *cur_bb;
  u32 next_val_id;
  u32 next_bb_id;
} vir_builder_t;

const char *vir_opcode_name(vir_opcode_e op);
const char *vir_type_name(vir_type_e ty);

vir_module_t *vir_module_new(const char *name);
void vir_module_free(vir_module_t *mod);

vir_builder_t *vir_builder_new(vir_module_t *mod);
void vir_builder_free(vir_builder_t *b);

vir_func_t *vir_builder_add_func(vir_builder_t *b, const char *name,
                                 u32 num_params);
vir_block_t *vir_builder_add_block(vir_builder_t *b, const char *name);
void vir_builder_set_block(vir_builder_t *b, vir_block_t *bb);

vir_value_t *vir_build_const_num(vir_builder_t *b, long val);
vir_value_t *vir_build_const_str(vir_builder_t *b, const char *val);
vir_value_t *vir_build_const_nil(vir_builder_t *b);
vir_value_t *vir_build_const_sym(vir_builder_t *b, const char *name);

vir_value_t *vir_build_binop(vir_builder_t *b, vir_opcode_e op,
                             vir_value_t *lhs, vir_value_t *rhs);
vir_value_t *vir_build_truthy(vir_builder_t *b, vir_value_t *val);
vir_value_t *vir_build_unbox_num(vir_builder_t *b, vir_value_t *val);
vir_value_t *vir_build_box_num(vir_builder_t *b, vir_value_t *val);

void vir_build_br(vir_builder_t *b, vir_block_t *target);
void vir_build_br_if(vir_builder_t *b, vir_value_t *cond,
                     vir_block_t *true_bb, vir_block_t *false_bb);
void vir_build_ret(vir_builder_t *b, vir_value_t *val);

vir_value_t *vir_build_call(vir_builder_t *b, vir_value_t *fn,
                            vir_value_t **args, u32 num_args);
vir_value_t *vir_build_tail_call(vir_builder_t *b, vir_value_t *fn,
                                 vir_value_t **args, u32 num_args);
// Direct AOT-to-AOT call. `native_name` is the target's compiled symbol;
// `formal_names` is an array of N formal name strings (non-NULL); both
// are copied. `arg_vals` are the N already-lowered arg SSA values.
// vir_to_llvm builds a call_env, binds formals via lenv_put, calls
// native_fn(call_env). Skips valk_lval_eval_call entirely.
vir_value_t *vir_build_direct_call(vir_builder_t *b, const char *native_name,
                                   const char **formal_names,
                                   vir_value_t **arg_vals, u32 nargs);

vir_value_t *vir_build_env_get(vir_builder_t *b, vir_value_t *env,
                               const char *sym);
void vir_build_env_put(vir_builder_t *b, vir_value_t *env,
                       const char *sym, vir_value_t *val);
void vir_build_env_def(vir_builder_t *b, vir_value_t *env,
                       const char *sym, vir_value_t *val);

vir_value_t *vir_build_cons(vir_builder_t *b, vir_value_t *head,
                            vir_value_t *tail);
vir_value_t *vir_build_qcons(vir_builder_t *b, vir_value_t *head,
                             vir_value_t *tail);
vir_value_t *vir_build_lambda(vir_builder_t *b, vir_value_t *env,
                              vir_value_t *formals, vir_value_t *body);
vir_value_t *vir_build_literal(vir_builder_t *b, void *ast_node);

void vir_build_gc_safepoint(vir_builder_t *b);

vir_value_t *vir_build_phi(vir_builder_t *b, vir_type_e type);
void vir_phi_add_incoming(vir_value_t *phi, vir_value_t *val,
                          vir_block_t *from);

void vir_block_add_pred(vir_block_t *bb, vir_block_t *pred);
void vir_block_add_succ(vir_block_t *bb, vir_block_t *succ);

// AST → VIR lowering entry points (defined in src/vir/ast_to_vir.c).
struct valk_lval_t;
struct valk_lenv_t;
vir_func_t *vir_lower_toplevel(vir_builder_t *b, struct valk_lval_t *expr,
                               const char *name);
vir_func_t *vir_lower_lambda_body(vir_builder_t *b, struct valk_lval_t *body,
                                  const char *name);
// Same as vir_lower_lambda_body but with a build_env for resolving
// direct AOT-to-AOT calls. Used by build_aot.c during --build.
vir_func_t *vir_lower_lambda_body_with_env(vir_builder_t *b,
                                           struct valk_lval_t *body,
                                           const char *name,
                                           struct valk_lenv_t *build_env);
vir_func_t *vir_lower_program(vir_builder_t *b, struct valk_lval_t *exprs);

// IR pass: insert one VIR_GC_SAFEPOINT at the entry of every function
// in the module. Conservative native-stack scanning at the safepoint
// finds all roots — no per-call-site root tracking needed.
void vir_gc_insert_safepoints(vir_module_t *mod);

void vir_print_module(vir_module_t *mod, FILE *out);
void vir_print_func(vir_func_t *fn, FILE *out);
void vir_print_value(vir_value_t *val, FILE *out);
