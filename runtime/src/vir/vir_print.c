#include "vir.h"
#include <stdio.h>

static void print_ref(vir_value_t *v, FILE *out) {
  if (!v) { fprintf(out, "null"); return; }
  fprintf(out, "%%%u", v->id);
}

void vir_print_value(vir_value_t *val, FILE *out) {
  if (!val) return;

  if (val->type != VIR_TYPE_VOID) {
    fprintf(out, "  %%%u = %s", val->id, vir_opcode_name(val->opcode));
  } else {
    fprintf(out, "  %s", vir_opcode_name(val->opcode));
  }

  switch (val->opcode) {
    case VIR_CONST_NUM:
      fprintf(out, " %ld", val->num_val);
      break;
    case VIR_CONST_STR:
      fprintf(out, " \"%s\"", val->str_val);
      break;
    case VIR_CONST_NIL:
      break;
    case VIR_CONST_SYM:
      fprintf(out, " @%s", val->str_val);
      break;

    case VIR_ADD: case VIR_SUB: case VIR_MUL:
    case VIR_DIV: case VIR_MOD:
    case VIR_EQ: case VIR_NE: case VIR_LT:
    case VIR_LE: case VIR_GT: case VIR_GE:
    case VIR_CONS: case VIR_QCONS:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      fprintf(out, ", ");
      print_ref(val->operands[1], out);
      break;

    case VIR_TRUTHY:
    case VIR_UNBOX_NUM:
    case VIR_BOX_NUM:
    case VIR_COPY:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      break;

    case VIR_BR:
      fprintf(out, " %s", val->br.target->name);
      break;
    case VIR_BR_IF:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      fprintf(out, ", %s, %s",
        val->br_if.true_bb->name, val->br_if.false_bb->name);
      break;
    case VIR_RET:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      break;

    case VIR_CALL:
    case VIR_TAIL_CALL:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      fprintf(out, "(");
      for (u32 i = 0; i < val->call.num_args; i++) {
        if (i > 0) fprintf(out, ", ");
        print_ref(val->call.args[i], out);
      }
      fprintf(out, ")");
      break;

    case VIR_ENV_GET:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      fprintf(out, ", @%s", val->str_val);
      break;
    case VIR_ENV_PUT:
    case VIR_ENV_DEF:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      fprintf(out, ", @%s, ", val->str_val);
      print_ref(val->operands[1], out);
      break;

    case VIR_LAMBDA:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      fprintf(out, ", ");
      print_ref(val->operands[1], out);
      fprintf(out, ", ");
      print_ref(val->operands[2], out);
      break;

    case VIR_LITERAL:
      fprintf(out, " <ast:%p>", val->ast_node);
      break;

    case VIR_GC_ROOT:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      break;
    case VIR_GC_UNROOT:
      fprintf(out, " ");
      print_ref(val->operands[0], out);
      break;
    case VIR_GC_SAFEPOINT:
      break;

    case VIR_PHI:
      fprintf(out, " [");
      for (u32 i = 0; i < val->phi.num_incoming; i++) {
        if (i > 0) fprintf(out, ", ");
        print_ref(val->phi.incoming_vals[i], out);
        fprintf(out, " from %s", val->phi.incoming_blocks[i]->name);
      }
      fprintf(out, "]");
      break;
  }

  fprintf(out, "\n");
}

void vir_print_func(vir_func_t *fn, FILE *out) {
  fprintf(out, "func @%s(", fn->name);
  for (u32 i = 0; i < fn->num_params; i++) {
    if (i > 0) fprintf(out, ", ");
    fprintf(out, "ptr %%%u", fn->params[i]->id);
  }
  fprintf(out, ") {\n");

  vir_block_t *bb = fn->entry;
  while (bb) {
    fprintf(out, "%s:", bb->name);
    if (bb->num_preds > 0) {
      fprintf(out, "  ; preds:");
      for (u32 i = 0; i < bb->num_preds; i++)
        fprintf(out, " %s", bb->preds[i]->name);
    }
    fprintf(out, "\n");

    vir_value_t *v = bb->first;
    while (v) {
      vir_print_value(v, out);
      v = v->next;
    }
    bb = bb->next;
  }
  fprintf(out, "}\n");
}

void vir_print_module(vir_module_t *mod, FILE *out) {
  fprintf(out, "; module %s\n\n", mod->name);
  vir_func_t *fn = mod->func_list;
  while (fn) {
    vir_print_func(fn, out);
    fprintf(out, "\n");
    fn = fn->next;
  }
}
