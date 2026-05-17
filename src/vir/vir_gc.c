// VIR GC support.
//
// Historically this file contained `vir_gc_insert_roots`, an IR pass
// that ran liveness analysis on each VIR block, found live VIR_TYPE_PTR
// SSA values at every "GC point" (CALL, ENV_*, CONS, etc.), and
// bracketed them with VIR_GC_ROOT/UNROOT opcodes that lowered to
// runtime calls into a per-thread root_stack.
//
// That whole apparatus was retired in favor of conservative native-
// stack scanning (see scan_thread_native_stack in src/gc_mark.c). At
// every STW pause the marker walks each registered thread's native C
// stack and conservatively marks anything shaped like a heap-object
// pointer — covering AOT formals, register spills, C-locals in
// builtins, and anywhere else the compiler might have parked a
// valk_lval_t* without compiler-emitted bookkeeping. The compiler now
// emits only safepoint polls; the runtime does the rest.
//
// The remaining surface here is `vir_gc_insert_safepoints`, which
// places one VIR_GC_SAFEPOINT op at function entry. Function-entry
// safepoints are sufficient for the LSP workload (every back-edge in
// hot loops eventually reaches a function call, and CALL itself enters
// a callee whose entry has a safepoint). If we observe GC starvation
// in pure-AOT loops in the future, this is the place to add back-edge
// safepoints.

#include "vir.h"
#include <stdlib.h>
#include <string.h>

void vir_gc_insert_safepoints(vir_module_t *mod) {
  vir_builder_t tmp = {.module = mod};

  vir_func_t *fn = mod->func_list;
  while (fn) {
    u32 max_id = 0;
    vir_block_t *bb = fn->block_list;
    while (bb) {
      vir_value_t *v = bb->first;
      while (v) {
        if (v->id > max_id) max_id = v->id;
        v = v->next;
      }
      bb = bb->next;
    }
    tmp.next_val_id = max_id + 1;

    if (fn->entry) {
      vir_value_t *sp = calloc(1, sizeof(vir_value_t));
      sp->opcode = VIR_GC_SAFEPOINT;
      sp->type = VIR_TYPE_VOID;
      sp->id = tmp.next_val_id++;
      sp->parent = fn->entry;

      sp->next = fn->entry->first;
      fn->entry->first = sp;
      if (!fn->entry->last) fn->entry->last = sp;
      fn->entry->num_instrs++;
    }

    fn = fn->next;
  }
}
