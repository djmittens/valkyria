#include "vir.h"
#include <stdlib.h>
#include <string.h>

static bool is_gc_point(vir_value_t *v) {
  switch (v->opcode) {
    case VIR_CALL:
    case VIR_TAIL_CALL:
    case VIR_ENV_GET:
    case VIR_ENV_PUT:
    case VIR_ENV_DEF:
    case VIR_CONS:
    case VIR_QCONS:
    case VIR_LAMBDA:
    case VIR_CONST_NUM:
    case VIR_CONST_STR:
    case VIR_CONST_SYM:
      return true;
    default:
      return false;
  }
}

static bool is_ptr_value(vir_value_t *v) {
  return v && v->type == VIR_TYPE_PTR;
}

typedef struct {
  vir_value_t **items;
  u32 count;
  u32 cap;
} val_set_t;

static void val_set_init(val_set_t *s) {
  s->items = NULL;
  s->count = 0;
  s->cap = 0;
}

static void val_set_free(val_set_t *s) {
  free(s->items);
}

static bool val_set_contains(val_set_t *s, vir_value_t *v) {
  for (u32 i = 0; i < s->count; i++)
    if (s->items[i] == v) return true;
  return false;
}

static void val_set_add(val_set_t *s, vir_value_t *v) {
  if (val_set_contains(s, v)) return;
  if (s->count >= s->cap) {
    s->cap = s->cap ? s->cap * 2 : 8;
    s->items = realloc(s->items, s->cap * sizeof(vir_value_t *));
  }
  s->items[s->count++] = v;
}

static bool is_used_after(vir_value_t *def, vir_value_t *point) {
  vir_value_t *v = point->next;
  while (v) {
    for (u32 i = 0; i < v->num_operands; i++)
      if (v->operands[i] == def) return true;
    if (v->opcode == VIR_CALL || v->opcode == VIR_TAIL_CALL) {
      for (u32 i = 0; i < v->call.num_args; i++)
        if (v->call.args[i] == def) return true;
    }
    if (v->opcode == VIR_PHI) {
      for (u32 i = 0; i < v->phi.num_incoming; i++)
        if (v->phi.incoming_vals[i] == def) return true;
    }
    v = v->next;
  }
  return false;
}

static void collect_live_ptrs_at(vir_block_t *bb, vir_value_t *point,
                                 val_set_t *live) {
  vir_value_t *v = bb->first;
  while (v && v != point) {
    if (is_ptr_value(v) && is_used_after(v, point))
      val_set_add(live, v);
    v = v->next;
  }
}

static void insert_gc_for_block(vir_builder_t *b, vir_block_t *bb,
                                vir_func_t *fn) {
  vir_value_t *new_first = NULL;
  vir_value_t *new_last = NULL;
  u32 new_count = 0;

  vir_value_t *v = bb->first;
  while (v) {
    vir_value_t *next = v->next;
    v->next = NULL;

    if (is_gc_point(v)) {
      val_set_t live;
      val_set_init(&live);
      collect_live_ptrs_at(bb, v, &live);

      if (fn->num_params > 0 && is_ptr_value(fn->params[0]))
        val_set_add(&live, fn->params[0]);

      if (live.count > 0) {
        vir_value_t *save = calloc(1, sizeof(vir_value_t));
        save->opcode = VIR_GC_ROOT;
        save->type = VIR_TYPE_I64;
        save->id = b->next_val_id++;
        save->gc_save_id = b->next_gc_save_id++;
        save->parent = bb;

        save->num_operands = live.count;
        save->operands = calloc(live.count, sizeof(vir_value_t *));
        memcpy(save->operands, live.items,
               live.count * sizeof(vir_value_t *));

        if (!new_first) { new_first = save; new_last = save; }
        else { new_last->next = save; new_last = save; }
        new_count++;

        if (!new_first) { new_first = v; new_last = v; }
        else { new_last->next = v; new_last = v; }
        new_count++;

        vir_value_t *restore = calloc(1, sizeof(vir_value_t));
        restore->opcode = VIR_GC_UNROOT;
        restore->type = VIR_TYPE_VOID;
        restore->id = b->next_val_id++;
        restore->parent = bb;
        restore->operands = calloc(1, sizeof(vir_value_t *));
        restore->operands[0] = save;
        restore->num_operands = 1;

        new_last->next = restore;
        new_last = restore;
        new_count++;
      } else {
        if (!new_first) { new_first = v; new_last = v; }
        else { new_last->next = v; new_last = v; }
        new_count++;
      }

      val_set_free(&live);
    } else {
      if (!new_first) { new_first = v; new_last = v; }
      else { new_last->next = v; new_last = v; }
      new_count++;
    }

    v = next;
  }

  bb->first = new_first;
  bb->last = new_last;
  bb->num_instrs = new_count;
}

void vir_gc_insert_roots(vir_module_t *mod) {
  vir_builder_t tmp = {.module = mod, .next_val_id = 0, .next_gc_save_id = 0};

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

    bb = fn->block_list;
    while (bb) {
      insert_gc_for_block(&tmp, bb, fn);
      bb = bb->next;
    }
    fn = fn->next;
  }
}

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
