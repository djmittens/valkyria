#include "vm.h"

#include <string.h>

#include "common.h"
#include "memory.h"
#include "parser.h"

void valk_vm_stack_init(valk_vm_stack_t* self, size_t capacity) {
  self->capacity = capacity;
  self->sentinel = (valk_vm_frame_t*)(self + 1);
  self->sentinel->prev = self->sentinel;
  self->sentinel->next = self->sentinel;
  self->sentinel->free = capacity;
}

valk_vm_frame_t* valk_vm_frame_start(valk_vm_t* vm) {
  valk_vm_frame_t* self = vm->stack->sp;
  VALK_ASSERT(self->free > sizeof(valk_vm_frame_t), "Stack overflow LULZ, %ld",
              self->free);

  valk_vm_frame_t* res =
      (void*)((uint8_t*)self + sizeof(valk_vm_frame_t) + self->used);

  res->prev = self;
  res->next = vm->stack->sentinel;
  res->used = 0;
  res->free = self->free - sizeof(valk_vm_frame_t);

  vm->stack->sp = res;

  return res;
}

static valk_lval_t* __valk_vm_escape(valk_vm_t* vm, valk_lval_t* lval);
static valk_lenv_t* __valk_vm_lenv_escape(valk_vm_t* vm, valk_lenv_t* lenv) {
  if (LVAL_FLAG_GC & lenv->flags || lenv == nullptr) {
    // We did it, we are fully gc !
    return lenv;
  }

  size_t xtra =
      lenv->count * (sizeof(lenv->symbols[0]) + sizeof(lenv->vals[0]));

  size_t lens[lenv->count];
  for (size_t i = 0; i < lenv->count; i++) {
    lens[i] = strlen(lenv->symbols[i]) + 1;
    xtra += lens[i];
  }

  valk_lenv_t* res = valk_gc_alloc(vm->heap, sizeof(valk_lval_t) + xtra);

  char* offset = (char*)res + sizeof(valk_lval_t);
  res->symbols = (char**)(offset);
  offset += lenv->count;

  res->vals = (valk_lval_t**)(offset);
  offset += lenv->count;


  for (size_t i = 0; i < lenv->count; i++) {
    memcpy(offset, lenv->symbols[i], lens[i]);
    lenv->vals[i] = __valk_vm_escape(vm, lenv->vals[i]);
    offset += lens[i];
  }

  // TODO(networking): Should this really be like... Something lenv related?
  res->flags |= LVAL_FLAG_GC;

  // if(lenv->parent == nullptr)
  return res;
}

static valk_lval_t* __valk_vm_escape(valk_vm_t* vm, valk_lval_t* lval) {
  valk_lval_t* res = lval;
  if (!(LVAL_FLAG_GC & lval->flags)) {
    size_t xtra = 0;
    switch (LVAL_TYPE(lval)) {
      case LVAL_NUM:
        res = valk_gc_alloc(vm->heap, sizeof(valk_lval_t) + xtra);
        memcpy(res, lval, sizeof(valk_lval_t));
        break;
      case LVAL_SYM:
      case LVAL_ERR:
      case LVAL_STR:
        xtra = strlen(lval->str);
        res = valk_gc_alloc(vm->heap, sizeof(valk_lval_t) + xtra);
        memcpy(res, lval, sizeof(valk_lval_t));
        res->str = (char*)(res + 1);
        strcpy(res->str, lval->str);
        break;
      case LVAL_QEXPR:
      case LVAL_SEXPR:
        xtra = lval->expr.count * sizeof(lval->expr.cell[0]);
        res = valk_gc_alloc(vm->heap, sizeof(valk_lval_t) + xtra);
        memcpy(res, lval, sizeof(valk_lval_t) + xtra);
        res->expr.cell = (valk_lval_t**)(res + 1);
        // copy over our cells
        memcpy(res->expr.cell, lval->expr.cell, xtra);
        for (size_t i = 0; i < lval->expr.count; i++) {
          res->expr.cell[i] = __valk_vm_escape(vm, lval->expr.cell[i]);
        }
        break;
      case LVAL_FUN: {
        // copy env
        // escape
        res = valk_gc_alloc(vm->heap, sizeof(valk_lval_t) + xtra);
        memcpy(res, lval, sizeof(valk_lval_t));
        res->fun.env = __valk_vm_lenv_escape(vm, lval->fun.env);
        res->fun.formals = __valk_vm_escape(vm, lval->fun.formals);
        res->fun.body = __valk_vm_escape(vm, lval->fun.body);
        break;
      }
      case LVAL_REF:
        break;
    }
  }
  res->flags |= LVAL_FLAG_GC;
  return res;
}

valk_lval_t* valk_vm_frame_end(valk_vm_t* vm, valk_lval_t* lval) {
  vm->stack->sp = vm->stack->sp->prev;
  // TODO(networking): detect an expr escape, and move it out to the heap
  return __valk_vm_escape(vm, lval);
}

void* valk_vm_frame_push_str(valk_vm_stack_t* stack, const char* str);
void* valk_vm_frame_push_num(valk_vm_stack_t* stack, int64_t num);
