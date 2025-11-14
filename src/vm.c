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
  if (LVAL_FLAG_GC_MARK & lenv->flags || lenv == nullptr) {
    // We did it, we are fully gc !
    return lenv;
  }

  size_t xtra =
      lenv->symbols.count * (sizeof(lenv->symbols.items[0]) + sizeof(lenv->vals.items[0]));

  size_t lens[lenv->symbols.count];
  for (size_t i = 0; i < lenv->symbols.count; i++) {
    lens[i] = strlen(lenv->symbols.items[i]) + 1;
    xtra += lens[i];
  }

  valk_lenv_t* res = valk_gc_alloc(vm->heap, sizeof(valk_lval_t) + xtra);

  char* offset = (char*)res + sizeof(valk_lval_t);
  res->symbols.items = (char**)(offset);
  offset += lenv->symbols.count;

  res->vals.items = (valk_lval_t**)(offset);
  offset += lenv->vals.count;

  for (size_t i = 0; i < lenv->symbols.count; i++) {
    memcpy(offset, lenv->symbols.items[i], lens[i]);
    lenv->vals.items[i] = __valk_vm_escape(vm, lenv->vals.items[i]);
    offset += lens[i];
  }

  // TODO(networking): Should this really be like... Something lenv related?
  res->flags |= LVAL_FLAG_GC_MARK;

  // if(lenv->parent == nullptr)
  return res;
}

static valk_lval_t* __valk_vm_escape(valk_vm_t* vm, valk_lval_t* lval) {
  valk_lval_t* res = lval;
  if (!(LVAL_FLAG_GC_MARK & lval->flags)) {
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
      case LVAL_CONS:
        // Cons-based lists: recursively escape head and tail
        res = valk_gc_alloc(vm->heap, sizeof(valk_lval_t));
        memcpy(res, lval, sizeof(valk_lval_t));
        res->cons.head = __valk_vm_escape(vm, lval->cons.head);
        res->cons.tail = __valk_vm_escape(vm, lval->cons.tail);
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
      case LVAL_NIL:
        res = valk_gc_alloc(vm->heap, sizeof(valk_lval_t));
        memcpy(res, lval, sizeof(valk_lval_t));
        res->cons.head = nullptr;
        res->cons.tail = nullptr;
        break;
      case LVAL_ENV:
      case LVAL_REF:
        break;
      case LVAL_UNDEFINED:
        VALK_RAISE("LVAL is undefined, something went wrong");
        break;
    }
  }
  res->flags |= LVAL_FLAG_GC_MARK;
  return res;
}

valk_lval_t* valk_vm_frame_end(valk_vm_t* vm, valk_lval_t* lval) {
  vm->stack->sp = vm->stack->sp->prev;
  // TODO(networking): detect an expr escape, and move it out to the heap
  return __valk_vm_escape(vm, lval);
}

valk_lval_t* valk_vm_exec(valk_vm_t* vm, valk_lval_t* lval) {
  UNUSED(vm);
  UNUSED(lval);
  return NULL;
}

void* valk_vm_frame_push_str(valk_vm_stack_t* stack, const char* str);
void* valk_vm_frame_push_num(valk_vm_stack_t* stack, int64_t num);
