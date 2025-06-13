#pragma once

#include "parser.h"
typedef struct valk_vm_frame_t {
  struct valk_vm_frame_t* prev;
  struct valk_vm_frame_t* next;
  size_t used;
  size_t free;
} valk_vm_frame_t;

typedef struct {
  valk_vm_frame_t* sentinel;
  valk_vm_frame_t* sp;
  size_t capacity;
} valk_vm_stack_t;

typedef struct {
  valk_gc_heap_t *heap;
  valk_vm_stack_t *stack;
} valk_vm_t;

void valk_vm_stack_init(valk_vm_stack_t* self, size_t capacity);

valk_vm_frame_t* valk_vm_frame_start(valk_vm_t* vm);
valk_lval_t* valk_vm_frame_end(valk_vm_t* vm, valk_lval_t* lval);

void* valk_vm_frame_push_str(valk_vm_stack_t* stack, const char* str);
void* valk_vm_frame_push_num(valk_vm_stack_t* stack, int64_t num);
