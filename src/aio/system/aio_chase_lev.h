#pragma once

#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>

typedef struct valk_chase_lev_array {
  int64_t size;
  _Atomic(void *) *buffer;
} valk_chase_lev_array_t;

typedef struct valk_chase_lev_garbage {
  valk_chase_lev_array_t *array;
  struct valk_chase_lev_garbage *next;
} valk_chase_lev_garbage_t;

typedef struct valk_chase_lev_deque {
  _Atomic(int64_t) top;
  _Atomic(int64_t) bottom;
  _Atomic(valk_chase_lev_array_t *) array;
  valk_chase_lev_garbage_t *garbage;
  _Atomic(int) push_lock;
} valk_chase_lev_deque_t;

#define VALK_CHASE_LEV_EMPTY ((void *)0)
#define VALK_CHASE_LEV_ABORT ((void *)1)

void valk_chase_lev_init(valk_chase_lev_deque_t *deque, int64_t initial_size);
void valk_chase_lev_destroy(valk_chase_lev_deque_t *deque);

void valk_chase_lev_push(valk_chase_lev_deque_t *deque, void *item);
void *valk_chase_lev_pop(valk_chase_lev_deque_t *deque);
void *valk_chase_lev_steal(valk_chase_lev_deque_t *deque);

bool valk_chase_lev_empty(valk_chase_lev_deque_t *deque);
int64_t valk_chase_lev_size(valk_chase_lev_deque_t *deque);
