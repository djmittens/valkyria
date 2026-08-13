#pragma once

#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

typedef struct valk_mpmc_slot {
  _Atomic(size_t) sequence;
  _Atomic(void *) data;
} valk_mpmc_slot_t;

typedef struct valk_mpmc_queue {
  valk_mpmc_slot_t *buffer;
  size_t mask;
  char _pad0[64 - sizeof(valk_mpmc_slot_t *) - sizeof(size_t)];
  _Atomic(size_t) head;
  char _pad1[64 - sizeof(_Atomic(size_t))];
  _Atomic(size_t) tail;
  char _pad2[64 - sizeof(_Atomic(size_t))];
} valk_mpmc_queue_t;

void valk_mpmc_init(valk_mpmc_queue_t *q, size_t capacity);
void valk_mpmc_destroy(valk_mpmc_queue_t *q);

bool valk_mpmc_push(valk_mpmc_queue_t *q, void *item);
void *valk_mpmc_pop(valk_mpmc_queue_t *q);

bool valk_mpmc_empty(valk_mpmc_queue_t *q);
size_t valk_mpmc_size(valk_mpmc_queue_t *q);
