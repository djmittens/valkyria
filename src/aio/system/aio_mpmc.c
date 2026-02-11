#include "aio_mpmc.h"
#include <stdlib.h>
#include <string.h>

void valk_mpmc_init(valk_mpmc_queue_t *q, size_t capacity) {
  capacity = capacity < 2 ? 2 : capacity;
  size_t cap = 1;
  while (cap < capacity) cap <<= 1;

  q->buffer = aligned_alloc(64, cap * sizeof(valk_mpmc_slot_t));
  q->mask = cap - 1;

  for (size_t i = 0; i < cap; i++) {
    atomic_store_explicit(&q->buffer[i].sequence, i, memory_order_relaxed);
    atomic_store_explicit(&q->buffer[i].data, NULL, memory_order_relaxed);
  }

  atomic_store_explicit(&q->head, 0, memory_order_relaxed);
  atomic_store_explicit(&q->tail, 0, memory_order_relaxed);
}

void valk_mpmc_destroy(valk_mpmc_queue_t *q) {
  free(q->buffer);
  q->buffer = NULL;
}

bool valk_mpmc_push(valk_mpmc_queue_t *q, void *item) {
  size_t tail = atomic_load_explicit(&q->tail, memory_order_relaxed);

  for (;;) {
    valk_mpmc_slot_t *slot = &q->buffer[tail & q->mask];
    size_t seq = atomic_load_explicit(&slot->sequence, memory_order_acquire);
    intptr_t diff = (intptr_t)seq - (intptr_t)tail;

    if (diff == 0) {
      if (atomic_compare_exchange_weak_explicit(&q->tail, &tail, tail + 1,
                                                 memory_order_relaxed,
                                                 memory_order_relaxed)) {
        atomic_store_explicit(&slot->data, item, memory_order_relaxed);
        atomic_store_explicit(&slot->sequence, tail + 1, memory_order_release);
        return true;
      }
    } else if (diff < 0) {
      return false;
    } else {
      tail = atomic_load_explicit(&q->tail, memory_order_relaxed);
    }
  }
}

void *valk_mpmc_pop(valk_mpmc_queue_t *q) {
  size_t head = atomic_load_explicit(&q->head, memory_order_relaxed);

  for (;;) {
    valk_mpmc_slot_t *slot = &q->buffer[head & q->mask];
    size_t seq = atomic_load_explicit(&slot->sequence, memory_order_acquire);
    intptr_t diff = (intptr_t)seq - (intptr_t)(head + 1);

    if (diff == 0) {
      if (atomic_compare_exchange_weak_explicit(&q->head, &head, head + 1,
                                                 memory_order_relaxed,
                                                 memory_order_relaxed)) {
        void *data = atomic_load_explicit(&slot->data, memory_order_relaxed);
        atomic_store_explicit(&slot->sequence, head + q->mask + 1, memory_order_release);
        return data;
      }
    } else if (diff < 0) {
      return NULL;
    } else {
      head = atomic_load_explicit(&q->head, memory_order_relaxed);
    }
  }
}

bool valk_mpmc_empty(valk_mpmc_queue_t *q) {
  size_t head = atomic_load_explicit(&q->head, memory_order_relaxed);
  size_t tail = atomic_load_explicit(&q->tail, memory_order_relaxed);
  return head >= tail;
}

size_t valk_mpmc_size(valk_mpmc_queue_t *q) {
  size_t head = atomic_load_explicit(&q->head, memory_order_relaxed);
  size_t tail = atomic_load_explicit(&q->tail, memory_order_relaxed);
  return tail > head ? tail - head : 0;
}
