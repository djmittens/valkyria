#include "aio_chase_lev.h"
#include "types.h"
#include <stdlib.h>
#include <string.h>

static valk_chase_lev_array_t *valk_chase_lev_array_new(int64_t size) {
  valk_chase_lev_array_t *arr = malloc(sizeof(valk_chase_lev_array_t));
  arr->size = size;
  arr->buffer = calloc((size_t)size, sizeof(_Atomic(void *)));
  return arr;
}

static void valk_chase_lev_array_free(valk_chase_lev_array_t *arr) {
  if (!arr) return; // LCOV_EXCL_BR_LINE: defensive null check, static function always called with valid arr
  free(arr->buffer);
  free(arr);
}

static void *valk_chase_lev_array_get(valk_chase_lev_array_t *arr, int64_t idx) {
  return atomic_load_explicit(&arr->buffer[idx % arr->size], memory_order_relaxed);
}

static void valk_chase_lev_array_put(valk_chase_lev_array_t *arr, int64_t idx, void *item) {
  atomic_store_explicit(&arr->buffer[idx % arr->size], item, memory_order_relaxed);
}

static valk_chase_lev_array_t *valk_chase_lev_array_grow(valk_chase_lev_array_t *arr,
                                                          int64_t top,
                                                          int64_t bottom) {
  valk_chase_lev_array_t *new_arr = valk_chase_lev_array_new(arr->size * 2);
  for (int64_t i = top; i < bottom; i++) {
    valk_chase_lev_array_put(new_arr, i, valk_chase_lev_array_get(arr, i));
  }
  return new_arr;
}

void valk_chase_lev_init(valk_chase_lev_deque_t *deque, int64_t initial_size) {
  atomic_store_explicit(&deque->top, 0, memory_order_relaxed);
  atomic_store_explicit(&deque->bottom, 0, memory_order_relaxed);
  valk_chase_lev_array_t *arr = valk_chase_lev_array_new(initial_size);
  atomic_store_explicit(&deque->array, arr, memory_order_relaxed);
}

void valk_chase_lev_destroy(valk_chase_lev_deque_t *deque) {
  valk_chase_lev_array_t *arr = atomic_load_explicit(&deque->array, memory_order_relaxed);
  valk_chase_lev_array_free(arr);
}

void valk_chase_lev_push(valk_chase_lev_deque_t *deque, void *item) {
  int64_t b = atomic_load_explicit(&deque->bottom, memory_order_relaxed);
  int64_t t = atomic_load_explicit(&deque->top, memory_order_acquire);
  valk_chase_lev_array_t *arr = atomic_load_explicit(&deque->array, memory_order_relaxed);

  if (b - t > arr->size - 1) {
    valk_chase_lev_array_t *new_arr = valk_chase_lev_array_grow(arr, t, b);
    atomic_store_explicit(&deque->array, new_arr, memory_order_release);
    arr = new_arr;
  }

  atomic_store_explicit(&arr->buffer[b % arr->size], item, memory_order_release);
  atomic_thread_fence(memory_order_release);
  atomic_store_explicit(&deque->bottom, b + 1, memory_order_relaxed);
}

void *valk_chase_lev_pop(valk_chase_lev_deque_t *deque) {
  int64_t b = atomic_load_explicit(&deque->bottom, memory_order_relaxed) - 1;
  valk_chase_lev_array_t *arr = atomic_load_explicit(&deque->array, memory_order_relaxed);
  atomic_store_explicit(&deque->bottom, b, memory_order_relaxed);
  atomic_thread_fence(memory_order_seq_cst);

  int64_t t = atomic_load_explicit(&deque->top, memory_order_relaxed);
  void *item;

  if (t <= b) {
    item = valk_chase_lev_array_get(arr, b);
    if (t == b) {
      if (!atomic_compare_exchange_strong_explicit(&deque->top, &t, t + 1,
                                                    memory_order_seq_cst,
                                                    memory_order_relaxed)) {
        item = VALK_CHASE_LEV_EMPTY;
      }
      atomic_store_explicit(&deque->bottom, b + 1, memory_order_relaxed);
    }
  } else {
    item = VALK_CHASE_LEV_EMPTY;
    atomic_store_explicit(&deque->bottom, b + 1, memory_order_relaxed);
  }

  return item;
}

void *valk_chase_lev_steal(valk_chase_lev_deque_t *deque) {
  int64_t t = atomic_load_explicit(&deque->top, memory_order_acquire);
  atomic_thread_fence(memory_order_seq_cst);
  int64_t b = atomic_load_explicit(&deque->bottom, memory_order_acquire);

  void *item = VALK_CHASE_LEV_EMPTY;

  if (t < b) {
    valk_chase_lev_array_t *arr = atomic_load_explicit(&deque->array, memory_order_acquire);
    item = atomic_load_explicit(&arr->buffer[t % arr->size], memory_order_acquire);
    if (!atomic_compare_exchange_strong_explicit(&deque->top, &t, t + 1,
                                                  memory_order_seq_cst,
                                                  memory_order_relaxed)) {
      return VALK_CHASE_LEV_ABORT;
    }
  }

  return item;
}

bool valk_chase_lev_empty(valk_chase_lev_deque_t *deque) {
  int64_t t = atomic_load_explicit(&deque->top, memory_order_relaxed);
  int64_t b = atomic_load_explicit(&deque->bottom, memory_order_relaxed);
  return t >= b;
}

int64_t valk_chase_lev_size(valk_chase_lev_deque_t *deque) {
  int64_t t = atomic_load_explicit(&deque->top, memory_order_relaxed);
  int64_t b = atomic_load_explicit(&deque->bottom, memory_order_relaxed);
  return b - t;
}
