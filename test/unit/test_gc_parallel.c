#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/gc.h"
#include "../../src/parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

void test_gc_coordinator_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();

  VALK_TEST_ASSERT(atomic_load(&valk_gc_coord.phase) == VALK_GC_PHASE_IDLE,
                   "Phase should be IDLE after init");
  VALK_TEST_ASSERT(atomic_load(&valk_gc_coord.threads_registered) == 0,
                   "threads_registered should be 0");
  VALK_TEST_ASSERT(atomic_load(&valk_gc_coord.threads_paused) == 0,
                   "threads_paused should be 0");

  VALK_PASS();
}

void test_gc_atomic_mark_single(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  valk_lval_t *val = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  val->flags = LVAL_NUM | LVAL_ALLOC_HEAP;
  val->num = 42;

  VALK_TEST_ASSERT(!valk_gc_is_marked(val), "Should not be marked initially");

  bool first = valk_gc_try_mark(val);
  VALK_TEST_ASSERT(first == true, "First mark should succeed");
  VALK_TEST_ASSERT(valk_gc_is_marked(val), "Should be marked after try_mark");

  bool second = valk_gc_try_mark(val);
  VALK_TEST_ASSERT(second == false, "Second mark should fail");

  valk_gc_clear_mark(val);
  VALK_TEST_ASSERT(!valk_gc_is_marked(val), "Should not be marked after clear");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_atomic_mark_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool result = valk_gc_try_mark(NULL);
  VALK_TEST_ASSERT(result == false, "try_mark(NULL) should return false");

  bool is_marked = valk_gc_is_marked(NULL);
  VALK_TEST_ASSERT(is_marked == true, "is_marked(NULL) should return true");

  valk_gc_clear_mark(NULL);

  VALK_PASS();
}

typedef struct {
  valk_lval_t *val;
  int success_count;
  int attempts;
} mark_race_ctx_t;

static void *mark_race_thread(void *arg) {
  mark_race_ctx_t *ctx = arg;
  int local_success = 0;
  for (int i = 0; i < ctx->attempts; i++) {
    if (valk_gc_try_mark(ctx->val)) {
      local_success++;
    }
    valk_gc_clear_mark(ctx->val);
  }
  ctx->success_count = local_success;
  return NULL;
}

void test_gc_atomic_mark_multithread(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  valk_lval_t *val = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  val->flags = LVAL_NUM | LVAL_ALLOC_HEAP;

  const int NUM_THREADS = 4;
  const int ATTEMPTS = 1000;
  pthread_t threads[NUM_THREADS];
  mark_race_ctx_t ctxs[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    ctxs[i].val = val;
    ctxs[i].success_count = 0;
    ctxs[i].attempts = ATTEMPTS;
    pthread_create(&threads[i], NULL, mark_race_thread, &ctxs[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], NULL);
  }

  int total_success = 0;
  for (int i = 0; i < NUM_THREADS; i++) {
    total_success += ctxs[i].success_count;
  }

  VALK_TEST_ASSERT(total_success > 0, "At least some marks should succeed");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_barrier_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_barrier_t barrier;
  valk_barrier_init(&barrier, 1);

  valk_barrier_wait(&barrier);

  valk_barrier_destroy(&barrier);

  VALK_PASS();
}

typedef struct {
  valk_barrier_t *barrier;
  int *counter;
  pthread_mutex_t *mutex;
} barrier_ctx_t;

static void *barrier_thread(void *arg) {
  barrier_ctx_t *ctx = arg;

  pthread_mutex_lock(ctx->mutex);
  (*ctx->counter)++;
  pthread_mutex_unlock(ctx->mutex);

  valk_barrier_wait(ctx->barrier);

  return NULL;
}

void test_gc_barrier_multithread(VALK_TEST_ARGS()) {
  VALK_TEST();

  const int NUM_THREADS = 4;
  valk_barrier_t barrier;
  valk_barrier_init(&barrier, NUM_THREADS);

  int counter = 0;
  pthread_mutex_t mutex;
  pthread_mutex_init(&mutex, NULL);

  pthread_t threads[NUM_THREADS];
  barrier_ctx_t ctxs[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    ctxs[i].barrier = &barrier;
    ctxs[i].counter = &counter;
    ctxs[i].mutex = &mutex;
    pthread_create(&threads[i], NULL, barrier_thread, &ctxs[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], NULL);
  }

  VALK_TEST_ASSERT(counter == NUM_THREADS, "All threads should have incremented counter");

  pthread_mutex_destroy(&mutex);
  valk_barrier_destroy(&barrier);

  VALK_PASS();
}

void test_gc_mark_queue_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  VALK_TEST_ASSERT(atomic_load(&queue.top) == 0, "top should be 0");
  VALK_TEST_ASSERT(atomic_load(&queue.bottom) == 0, "bottom should be 0");
  VALK_TEST_ASSERT(valk_gc_mark_queue_empty(&queue), "Queue should be empty");

  VALK_PASS();
}

void test_gc_mark_queue_push_pop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_lval_t *vals[10];
  for (int i = 0; i < 10; i++) {
    vals[i] = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
    vals[i]->flags = LVAL_NUM;
    vals[i]->num = i;
  }

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  for (int i = 0; i < 10; i++) {
    bool pushed = valk_gc_mark_queue_push(&queue, vals[i]);
    VALK_TEST_ASSERT(pushed, "Push %d should succeed", i);
  }

  VALK_TEST_ASSERT(!valk_gc_mark_queue_empty(&queue), "Queue should not be empty");

  for (int i = 9; i >= 0; i--) {
    valk_lval_t *popped = valk_gc_mark_queue_pop(&queue);
    VALK_TEST_ASSERT(popped == vals[i], "Pop should return vals[%d]", i);
  }

  VALK_TEST_ASSERT(valk_gc_mark_queue_empty(&queue), "Queue should be empty after pops");

  valk_lval_t *empty_pop = valk_gc_mark_queue_pop(&queue);
  VALK_TEST_ASSERT(empty_pop == NULL, "Pop from empty queue should return NULL");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_mark_queue_steal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_lval_t *vals[5];
  for (int i = 0; i < 5; i++) {
    vals[i] = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
    vals[i]->flags = LVAL_NUM;
    vals[i]->num = i;
  }

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  for (int i = 0; i < 5; i++) {
    valk_gc_mark_queue_push(&queue, vals[i]);
  }

  valk_lval_t *stolen = valk_gc_mark_queue_steal(&queue);
  VALK_TEST_ASSERT(stolen == vals[0], "Steal should return first element (FIFO)");

  stolen = valk_gc_mark_queue_steal(&queue);
  VALK_TEST_ASSERT(stolen == vals[1], "Second steal should return second element");

  valk_lval_t *popped = valk_gc_mark_queue_pop(&queue);
  VALK_TEST_ASSERT(popped == vals[4], "Pop should return last element (LIFO)");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_mark_queue_full(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(100 * 1024 * 1024);

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  int pushed = 0;
  for (size_t i = 0; i < VALK_GC_MARK_QUEUE_SIZE + 100; i++) {
    valk_lval_t *val = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
    val->flags = LVAL_NUM;
    if (valk_gc_mark_queue_push(&queue, val)) {
      pushed++;
    }
  }

  VALK_TEST_ASSERT(pushed == VALK_GC_MARK_QUEUE_SIZE, 
                   "Should push exactly VALK_GC_MARK_QUEUE_SIZE items (pushed=%d)", pushed);

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_thread_register_unregister(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();

  size_t before = atomic_load(&valk_gc_coord.threads_registered);

  valk_gc_thread_register();
  VALK_TEST_ASSERT(valk_thread_ctx.gc_registered, "Should be registered");
  VALK_TEST_ASSERT(atomic_load(&valk_gc_coord.threads_registered) == before + 1,
                   "threads_registered should increase");

  size_t my_id = valk_thread_ctx.gc_thread_id;
  VALK_TEST_ASSERT(valk_gc_coord.threads[my_id].active, "Thread slot should be active");

  valk_gc_thread_unregister();
  VALK_TEST_ASSERT(!valk_thread_ctx.gc_registered, "Should be unregistered");
  VALK_TEST_ASSERT(!valk_gc_coord.threads[my_id].active, "Thread slot should be inactive");

  VALK_PASS();
}

void test_gc_global_roots_add_remove(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  valk_lval_t *val1 = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  valk_lval_t *val2 = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  val1->flags = LVAL_NUM;
  val2->flags = LVAL_NUM;

  size_t before = valk_gc_global_roots.count;

  valk_gc_add_global_root(&val1);
  VALK_TEST_ASSERT(valk_gc_global_roots.count == before + 1, "count should increase");

  valk_gc_add_global_root(&val2);
  VALK_TEST_ASSERT(valk_gc_global_roots.count == before + 2, "count should increase again");

  valk_gc_remove_global_root(&val1);
  VALK_TEST_ASSERT(valk_gc_global_roots.count == before + 1, "count should decrease");

  valk_gc_remove_global_root(&val2);
  VALK_TEST_ASSERT(valk_gc_global_roots.count == before, "count should return to original");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_safe_point_idle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);

  VALK_GC_SAFE_POINT();

  VALK_PASS();
}

typedef struct {
  valk_gc_mark_queue_t *queue;
  valk_lval_t **vals;
  int count;
  int stolen;
} steal_ctx_t;

static void *stealer_thread(void *arg) {
  steal_ctx_t *ctx = arg;
  ctx->stolen = 0;
  for (int i = 0; i < ctx->count * 2; i++) {
    valk_lval_t *val = valk_gc_mark_queue_steal(ctx->queue);
    if (val != NULL) {
      ctx->stolen++;
    }
  }
  return NULL;
}

void test_gc_mark_queue_concurrent_steal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  const int NUM_VALS = 100;
  valk_lval_t *vals[NUM_VALS];
  for (int i = 0; i < NUM_VALS; i++) {
    vals[i] = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
    vals[i]->flags = LVAL_NUM;
    vals[i]->num = i;
  }

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  for (int i = 0; i < NUM_VALS; i++) {
    valk_gc_mark_queue_push(&queue, vals[i]);
  }

  const int NUM_STEALERS = 3;
  pthread_t threads[NUM_STEALERS];
  steal_ctx_t ctxs[NUM_STEALERS];

  for (int i = 0; i < NUM_STEALERS; i++) {
    ctxs[i].queue = &queue;
    ctxs[i].vals = vals;
    ctxs[i].count = NUM_VALS;
    ctxs[i].stolen = 0;
    pthread_create(&threads[i], NULL, stealer_thread, &ctxs[i]);
  }

  int owner_popped = 0;
  while (true) {
    valk_lval_t *val = valk_gc_mark_queue_pop(&queue);
    if (val == NULL) break;
    owner_popped++;
  }

  for (int i = 0; i < NUM_STEALERS; i++) {
    pthread_join(threads[i], NULL);
  }

  int total_stolen = 0;
  for (int i = 0; i < NUM_STEALERS; i++) {
    total_stolen += ctxs[i].stolen;
  }

  int total = owner_popped + total_stolen;
  VALK_TEST_ASSERT(total == NUM_VALS, 
                   "Total processed should equal NUM_VALS (got %d, expected %d)", 
                   total, NUM_VALS);

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_phase_transitions(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();

  VALK_TEST_ASSERT(atomic_load(&valk_gc_coord.phase) == VALK_GC_PHASE_IDLE,
                   "Should start IDLE");

  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  bool cas = atomic_compare_exchange_strong(&valk_gc_coord.phase, &expected,
                                             VALK_GC_PHASE_STW_REQUESTED);
  VALK_TEST_ASSERT(cas, "CAS to STW_REQUESTED should succeed");
  VALK_TEST_ASSERT(atomic_load(&valk_gc_coord.phase) == VALK_GC_PHASE_STW_REQUESTED,
                   "Phase should be STW_REQUESTED");

  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_MARKING);
  VALK_TEST_ASSERT(atomic_load(&valk_gc_coord.phase) == VALK_GC_PHASE_MARKING,
                   "Phase should be MARKING");

  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_SWEEPING);
  VALK_TEST_ASSERT(atomic_load(&valk_gc_coord.phase) == VALK_GC_PHASE_SWEEPING,
                   "Phase should be SWEEPING");

  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  VALK_TEST_ASSERT(atomic_load(&valk_gc_coord.phase) == VALK_GC_PHASE_IDLE,
                   "Phase should be IDLE again");

  VALK_PASS();
}

void test_gc_root_stack_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();
  valk_gc_thread_register();

  VALK_TEST_ASSERT(valk_thread_ctx.root_stack != NULL, "root_stack should be allocated");
  VALK_TEST_ASSERT(valk_thread_ctx.root_stack_capacity == 256, "capacity should be 256");
  VALK_TEST_ASSERT(valk_thread_ctx.root_stack_count == 0, "count should be 0");

  valk_gc_thread_unregister();

  VALK_TEST_ASSERT(valk_thread_ctx.root_stack == NULL, "root_stack should be freed");

  VALK_PASS();
}

// ============================================================================
// Phase 1: Page Pool and TLAB Tests
// ============================================================================

void test_gc_page_pool_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  VALK_TEST_ASSERT(pool.all_pages == NULL, "all_pages should be NULL");
  VALK_TEST_ASSERT(pool.partial_pages == NULL, "partial_pages should be NULL");
  VALK_TEST_ASSERT(pool.num_pages == 0, "num_pages should be 0");
  VALK_TEST_ASSERT(atomic_load(&pool.total_slots) == 0, "total_slots should be 0");
  VALK_TEST_ASSERT(atomic_load(&pool.used_slots) == 0, "used_slots should be 0");

  valk_gc_page_pool_destroy(&pool);

  VALK_PASS();
}

void test_gc_page_alloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  valk_gc_page_t *page = valk_gc_page_alloc(&pool);
  VALK_TEST_ASSERT(page != NULL, "page should be allocated");
  VALK_TEST_ASSERT(pool.num_pages == 1, "num_pages should be 1");
  VALK_TEST_ASSERT(pool.all_pages == page, "all_pages should point to page");
  VALK_TEST_ASSERT(atomic_load(&pool.total_slots) == VALK_GC_SLOTS_PER_PAGE,
                   "total_slots should equal SLOTS_PER_PAGE");
  VALK_TEST_ASSERT(atomic_load(&page->num_allocated) == 0, "num_allocated should be 0");

  for (size_t i = 0; i < VALK_GC_BITMAP_SIZE; i++) {
    VALK_TEST_ASSERT(page->mark_bits[i] == 0, "mark_bits[%zu] should be 0", i);
    VALK_TEST_ASSERT(page->alloc_bits[i] == 0, "alloc_bits[%zu] should be 0", i);
  }

  valk_gc_page_pool_destroy(&pool);

  VALK_PASS();
}

void test_gc_page_alloc_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  const int NUM_PAGES = 5;
  for (int i = 0; i < NUM_PAGES; i++) {
    valk_gc_page_t *page = valk_gc_page_alloc(&pool);
    VALK_TEST_ASSERT(page != NULL, "page %d should be allocated", i);
  }

  VALK_TEST_ASSERT(pool.num_pages == NUM_PAGES, "num_pages should be %d", NUM_PAGES);
  VALK_TEST_ASSERT(atomic_load(&pool.total_slots) == (size_t)(NUM_PAGES * VALK_GC_SLOTS_PER_PAGE),
                   "total_slots should be correct");

  valk_gc_page_pool_destroy(&pool);

  VALK_PASS();
}

void test_gc_tlab_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_tlab_t tlab;
  valk_gc_tlab_init(&tlab);

  VALK_TEST_ASSERT(tlab.page == NULL, "page should be NULL");
  VALK_TEST_ASSERT(tlab.next_slot == 0, "next_slot should be 0");
  VALK_TEST_ASSERT(tlab.limit_slot == 0, "limit_slot should be 0");

  VALK_PASS();
}

void test_gc_tlab_refill(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  valk_gc_tlab_t tlab;
  valk_gc_tlab_init(&tlab);

  bool success = valk_gc_tlab_refill(&tlab, &pool);
  VALK_TEST_ASSERT(success, "TLAB refill should succeed");
  VALK_TEST_ASSERT(tlab.page != NULL, "TLAB page should be set");
  VALK_TEST_ASSERT(tlab.next_slot == 0, "next_slot should be 0");
  VALK_TEST_ASSERT(tlab.limit_slot == VALK_GC_TLAB_SLOTS, "limit_slot should be TLAB_SLOTS");

  valk_gc_page_pool_destroy(&pool);

  VALK_PASS();
}

void test_gc_tlab_alloc_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  valk_gc_tlab_t tlab;
  valk_gc_tlab_init(&tlab);
  valk_gc_tlab_refill(&tlab, &pool);

  VALK_TEST_ASSERT(atomic_load(&tlab.page->num_allocated) == VALK_GC_TLAB_SLOTS,
                   "num_allocated should be TLAB_SLOTS after refill");
  
  for (u32 i = 0; i < VALK_GC_TLAB_SLOTS; i++) {
    VALK_TEST_ASSERT(valk_gc_bitmap_test(tlab.page->alloc_bits, i), 
                     "slot %u should be pre-allocated", i);
  }
  VALK_TEST_ASSERT(!valk_gc_bitmap_test(tlab.page->alloc_bits, VALK_GC_TLAB_SLOTS), 
                   "slot beyond TLAB should not be allocated");

  void *ptr1 = valk_gc_tlab_alloc(&tlab);
  VALK_TEST_ASSERT(ptr1 != NULL, "First allocation should succeed");
  VALK_TEST_ASSERT(tlab.next_slot == 1, "next_slot should be 1");

  void *ptr2 = valk_gc_tlab_alloc(&tlab);
  VALK_TEST_ASSERT(ptr2 != NULL, "Second allocation should succeed");
  VALK_TEST_ASSERT(ptr2 != ptr1, "Allocations should be different");
  VALK_TEST_ASSERT((char*)ptr2 - (char*)ptr1 == VALK_GC_SLOT_SIZE,
                   "Allocations should be SLOT_SIZE apart");

  valk_gc_page_pool_destroy(&pool);

  VALK_PASS();
}

void test_gc_tlab_exhaust_and_refill(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  valk_gc_tlab_t tlab;
  valk_gc_tlab_init(&tlab);
  valk_gc_tlab_refill(&tlab, &pool);

  valk_gc_page_t *first_page = tlab.page;

  for (u32 i = 0; i < VALK_GC_TLAB_SLOTS; i++) {
    void *ptr = valk_gc_tlab_alloc(&tlab);
    VALK_TEST_ASSERT(ptr != NULL, "Allocation %u should succeed", i);
  }

  VALK_TEST_ASSERT(tlab.next_slot == tlab.limit_slot, "TLAB should be exhausted");

  void *ptr_exhausted = valk_gc_tlab_alloc(&tlab);
  VALK_TEST_ASSERT(ptr_exhausted == NULL, "Exhausted TLAB should return NULL");

  bool refill_success = valk_gc_tlab_refill(&tlab, &pool);
  VALK_TEST_ASSERT(refill_success, "Second refill should succeed");

  void *ptr_after_refill = valk_gc_tlab_alloc(&tlab);
  VALK_TEST_ASSERT(ptr_after_refill != NULL, "Allocation after refill should succeed");

  (void)first_page;

  valk_gc_page_pool_destroy(&pool);

  VALK_PASS();
}

void test_gc_bitmap_operations(VALK_TEST_ARGS()) {
  VALK_TEST();

  u8 bitmap[16] = {0};

  VALK_TEST_ASSERT(!valk_gc_bitmap_test(bitmap, 0), "bit 0 should be clear");
  VALK_TEST_ASSERT(!valk_gc_bitmap_test(bitmap, 7), "bit 7 should be clear");
  VALK_TEST_ASSERT(!valk_gc_bitmap_test(bitmap, 8), "bit 8 should be clear");
  VALK_TEST_ASSERT(!valk_gc_bitmap_test(bitmap, 127), "bit 127 should be clear");

  valk_gc_bitmap_set(bitmap, 0);
  VALK_TEST_ASSERT(valk_gc_bitmap_test(bitmap, 0), "bit 0 should be set");
  VALK_TEST_ASSERT(!valk_gc_bitmap_test(bitmap, 1), "bit 1 should be clear");

  valk_gc_bitmap_set(bitmap, 7);
  VALK_TEST_ASSERT(valk_gc_bitmap_test(bitmap, 7), "bit 7 should be set");
  VALK_TEST_ASSERT(bitmap[0] == 0x81, "bitmap[0] should be 0x81");

  valk_gc_bitmap_set(bitmap, 8);
  VALK_TEST_ASSERT(valk_gc_bitmap_test(bitmap, 8), "bit 8 should be set");
  VALK_TEST_ASSERT(bitmap[1] == 0x01, "bitmap[1] should be 0x01");

  valk_gc_bitmap_clear(bitmap, 0);
  VALK_TEST_ASSERT(!valk_gc_bitmap_test(bitmap, 0), "bit 0 should be cleared");
  VALK_TEST_ASSERT(valk_gc_bitmap_test(bitmap, 7), "bit 7 should still be set");

  valk_gc_bitmap_set(bitmap, 127);
  VALK_TEST_ASSERT(valk_gc_bitmap_test(bitmap, 127), "bit 127 should be set");

  VALK_PASS();
}

typedef struct {
  valk_gc_page_pool_t *pool;
  int allocs_per_thread;
  void **results;
  int success_count;
} tlab_thread_ctx_t;

static void *tlab_alloc_thread(void *arg) {
  tlab_thread_ctx_t *ctx = arg;
  
  valk_gc_tlab_t tlab;
  valk_gc_tlab_init(&tlab);
  
  ctx->success_count = 0;
  
  for (int i = 0; i < ctx->allocs_per_thread; i++) {
    void *ptr = valk_gc_tlab_alloc(&tlab);
    if (!ptr) {
      if (!valk_gc_tlab_refill(&tlab, ctx->pool)) {
        break;
      }
      ptr = valk_gc_tlab_alloc(&tlab);
    }
    if (ptr) {
      ctx->results[i] = ptr;
      ctx->success_count++;
    }
  }
  
  return NULL;
}

void test_gc_tlab_multithread(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  const int NUM_THREADS = 4;
  const int ALLOCS_PER_THREAD = 100;
  
  pthread_t threads[NUM_THREADS];
  tlab_thread_ctx_t ctxs[NUM_THREADS];
  void *results[NUM_THREADS][ALLOCS_PER_THREAD];

  for (int i = 0; i < NUM_THREADS; i++) {
    ctxs[i].pool = &pool;
    ctxs[i].allocs_per_thread = ALLOCS_PER_THREAD;
    ctxs[i].results = results[i];
    ctxs[i].success_count = 0;
    pthread_create(&threads[i], NULL, tlab_alloc_thread, &ctxs[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], NULL);
  }

  int total_success = 0;
  for (int i = 0; i < NUM_THREADS; i++) {
    total_success += ctxs[i].success_count;
  }

  VALK_TEST_ASSERT(total_success == NUM_THREADS * ALLOCS_PER_THREAD,
                   "All allocations should succeed (got %d, expected %d)",
                   total_success, NUM_THREADS * ALLOCS_PER_THREAD);

  for (int i = 0; i < NUM_THREADS; i++) {
    for (int j = 0; j < ctxs[i].success_count; j++) {
      void *ptr = results[i][j];
      VALK_TEST_ASSERT(ptr != NULL, "Thread %d alloc %d should not be NULL", i, j);
      
      for (int k = i; k < NUM_THREADS; k++) {
        int start = (k == i) ? j + 1 : 0;
        for (int l = start; l < ctxs[k].success_count; l++) {
          VALK_TEST_ASSERT(ptr != results[k][l],
                           "Duplicate pointer found: thread %d/%d and %d/%d",
                           i, j, k, l);
        }
      }
    }
  }

  valk_gc_page_pool_destroy(&pool);

  VALK_PASS();
}

void test_gc_page_pool_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  u64 pages, total, used;
  valk_gc_page_pool_stats(&pool, &pages, &total, &used);
  VALK_TEST_ASSERT(pages == 0, "pages should be 0");
  VALK_TEST_ASSERT(total == 0, "total should be 0");
  VALK_TEST_ASSERT(used == 0, "used should be 0");

  valk_gc_page_alloc(&pool);
  valk_gc_page_pool_stats(&pool, &pages, &total, &used);
  VALK_TEST_ASSERT(pages == 1, "pages should be 1");
  VALK_TEST_ASSERT(total == VALK_GC_SLOTS_PER_PAGE, "total should be SLOTS_PER_PAGE");

  valk_gc_page_pool_destroy(&pool);

  VALK_PASS();
}

// ============================================================================
// Phase 2/3 Tests: Root Management
// ============================================================================

void test_gc_root_push_pop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();
  valk_gc_thread_register();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  valk_lval_t *val1 = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  valk_lval_t *val2 = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  val1->flags = LVAL_NUM;
  val2->flags = LVAL_NUM;

  size_t before = valk_thread_ctx.root_stack_count;

  valk_gc_root_t r1 = valk_gc_root_push(val1);
  VALK_TEST_ASSERT(valk_thread_ctx.root_stack_count == before + 1, "count should increase");
  VALK_TEST_ASSERT(valk_thread_ctx.root_stack[before] == val1, "val1 should be on stack");

  valk_gc_root_t r2 = valk_gc_root_push(val2);
  VALK_TEST_ASSERT(valk_thread_ctx.root_stack_count == before + 2, "count should increase");

  valk_gc_root_pop();
  VALK_TEST_ASSERT(valk_thread_ctx.root_stack_count == before + 1, "count should decrease");

  valk_gc_root_cleanup(&r1);
  VALK_TEST_ASSERT(valk_thread_ctx.root_stack_count == before, "cleanup should restore");

  (void)r2;
  valk_gc_malloc_heap_destroy(heap);
  valk_gc_thread_unregister();

  VALK_PASS();
}

void test_gc_root_scoped(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();
  valk_gc_thread_register();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  valk_lval_t *val = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  val->flags = LVAL_NUM;

  size_t before = valk_thread_ctx.root_stack_count;

  {
    VALK_GC_ROOT(val);
    VALK_TEST_ASSERT(valk_thread_ctx.root_stack_count == before + 1, 
                     "VALK_GC_ROOT should push");
  }

  VALK_TEST_ASSERT(valk_thread_ctx.root_stack_count == before, 
                   "Should auto-pop on scope exit");

  valk_gc_malloc_heap_destroy(heap);
  valk_gc_thread_unregister();

  VALK_PASS();
}

typedef struct {
  int count;
  valk_lval_t *found[10];
} root_visitor_ctx_t;

static void root_visitor_fn(valk_lval_t *root, void *c) {
  root_visitor_ctx_t *vc = c;
  if (vc->count < 10) vc->found[vc->count++] = root;
}

void test_gc_visit_thread_roots(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();
  valk_gc_thread_register();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  valk_lval_t *val1 = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  valk_lval_t *val2 = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  val1->flags = LVAL_NUM;
  val1->num = 42;
  val2->flags = LVAL_NUM;
  val2->num = 99;

  valk_gc_root_push(val1);
  valk_gc_root_push(val2);

  root_visitor_ctx_t ctx = {0};
  valk_gc_visit_thread_roots(root_visitor_fn, &ctx);

  VALK_TEST_ASSERT(ctx.count >= 2, "Should visit at least 2 roots");

  bool found_val1 = false, found_val2 = false;
  for (int i = 0; i < ctx.count; i++) {
    if (ctx.found[i] == val1) found_val1 = true;
    if (ctx.found[i] == val2) found_val2 = true;
  }
  VALK_TEST_ASSERT(found_val1, "Should find val1");
  VALK_TEST_ASSERT(found_val2, "Should find val2");

  valk_gc_malloc_heap_destroy(heap);
  valk_gc_thread_unregister();

  VALK_PASS();
}

// ============================================================================
// Phase 4 Tests: Parallel Mark
// ============================================================================

void test_gc_termination_check(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();
  valk_gc_thread_register();

  bool terminated = valk_gc_check_termination();
  VALK_TEST_ASSERT(terminated == true, 
                   "With empty queues and 1 registered thread, should terminate");

  valk_gc_thread_unregister();

  VALK_PASS();
}

void test_gc_mark_linked_list(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();
  valk_gc_thread_register();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  const int LIST_LEN = 100;
  valk_lval_t *nodes[LIST_LEN];
  
  for (int i = 0; i < LIST_LEN; i++) {
    nodes[i] = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
    nodes[i]->flags = LVAL_CONS;
    nodes[i]->cons.head = NULL;
    nodes[i]->cons.tail = (i > 0) ? nodes[i-1] : NULL;
  }

  valk_gc_root_push(nodes[LIST_LEN - 1]);

  valk_barrier_init(&valk_gc_coord.barrier, 1);
  valk_gc_coord.barrier_initialized = true;

  valk_gc_parallel_mark();

  for (int i = 0; i < LIST_LEN; i++) {
    VALK_TEST_ASSERT(valk_gc_is_marked(nodes[i]), "node[%d] should be marked", i);
  }

  for (int i = 0; i < LIST_LEN; i++) {
    valk_gc_clear_mark(nodes[i]);
  }

  valk_gc_malloc_heap_destroy(heap);
  valk_gc_thread_unregister();

  VALK_PASS();
}

// ============================================================================
// Phase 5 Tests: Parallel Sweep
// ============================================================================

void test_gc_sweep_page_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();
  valk_gc_thread_register();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  valk_gc_tlab_t tlab;
  valk_gc_tlab_init(&tlab);
  valk_gc_tlab_refill(&tlab, &pool);

  void *ptr1 = valk_gc_tlab_alloc(&tlab);
  void *ptr2 = valk_gc_tlab_alloc(&tlab);
  void *ptr3 = valk_gc_tlab_alloc(&tlab);

  VALK_TEST_ASSERT(ptr1 != NULL && ptr2 != NULL && ptr3 != NULL, 
                   "All allocations should succeed");

  valk_gc_bitmap_set(tlab.page->mark_bits, 0);

  size_t used_before = atomic_load(&pool.used_slots);

  valk_gc_parallel_sweep(&pool);

  size_t used_after = atomic_load(&pool.used_slots);
  VALK_TEST_ASSERT(used_after < used_before, 
                   "used_slots should decrease after sweep (before=%zu, after=%zu)",
                   used_before, used_after);

  VALK_TEST_ASSERT(valk_gc_bitmap_test(tlab.page->alloc_bits, 0), 
                   "slot 0 should still be allocated (was marked)");
  VALK_TEST_ASSERT(!valk_gc_bitmap_test(tlab.page->alloc_bits, 1), 
                   "slot 1 should be freed (not marked)");
  VALK_TEST_ASSERT(!valk_gc_bitmap_test(tlab.page->alloc_bits, 2), 
                   "slot 2 should be freed (not marked)");

  valk_gc_page_pool_destroy(&pool);
  valk_gc_thread_unregister();

  VALK_PASS();
}

void test_gc_sweep_clears_marks(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_coordinator_init();
  valk_gc_thread_register();

  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);

  valk_gc_tlab_t tlab;
  valk_gc_tlab_init(&tlab);
  valk_gc_tlab_refill(&tlab, &pool);

  valk_gc_tlab_alloc(&tlab);
  
  valk_gc_bitmap_set(tlab.page->mark_bits, 0);
  VALK_TEST_ASSERT(valk_gc_bitmap_test(tlab.page->mark_bits, 0), 
                   "mark should be set before sweep");

  valk_gc_parallel_sweep(&pool);

  VALK_TEST_ASSERT(!valk_gc_bitmap_test(tlab.page->mark_bits, 0), 
                   "mark should be cleared after sweep");

  valk_gc_page_pool_destroy(&pool);
  valk_gc_thread_unregister();

  VALK_PASS();
}

// ============================================================================
// Phase 6: Integration Tests
// ============================================================================

void test_gc_maybe_collect_below_threshold(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_gc_coordinator_init();
  valk_gc_thread_register();
  
  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);
  
  atomic_store(&pool.gc_threshold, 1000);
  atomic_store(&pool.used_slots, 100);
  
  valk_gc_phase_e phase_before = atomic_load(&valk_gc_coord.phase);
  
  valk_gc_maybe_collect(&pool);
  
  valk_gc_phase_e phase_after = atomic_load(&valk_gc_coord.phase);
  VALK_TEST_ASSERT(phase_before == phase_after && phase_after == VALK_GC_PHASE_IDLE, 
                   "no collection should occur below threshold - phase stays IDLE");
  
  valk_gc_page_pool_destroy(&pool);
  valk_gc_thread_unregister();
  
  VALK_PASS();
}

void test_gc_full_cycle_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_gc_coordinator_init();
  valk_gc_thread_register();
  
  valk_gc_page_pool_t pool;
  valk_gc_page_pool_init(&pool);
  
  valk_gc_tlab_t tlab;
  valk_gc_tlab_init(&tlab);
  valk_gc_tlab_refill(&tlab, &pool);
  
  void *slot1 = valk_gc_tlab_alloc(&tlab);
  void *slot2 = valk_gc_tlab_alloc(&tlab);
  VALK_TEST_ASSERT(slot1 != NULL && slot2 != NULL, "should alloc slots");
  
  size_t used_before = atomic_load(&pool.used_slots);
  
  if (valk_gc_coord.barrier_initialized) {
    valk_barrier_destroy(&valk_gc_coord.barrier);
  }
  valk_barrier_init(&valk_gc_coord.barrier, 1);
  valk_gc_coord.barrier_initialized = true;
  
  valk_gc_full_cycle(&pool);
  
  size_t used_after = atomic_load(&pool.used_slots);
  VALK_TEST_ASSERT(used_after < used_before, 
                   "sweep should free unmarked slots");
  
  valk_gc_page_pool_destroy(&pool);
  valk_gc_thread_unregister();
  
  VALK_PASS();
}

void test_gc_safe_point_with_stw(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_gc_coordinator_init();
  valk_gc_thread_register();
  
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  
  size_t paused_before = atomic_load(&valk_gc_coord.threads_paused);
  VALK_GC_SAFE_POINT();
  size_t paused_after = atomic_load(&valk_gc_coord.threads_paused);
  
  VALK_TEST_ASSERT(paused_before == paused_after, 
                   "idle safe point should not change pause count");
  
  valk_gc_thread_unregister();
  
  VALK_PASS();
}

// ============================================================================
// Phase 7 Tests: Global Pool and TLAB Slow Path
// ============================================================================

void test_gc_global_pool_init(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_global_pool_init();
  
  u64 pages, total, used;
  valk_gc_page_pool_stats(&valk_gc_global_pool, &pages, &total, &used);
  
  VALK_TEST_ASSERT(pages == 0, "global pool should start empty");
  VALK_TEST_ASSERT(total == 0, "global pool total should be 0");
  VALK_TEST_ASSERT(used == 0, "global pool used should be 0");
  
  valk_gc_global_pool_destroy();
  
  VALK_PASS();
}

void test_gc_tlab_alloc_slow_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_global_pool_init();
  
  valk_thread_context_t *ctx = &valk_thread_ctx;
  ctx->tlab = NULL;
  ctx->tlab_enabled = false;
  
  void *ptr1 = valk_gc_tlab_alloc_slow(sizeof(valk_lval_t));
  VALK_TEST_ASSERT(ptr1 != NULL, "first slow alloc should succeed");
  VALK_TEST_ASSERT(ctx->tlab != NULL, "tlab should be initialized after alloc");
  VALK_TEST_ASSERT(ctx->tlab_enabled, "tlab_enabled should be true after alloc");
  
  void *ptr2 = valk_gc_tlab_alloc_slow(sizeof(valk_lval_t));
  VALK_TEST_ASSERT(ptr2 != NULL, "second slow alloc should succeed");
  VALK_TEST_ASSERT(ptr2 != ptr1, "allocations should be different");
  
  if (ctx->tlab) {
    free(ctx->tlab);
    ctx->tlab = NULL;
    ctx->tlab_enabled = false;
  }
  
  valk_gc_global_pool_destroy();
  
  VALK_PASS();
}

void test_gc_tlab_alloc_slow_many(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_global_pool_init();
  
  valk_thread_context_t *ctx = &valk_thread_ctx;
  ctx->tlab = NULL;
  ctx->tlab_enabled = false;
  
  void *allocations[100];
  for (int i = 0; i < 100; i++) {
    allocations[i] = valk_gc_tlab_alloc_slow(sizeof(valk_lval_t));
    VALK_TEST_ASSERT(allocations[i] != NULL, "alloc %d should succeed", i);
  }
  
  for (int i = 0; i < 100; i++) {
    for (int j = i + 1; j < 100; j++) {
      VALK_TEST_ASSERT(allocations[i] != allocations[j], 
                       "allocations should be unique");
    }
  }
  
  u64 pages, total, used;
  valk_gc_page_pool_stats(&valk_gc_global_pool, &pages, &total, &used);
  VALK_TEST_ASSERT(pages > 0, "should have allocated pages");
  VALK_TEST_ASSERT(used >= 100, "should have 100+ slots used");
  
  if (ctx->tlab) {
    free(ctx->tlab);
    ctx->tlab = NULL;
    ctx->tlab_enabled = false;
  }
  
  valk_gc_global_pool_destroy();
  
  VALK_PASS();
}

void test_gc_tlab_alloc_slow_too_large(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_global_pool_init();
  
  void *ptr = valk_gc_tlab_alloc_slow(VALK_GC_SLOT_SIZE + 1);
  VALK_TEST_ASSERT(ptr == NULL, "alloc larger than slot size should fail");
  
  valk_gc_global_pool_destroy();
  
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_gc_coordinator_init", test_gc_coordinator_init);
  valk_testsuite_add_test(suite, "test_gc_atomic_mark_single", test_gc_atomic_mark_single);
  valk_testsuite_add_test(suite, "test_gc_atomic_mark_null", test_gc_atomic_mark_null);
  valk_testsuite_add_test(suite, "test_gc_atomic_mark_multithread", test_gc_atomic_mark_multithread);
  valk_testsuite_add_test(suite, "test_gc_barrier_basic", test_gc_barrier_basic);
  valk_testsuite_add_test(suite, "test_gc_barrier_multithread", test_gc_barrier_multithread);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_init", test_gc_mark_queue_init);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_push_pop", test_gc_mark_queue_push_pop);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_steal", test_gc_mark_queue_steal);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_full", test_gc_mark_queue_full);
  valk_testsuite_add_test(suite, "test_gc_thread_register_unregister", test_gc_thread_register_unregister);
  valk_testsuite_add_test(suite, "test_gc_global_roots_add_remove", test_gc_global_roots_add_remove);
  valk_testsuite_add_test(suite, "test_gc_safe_point_idle", test_gc_safe_point_idle);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_concurrent_steal", test_gc_mark_queue_concurrent_steal);
  valk_testsuite_add_test(suite, "test_gc_phase_transitions", test_gc_phase_transitions);
  valk_testsuite_add_test(suite, "test_gc_root_stack_init", test_gc_root_stack_init);
  
  valk_testsuite_add_test(suite, "test_gc_page_pool_init", test_gc_page_pool_init);
  valk_testsuite_add_test(suite, "test_gc_page_alloc", test_gc_page_alloc);
  valk_testsuite_add_test(suite, "test_gc_page_alloc_multiple", test_gc_page_alloc_multiple);
  valk_testsuite_add_test(suite, "test_gc_tlab_init", test_gc_tlab_init);
  valk_testsuite_add_test(suite, "test_gc_tlab_refill", test_gc_tlab_refill);
  valk_testsuite_add_test(suite, "test_gc_tlab_alloc_basic", test_gc_tlab_alloc_basic);
  valk_testsuite_add_test(suite, "test_gc_tlab_exhaust_and_refill", test_gc_tlab_exhaust_and_refill);
  valk_testsuite_add_test(suite, "test_gc_bitmap_operations", test_gc_bitmap_operations);
  valk_testsuite_add_test(suite, "test_gc_tlab_multithread", test_gc_tlab_multithread);
  valk_testsuite_add_test(suite, "test_gc_page_pool_stats", test_gc_page_pool_stats);
  
  valk_testsuite_add_test(suite, "test_gc_root_push_pop", test_gc_root_push_pop);
  valk_testsuite_add_test(suite, "test_gc_root_scoped", test_gc_root_scoped);
  valk_testsuite_add_test(suite, "test_gc_visit_thread_roots", test_gc_visit_thread_roots);
  valk_testsuite_add_test(suite, "test_gc_termination_check", test_gc_termination_check);
  valk_testsuite_add_test(suite, "test_gc_mark_linked_list", test_gc_mark_linked_list);
  valk_testsuite_add_test(suite, "test_gc_sweep_page_basic", test_gc_sweep_page_basic);
  valk_testsuite_add_test(suite, "test_gc_sweep_clears_marks", test_gc_sweep_clears_marks);
  
  valk_testsuite_add_test(suite, "test_gc_maybe_collect_below_threshold", test_gc_maybe_collect_below_threshold);
  valk_testsuite_add_test(suite, "test_gc_full_cycle_basic", test_gc_full_cycle_basic);
  valk_testsuite_add_test(suite, "test_gc_safe_point_with_stw", test_gc_safe_point_with_stw);
  
  valk_testsuite_add_test(suite, "test_gc_global_pool_init", test_gc_global_pool_init);
  valk_testsuite_add_test(suite, "test_gc_tlab_alloc_slow_basic", test_gc_tlab_alloc_slow_basic);
  valk_testsuite_add_test(suite, "test_gc_tlab_alloc_slow_many", test_gc_tlab_alloc_slow_many);
  valk_testsuite_add_test(suite, "test_gc_tlab_alloc_slow_too_large", test_gc_tlab_alloc_slow_too_large);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
