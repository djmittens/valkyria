#include "../testing.h"
#include "../../src/memory.h"

#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_ring_init_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t ring_size = valk_next_pow2(128);
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + ring_size);
  valk_ring_init(ring, ring_size);

  VALK_TEST_ASSERT(ring->capacity == ring_size, "Capacity should match");
  VALK_TEST_ASSERT(ring->offset == 0, "Initial offset should be 0");

  free(ring);

  VALK_PASS();
}

void test_ring_write_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t ring_size = valk_next_pow2(64);
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + ring_size);
  valk_ring_init(ring, ring_size);

  u8 data[] = "hello world";
  valk_ring_write(ring, data, sizeof(data) - 1);

  VALK_TEST_ASSERT(ring->offset == sizeof(data) - 1, "Offset should advance");

  free(ring);

  VALK_PASS();
}

void test_ring_write_wrap(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t ring_size = valk_next_pow2(32);
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + ring_size);
  valk_ring_init(ring, ring_size);

  u8 data[50];
  memset(data, 'A', sizeof(data));
  valk_ring_write(ring, data, sizeof(data));

  VALK_TEST_ASSERT(ring->offset == (sizeof(data) % ring_size), "Offset should wrap");

  free(ring);

  VALK_PASS();
}

void test_ring_rewind(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t ring_size = valk_next_pow2(64);
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + ring_size);
  valk_ring_init(ring, ring_size);

  u8 data[] = "0123456789";
  valk_ring_write(ring, data, 10);

  size_t before = ring->offset;
  valk_ring_rewind(ring, 5);
  size_t after = ring->offset;

  VALK_TEST_ASSERT(after == before - 5, "Offset should rewind by 5");

  free(ring);

  VALK_PASS();
}

void test_ring_rewind_wrap(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t ring_size = valk_next_pow2(32);
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + ring_size);
  valk_ring_init(ring, ring_size);

  ring->offset = 3;
  valk_ring_rewind(ring, 10);

  VALK_TEST_ASSERT(ring->offset == (ring_size + 3 - 10) % ring_size, "Offset should wrap on rewind");

  free(ring);

  VALK_PASS();
}

void test_ring_read(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t ring_size = valk_next_pow2(64);
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + ring_size);
  valk_ring_init(ring, ring_size);

  u8 write_data[] = "hello world";
  valk_ring_write(ring, write_data, 11);

  ring->offset = 0;

  u8 read_data[12] = {0};
  valk_ring_read(ring, 11, read_data);

  VALK_TEST_ASSERT(memcmp(read_data, write_data, 11) == 0, "Read data should match written");

  free(ring);

  VALK_PASS();
}

void test_slab_new_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 10);
  VALK_TEST_ASSERT(slab != nullptr, "Slab should be created");
  VALK_TEST_ASSERT(slab->type == VALK_ALLOC_SLAB, "Type should be SLAB");
  VALK_TEST_ASSERT(slab->itemSize == 64, "Item size should be 64");
  VALK_TEST_ASSERT(slab->numItems == 10, "Num items should be 10");
  VALK_TEST_ASSERT(valk_slab_available(slab) == 10, "All items should be free");

  valk_slab_free(slab);

  VALK_PASS();
}

void test_slab_acquire_release(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 5);

  valk_slab_item_t *item1 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item1 != nullptr, "Should acquire first item");
  VALK_TEST_ASSERT(valk_slab_available(slab) == 4, "Should have 4 free");

  valk_slab_item_t *item2 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item2 != nullptr, "Should acquire second item");
  VALK_TEST_ASSERT(valk_slab_available(slab) == 3, "Should have 3 free");

  valk_slab_release(slab, item1);
  VALK_TEST_ASSERT(valk_slab_available(slab) == 4, "Should have 4 free after release");

  valk_slab_release(slab, item2);
  VALK_TEST_ASSERT(valk_slab_available(slab) == 5, "Should have 5 free after release");

  valk_slab_free(slab);

  VALK_PASS();
}

void test_slab_exhaustion(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 3);

  valk_slab_item_t *items[3];
  for (int i = 0; i < 3; i++) {
    items[i] = valk_slab_aquire(slab);
    VALK_TEST_ASSERT(items[i] != nullptr, "Should acquire item %d", i);
  }

  valk_slab_item_t *overflow = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(overflow == nullptr, "Should return nullptr when exhausted");

  VALK_TEST_ASSERT(slab->overflowCount >= 1, "Overflow count should increment");

  for (int i = 0; i < 3; i++) {
    valk_slab_release(slab, items[i]);
  }

  valk_slab_free(slab);

  VALK_PASS();
}

void test_slab_peak_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 10);

  valk_slab_item_t *items[5];
  for (int i = 0; i < 5; i++) {
    items[i] = valk_slab_aquire(slab);
  }

  VALK_TEST_ASSERT(slab->peakUsed >= 5, "Peak should be at least 5");

  for (int i = 0; i < 5; i++) {
    valk_slab_release(slab, items[i]);
  }

  VALK_TEST_ASSERT(slab->peakUsed >= 5, "Peak should remain at 5 after release");

  valk_slab_free(slab);

  VALK_PASS();
}

void test_slab_item_stride(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t stride = valk_slab_item_stride(64);
  VALK_TEST_ASSERT(stride >= 64 + sizeof(valk_slab_item_t), "Stride should include header");
  VALK_TEST_ASSERT((stride % 64) == 0, "Stride should be 64-byte aligned");

  VALK_PASS();
}

void test_slab_size_calculation(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t size = valk_slab_size(64, 10);
  VALK_TEST_ASSERT(size > sizeof(valk_slab_t), "Size should be larger than header");

  size_t stride = valk_slab_item_stride(64);
  VALK_TEST_ASSERT(size >= sizeof(valk_slab_t) + (stride * 10), "Size should fit all items");

  VALK_PASS();
}

void test_arena_init_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);

  VALK_TEST_ASSERT(arena->type == VALK_ALLOC_ARENA, "Type should be ARENA");
  VALK_TEST_ASSERT(arena->capacity == 4096, "Capacity should be 4096");
  VALK_TEST_ASSERT(arena->stats.total_allocations == 0, "Initial allocations should be 0");

  free(arena);

  VALK_PASS();
}

void test_arena_alloc_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);

  valk_thread_ctx.heap = nullptr;

  void *ptr = valk_mem_arena_alloc(arena, 100);
  VALK_TEST_ASSERT(ptr != nullptr, "Should allocate from arena");
  VALK_TEST_ASSERT(arena->stats.total_allocations == 1, "Should count allocation");
  VALK_TEST_ASSERT(arena->offset > 0, "Offset should advance");

  free(arena);

  VALK_PASS();
}

void test_arena_reset(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);

  valk_mem_arena_alloc(arena, 100);
  valk_mem_arena_alloc(arena, 200);

  size_t before_reset = arena->offset;
  VALK_TEST_ASSERT(before_reset > 0, "Offset should be positive before reset");

  valk_mem_arena_reset(arena);
  VALK_TEST_ASSERT(arena->offset == 0, "Offset should be 0 after reset");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.num_resets) == 1, "Reset count should increment");

  free(arena);

  VALK_PASS();
}

void test_arena_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);

  valk_mem_arena_alloc(arena, 100);
  valk_mem_arena_alloc(arena, 200);
  valk_mem_arena_alloc(arena, 300);

  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_allocations) == 3, "Should count 3 allocations");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_bytes_allocated) >= 600, "Should count at least 600 bytes");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.high_water_mark) > 0, "High water mark should be set");

  free(arena);

  VALK_PASS();
}

void test_arena_reset_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);

  valk_mem_arena_alloc(arena, 100);
  valk_mem_arena_reset(arena);

  size_t hwm_before = atomic_load(&arena->stats.high_water_mark);

  valk_mem_arena_reset_stats(arena);

  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_allocations) == 0, "Allocations should be reset");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.num_resets) == 0, "Resets should be reset");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.high_water_mark) == hwm_before, "HWM should NOT be reset");

  free(arena);

  VALK_PASS();
}

void test_ptr_in_arena(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);

  void *ptr = valk_mem_arena_alloc(arena, 100);

  VALK_TEST_ASSERT(valk_ptr_in_arena(arena, ptr) == true, "Arena ptr should be in arena");

  int external_var = 42;
  VALK_TEST_ASSERT(valk_ptr_in_arena(arena, &external_var) == false, "Stack ptr should not be in arena");

  void *heap_ptr = malloc(100);
  VALK_TEST_ASSERT(valk_ptr_in_arena(arena, heap_ptr) == false, "Heap ptr should not be in arena");
  free(heap_ptr);

  free(arena);

  VALK_PASS();
}

void test_ptr_in_arena_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_ptr_in_arena(nullptr, nullptr) == false, "nullptr arena should return false");

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);

  VALK_TEST_ASSERT(valk_ptr_in_arena(arena, nullptr) == false, "nullptr ptr should return false");

  free(arena);

  VALK_PASS();
}

void test_buffer_alloc_append(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_buffer_t buf;
  valk_buffer_alloc(&buf, 1024);

  VALK_TEST_ASSERT(buf.capacity == 1024, "Capacity should be 1024");
  VALK_TEST_ASSERT(buf.count == 0, "Initial count should be 0");
  VALK_TEST_ASSERT(buf.items != nullptr, "Items should be allocated");

  char data[] = "hello";
  valk_buffer_append(&buf, data, 5);
  VALK_TEST_ASSERT(buf.count == 5, "Count should be 5");

  valk_buffer_append(&buf, data, 5);
  VALK_TEST_ASSERT(buf.count == 10, "Count should be 10");

  valk_mem_free(buf.items);

  VALK_PASS();
}

void test_buffer_is_full(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_buffer_t buf;
  valk_buffer_alloc(&buf, 100);

  VALK_TEST_ASSERT(valk_buffer_is_full(&buf) == 0, "Empty buffer should not be full");

  buf.count = buf.capacity;
  VALK_TEST_ASSERT(valk_buffer_is_full(&buf) == 1, "Full buffer should be full");

  valk_mem_free(buf.items);

  VALK_PASS();
}

void test_next_pow2(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_next_pow2(0) == 1, "0 -> 1");
  VALK_TEST_ASSERT(valk_next_pow2(1) == 1, "1 -> 1");
  VALK_TEST_ASSERT(valk_next_pow2(2) == 2, "2 -> 2");
  VALK_TEST_ASSERT(valk_next_pow2(3) == 4, "3 -> 4");
  VALK_TEST_ASSERT(valk_next_pow2(5) == 8, "5 -> 8");
  VALK_TEST_ASSERT(valk_next_pow2(17) == 32, "17 -> 32");
  VALK_TEST_ASSERT(valk_next_pow2(1023) == 1024, "1023 -> 1024");
  VALK_TEST_ASSERT(valk_next_pow2(1024) == 1024, "1024 -> 1024");
  VALK_TEST_ASSERT(valk_next_pow2(1025) == 2048, "1025 -> 2048");

  VALK_PASS();
}

void test_allocator_type_to_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(strcmp(valk_mem_allocator_e_to_string(VALK_ALLOC_NULL), "nullptr Alloc") == 0, "nullptr");
  VALK_TEST_ASSERT(strcmp(valk_mem_allocator_e_to_string(VALK_ALLOC_MALLOC), "Malloc Alloc") == 0, "MALLOC");
  VALK_TEST_ASSERT(strcmp(valk_mem_allocator_e_to_string(VALK_ALLOC_ARENA), "Arena Alloc") == 0, "ARENA");
  VALK_TEST_ASSERT(strcmp(valk_mem_allocator_e_to_string(VALK_ALLOC_SLAB), "Slab Alloc") == 0, "SLAB");
  VALK_TEST_ASSERT(strcmp(valk_mem_allocator_e_to_string(VALK_ALLOC_GC_HEAP), "GC Heap Alloc") == 0, "GC_HEAP");

  VALK_PASS();
}

void test_process_memory_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_process_memory_t pm;
  valk_process_memory_collect(&pm);

  VALK_TEST_ASSERT(pm.rss_bytes > 0, "RSS should be positive");
  VALK_TEST_ASSERT(pm.vms_bytes >= pm.rss_bytes, "VMS should be >= RSS");
  VALK_TEST_ASSERT(pm.system_total_bytes > 0, "System total should be positive");

  VALK_PASS();
}

void test_process_memory_collect_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_process_memory_collect(nullptr);

  VALK_PASS();
}

void test_smaps_collect_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_smaps_collect(nullptr);

  VALK_PASS();
}

void test_smaps_collect_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_smaps_breakdown_t smaps;
  valk_smaps_collect(&smaps);

  VALK_PASS();
}

void test_arena_print_stats_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_print_stats(nullptr, stdout);
  valk_mem_arena_print_stats(nullptr, nullptr);

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);
  valk_mem_arena_print_stats(arena, nullptr);
  free(arena);

  VALK_PASS();
}

void test_slab_release_ptr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 5);

  valk_slab_item_t *item = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(valk_slab_available(slab) == 4, "Should have 4 free");

  valk_slab_release_ptr(slab, item->data);
  VALK_TEST_ASSERT(valk_slab_available(slab) == 5, "Should have 5 free after release_ptr");

  valk_slab_free(slab);

  VALK_PASS();
}

static valk_slab_t *concurrent_slab = nullptr;
static _Atomic int concurrent_errors = 0;

static void *concurrent_slab_thread(void *arg) {
  int id = *(int *)arg;
  (void)id;

  for (int i = 0; i < 1000; i++) {
    valk_slab_item_t *item = valk_slab_aquire(concurrent_slab);
    if (item) {
      memset(item->data, 0xAB, 64);
      valk_slab_release(concurrent_slab, item);
    }
  }
  return nullptr;
}

void test_slab_concurrent(VALK_TEST_ARGS()) {
  VALK_TEST();

  concurrent_slab = valk_slab_new(64, 20);
  atomic_store(&concurrent_errors, 0);

  pthread_t threads[4];
  int thread_ids[4] = {0, 1, 2, 3};

  for (int i = 0; i < 4; i++) {
    pthread_create(&threads[i], nullptr, concurrent_slab_thread, &thread_ids[i]);
  }

  for (int i = 0; i < 4; i++) {
    pthread_join(threads[i], nullptr);
  }

  VALK_TEST_ASSERT(valk_slab_available(concurrent_slab) == 20, "All items should be returned");

  valk_slab_free(concurrent_slab);
  concurrent_slab = nullptr;

  VALK_PASS();
}

void test_allocator_malloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *ptr = valk_mem_allocator_alloc(&valk_malloc_allocator, 1024);
  VALK_TEST_ASSERT(ptr != nullptr, "Should allocate via malloc");

  memset(ptr, 0xCD, 1024);

  ptr = valk_mem_allocator_realloc(&valk_malloc_allocator, ptr, 2048);
  VALK_TEST_ASSERT(ptr != nullptr, "Should realloc via malloc");

  valk_mem_allocator_free(&valk_malloc_allocator, ptr);

  VALK_PASS();
}

void test_allocator_malloc_calloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *ptr = valk_mem_allocator_calloc(&valk_malloc_allocator, 10, 100);
  VALK_TEST_ASSERT(ptr != nullptr, "Should calloc via malloc");

  char *bytes = (char *)ptr;
  for (int i = 0; i < 1000; i++) {
    VALK_TEST_ASSERT(bytes[i] == 0, "Calloc should zero memory");
  }

  valk_mem_allocator_free(&valk_malloc_allocator, ptr);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_ring_init_basic", test_ring_init_basic);
  valk_testsuite_add_test(suite, "test_ring_write_basic", test_ring_write_basic);
  valk_testsuite_add_test(suite, "test_ring_write_wrap", test_ring_write_wrap);
  valk_testsuite_add_test(suite, "test_ring_rewind", test_ring_rewind);
  valk_testsuite_add_test(suite, "test_ring_rewind_wrap", test_ring_rewind_wrap);
  valk_testsuite_add_test(suite, "test_ring_read", test_ring_read);
  valk_testsuite_add_test(suite, "test_slab_new_basic", test_slab_new_basic);
  valk_testsuite_add_test(suite, "test_slab_acquire_release", test_slab_acquire_release);
  valk_testsuite_add_test(suite, "test_slab_exhaustion", test_slab_exhaustion);
  valk_testsuite_add_test(suite, "test_slab_peak_tracking", test_slab_peak_tracking);
  valk_testsuite_add_test(suite, "test_slab_item_stride", test_slab_item_stride);
  valk_testsuite_add_test(suite, "test_slab_size_calculation", test_slab_size_calculation);
  valk_testsuite_add_test(suite, "test_arena_init_basic", test_arena_init_basic);
  valk_testsuite_add_test(suite, "test_arena_alloc_basic", test_arena_alloc_basic);
  valk_testsuite_add_test(suite, "test_arena_reset", test_arena_reset);
  valk_testsuite_add_test(suite, "test_arena_stats", test_arena_stats);
  valk_testsuite_add_test(suite, "test_arena_reset_stats", test_arena_reset_stats);
  valk_testsuite_add_test(suite, "test_ptr_in_arena", test_ptr_in_arena);
  valk_testsuite_add_test(suite, "test_ptr_in_arena_null", test_ptr_in_arena_null);
  valk_testsuite_add_test(suite, "test_buffer_alloc_append", test_buffer_alloc_append);
  valk_testsuite_add_test(suite, "test_buffer_is_full", test_buffer_is_full);
  valk_testsuite_add_test(suite, "test_next_pow2", test_next_pow2);
  valk_testsuite_add_test(suite, "test_allocator_type_to_string", test_allocator_type_to_string);
  valk_testsuite_add_test(suite, "test_process_memory_collect", test_process_memory_collect);
  valk_testsuite_add_test(suite, "test_process_memory_collect_null", test_process_memory_collect_null);
  valk_testsuite_add_test(suite, "test_smaps_collect_null", test_smaps_collect_null);
  valk_testsuite_add_test(suite, "test_smaps_collect_basic", test_smaps_collect_basic);
  valk_testsuite_add_test(suite, "test_arena_print_stats_null", test_arena_print_stats_null);
  valk_testsuite_add_test(suite, "test_slab_release_ptr", test_slab_release_ptr);
  valk_testsuite_add_test(suite, "test_slab_concurrent", test_slab_concurrent);
  valk_testsuite_add_test(suite, "test_allocator_malloc", test_allocator_malloc);
  valk_testsuite_add_test(suite, "test_allocator_malloc_calloc", test_allocator_malloc_calloc);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
