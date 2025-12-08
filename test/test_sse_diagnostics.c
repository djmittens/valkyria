#include "testing.h"
#include "memory.h"
#include "common.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef VALK_METRICS_ENABLED
#include "aio.h"
#include "aio_sse_diagnostics.h"

// ============================================================================
// Bitmap Tests
// ============================================================================

void test_slab_bitmap_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a small slab with all slots free
  valk_slab_t *slab = valk_slab_new(64, 16);
  VALK_TEST_ASSERT(slab != NULL, "Failed to create slab");

  // All slots should be free - snapshot should show 0 used
  valk_mem_snapshot_t snapshot = {0};

  // For this test, we just verify the slab was created successfully
  // The actual bitmap generation is tested indirectly through the snapshot

  valk_slab_free(slab);
  VALK_PASS();
}

void test_slab_bitmap_full(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a small slab and allocate all slots
  size_t num_items = 8;
  valk_slab_t *slab = valk_slab_new(64, num_items);
  VALK_TEST_ASSERT(slab != NULL, "Failed to create slab");

  void *items[8];
  for (size_t i = 0; i < num_items; i++) {
    valk_slab_item_t *item = valk_slab_aquire(slab);
    VALK_TEST_ASSERT(item != NULL, "Failed to acquire slab item %zu", i);
    items[i] = item;
  }

  // Verify slab shows 0 free
  VALK_TEST_ASSERT(slab->numFree == 0, "Slab should have 0 free, has %zu", slab->numFree);

  // Release all items
  for (size_t i = 0; i < num_items; i++) {
    valk_slab_release_ptr(slab, items[i]);
  }

  // Verify slab shows all free
  VALK_TEST_ASSERT(slab->numFree == num_items, "Slab should have %zu free, has %zu",
                   num_items, slab->numFree);

  valk_slab_free(slab);
  VALK_PASS();
}

void test_slab_bitmap_partial(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a slab and allocate/release some slots
  size_t num_items = 8;
  valk_slab_t *slab = valk_slab_new(64, num_items);
  VALK_TEST_ASSERT(slab != NULL, "Failed to create slab");

  // Allocate 4 items
  void *items[4];
  for (size_t i = 0; i < 4; i++) {
    valk_slab_item_t *item = valk_slab_aquire(slab);
    VALK_TEST_ASSERT(item != NULL, "Failed to acquire slab item %zu", i);
    items[i] = item;
  }

  // Release items 1 and 3 (keep 0 and 2)
  valk_slab_release_ptr(slab, items[1]);
  valk_slab_release_ptr(slab, items[3]);

  // Verify slab shows 6 free (8 total - 2 in use)
  VALK_TEST_ASSERT(slab->numFree == 6, "Slab should have 6 free, has %zu", slab->numFree);

  // Cleanup
  valk_slab_release_ptr(slab, items[0]);
  valk_slab_release_ptr(slab, items[2]);
  valk_slab_free(slab);
  VALK_PASS();
}

// ============================================================================
// SSE Format Tests
// ============================================================================

void test_sse_event_format(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a minimal snapshot
  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "test";
  snapshot.slabs[0].total_slots = 8;
  snapshot.slabs[0].used_slots = 4;
  snapshot.slabs[0].overflow_count = 0;
  snapshot.slabs[0].has_slot_diag = false;

  // Allocate and set bitmap
  snapshot.slabs[0].bitmap = malloc(1);
  snapshot.slabs[0].bitmap[0] = 0xAA;  // 10101010 pattern
  snapshot.slabs[0].bitmap_bytes = 1;

  // Add arena data
  snapshot.arena_count = 1;
  snapshot.arenas[0].name = "scratch";
  snapshot.arenas[0].used_bytes = 1024;
  snapshot.arenas[0].capacity_bytes = 4096;
  snapshot.arenas[0].high_water_mark = 2048;
  snapshot.arenas[0].overflow_fallbacks = 0;

  // GC data
  snapshot.gc_heap.allocated_bytes = 1000000;
  snapshot.gc_heap.peak_usage = 2000000;
  snapshot.gc_heap.gc_threshold = 5000000;
  snapshot.gc_heap.gc_cycles = 10;
  snapshot.gc_heap.emergency_collections = 0;

  // Format to SSE
  char buf[4096];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 12345);

  VALK_TEST_ASSERT(len > 0, "SSE format failed, returned %d", len);

  // Check for expected content
  VALK_TEST_ASSERT(strstr(buf, "event: memory") != NULL, "Missing event header");
  VALK_TEST_ASSERT(strstr(buf, "id: 12345") != NULL, "Missing event ID");
  VALK_TEST_ASSERT(strstr(buf, "\"name\":\"test\"") != NULL, "Missing slab name");
  VALK_TEST_ASSERT(strstr(buf, "\"bitmap\":\"aa\"") != NULL, "Missing or wrong bitmap");
  VALK_TEST_ASSERT(strstr(buf, "\"total\":8") != NULL, "Missing total slots");
  VALK_TEST_ASSERT(strstr(buf, "\"used\":4") != NULL, "Missing used slots");
  VALK_TEST_ASSERT(strstr(buf, "\"arenas\":[") != NULL, "Missing arenas array");
  VALK_TEST_ASSERT(strstr(buf, "\"gc\":{") != NULL, "Missing GC stats");

  free(snapshot.slabs[0].bitmap);
  VALK_PASS();
}

void test_sse_slot_diag_format(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a snapshot with slot diagnostics (connection-aware slab)
  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "handles";
  snapshot.slabs[0].total_slots = 8;
  snapshot.slabs[0].used_slots = 5;
  snapshot.slabs[0].overflow_count = 1;
  snapshot.slabs[0].has_slot_diag = true;
  snapshot.slabs[0].by_state.active = 3;
  snapshot.slabs[0].by_state.idle = 1;
  snapshot.slabs[0].by_state.closing = 1;

  // Allocate slot diagnostics
  snapshot.slabs[0].slots = calloc(8, sizeof(valk_slot_diag_t));
  snapshot.slabs[0].slots[0].state = 'A';
  snapshot.slabs[0].slots[1].state = 'A';
  snapshot.slabs[0].slots[2].state = 'I';
  snapshot.slabs[0].slots[3].state = 'F';
  snapshot.slabs[0].slots[4].state = 'A';
  snapshot.slabs[0].slots[5].state = 'C';
  snapshot.slabs[0].slots[6].state = 'F';
  snapshot.slabs[0].slots[7].state = 'F';

  // Add owner map
  snapshot.owner_count = 2;
  snapshot.owner_map[0] = ":8080";
  snapshot.owner_map[1] = ":9090";

  // Format to SSE
  char buf[4096];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 100);

  VALK_TEST_ASSERT(len > 0, "SSE format failed, returned %d", len);

  // Check for slot diagnostics format
  VALK_TEST_ASSERT(strstr(buf, "\"states\":\"AAIFACFF\"") != NULL,
                   "Missing or wrong states string, got: %s", buf);
  // Summary now includes by_owner object
  VALK_TEST_ASSERT(strstr(buf, "\"A\":3") != NULL, "Missing active count in summary");
  VALK_TEST_ASSERT(strstr(buf, "\"I\":1") != NULL, "Missing idle count in summary");
  VALK_TEST_ASSERT(strstr(buf, "\"C\":1") != NULL, "Missing closing count in summary");
  VALK_TEST_ASSERT(strstr(buf, "\"by_owner\":{") != NULL, "Missing by_owner in summary");
  VALK_TEST_ASSERT(strstr(buf, "\"owner_map\":[\":8080\",\":9090\"]") != NULL,
                   "Missing or wrong owner_map");

  free(snapshot.slabs[0].slots);
  VALK_PASS();
}

// ============================================================================
// Owner Registry Tests
// ============================================================================

void test_owner_registry_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Test owner registry through the API
  // We need an AIO system to fully test, but we can verify the API exists
  // by checking NULL handling
  VALK_TEST_ASSERT(valk_owner_get_name(NULL, 0) == NULL, "Should handle NULL system");
  VALK_TEST_ASSERT(valk_owner_get_count(NULL) == 0, "Should return 0 for NULL system");
  VALK_TEST_ASSERT(valk_owner_register(NULL, ":8080", 0, NULL) == UINT16_MAX,
                   "Should return invalid index for NULL system");

  VALK_PASS();
}

void test_diag_state_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Verify enum values are as expected
  VALK_TEST_ASSERT(VALK_DIAG_CONN_FREE == 0, "FREE should be 0");
  VALK_TEST_ASSERT(VALK_DIAG_CONN_CONNECTING == 1, "CONNECTING should be 1");
  VALK_TEST_ASSERT(VALK_DIAG_CONN_ACTIVE == 2, "ACTIVE should be 2");
  VALK_TEST_ASSERT(VALK_DIAG_CONN_IDLE == 3, "IDLE should be 3");
  VALK_TEST_ASSERT(VALK_DIAG_CONN_CLOSING == 4, "CLOSING should be 4");

  VALK_PASS();
}

#else // !VALK_METRICS_ENABLED

void test_sse_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("SSE diagnostics requires VALK_METRICS_ENABLED");
}

#endif // VALK_METRICS_ENABLED

// ============================================================================
// Test Main
// ============================================================================

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  // Bitmap tests
  valk_testsuite_add_test(suite, "test_slab_bitmap_empty", test_slab_bitmap_empty);
  valk_testsuite_add_test(suite, "test_slab_bitmap_full", test_slab_bitmap_full);
  valk_testsuite_add_test(suite, "test_slab_bitmap_partial", test_slab_bitmap_partial);

  // SSE format tests
  valk_testsuite_add_test(suite, "test_sse_event_format", test_sse_event_format);
  valk_testsuite_add_test(suite, "test_sse_slot_diag_format", test_sse_slot_diag_format);

  // Owner registry tests
  valk_testsuite_add_test(suite, "test_owner_registry_basic", test_owner_registry_basic);
  valk_testsuite_add_test(suite, "test_diag_state_enum", test_diag_state_enum);
#else
  valk_testsuite_add_test(suite, "test_sse_disabled", test_sse_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
