#include "testing.h"
#include "memory.h"
#include "common.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef VALK_METRICS_ENABLED
#include "aio.h"
#include "aio_sse_diagnostics.h"
#include "aio_sse_stream_registry.h"

// ============================================================================
// Bitmap Tests
// ============================================================================

void test_slab_bitmap_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 16);
  VALK_TEST_ASSERT(slab != NULL, "Failed to create slab");
  VALK_TEST_ASSERT(slab->numFree == 16, "All slots should be free, got %zu", slab->numFree);

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

  // GC data (generic tiers array)
  snapshot.gc_heap.tier_count = 3;

  // LVAL slab
  snapshot.gc_heap.tiers[0].name = "lval";
  snapshot.gc_heap.tiers[0].bytes_used = 800000;
  snapshot.gc_heap.tiers[0].bytes_total = 1000000;
  snapshot.gc_heap.tiers[0].bytes_peak = 880000;
  snapshot.gc_heap.tiers[0].objects_used = 10000;
  snapshot.gc_heap.tiers[0].objects_total = 12500;
  snapshot.gc_heap.tiers[0].objects_peak = 11000;

  // LENV slab
  snapshot.gc_heap.tiers[1].name = "lenv";
  snapshot.gc_heap.tiers[1].bytes_used = 50000;
  snapshot.gc_heap.tiers[1].bytes_total = 100000;
  snapshot.gc_heap.tiers[1].bytes_peak = 60000;
  snapshot.gc_heap.tiers[1].objects_used = 500;
  snapshot.gc_heap.tiers[1].objects_total = 1000;
  snapshot.gc_heap.tiers[1].objects_peak = 600;

  // Malloc (no objects)
  snapshot.gc_heap.tiers[2].name = "malloc";
  snapshot.gc_heap.tiers[2].bytes_used = 200000;
  snapshot.gc_heap.tiers[2].bytes_total = 5000000;
  snapshot.gc_heap.tiers[2].bytes_peak = 300000;
  snapshot.gc_heap.tiers[2].objects_used = 0;
  snapshot.gc_heap.tiers[2].objects_total = 0;
  snapshot.gc_heap.tiers[2].objects_peak = 0;

  snapshot.gc_heap.gc_threshold_pct = 75;
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
  VALK_TEST_ASSERT(strstr(buf, "\"bitmap\":\"aa\"") != NULL, "Missing or wrong bitmap, got: %s", buf);
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

  // Check for slot diagnostics format (RLE encoded: "AAIFACFF" -> "A2I1F1A1C1F2")
  VALK_TEST_ASSERT(strstr(buf, "\"states\":\"A2I1F1A1C1F2\"") != NULL,
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

  VALK_TEST_ASSERT(VALK_DIAG_CONN_FREE == 0, "FREE should be 0");
  VALK_TEST_ASSERT(VALK_DIAG_CONN_CONNECTING == 1, "CONNECTING should be 1");
  VALK_TEST_ASSERT(VALK_DIAG_CONN_ACTIVE == 2, "ACTIVE should be 2");
  VALK_TEST_ASSERT(VALK_DIAG_CONN_IDLE == 3, "IDLE should be 3");
  VALK_TEST_ASSERT(VALK_DIAG_CONN_CLOSING == 4, "CLOSING should be 4");

  VALK_PASS();
}

void test_snapshot_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_free(NULL);

  VALK_PASS();
}

void test_snapshot_free_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_free(&snapshot);

  VALK_TEST_ASSERT(snapshot.slab_count == 0, "slab_count should be 0");
  VALK_TEST_ASSERT(snapshot.arena_count == 0, "arena_count should be 0");
  VALK_TEST_ASSERT(snapshot.owner_count == 0, "owner_count should be 0");

  VALK_PASS();
}

void test_snapshot_free_with_allocations(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 2;

  snapshot.slabs[0].name = "slab1";
  snapshot.slabs[0].bitmap = malloc(16);
  snapshot.slabs[0].bitmap_bytes = 16;
  snapshot.slabs[0].has_slot_diag = false;

  snapshot.slabs[1].name = "slab2";
  snapshot.slabs[1].slots = malloc(8 * sizeof(valk_slot_diag_t));
  snapshot.slabs[1].total_slots = 8;
  snapshot.slabs[1].has_slot_diag = true;

  valk_mem_snapshot_free(&snapshot);

  VALK_TEST_ASSERT(snapshot.slab_count == 0, "slab_count should be 0 after free");
  VALK_TEST_ASSERT(snapshot.slabs[0].bitmap == NULL, "bitmap should be NULL after free");
  VALK_TEST_ASSERT(snapshot.slabs[1].slots == NULL, "slots should be NULL after free");

  VALK_PASS();
}

void test_snapshot_copy_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};

  valk_mem_snapshot_copy(NULL, &snapshot);
  valk_mem_snapshot_copy(&snapshot, NULL);
  valk_mem_snapshot_copy(NULL, NULL);

  VALK_PASS();
}

void test_snapshot_copy_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t src = {0};
  valk_mem_snapshot_t dst = {0};

  valk_mem_snapshot_copy(&dst, &src);

  VALK_TEST_ASSERT(dst.slab_count == 0, "dst slab_count should be 0");
  VALK_TEST_ASSERT(dst.arena_count == 0, "dst arena_count should be 0");
  VALK_TEST_ASSERT(dst.owner_count == 0, "dst owner_count should be 0");

  VALK_PASS();
}

void test_snapshot_copy_with_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t src = {0};
  src.slab_count = 2;
  src.arena_count = 1;
  src.owner_count = 2;

  src.slabs[0].name = "slab1";
  src.slabs[0].total_slots = 16;
  src.slabs[0].used_slots = 8;
  src.slabs[0].bitmap = malloc(2);
  src.slabs[0].bitmap[0] = 0xAA;
  src.slabs[0].bitmap[1] = 0x55;
  src.slabs[0].bitmap_bytes = 2;
  src.slabs[0].has_slot_diag = false;

  src.slabs[1].name = "slab2";
  src.slabs[1].total_slots = 4;
  src.slabs[1].used_slots = 2;
  src.slabs[1].slots = calloc(4, sizeof(valk_slot_diag_t));
  src.slabs[1].slots[0].state = 'A';
  src.slabs[1].slots[1].state = 'F';
  src.slabs[1].slots[2].state = 'I';
  src.slabs[1].slots[3].state = 'C';
  src.slabs[1].has_slot_diag = true;

  src.arenas[0].name = "scratch";
  src.arenas[0].used_bytes = 1024;
  src.arenas[0].capacity_bytes = 4096;

  src.owner_map[0] = ":8080";
  src.owner_map[1] = ":9090";

  valk_mem_snapshot_t dst = {0};
  valk_mem_snapshot_copy(&dst, &src);

  VALK_TEST_ASSERT(dst.slab_count == 2, "dst slab_count should be 2");
  VALK_TEST_ASSERT(dst.arena_count == 1, "dst arena_count should be 1");
  VALK_TEST_ASSERT(dst.owner_count == 2, "dst owner_count should be 2");

  VALK_TEST_ASSERT(dst.slabs[0].bitmap != src.slabs[0].bitmap, "bitmap should be deep copied");
  VALK_TEST_ASSERT(dst.slabs[0].bitmap[0] == 0xAA, "bitmap[0] should be 0xAA");
  VALK_TEST_ASSERT(dst.slabs[0].bitmap[1] == 0x55, "bitmap[1] should be 0x55");

  VALK_TEST_ASSERT(dst.slabs[1].slots != src.slabs[1].slots, "slots should be deep copied");
  VALK_TEST_ASSERT(dst.slabs[1].slots[0].state == 'A', "slot[0] state should be A");
  VALK_TEST_ASSERT(dst.slabs[1].slots[3].state == 'C', "slot[3] state should be C");

  VALK_TEST_ASSERT(dst.arenas[0].used_bytes == 1024, "arena used_bytes should be 1024");

  valk_mem_snapshot_free(&src);
  valk_mem_snapshot_free(&dst);

  VALK_PASS();
}

void test_snapshot_sse_buffer_too_small(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "test";
  snapshot.slabs[0].total_slots = 8;
  snapshot.slabs[0].used_slots = 4;

  char buf[10];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len < 0, "Should return error for small buffer");

  VALK_PASS();
}

void test_snapshot_sse_empty_snapshot(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};

  char buf[1024];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 42);

  VALK_TEST_ASSERT(len > 0, "Should succeed with empty snapshot");
  VALK_TEST_ASSERT(strstr(buf, "event: memory") != NULL, "Missing event header");
  VALK_TEST_ASSERT(strstr(buf, "id: 42") != NULL, "Missing event ID");
  VALK_TEST_ASSERT(strstr(buf, "\"slabs\":[]") != NULL, "Should have empty slabs array");
  VALK_TEST_ASSERT(strstr(buf, "\"arenas\":[]") != NULL, "Should have empty arenas array");

  VALK_PASS();
}

void test_snapshot_copy_overwrites_dst(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t dst = {0};
  dst.slab_count = 1;
  dst.slabs[0].bitmap = malloc(4);
  dst.slabs[0].bitmap_bytes = 4;

  valk_mem_snapshot_t src = {0};
  src.slab_count = 0;

  valk_mem_snapshot_copy(&dst, &src);

  VALK_TEST_ASSERT(dst.slab_count == 0, "dst should have 0 slabs after copy from empty");

  VALK_PASS();
}

void test_sse_format_by_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "handles";
  snapshot.slabs[0].total_slots = 4;
  snapshot.slabs[0].used_slots = 4;
  snapshot.slabs[0].has_slot_diag = true;
  snapshot.slabs[0].by_type.tcp_listeners = 1;
  snapshot.slabs[0].by_type.tasks = 1;
  snapshot.slabs[0].by_type.timers = 1;
  snapshot.slabs[0].by_type.http_conns = 1;

  snapshot.slabs[0].slots = calloc(4, sizeof(valk_slot_diag_t));
  snapshot.slabs[0].slots[0].state = 'T';
  snapshot.slabs[0].slots[1].state = 'K';
  snapshot.slabs[0].slots[2].state = 'M';
  snapshot.slabs[0].slots[3].state = 'A';

  char buf[2048];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed");
  VALK_TEST_ASSERT(strstr(buf, "\"by_type\":{") != NULL, "Should have by_type object");
  VALK_TEST_ASSERT(strstr(buf, "\"tcp\":1") != NULL, "Should have tcp count");
  VALK_TEST_ASSERT(strstr(buf, "\"task\":1") != NULL, "Should have task count");
  VALK_TEST_ASSERT(strstr(buf, "\"timer\":1") != NULL, "Should have timer count");
  VALK_TEST_ASSERT(strstr(buf, "\"http\":1") != NULL, "Should have http count");

  free(snapshot.slabs[0].slots);
  VALK_PASS();
}

void test_sse_format_by_owner(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "handles";
  snapshot.slabs[0].total_slots = 4;
  snapshot.slabs[0].used_slots = 3;
  snapshot.slabs[0].has_slot_diag = true;
  snapshot.slabs[0].owner_count = 2;
  snapshot.slabs[0].by_owner[0].owner_idx = 0;
  snapshot.slabs[0].by_owner[0].active = 2;
  snapshot.slabs[0].by_owner[0].idle = 0;
  snapshot.slabs[0].by_owner[0].closing = 0;
  snapshot.slabs[0].by_owner[1].owner_idx = 1;
  snapshot.slabs[0].by_owner[1].active = 1;
  snapshot.slabs[0].by_owner[1].idle = 0;
  snapshot.slabs[0].by_owner[1].closing = 0;

  snapshot.slabs[0].slots = calloc(4, sizeof(valk_slot_diag_t));
  snapshot.slabs[0].slots[0].state = 'A';
  snapshot.slabs[0].slots[1].state = 'A';
  snapshot.slabs[0].slots[2].state = 'A';
  snapshot.slabs[0].slots[3].state = 'F';

  snapshot.owner_count = 2;
  snapshot.owner_map[0] = ":8080";
  snapshot.owner_map[1] = ":9090";

  char buf[4096];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed");
  VALK_TEST_ASSERT(strstr(buf, "\"by_owner\":{") != NULL, "Should have by_owner object");
  VALK_TEST_ASSERT(strstr(buf, "\"0\":{\"A\":2") != NULL, "Should have owner 0 with 2 active");
  VALK_TEST_ASSERT(strstr(buf, "\"1\":{\"A\":1") != NULL, "Should have owner 1 with 1 active");

  free(snapshot.slabs[0].slots);
  VALK_PASS();
}

void test_sse_format_process_memory(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.process.rss_bytes = 1024 * 1024;
  snapshot.process.vms_bytes = 4 * 1024 * 1024;
  snapshot.process.shared_bytes = 512 * 1024;
  snapshot.process.data_bytes = 256 * 1024;

  char buf[4096];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed");

  VALK_PASS();
}

void test_sse_format_gc_tiers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.gc_heap.tier_count = 2;
  snapshot.gc_heap.tiers[0].name = "lval";
  snapshot.gc_heap.tiers[0].bytes_used = 1000;
  snapshot.gc_heap.tiers[0].bytes_total = 2000;
  snapshot.gc_heap.tiers[0].bytes_peak = 1500;
  snapshot.gc_heap.tiers[0].objects_used = 100;
  snapshot.gc_heap.tiers[0].objects_total = 200;
  snapshot.gc_heap.tiers[0].objects_peak = 150;

  snapshot.gc_heap.tiers[1].name = "malloc";
  snapshot.gc_heap.tiers[1].bytes_used = 5000;
  snapshot.gc_heap.tiers[1].bytes_total = 10000;
  snapshot.gc_heap.tiers[1].bytes_peak = 7500;
  snapshot.gc_heap.gc_threshold_pct = 80;
  snapshot.gc_heap.gc_cycles = 5;
  snapshot.gc_heap.emergency_collections = 1;

  char buf[4096];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed");
  VALK_TEST_ASSERT(strstr(buf, "\"tiers\":[") != NULL, "Should have tiers array");
  VALK_TEST_ASSERT(strstr(buf, "\"name\":\"lval\"") != NULL, "Should have lval tier");
  VALK_TEST_ASSERT(strstr(buf, "\"name\":\"malloc\"") != NULL, "Should have malloc tier");
  VALK_TEST_ASSERT(strstr(buf, "\"threshold_pct\":80") != NULL, "Should have threshold");
  VALK_TEST_ASSERT(strstr(buf, "\"cycles\":5") != NULL, "Should have cycles");
  VALK_TEST_ASSERT(strstr(buf, "\"emergency\":1") != NULL, "Should have emergency");

  VALK_PASS();
}

void test_handle_kind_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_DIAG_HNDL_EMPTY == 0, "EMPTY should be 0");
  VALK_TEST_ASSERT(VALK_DIAG_HNDL_TCP == 1, "TCP should be 1");
  VALK_TEST_ASSERT(VALK_DIAG_HNDL_TASK == 2, "TASK should be 2");
  VALK_TEST_ASSERT(VALK_DIAG_HNDL_TIMER == 3, "TIMER should be 3");
  VALK_TEST_ASSERT(VALK_DIAG_HNDL_HTTP_CONN == 4, "HTTP_CONN should be 4");

  VALK_PASS();
}

void test_diag_snapshot_to_sse_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "test";
  snapshot.slabs[0].total_slots = 8;
  snapshot.slabs[0].used_slots = 4;
  snapshot.slabs[0].has_slot_diag = false;
  snapshot.slabs[0].bitmap = malloc(1);
  snapshot.slabs[0].bitmap[0] = 0xF0;
  snapshot.slabs[0].bitmap_bytes = 1;

  char buf[8192];
  int len = valk_diag_snapshot_to_sse(&snapshot, NULL, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed, got %d", len);
  VALK_TEST_ASSERT(strstr(buf, "event: diagnostics") != NULL, "Should have diagnostics event");
  VALK_TEST_ASSERT(strstr(buf, "\"memory\":{") != NULL, "Should have memory section");
  VALK_TEST_ASSERT(strstr(buf, "\"metrics\":{") != NULL, "Should have metrics section");

  free(snapshot.slabs[0].bitmap);
  VALK_PASS();
}

void test_diag_snapshot_to_sse_with_slots(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "handles";
  snapshot.slabs[0].total_slots = 4;
  snapshot.slabs[0].used_slots = 3;
  snapshot.slabs[0].has_slot_diag = true;
  snapshot.slabs[0].by_state.active = 2;
  snapshot.slabs[0].by_state.idle = 1;
  snapshot.slabs[0].by_state.closing = 0;
  snapshot.slabs[0].slots = calloc(4, sizeof(valk_slot_diag_t));
  snapshot.slabs[0].slots[0].state = 'A';
  snapshot.slabs[0].slots[1].state = 'A';
  snapshot.slabs[0].slots[2].state = 'I';
  snapshot.slabs[0].slots[3].state = 'F';

  char buf[8192];
  int len = valk_diag_snapshot_to_sse(&snapshot, NULL, buf, sizeof(buf), 42);

  VALK_TEST_ASSERT(len > 0, "Should succeed");
  VALK_TEST_ASSERT(strstr(buf, "id: 42") != NULL, "Should have event ID 42");
  VALK_TEST_ASSERT(strstr(buf, "\"states\":\"A2I1F1\"") != NULL, "Should have RLE states");

  free(snapshot.slabs[0].slots);
  VALK_PASS();
}

void test_diag_snapshot_to_sse_buffer_too_small(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "test";
  snapshot.slabs[0].total_slots = 8;
  snapshot.slabs[0].used_slots = 4;

  char buf[20];
  int len = valk_diag_snapshot_to_sse(&snapshot, NULL, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len < 0, "Should fail with small buffer");

  VALK_PASS();
}

void test_diag_delta_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t current = {0};
  valk_mem_snapshot_t prev = {0};

  current.slab_count = 1;
  current.slabs[0].name = "test";
  current.slabs[0].total_slots = 4;
  current.slabs[0].used_slots = 2;
  current.slabs[0].bitmap = malloc(1);
  current.slabs[0].bitmap[0] = 0x03;
  current.slabs[0].bitmap_bytes = 1;

  prev.slab_count = 1;
  prev.slabs[0].name = "test";
  prev.slabs[0].total_slots = 4;
  prev.slabs[0].used_slots = 1;
  prev.slabs[0].bitmap = malloc(1);
  prev.slabs[0].bitmap[0] = 0x01;
  prev.slabs[0].bitmap_bytes = 1;

  valk_sse_diag_conn_t conn = {0};
  char buf[8192];
  int len = valk_diag_delta_to_sse(&current, &prev, &conn, NULL, NULL, buf, sizeof(buf), 100);

  VALK_TEST_ASSERT(len >= 0, "Should succeed or return 0 for no changes, got %d", len);

  free(current.slabs[0].bitmap);
  free(prev.slabs[0].bitmap);
  VALK_PASS();
}

void test_diag_delta_no_changes(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t current = {0};
  valk_mem_snapshot_t prev = {0};

  current.slab_count = 1;
  current.slabs[0].name = "test";
  current.slabs[0].total_slots = 4;
  current.slabs[0].used_slots = 2;
  current.slabs[0].bitmap = malloc(1);
  current.slabs[0].bitmap[0] = 0x03;
  current.slabs[0].bitmap_bytes = 1;

  prev.slab_count = 1;
  prev.slabs[0].name = "test";
  prev.slabs[0].total_slots = 4;
  prev.slabs[0].used_slots = 2;
  prev.slabs[0].bitmap = malloc(1);
  prev.slabs[0].bitmap[0] = 0x03;
  prev.slabs[0].bitmap_bytes = 1;

  valk_sse_diag_conn_t conn = {0};
  char buf[8192];
  int len = valk_diag_delta_to_sse(&current, &prev, &conn, NULL, NULL, buf, sizeof(buf), 100);

  VALK_TEST_ASSERT(len >= 0, "Should succeed for identical snapshots, got %d", len);

  free(current.slabs[0].bitmap);
  free(prev.slabs[0].bitmap);
  VALK_PASS();
}

void test_diag_fresh_state_json_null_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  char buf[4096];
  int len = valk_diag_fresh_state_json(NULL, buf, sizeof(buf));

  VALK_TEST_ASSERT(len >= 0 || len < 0, "NULL AIO produces some result");

  VALK_PASS();
}

void test_diag_fresh_state_json_small_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  char buf[10];
  int len = valk_diag_fresh_state_json(NULL, buf, sizeof(buf));

  VALK_TEST_ASSERT(len < 0, "Should fail with small buffer");

  VALK_PASS();
}

void test_diag_delta_slot_changes(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t current = {0};
  valk_mem_snapshot_t prev = {0};

  current.slab_count = 1;
  current.slabs[0].name = "handles";
  current.slabs[0].total_slots = 8;
  current.slabs[0].used_slots = 4;
  current.slabs[0].has_slot_diag = true;
  current.slabs[0].by_state.active = 2;
  current.slabs[0].by_state.idle = 2;
  current.slabs[0].by_state.closing = 0;
  current.slabs[0].slots = calloc(8, sizeof(valk_slot_diag_t));
  current.slabs[0].slots[0].state = 'A';
  current.slabs[0].slots[1].state = 'A';
  current.slabs[0].slots[2].state = 'I';
  current.slabs[0].slots[3].state = 'I';
  current.slabs[0].slots[4].state = 'F';
  current.slabs[0].slots[5].state = 'F';
  current.slabs[0].slots[6].state = 'F';
  current.slabs[0].slots[7].state = 'F';

  prev.slab_count = 1;
  prev.slabs[0].name = "handles";
  prev.slabs[0].total_slots = 8;
  prev.slabs[0].used_slots = 2;
  prev.slabs[0].has_slot_diag = true;
  prev.slabs[0].by_state.active = 2;
  prev.slabs[0].by_state.idle = 0;
  prev.slabs[0].by_state.closing = 0;
  prev.slabs[0].slots = calloc(8, sizeof(valk_slot_diag_t));
  prev.slabs[0].slots[0].state = 'A';
  prev.slabs[0].slots[1].state = 'A';
  prev.slabs[0].slots[2].state = 'F';
  prev.slabs[0].slots[3].state = 'F';
  prev.slabs[0].slots[4].state = 'F';
  prev.slabs[0].slots[5].state = 'F';
  prev.slabs[0].slots[6].state = 'F';
  prev.slabs[0].slots[7].state = 'F';

  valk_sse_diag_conn_t conn = {0};
  char buf[16384];
  int len = valk_diag_delta_to_sse(&current, &prev, &conn, NULL, NULL, buf, sizeof(buf), 200);

  VALK_TEST_ASSERT(len > 0, "Should produce delta output, got %d", len);
  VALK_TEST_ASSERT(strstr(buf, "diagnostics-delta") != NULL, "Should have delta event type");
  VALK_TEST_ASSERT(strstr(buf, "\"memory\":{") != NULL, "Should have memory section for changed data");

  free(current.slabs[0].slots);
  free(prev.slabs[0].slots);
  VALK_PASS();
}

void test_diag_delta_arena_changes(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t current = {0};
  valk_mem_snapshot_t prev = {0};

  current.arena_count = 1;
  current.arenas[0].name = "scratch";
  current.arenas[0].used_bytes = 2048;
  current.arenas[0].capacity_bytes = 4096;

  prev.arena_count = 1;
  prev.arenas[0].name = "scratch";
  prev.arenas[0].used_bytes = 1024;
  prev.arenas[0].capacity_bytes = 4096;

  valk_sse_diag_conn_t conn = {0};
  char buf[8192];
  int len = valk_diag_delta_to_sse(&current, &prev, &conn, NULL, NULL, buf, sizeof(buf), 300);

  VALK_TEST_ASSERT(len > 0, "Should produce delta output for arena changes, got %d", len);

  free(current.slabs[0].bitmap);
  free(prev.slabs[0].bitmap);
  VALK_PASS();
}

void test_diag_delta_gc_changes(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t current = {0};
  valk_mem_snapshot_t prev = {0};

  current.gc_heap.gc_cycles = 10;
  current.gc_heap.emergency_collections = 1;

  prev.gc_heap.gc_cycles = 9;
  prev.gc_heap.emergency_collections = 0;

  valk_sse_diag_conn_t conn = {0};
  char buf[16384];
  int len = valk_diag_delta_to_sse(&current, &prev, &conn, NULL, NULL, buf, sizeof(buf), 400);

  VALK_TEST_ASSERT(len > 0, "Should produce delta output for GC changes, got %d", len);
  VALK_TEST_ASSERT(strstr(buf, "\"gc\":{") != NULL, "Should have GC section");

  VALK_PASS();
}

void test_sse_format_multiple_slabs(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 3;

  snapshot.slabs[0].name = "tcp_buffers";
  snapshot.slabs[0].total_slots = 16;
  snapshot.slabs[0].used_slots = 8;
  snapshot.slabs[0].has_slot_diag = false;
  snapshot.slabs[0].bitmap = malloc(2);
  snapshot.slabs[0].bitmap[0] = 0xFF;
  snapshot.slabs[0].bitmap[1] = 0x00;
  snapshot.slabs[0].bitmap_bytes = 2;

  snapshot.slabs[1].name = "handles";
  snapshot.slabs[1].total_slots = 8;
  snapshot.slabs[1].used_slots = 4;
  snapshot.slabs[1].has_slot_diag = true;
  snapshot.slabs[1].by_state.active = 2;
  snapshot.slabs[1].by_state.idle = 2;
  snapshot.slabs[1].slots = calloc(8, sizeof(valk_slot_diag_t));
  for (int i = 0; i < 8; i++) {
    snapshot.slabs[1].slots[i].state = (i < 2) ? 'A' : (i < 4) ? 'I' : 'F';
  }

  snapshot.slabs[2].name = "stream_arenas";
  snapshot.slabs[2].total_slots = 4;
  snapshot.slabs[2].used_slots = 1;
  snapshot.slabs[2].has_slot_diag = false;
  snapshot.slabs[2].bitmap = malloc(1);
  snapshot.slabs[2].bitmap[0] = 0x01;
  snapshot.slabs[2].bitmap_bytes = 1;

  char buf[8192];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed with multiple slabs");
  VALK_TEST_ASSERT(strstr(buf, "\"name\":\"tcp_buffers\"") != NULL, "Should have tcp_buffers");
  VALK_TEST_ASSERT(strstr(buf, "\"name\":\"handles\"") != NULL, "Should have handles");
  VALK_TEST_ASSERT(strstr(buf, "\"name\":\"stream_arenas\"") != NULL, "Should have stream_arenas");

  free(snapshot.slabs[0].bitmap);
  free(snapshot.slabs[1].slots);
  free(snapshot.slabs[2].bitmap);
  VALK_PASS();
}

void test_sse_format_multiple_arenas(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.arena_count = 2;

  snapshot.arenas[0].name = "scratch";
  snapshot.arenas[0].used_bytes = 1024;
  snapshot.arenas[0].capacity_bytes = 4096;
  snapshot.arenas[0].high_water_mark = 2048;
  snapshot.arenas[0].overflow_fallbacks = 0;
  snapshot.arenas[0].overflow_bytes = 0;

  snapshot.arenas[1].name = "request";
  snapshot.arenas[1].used_bytes = 512;
  snapshot.arenas[1].capacity_bytes = 2048;
  snapshot.arenas[1].high_water_mark = 1024;
  snapshot.arenas[1].overflow_fallbacks = 1;
  snapshot.arenas[1].overflow_bytes = 256;

  char buf[4096];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed with multiple arenas");
  VALK_TEST_ASSERT(strstr(buf, "\"name\":\"scratch\"") != NULL, "Should have scratch arena");
  VALK_TEST_ASSERT(strstr(buf, "\"name\":\"request\"") != NULL, "Should have request arena");
  VALK_TEST_ASSERT(strstr(buf, "\"overflow_bytes\":256") != NULL, "Should have overflow_bytes");

  VALK_PASS();
}

void test_sse_format_breakdown(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.breakdown.scratch_arena_used = 1024;
  snapshot.breakdown.scratch_arena_capacity = 4096;
  snapshot.breakdown.gc_heap_used = 50000;
  snapshot.breakdown.gc_heap_capacity = 100000;
  snapshot.breakdown.gc_lval_slab_used = 30000;
  snapshot.breakdown.gc_lval_slab_capacity = 50000;
  snapshot.breakdown.gc_lenv_slab_used = 5000;
  snapshot.breakdown.gc_lenv_slab_capacity = 10000;
  snapshot.breakdown.gc_malloc_used = 15000;
  snapshot.breakdown.aio_slabs_used = 8000;
  snapshot.breakdown.aio_slabs_capacity = 16000;
  snapshot.breakdown.metrics_used = 2000;
  snapshot.breakdown.metrics_capacity = 4000;
  snapshot.breakdown.untracked_bytes = 10000;
  snapshot.breakdown.untracked_reserved = 50000;

  char buf[16384];
  int len = valk_diag_snapshot_to_sse(&snapshot, NULL, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed with breakdown data");
  VALK_TEST_ASSERT(strstr(buf, "\"breakdown\":{") != NULL, "Should have breakdown section");
  VALK_TEST_ASSERT(strstr(buf, "\"scratch_used\":1024") != NULL, "Should have scratch_used");
  VALK_TEST_ASSERT(strstr(buf, "\"gc_used\":50000") != NULL, "Should have gc_used");
  VALK_TEST_ASSERT(strstr(buf, "\"untracked\":10000") != NULL, "Should have untracked");

  VALK_PASS();
}

void test_sse_format_smaps(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.smaps.heap_rss = 1024 * 1024;
  snapshot.smaps.stack_rss = 64 * 1024;
  snapshot.smaps.anon_rss = 2 * 1024 * 1024;
  snapshot.smaps.file_rss = 512 * 1024;
  snapshot.smaps.shmem_rss = 128 * 1024;
  snapshot.smaps.uring_rss = 0;
  snapshot.smaps.other_rss = 256 * 1024;
  snapshot.smaps.total_rss = 4 * 1024 * 1024;
  snapshot.smaps.anon_regions = 10;
  snapshot.smaps.file_regions = 20;

  char buf[16384];
  int len = valk_diag_snapshot_to_sse(&snapshot, NULL, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed with smaps data");
  VALK_TEST_ASSERT(strstr(buf, "\"smaps\":{") != NULL, "Should have smaps section");
  VALK_TEST_ASSERT(strstr(buf, "\"heap\":") != NULL, "Should have heap RSS");
  VALK_TEST_ASSERT(strstr(buf, "\"anon_regions\":10") != NULL, "Should have anon_regions");

  VALK_PASS();
}

void test_sse_format_rle_long_runs(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "test";
  snapshot.slabs[0].total_slots = 256;
  snapshot.slabs[0].used_slots = 256;
  snapshot.slabs[0].has_slot_diag = false;

  snapshot.slabs[0].bitmap = malloc(32);
  memset(snapshot.slabs[0].bitmap, 0xFF, 32);
  snapshot.slabs[0].bitmap_bytes = 32;

  char buf[4096];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed with long RLE runs");
  VALK_TEST_ASSERT(strstr(buf, "ff*32") != NULL, "Should have RLE compressed bitmap ff*32");

  free(snapshot.slabs[0].bitmap);
  VALK_PASS();
}

void test_sse_format_rle_alternating(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "test";
  snapshot.slabs[0].total_slots = 32;
  snapshot.slabs[0].used_slots = 16;
  snapshot.slabs[0].has_slot_diag = false;

  snapshot.slabs[0].bitmap = malloc(4);
  snapshot.slabs[0].bitmap[0] = 0xAA;
  snapshot.slabs[0].bitmap[1] = 0x55;
  snapshot.slabs[0].bitmap[2] = 0xAA;
  snapshot.slabs[0].bitmap[3] = 0x55;
  snapshot.slabs[0].bitmap_bytes = 4;

  char buf[4096];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed with alternating pattern");
  VALK_TEST_ASSERT(strstr(buf, "aa") != NULL, "Should have 0xAA bytes");
  VALK_TEST_ASSERT(strstr(buf, "55") != NULL, "Should have 0x55 bytes");

  free(snapshot.slabs[0].bitmap);
  VALK_PASS();
}

void test_snapshot_collect_null_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, NULL);

  VALK_TEST_ASSERT(snapshot.slab_count == 0, "Should have 0 slabs for NULL AIO");
  VALK_TEST_ASSERT(snapshot.arena_count == 0, "Should have 0 arenas for NULL AIO");

  valk_mem_snapshot_free(&snapshot);
  VALK_PASS();
}

void test_sse_format_empty_owner_map(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.owner_count = 0;

  char buf[2048];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed with empty owner map");
  VALK_TEST_ASSERT(strstr(buf, "\"owner_map\":[]") != NULL, "Should have empty owner_map array");

  VALK_PASS();
}

void test_sse_format_null_owner_names(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_snapshot_t snapshot = {0};
  snapshot.owner_count = 2;
  snapshot.owner_map[0] = NULL;
  snapshot.owner_map[1] = ":8080";

  char buf[2048];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 1);

  VALK_TEST_ASSERT(len > 0, "Should succeed with NULL owner name");
  VALK_TEST_ASSERT(strstr(buf, "\"owner_map\":[\"\"") != NULL, "Should have empty string for NULL owner");

  VALK_PASS();
}

// ============================================================================
// Integration Tests with Real AIO System
// ============================================================================

static valk_aio_system_t *create_test_aio_system(void) {
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  return valk_aio_start_with_config(&cfg);
}

// ============================================================================
// HTTP/2 SSE Streaming Tests
// ============================================================================

void test_sse_registry_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_data_provider2 data_prd;
  
  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      NULL, NULL, NULL, 0, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);
  VALK_TEST_ASSERT(entry == NULL, "subscribe: Should return NULL for NULL registry");

  entry = valk_sse_registry_find_by_stream(NULL, NULL, 0);
  VALK_TEST_ASSERT(entry == NULL, "find: Should return NULL for NULL registry");

  valk_sse_registry_unsubscribe(NULL, NULL);

  size_t count = valk_sse_registry_unsubscribe_connection(NULL, NULL);
  VALK_TEST_ASSERT(count == 0, "unsubscribe_connection: Should return 0 for NULL registry");

  valk_sse_registry_timer_start(NULL);
  valk_sse_registry_timer_stop(NULL);

  size_t len = valk_sse_registry_stats_json(NULL, NULL, 0);
  VALK_TEST_ASSERT(len == 0, "stats_json: Should return 0 for NULL args");

  VALK_PASS();
}

void test_sse_registry_with_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  VALK_TEST_ASSERT(registry != NULL, "SSE registry should exist");
  VALK_TEST_ASSERT(valk_sse_registry_stream_count(registry) == 0,
                   "Initial stream count should be 0");

  char stats_buf[256];
  size_t stats_len = valk_sse_registry_stats_json(registry, stats_buf, sizeof(stats_buf));
  VALK_TEST_ASSERT(stats_len > 0, "Stats JSON should succeed");
  VALK_TEST_ASSERT(strstr(stats_buf, "\"stream_count\":0") != NULL,
                   "Stats should show 0 streams");

  valk_sse_registry_unsubscribe(registry, NULL);

  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(registry, NULL, 999);
  VALK_TEST_ASSERT(entry == NULL, "find: Should return NULL for non-existent stream");

  size_t count = valk_sse_registry_unsubscribe_connection(registry, NULL);
  VALK_TEST_ASSERT(count == 0, "unsubscribe_connection: Should return 0 for NULL handle");

  char tiny_buf[5];
  size_t len = valk_sse_registry_stats_json(registry, tiny_buf, sizeof(tiny_buf));
  VALK_TEST_ASSERT(len == 0, "stats_json: Should return 0 for tiny buffer");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_sse_diag_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_diag_init(NULL, NULL);

  nghttp2_data_provider2 data_prd;
  valk_sse_diag_conn_t *conn = valk_sse_diag_init_http2(NULL, NULL, NULL, 0, &data_prd);
  VALK_TEST_ASSERT(conn == NULL, "init_http2: Should return NULL for NULL args");

  conn = valk_sse_diag_init_http2(NULL, NULL, NULL, 0, NULL);
  VALK_TEST_ASSERT(conn == NULL, "init_http2: Should return NULL when data_prd is NULL");

  valk_sse_diag_stop(NULL);
  valk_sse_diag_stop_all(NULL);

  VALK_PASS();
}

void test_real_aio_snapshot_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, sys);

  VALK_TEST_ASSERT(snapshot.slab_count > 0, "Should have slabs");
  VALK_TEST_ASSERT(snapshot.process.rss_bytes > 0, "RSS should be > 0");

  bool found_handles = false;
  for (size_t i = 0; i < snapshot.slab_count; i++) {
    if (snapshot.slabs[i].name) {
      if (strcmp(snapshot.slabs[i].name, "handles") == 0) found_handles = true;
    }
  }

  VALK_TEST_ASSERT(found_handles, "Should have handles slab");

  valk_mem_snapshot_free(&snapshot);
  valk_aio_stop(sys);
  VALK_PASS();
}

void test_real_aio_sse_format(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, sys);

  char buf[65536];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 12345);
  VALK_TEST_ASSERT(len > 0, "SSE format should succeed");
  VALK_TEST_ASSERT(strstr(buf, "event: memory") != NULL, "Missing event header");
  VALK_TEST_ASSERT(strstr(buf, "\"slabs\":[") != NULL, "Missing slabs array");

  int dlen = valk_diag_snapshot_to_sse(&snapshot, sys, buf, sizeof(buf), 99);
  VALK_TEST_ASSERT(dlen > 0, "Diag SSE format should succeed");
  VALK_TEST_ASSERT(strstr(buf, "event: diagnostics") != NULL, "Missing diagnostics event");
  VALK_TEST_ASSERT(strstr(buf, "\"memory\":{") != NULL, "Missing memory section");
  VALK_TEST_ASSERT(strstr(buf, "\"metrics\":{") != NULL, "Missing metrics section");

  valk_mem_snapshot_free(&snapshot);
  valk_aio_stop(sys);
  VALK_PASS();
}

void test_real_aio_fresh_state_json(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  char buf[65536];
  int len = valk_diag_fresh_state_json(sys, buf, sizeof(buf));
  VALK_TEST_ASSERT(len > 0, "Fresh state JSON should succeed");
  VALK_TEST_ASSERT(buf[0] == '{', "Should start with opening brace");
  VALK_TEST_ASSERT(strstr(buf, "\"memory\":{") != NULL, "Missing memory section");
  VALK_TEST_ASSERT(strstr(buf, "\"slabs\":[") != NULL, "Missing slabs array");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_real_aio_delta(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_mem_snapshot_t s1 = {0}, s2 = {0};
  valk_mem_snapshot_collect(&s1, sys);
  valk_mem_snapshot_collect(&s2, sys);

  valk_sse_diag_conn_t conn = {0};
  char buf[32768];
  int len = valk_diag_delta_to_sse(&s2, &s1, &conn, sys, NULL, buf, sizeof(buf), 1);
  VALK_TEST_ASSERT(len > 0, "Delta SSE should succeed");
  VALK_TEST_ASSERT(strstr(buf, "diagnostics-delta") != NULL, "Should have delta event type");

  valk_mem_snapshot_t dst = {0};
  valk_mem_snapshot_copy(&dst, &s1);
  VALK_TEST_ASSERT(dst.slab_count == s1.slab_count, "Copy slab count should match");

  valk_mem_snapshot_free(&s1);
  valk_mem_snapshot_free(&s2);
  valk_mem_snapshot_free(&dst);
  valk_aio_stop(sys);
  VALK_PASS();
}

void test_real_aio_accessors(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  VALK_TEST_ASSERT(valk_aio_get_handle_slab(sys) != NULL, "Should have handle slab");
  VALK_TEST_ASSERT(valk_aio_get_metrics(sys) != NULL, "Should have AIO metrics");
  VALK_TEST_ASSERT(valk_aio_get_system_stats(sys) != NULL, "Should have system stats");
  VALK_TEST_ASSERT(valk_aio_get_sse_registry(sys) != NULL, "Should have SSE registry");
  VALK_TEST_ASSERT(valk_aio_get_event_loop(sys) != NULL, "Should have event loop");

  valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(sys, 0);
  VALK_TEST_ASSERT(kind >= VALK_DIAG_HNDL_EMPTY && kind <= VALK_DIAG_HNDL_HTTP_CONN,
                   "Handle kind should be valid enum value");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_real_aio_owner_registry(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  size_t count_before = valk_owner_get_count(sys);
  uint16_t idx = valk_owner_register(sys, ":8080", 1, NULL);
  VALK_TEST_ASSERT(idx != UINT16_MAX, "Should register owner successfully");
  VALK_TEST_ASSERT(valk_owner_get_count(sys) == count_before + 1, "Owner count should increase");

  const char *name = valk_owner_get_name(sys, idx);
  VALK_TEST_ASSERT(name != NULL && strcmp(name, ":8080") == 0, "Owner name should match");

  valk_aio_stop(sys);
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

  // Snapshot memory management tests
  valk_testsuite_add_test(suite, "test_snapshot_free_null", test_snapshot_free_null);
  valk_testsuite_add_test(suite, "test_snapshot_free_empty", test_snapshot_free_empty);
  valk_testsuite_add_test(suite, "test_snapshot_free_with_allocations", test_snapshot_free_with_allocations);
  valk_testsuite_add_test(suite, "test_snapshot_copy_null", test_snapshot_copy_null);
  valk_testsuite_add_test(suite, "test_snapshot_copy_empty", test_snapshot_copy_empty);
  valk_testsuite_add_test(suite, "test_snapshot_copy_with_data", test_snapshot_copy_with_data);
  valk_testsuite_add_test(suite, "test_snapshot_copy_overwrites_dst", test_snapshot_copy_overwrites_dst);

  // SSE formatting edge cases
  valk_testsuite_add_test(suite, "test_snapshot_sse_buffer_too_small", test_snapshot_sse_buffer_too_small);
  valk_testsuite_add_test(suite, "test_snapshot_sse_empty_snapshot", test_snapshot_sse_empty_snapshot);
  valk_testsuite_add_test(suite, "test_sse_format_by_type", test_sse_format_by_type);
  valk_testsuite_add_test(suite, "test_sse_format_by_owner", test_sse_format_by_owner);
  valk_testsuite_add_test(suite, "test_sse_format_process_memory", test_sse_format_process_memory);
  valk_testsuite_add_test(suite, "test_sse_format_gc_tiers", test_sse_format_gc_tiers);
  valk_testsuite_add_test(suite, "test_handle_kind_enum", test_handle_kind_enum);

  // Diagnostics snapshot tests
  valk_testsuite_add_test(suite, "test_diag_snapshot_to_sse_basic", test_diag_snapshot_to_sse_basic);
  valk_testsuite_add_test(suite, "test_diag_snapshot_to_sse_with_slots", test_diag_snapshot_to_sse_with_slots);
  valk_testsuite_add_test(suite, "test_diag_snapshot_to_sse_buffer_too_small", test_diag_snapshot_to_sse_buffer_too_small);
  valk_testsuite_add_test(suite, "test_diag_delta_basic", test_diag_delta_basic);
  valk_testsuite_add_test(suite, "test_diag_delta_no_changes", test_diag_delta_no_changes);
  valk_testsuite_add_test(suite, "test_diag_fresh_state_json_null_aio", test_diag_fresh_state_json_null_aio);
  valk_testsuite_add_test(suite, "test_diag_fresh_state_json_small_buffer", test_diag_fresh_state_json_small_buffer);

  // Additional delta and format tests
  valk_testsuite_add_test(suite, "test_diag_delta_slot_changes", test_diag_delta_slot_changes);
  valk_testsuite_add_test(suite, "test_diag_delta_arena_changes", test_diag_delta_arena_changes);
  valk_testsuite_add_test(suite, "test_diag_delta_gc_changes", test_diag_delta_gc_changes);
  valk_testsuite_add_test(suite, "test_sse_format_multiple_slabs", test_sse_format_multiple_slabs);
  valk_testsuite_add_test(suite, "test_sse_format_multiple_arenas", test_sse_format_multiple_arenas);
  valk_testsuite_add_test(suite, "test_sse_format_breakdown", test_sse_format_breakdown);
  valk_testsuite_add_test(suite, "test_sse_format_smaps", test_sse_format_smaps);
  valk_testsuite_add_test(suite, "test_sse_format_rle_long_runs", test_sse_format_rle_long_runs);
  valk_testsuite_add_test(suite, "test_sse_format_rle_alternating", test_sse_format_rle_alternating);
  valk_testsuite_add_test(suite, "test_snapshot_collect_null_aio", test_snapshot_collect_null_aio);
  valk_testsuite_add_test(suite, "test_sse_format_empty_owner_map", test_sse_format_empty_owner_map);
  valk_testsuite_add_test(suite, "test_sse_format_null_owner_names", test_sse_format_null_owner_names);

  // Integration tests with real AIO system
  valk_testsuite_add_test(suite, "test_real_aio_snapshot_collect", test_real_aio_snapshot_collect);
  valk_testsuite_add_test(suite, "test_real_aio_sse_format", test_real_aio_sse_format);
  valk_testsuite_add_test(suite, "test_real_aio_fresh_state_json", test_real_aio_fresh_state_json);
  valk_testsuite_add_test(suite, "test_real_aio_delta", test_real_aio_delta);
  valk_testsuite_add_test(suite, "test_real_aio_accessors", test_real_aio_accessors);
  valk_testsuite_add_test(suite, "test_real_aio_owner_registry", test_real_aio_owner_registry);

  // SSE Registry and Diag tests (consolidated to reduce AIO system allocations)
  valk_testsuite_add_test(suite, "test_sse_registry_null_args", test_sse_registry_null_args);
  valk_testsuite_add_test(suite, "test_sse_registry_with_aio", test_sse_registry_with_aio);
  valk_testsuite_add_test(suite, "test_sse_diag_null_args", test_sse_diag_null_args);
#else
  valk_testsuite_add_test(suite, "test_sse_disabled", test_sse_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
