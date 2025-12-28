#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/aio_sse_stream_registry.h"
#include "../../src/aio/aio.h"

#include <string.h>
#include <stdlib.h>

#ifdef VALK_METRICS_ENABLED
static valk_aio_system_t *create_test_aio_system(void) {
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  return valk_aio_start_with_config(&cfg);
}
#endif

void test_registry_init_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_init(NULL, NULL);

  valk_sse_stream_registry_t registry;
  valk_sse_registry_init(&registry, NULL);

  VALK_PASS();
}

void test_registry_init_and_shutdown(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry;
  memset(&registry, 0, sizeof(registry));
  
  valk_sse_registry_shutdown(&registry);
  
  ASSERT_EQ(registry.stream_count, 0);

  VALK_PASS();
}

void test_registry_entry_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *entry = calloc(1, sizeof(valk_sse_stream_entry_t));
  entry->stream_id = 123;
  entry->http2_stream_id = 456;
  entry->type = VALK_SSE_SUB_DIAGNOSTICS;
  atomic_store(&entry->active, true);
  atomic_store(&entry->being_removed, false);
  entry->first_event_sent = false;
  entry->last_event_id = 0;
  entry->pending_data = NULL;
  entry->pending_len = 0;
  entry->pending_offset = 0;
  entry->pending_capacity = 0;
  entry->metrics_baseline = NULL;

  ASSERT_EQ(entry->stream_id, 123);
  ASSERT_EQ(entry->http2_stream_id, 456);
  ASSERT_EQ(entry->type, VALK_SSE_SUB_DIAGNOSTICS);
  ASSERT_TRUE(atomic_load(&entry->active));
  ASSERT_FALSE(atomic_load(&entry->being_removed));

  atomic_store(&entry->active, false);
  ASSERT_FALSE(atomic_load(&entry->active));

  free(entry);
  VALK_PASS();
}

void test_registry_entry_pending_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *entry = calloc(1, sizeof(valk_sse_stream_entry_t));
  entry->pending_capacity = 1024;
  entry->pending_data = malloc(entry->pending_capacity);
  entry->pending_len = 100;
  entry->pending_offset = 50;

  ASSERT_EQ(entry->pending_capacity, 1024);
  ASSERT_EQ(entry->pending_len, 100);
  ASSERT_EQ(entry->pending_offset, 50);

  size_t remaining = entry->pending_len - entry->pending_offset;
  ASSERT_EQ(remaining, 50);

  free(entry->pending_data);
  free(entry);
  VALK_PASS();
}

void test_registry_entry_aio_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *entry = calloc(1, sizeof(valk_sse_stream_entry_t));
  
  entry->prev_aio_metrics.bytes_sent = 1000;
  entry->prev_aio_metrics.bytes_recv = 2000;
  entry->prev_aio_metrics.requests_total = 100;
  entry->prev_aio_metrics.connections_total = 10;
  entry->prev_aio_metrics.gc_cycles = 5;
  entry->prev_aio_metrics.pending_streams_current = 3;
  entry->prev_aio_metrics.pending_streams_total = 20;
  entry->prev_aio_metrics.pending_streams_processed = 15;
  entry->prev_aio_metrics.pending_streams_dropped = 2;

  ASSERT_EQ(entry->prev_aio_metrics.bytes_sent, 1000);
  ASSERT_EQ(entry->prev_aio_metrics.bytes_recv, 2000);
  ASSERT_EQ(entry->prev_aio_metrics.requests_total, 100);
  ASSERT_EQ(entry->prev_aio_metrics.connections_total, 10);
  ASSERT_EQ(entry->prev_aio_metrics.gc_cycles, 5);

  free(entry);
  VALK_PASS();
}

void test_registry_doubly_linked_list(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *entry1 = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *entry2 = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *entry3 = calloc(1, sizeof(valk_sse_stream_entry_t));

  entry1->stream_id = 1;
  entry2->stream_id = 2;
  entry3->stream_id = 3;

  entry1->next = entry2;
  entry1->prev = NULL;
  entry2->prev = entry1;
  entry2->next = entry3;
  entry3->prev = entry2;
  entry3->next = NULL;

  ASSERT_NULL(entry1->prev);
  ASSERT_EQ(entry1->next, entry2);
  ASSERT_EQ(entry2->prev, entry1);
  ASSERT_EQ(entry2->next, entry3);
  ASSERT_EQ(entry3->prev, entry2);
  ASSERT_NULL(entry3->next);

  entry2->prev->next = entry2->next;
  entry2->next->prev = entry2->prev;

  ASSERT_EQ(entry1->next, entry3);
  ASSERT_EQ(entry3->prev, entry1);

  free(entry1);
  free(entry2);
  free(entry3);
  VALK_PASS();
}

void test_registry_subscription_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *diag = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *metrics = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *memory = calloc(1, sizeof(valk_sse_stream_entry_t));

  diag->type = VALK_SSE_SUB_DIAGNOSTICS;
  metrics->type = VALK_SSE_SUB_METRICS_ONLY;
  memory->type = VALK_SSE_SUB_MEMORY_ONLY;

  ASSERT_EQ(diag->type, VALK_SSE_SUB_DIAGNOSTICS);
  ASSERT_EQ(metrics->type, VALK_SSE_SUB_METRICS_ONLY);
  ASSERT_EQ(memory->type, VALK_SSE_SUB_MEMORY_ONLY);

  free(diag);
  free(metrics);
  free(memory);
  VALK_PASS();
}

void test_registry_atomic_being_removed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *entry = calloc(1, sizeof(valk_sse_stream_entry_t));
  atomic_store(&entry->being_removed, false);

  bool expected = false;
  bool success = atomic_compare_exchange_strong(&entry->being_removed, &expected, true);
  ASSERT_TRUE(success);
  ASSERT_TRUE(atomic_load(&entry->being_removed));

  expected = false;
  success = atomic_compare_exchange_strong(&entry->being_removed, &expected, true);
  ASSERT_FALSE(success);

  free(entry);
  VALK_PASS();
}

void test_registry_struct_state(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry;
  memset(&registry, 0, sizeof(registry));

  registry.stream_count = 5;
  registry.timer_running = true;
  registry.timer_interval_ms = 100;
  registry.events_pushed_total = 1000;
  registry.bytes_pushed_total = 50000;

  ASSERT_EQ(registry.stream_count, 5);
  ASSERT_TRUE(registry.timer_running);
  ASSERT_EQ(registry.timer_interval_ms, 100);
  ASSERT_EQ(registry.events_pushed_total, 1000);
  ASSERT_EQ(registry.bytes_pushed_total, 50000);

  VALK_PASS();
}

void test_registry_shutdown_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_shutdown(NULL);

  VALK_PASS();
}

void test_registry_stream_count_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t count = valk_sse_registry_stream_count(NULL);
  ASSERT_EQ(count, 0);

  VALK_PASS();
}

void test_registry_stats_json_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  char buf[256];
  size_t len = valk_sse_registry_stats_json(NULL, buf, sizeof(buf));
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

void test_registry_stats_json_null_buf(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  size_t len = valk_sse_registry_stats_json(&registry, NULL, 256);
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

void test_registry_stats_json_zero_size(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  char buf[256];
  size_t len = valk_sse_registry_stats_json(&registry, buf, 0);
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

void test_registry_stats_json_valid(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  registry.stream_count = 5;
  registry.timer_running = true;
  registry.events_pushed_total = 100;
  registry.bytes_pushed_total = 10000;

  char buf[256];
  size_t len = valk_sse_registry_stats_json(&registry, buf, sizeof(buf));
  ASSERT_GT(len, 0);
  ASSERT_STR_CONTAINS(buf, "stream_count");
  ASSERT_STR_CONTAINS(buf, "timer_running");
  ASSERT_STR_CONTAINS(buf, "events_pushed_total");
  ASSERT_STR_CONTAINS(buf, "bytes_pushed_total");
  ASSERT_STR_CONTAINS(buf, "\"stream_count\":5");
  ASSERT_STR_CONTAINS(buf, "\"timer_running\":true");

  VALK_PASS();
}

void test_registry_stats_json_small_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  char buf[10];
  size_t len = valk_sse_registry_stats_json(&registry, buf, sizeof(buf));
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

void test_registry_subscribe_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_data_provider2 data_prd;

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      NULL, NULL, NULL, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);
  ASSERT_NULL(entry);

  VALK_PASS();
}

void test_registry_subscribe_null_data_prd(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      &registry, (valk_aio_handle_t *)1, (nghttp2_session *)1, 1,
      VALK_SSE_SUB_DIAGNOSTICS, NULL);
  ASSERT_NULL(entry);

  VALK_PASS();
}

void test_registry_unsubscribe_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_unsubscribe(NULL, NULL);

  valk_sse_stream_registry_t registry = {0};
  valk_sse_registry_unsubscribe(&registry, NULL);

  VALK_PASS();
}

void test_registry_unsubscribe_connection_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t count = valk_sse_registry_unsubscribe_connection(NULL, NULL);
  ASSERT_EQ(count, 0);

  valk_sse_stream_registry_t registry = {0};
  count = valk_sse_registry_unsubscribe_connection(&registry, NULL);
  ASSERT_EQ(count, 0);

  VALK_PASS();
}

void test_registry_find_by_stream_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(NULL, NULL, 0);
  ASSERT_NULL(entry);

  VALK_PASS();
}

void test_registry_find_by_stream_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(
      &registry, (valk_aio_handle_t *)1, 1);
  ASSERT_NULL(entry);

  VALK_PASS();
}

void test_registry_timer_start_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_timer_start(NULL);

  VALK_PASS();
}

void test_registry_timer_start_no_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  valk_sse_registry_timer_start(&registry);

  VALK_PASS();
}

void test_registry_timer_stop_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_timer_stop(NULL);

  VALK_PASS();
}

void test_registry_timer_stop_not_running(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  registry.timer_running = false;
  valk_sse_registry_timer_stop(&registry);

  VALK_PASS();
}

void test_subscription_type_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_EQ(VALK_SSE_SUB_DIAGNOSTICS, 0);
  ASSERT_EQ(VALK_SSE_SUB_METRICS_ONLY, 1);
  ASSERT_EQ(VALK_SSE_SUB_MEMORY_ONLY, 2);

  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
void test_registry_init_with_real_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);
  ASSERT_EQ(registry->stream_count, 0);
  ASSERT_EQ(registry->aio_system, sys);
  ASSERT_FALSE(registry->timer_running);
  ASSERT_EQ(registry->timer_interval_ms, 100);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_timer_start_with_real_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);
  ASSERT_FALSE(registry->timer_running);

  valk_sse_registry_timer_start(registry);
  ASSERT_TRUE(registry->timer_running);
  ASSERT_NOT_NULL(registry->timer_handle);

  valk_sse_registry_timer_start(registry);
  ASSERT_TRUE(registry->timer_running);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_timer_stop_with_real_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_sse_registry_timer_start(registry);
  ASSERT_TRUE(registry->timer_running);

  valk_sse_registry_timer_stop(registry);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_stats_with_real_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  size_t count = valk_sse_registry_stream_count(registry);
  ASSERT_EQ(count, 0);

  char buf[512];
  size_t len = valk_sse_registry_stats_json(registry, buf, sizeof(buf));
  ASSERT_GT(len, 0);
  ASSERT_STR_CONTAINS(buf, "\"stream_count\":0");
  ASSERT_STR_CONTAINS(buf, "\"timer_running\":false");

  valk_sse_registry_timer_start(registry);
  len = valk_sse_registry_stats_json(registry, buf, sizeof(buf));
  ASSERT_GT(len, 0);
  ASSERT_STR_CONTAINS(buf, "\"timer_running\":true");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_shutdown_with_entries(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_sse_stream_entry_t *entry1 = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *entry2 = calloc(1, sizeof(valk_sse_stream_entry_t));
  ASSERT_NOT_NULL(entry1);
  ASSERT_NOT_NULL(entry2);

  entry1->stream_id = 1;
  entry1->pending_data = malloc(1024);
  entry1->pending_capacity = 1024;
  atomic_store(&entry1->active, true);

  entry2->stream_id = 2;
  entry2->pending_data = malloc(1024);
  entry2->pending_capacity = 1024;
  atomic_store(&entry2->active, true);

  entry1->next = entry2;
  entry1->prev = NULL;
  entry2->prev = entry1;
  entry2->next = NULL;
  registry->streams = entry1;
  registry->stream_count = 2;

  valk_sse_registry_timer_start(registry);
  ASSERT_TRUE(registry->timer_running);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_find_with_entries(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;

  valk_sse_stream_entry_t *entry1 = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *entry2 = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *entry3 = calloc(1, sizeof(valk_sse_stream_entry_t));

  entry1->handle = fake_handle;
  entry1->http2_stream_id = 1;
  entry2->handle = fake_handle;
  entry2->http2_stream_id = 3;
  entry3->handle = (valk_aio_handle_t *)0x5678;
  entry3->http2_stream_id = 1;

  entry1->next = entry2;
  entry2->next = entry3;
  entry2->prev = entry1;
  entry3->prev = entry2;
  registry.streams = entry1;
  registry.stream_count = 3;

  valk_sse_stream_entry_t *found = valk_sse_registry_find_by_stream(&registry, fake_handle, 1);
  ASSERT_EQ(found, entry1);

  found = valk_sse_registry_find_by_stream(&registry, fake_handle, 3);
  ASSERT_EQ(found, entry2);

  found = valk_sse_registry_find_by_stream(&registry, (valk_aio_handle_t *)0x5678, 1);
  ASSERT_EQ(found, entry3);

  found = valk_sse_registry_find_by_stream(&registry, fake_handle, 999);
  ASSERT_NULL(found);

  found = valk_sse_registry_find_by_stream(&registry, (valk_aio_handle_t *)0x9999, 1);
  ASSERT_NULL(found);

  free(entry1);
  free(entry2);
  free(entry3);
  VALK_PASS();
}

void test_registry_unsubscribe_entry(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};

  valk_sse_stream_entry_t *entry1 = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *entry2 = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *entry3 = calloc(1, sizeof(valk_sse_stream_entry_t));

  entry1->stream_id = 1;
  entry1->pending_data = malloc(64);
  atomic_store(&entry1->active, true);
  atomic_store(&entry1->being_removed, false);

  entry2->stream_id = 2;
  entry2->pending_data = malloc(64);
  atomic_store(&entry2->active, true);
  atomic_store(&entry2->being_removed, false);

  entry3->stream_id = 3;
  entry3->pending_data = malloc(64);
  atomic_store(&entry3->active, true);
  atomic_store(&entry3->being_removed, false);

  entry1->next = entry2;
  entry1->prev = NULL;
  entry2->prev = entry1;
  entry2->next = entry3;
  entry3->prev = entry2;
  entry3->next = NULL;
  registry.streams = entry1;
  registry.stream_count = 3;

  valk_sse_registry_unsubscribe(&registry, entry2);
  ASSERT_EQ(registry.stream_count, 2);
  ASSERT_EQ(entry1->next, entry3);
  ASSERT_EQ(entry3->prev, entry1);

  valk_sse_registry_unsubscribe(&registry, entry1);
  ASSERT_EQ(registry.stream_count, 1);
  ASSERT_EQ(registry.streams, entry3);
  ASSERT_NULL(entry3->prev);

  valk_sse_registry_unsubscribe(&registry, entry3);
  ASSERT_EQ(registry.stream_count, 0);
  ASSERT_NULL(registry.streams);

  VALK_PASS();
}

void test_registry_unsubscribe_double_removal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};

  valk_sse_stream_entry_t *entry = calloc(1, sizeof(valk_sse_stream_entry_t));
  entry->stream_id = 1;
  entry->pending_data = malloc(64);
  atomic_store(&entry->active, true);
  atomic_store(&entry->being_removed, false);

  entry->next = NULL;
  entry->prev = NULL;
  registry.streams = entry;
  registry.stream_count = 1;

  valk_sse_registry_unsubscribe(&registry, entry);
  ASSERT_EQ(registry.stream_count, 0);

  valk_sse_stream_entry_t *entry2 = calloc(1, sizeof(valk_sse_stream_entry_t));
  entry2->stream_id = 2;
  atomic_store(&entry2->active, true);
  atomic_store(&entry2->being_removed, true);
  entry2->next = NULL;
  entry2->prev = NULL;
  registry.streams = entry2;
  registry.stream_count = 1;

  valk_sse_registry_unsubscribe(&registry, entry2);
  ASSERT_EQ(registry.stream_count, 1);

  free(entry2);
  VALK_PASS();
}

void test_registry_unsubscribe_connection_with_entries(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  valk_aio_handle_t *handle1 = (valk_aio_handle_t *)0x1234;
  valk_aio_handle_t *handle2 = (valk_aio_handle_t *)0x5678;

  valk_sse_stream_entry_t *entry1 = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *entry2 = calloc(1, sizeof(valk_sse_stream_entry_t));
  valk_sse_stream_entry_t *entry3 = calloc(1, sizeof(valk_sse_stream_entry_t));

  entry1->handle = handle1;
  entry1->stream_id = 1;
  atomic_store(&entry1->active, true);
  atomic_store(&entry1->being_removed, false);

  entry2->handle = handle1;
  entry2->stream_id = 2;
  atomic_store(&entry2->active, true);
  atomic_store(&entry2->being_removed, false);

  entry3->handle = handle2;
  entry3->stream_id = 3;
  atomic_store(&entry3->active, true);
  atomic_store(&entry3->being_removed, false);

  entry1->next = entry2;
  entry1->prev = NULL;
  entry2->prev = entry1;
  entry2->next = entry3;
  entry3->prev = entry2;
  entry3->next = NULL;
  registry.streams = entry1;
  registry.stream_count = 3;

  size_t count = valk_sse_registry_unsubscribe_connection(&registry, handle1);
  ASSERT_EQ(count, 2);
  ASSERT_EQ(registry.stream_count, 1);
  ASSERT_EQ(registry.streams, entry3);

  count = valk_sse_registry_unsubscribe_connection(&registry, handle2);
  ASSERT_EQ(count, 1);
  ASSERT_EQ(registry.stream_count, 0);
  ASSERT_NULL(registry.streams);

  VALK_PASS();
}

void test_registry_subscribe_valid(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);
  ASSERT_EQ(registry->stream_count, 0);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

  ASSERT_NOT_NULL(entry);
  ASSERT_EQ(registry->stream_count, 1);
  ASSERT_EQ(entry->handle, fake_handle);
  ASSERT_EQ(entry->session, fake_session);
  ASSERT_EQ(entry->http2_stream_id, 1);
  ASSERT_EQ(entry->type, VALK_SSE_SUB_DIAGNOSTICS);
  ASSERT_TRUE(atomic_load(&entry->active));
  ASSERT_FALSE(atomic_load(&entry->being_removed));
  ASSERT_FALSE(entry->first_event_sent);
  ASSERT_EQ(entry->last_event_id, 0);
  ASSERT_NULL(entry->pending_data);

  ASSERT_NOT_NULL(data_prd.source.ptr);
  ASSERT_EQ(data_prd.source.ptr, entry);
  ASSERT_NOT_NULL(data_prd.read_callback);

  ASSERT_TRUE(registry->timer_running);

  atomic_store(&entry->active, false);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_subscribe_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd1 = {0};
  nghttp2_data_provider2 data_prd2 = {0};
  nghttp2_data_provider2 data_prd3 = {0};

  valk_sse_stream_entry_t *entry1 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd1);
  valk_sse_stream_entry_t *entry2 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 3, VALK_SSE_SUB_METRICS_ONLY, &data_prd2);
  valk_sse_stream_entry_t *entry3 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 5, VALK_SSE_SUB_MEMORY_ONLY, &data_prd3);

  ASSERT_NOT_NULL(entry1);
  ASSERT_NOT_NULL(entry2);
  ASSERT_NOT_NULL(entry3);
  ASSERT_EQ(registry->stream_count, 3);

  ASSERT_EQ(entry1->type, VALK_SSE_SUB_DIAGNOSTICS);
  ASSERT_EQ(entry2->type, VALK_SSE_SUB_METRICS_ONLY);
  ASSERT_EQ(entry3->type, VALK_SSE_SUB_MEMORY_ONLY);

  ASSERT_NE(entry1->stream_id, entry2->stream_id);
  ASSERT_NE(entry2->stream_id, entry3->stream_id);

  ASSERT_EQ(registry->streams, entry3);
  ASSERT_EQ(entry3->next, entry2);
  ASSERT_EQ(entry2->next, entry1);
  ASSERT_NULL(entry1->next);

  atomic_store(&entry1->active, false);
  atomic_store(&entry2->active, false);
  atomic_store(&entry3->active, false);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_subscribe_and_unsubscribe(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

  ASSERT_NOT_NULL(entry);
  ASSERT_EQ(registry->stream_count, 1);

  valk_sse_registry_unsubscribe(registry, entry);
  ASSERT_EQ(registry->stream_count, 0);
  ASSERT_NULL(registry->streams);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_subscribe_find_and_unsubscribe(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *handle1 = (valk_aio_handle_t *)0x1111;
  valk_aio_handle_t *handle2 = (valk_aio_handle_t *)0x2222;
  nghttp2_session *session1 = (nghttp2_session *)0xAAAA;
  nghttp2_session *session2 = (nghttp2_session *)0xBBBB;
  nghttp2_data_provider2 data_prd1 = {0};
  nghttp2_data_provider2 data_prd2 = {0};
  nghttp2_data_provider2 data_prd3 = {0};

  valk_sse_stream_entry_t *entry1 = valk_sse_registry_subscribe(
      registry, handle1, session1, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd1);
  valk_sse_stream_entry_t *entry2 = valk_sse_registry_subscribe(
      registry, handle1, session1, 3, VALK_SSE_SUB_METRICS_ONLY, &data_prd2);
  valk_sse_stream_entry_t *entry3 = valk_sse_registry_subscribe(
      registry, handle2, session2, 1, VALK_SSE_SUB_MEMORY_ONLY, &data_prd3);

  ASSERT_EQ(registry->stream_count, 3);

  valk_sse_stream_entry_t *found = valk_sse_registry_find_by_stream(registry, handle1, 1);
  ASSERT_EQ(found, entry1);

  found = valk_sse_registry_find_by_stream(registry, handle1, 3);
  ASSERT_EQ(found, entry2);

  found = valk_sse_registry_find_by_stream(registry, handle2, 1);
  ASSERT_EQ(found, entry3);

  found = valk_sse_registry_find_by_stream(registry, handle1, 999);
  ASSERT_NULL(found);

  size_t count = valk_sse_registry_unsubscribe_connection(registry, handle1);
  ASSERT_EQ(count, 2);
  ASSERT_EQ(registry->stream_count, 1);

  atomic_store(&entry3->active, false);
  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_shutdown_with_subscribed_entries(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd1 = {0};
  nghttp2_data_provider2 data_prd2 = {0};

  valk_sse_stream_entry_t *entry1 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd1);
  valk_sse_stream_entry_t *entry2 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 3, VALK_SSE_SUB_METRICS_ONLY, &data_prd2);

  ASSERT_NOT_NULL(entry1);
  ASSERT_NOT_NULL(entry2);
  ASSERT_EQ(registry->stream_count, 2);
  ASSERT_TRUE(registry->timer_running);

  entry1->pending_data = malloc(1024);
  entry1->pending_capacity = 1024;
  entry2->pending_data = malloc(512);
  entry2->pending_capacity = 512;

  atomic_store(&entry1->active, false);
  atomic_store(&entry2->active, false);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_data_provider_callback_inactive(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

  ASSERT_NOT_NULL(entry);
  ASSERT_NOT_NULL(data_prd.read_callback);

  atomic_store(&entry->active, false);

  u8 buf[1024];
  u32 data_flags = 0;
  nghttp2_data_source source = { .ptr = entry };

  nghttp2_ssize result = data_prd.read_callback(
      fake_session, 1, buf, sizeof(buf), &data_flags, &source, NULL);

  ASSERT_EQ(result, 0);
  ASSERT_TRUE(data_flags & NGHTTP2_DATA_FLAG_EOF);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_data_provider_callback_no_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

  ASSERT_NOT_NULL(entry);
  ASSERT_NOT_NULL(data_prd.read_callback);

  u8 buf[1024];
  u32 data_flags = 0;
  nghttp2_data_source source = { .ptr = entry };

  nghttp2_ssize result = data_prd.read_callback(
      fake_session, 1, buf, sizeof(buf), &data_flags, &source, NULL);

  ASSERT_EQ(result, NGHTTP2_ERR_DEFERRED);

  atomic_store(&entry->active, false);
  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_data_provider_callback_with_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

  ASSERT_NOT_NULL(entry);

  entry->pending_data = malloc(100);
  entry->pending_capacity = 100;
  memcpy(entry->pending_data, "event: test\ndata: hello\n\n", 25);
  entry->pending_len = 25;
  entry->pending_offset = 0;

  u8 buf[1024];
  u32 data_flags = 0;
  nghttp2_data_source source = { .ptr = entry };

  nghttp2_ssize result = data_prd.read_callback(
      fake_session, 1, buf, sizeof(buf), &data_flags, &source, NULL);

  ASSERT_EQ(result, 25);
  ASSERT_EQ(entry->pending_offset, 25);
  ASSERT_EQ(memcmp(buf, "event: test\ndata: hello\n\n", 25), 0);

  atomic_store(&entry->active, false);
  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_data_provider_callback_partial_read(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

  ASSERT_NOT_NULL(entry);

  entry->pending_data = malloc(100);
  entry->pending_capacity = 100;
  memcpy(entry->pending_data, "0123456789ABCDEF", 16);
  entry->pending_len = 16;
  entry->pending_offset = 0;

  u8 buf[10];
  u32 data_flags = 0;
  nghttp2_data_source source = { .ptr = entry };

  nghttp2_ssize result = data_prd.read_callback(
      fake_session, 1, buf, sizeof(buf), &data_flags, &source, NULL);

  ASSERT_EQ(result, 10);
  ASSERT_EQ(entry->pending_offset, 10);
  ASSERT_EQ(memcmp(buf, "0123456789", 10), 0);

  result = data_prd.read_callback(
      fake_session, 1, buf, sizeof(buf), &data_flags, &source, NULL);

  ASSERT_EQ(result, 6);
  ASSERT_EQ(entry->pending_offset, 16);
  ASSERT_EQ(memcmp(buf, "ABCDEF", 6), 0);

  result = data_prd.read_callback(
      fake_session, 1, buf, sizeof(buf), &data_flags, &source, NULL);

  ASSERT_EQ(result, NGHTTP2_ERR_DEFERRED);

  atomic_store(&entry->active, false);
  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_data_provider_null_entry(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

  ASSERT_NOT_NULL(entry);
  ASSERT_NOT_NULL(data_prd.read_callback);

  u8 buf[1024];
  u32 data_flags = 0;
  nghttp2_data_source source = { .ptr = NULL };

  nghttp2_ssize result = data_prd.read_callback(
      fake_session, 1, buf, sizeof(buf), &data_flags, &source, NULL);

  ASSERT_EQ(result, 0);
  ASSERT_TRUE(data_flags & NGHTTP2_DATA_FLAG_EOF);

  atomic_store(&entry->active, false);
  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_stats_after_subscribe(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

  ASSERT_NOT_NULL(entry);

  char buf[512];
  size_t len = valk_sse_registry_stats_json(registry, buf, sizeof(buf));
  ASSERT_GT(len, 0);
  ASSERT_STR_CONTAINS(buf, "\"stream_count\":1");
  ASSERT_STR_CONTAINS(buf, "\"timer_running\":true");

  atomic_store(&entry->active, false);
  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_shutdown_direct_with_streams(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd1 = {0};
  nghttp2_data_provider2 data_prd2 = {0};
  nghttp2_data_provider2 data_prd3 = {0};

  valk_sse_stream_entry_t *entry1 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd1);
  valk_sse_stream_entry_t *entry2 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 3, VALK_SSE_SUB_METRICS_ONLY, &data_prd2);
  valk_sse_stream_entry_t *entry3 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 5, VALK_SSE_SUB_MEMORY_ONLY, &data_prd3);

  ASSERT_NOT_NULL(entry1);
  ASSERT_NOT_NULL(entry2);
  ASSERT_NOT_NULL(entry3);
  ASSERT_EQ(registry->stream_count, 3);
  ASSERT_TRUE(registry->timer_running);

  entry1->pending_data = malloc(1024);
  entry1->pending_capacity = 1024;
  entry2->pending_data = malloc(512);
  entry2->pending_capacity = 512;

  valk_sse_registry_shutdown(registry);

  ASSERT_EQ(registry->stream_count, 0);
  ASSERT_NULL(registry->streams);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_shutdown_with_modular_delta(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  registry->modular_delta_initialized = true;
  valk_delta_snapshot_init(&registry->modular_delta);

  valk_sse_registry_shutdown(registry);

  ASSERT_FALSE(registry->modular_delta_initialized);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_subscribe_timer_already_running(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd1 = {0};
  nghttp2_data_provider2 data_prd2 = {0};

  valk_sse_stream_entry_t *entry1 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd1);

  ASSERT_NOT_NULL(entry1);
  ASSERT_TRUE(registry->timer_running);

  valk_sse_stream_entry_t *entry2 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 3, VALK_SSE_SUB_METRICS_ONLY, &data_prd2);

  ASSERT_NOT_NULL(entry2);
  ASSERT_TRUE(registry->timer_running);
  ASSERT_EQ(registry->stream_count, 2);

  atomic_store(&entry1->active, false);
  atomic_store(&entry2->active, false);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_subscribe_with_existing_streams(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  ASSERT_NOT_NULL(sys);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_handle_t *fake_handle = (valk_aio_handle_t *)0x1234;
  nghttp2_session *fake_session = (nghttp2_session *)0x5678;
  nghttp2_data_provider2 data_prd = {0};

  valk_sse_stream_entry_t *entry1 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

  ASSERT_NOT_NULL(entry1);
  ASSERT_EQ(registry->streams, entry1);
  ASSERT_NULL(entry1->prev);
  ASSERT_NULL(entry1->next);

  nghttp2_data_provider2 data_prd2 = {0};
  valk_sse_stream_entry_t *entry2 = valk_sse_registry_subscribe(
      registry, fake_handle, fake_session, 3, VALK_SSE_SUB_METRICS_ONLY, &data_prd2);

  ASSERT_NOT_NULL(entry2);
  ASSERT_EQ(registry->streams, entry2);
  ASSERT_NULL(entry2->prev);
  ASSERT_EQ(entry2->next, entry1);
  ASSERT_EQ(entry1->prev, entry2);
  ASSERT_NULL(entry1->next);

  atomic_store(&entry1->active, false);
  atomic_store(&entry2->active, false);

  valk_aio_stop(sys);
  VALK_PASS();
}
#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_registry_init_null_args", test_registry_init_null_args);
  valk_testsuite_add_test(suite, "test_registry_init_and_shutdown", test_registry_init_and_shutdown);
  valk_testsuite_add_test(suite, "test_registry_entry_lifecycle", test_registry_entry_lifecycle);
  valk_testsuite_add_test(suite, "test_registry_entry_pending_buffer", test_registry_entry_pending_buffer);
  valk_testsuite_add_test(suite, "test_registry_entry_aio_metrics", test_registry_entry_aio_metrics);
  valk_testsuite_add_test(suite, "test_registry_doubly_linked_list", test_registry_doubly_linked_list);
  valk_testsuite_add_test(suite, "test_registry_subscription_types", test_registry_subscription_types);
  valk_testsuite_add_test(suite, "test_registry_atomic_being_removed", test_registry_atomic_being_removed);
  valk_testsuite_add_test(suite, "test_registry_struct_state", test_registry_struct_state);
  valk_testsuite_add_test(suite, "test_registry_shutdown_null", test_registry_shutdown_null);
  valk_testsuite_add_test(suite, "test_registry_stream_count_null", test_registry_stream_count_null);
  valk_testsuite_add_test(suite, "test_registry_stats_json_null", test_registry_stats_json_null);
  valk_testsuite_add_test(suite, "test_registry_stats_json_null_buf", test_registry_stats_json_null_buf);
  valk_testsuite_add_test(suite, "test_registry_stats_json_zero_size", test_registry_stats_json_zero_size);
  valk_testsuite_add_test(suite, "test_registry_stats_json_valid", test_registry_stats_json_valid);
  valk_testsuite_add_test(suite, "test_registry_stats_json_small_buffer", test_registry_stats_json_small_buffer);
  valk_testsuite_add_test(suite, "test_registry_subscribe_null_args", test_registry_subscribe_null_args);
  valk_testsuite_add_test(suite, "test_registry_subscribe_null_data_prd", test_registry_subscribe_null_data_prd);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_null", test_registry_unsubscribe_null);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_connection_null", test_registry_unsubscribe_connection_null);
  valk_testsuite_add_test(suite, "test_registry_find_by_stream_null", test_registry_find_by_stream_null);
  valk_testsuite_add_test(suite, "test_registry_find_by_stream_empty", test_registry_find_by_stream_empty);
  valk_testsuite_add_test(suite, "test_registry_timer_start_null", test_registry_timer_start_null);
  valk_testsuite_add_test(suite, "test_registry_timer_start_no_aio", test_registry_timer_start_no_aio);
  valk_testsuite_add_test(suite, "test_registry_timer_stop_null", test_registry_timer_stop_null);
  valk_testsuite_add_test(suite, "test_registry_timer_stop_not_running", test_registry_timer_stop_not_running);
  valk_testsuite_add_test(suite, "test_subscription_type_enum", test_subscription_type_enum);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_registry_init_with_real_aio", test_registry_init_with_real_aio);
  valk_testsuite_add_test(suite, "test_registry_timer_start_with_real_aio", test_registry_timer_start_with_real_aio);
  valk_testsuite_add_test(suite, "test_registry_timer_stop_with_real_aio", test_registry_timer_stop_with_real_aio);
  valk_testsuite_add_test(suite, "test_registry_stats_with_real_aio", test_registry_stats_with_real_aio);
  valk_testsuite_add_test(suite, "test_registry_shutdown_with_entries", test_registry_shutdown_with_entries);
  valk_testsuite_add_test(suite, "test_registry_find_with_entries", test_registry_find_with_entries);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_entry", test_registry_unsubscribe_entry);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_double_removal", test_registry_unsubscribe_double_removal);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_connection_with_entries", test_registry_unsubscribe_connection_with_entries);
  valk_testsuite_add_test(suite, "test_registry_subscribe_valid", test_registry_subscribe_valid);
  valk_testsuite_add_test(suite, "test_registry_subscribe_multiple", test_registry_subscribe_multiple);
  valk_testsuite_add_test(suite, "test_registry_subscribe_and_unsubscribe", test_registry_subscribe_and_unsubscribe);
  valk_testsuite_add_test(suite, "test_registry_subscribe_find_and_unsubscribe", test_registry_subscribe_find_and_unsubscribe);
  valk_testsuite_add_test(suite, "test_registry_shutdown_with_subscribed_entries", test_registry_shutdown_with_subscribed_entries);
  valk_testsuite_add_test(suite, "test_registry_data_provider_callback_inactive", test_registry_data_provider_callback_inactive);
  valk_testsuite_add_test(suite, "test_registry_data_provider_callback_no_data", test_registry_data_provider_callback_no_data);
  valk_testsuite_add_test(suite, "test_registry_data_provider_callback_with_data", test_registry_data_provider_callback_with_data);
  valk_testsuite_add_test(suite, "test_registry_data_provider_callback_partial_read", test_registry_data_provider_callback_partial_read);
  valk_testsuite_add_test(suite, "test_registry_data_provider_null_entry", test_registry_data_provider_null_entry);
  valk_testsuite_add_test(suite, "test_registry_stats_after_subscribe", test_registry_stats_after_subscribe);
  valk_testsuite_add_test(suite, "test_registry_shutdown_direct_with_streams", test_registry_shutdown_direct_with_streams);
  valk_testsuite_add_test(suite, "test_registry_shutdown_with_modular_delta", test_registry_shutdown_with_modular_delta);
  valk_testsuite_add_test(suite, "test_registry_subscribe_timer_already_running", test_registry_subscribe_timer_already_running);
  valk_testsuite_add_test(suite, "test_registry_subscribe_with_existing_streams", test_registry_subscribe_with_existing_streams);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
