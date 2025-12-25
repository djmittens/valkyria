// Include aio.h first to get full struct definitions
#include "aio.h"
#include "aio_sse_stream_registry.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>
#include <nghttp2/nghttp2.h>

#include "aio_metrics.h"
#include "aio_sse_diagnostics.h"
#include "../log.h"
#include "../metrics_v2.h"
#include "metrics_delta.h"

// SSE buffer size - large enough for full snapshot + metrics
#define SSE_BUFFER_SIZE 262144  // 256KB

// Forward declarations
static void sse_registry_timer_cb(uv_timer_t *timer);
static nghttp2_ssize sse_registry_data_read_callback(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data);

// Forward declare flush function (implemented in aio_uv.c)
extern void valk_http2_flush_pending(valk_aio_handle_t *conn);

// Forward declare session validation (implemented in aio_uv.c)
extern bool valk_aio_http_session_valid(valk_aio_handle_t *handle, void *session);

// Forward declare connection state check (implemented in aio_uv.c)
extern bool valk_aio_http_connection_closing(valk_aio_handle_t *handle);

// Global metrics registry
extern valk_metrics_registry_t g_metrics;

// ============================================================================
// Registry Lifecycle
// ============================================================================

void valk_sse_registry_init(valk_sse_stream_registry_t *registry, valk_aio_system_t *aio) {
  if (!registry || !aio) {
    VALK_ERROR("Invalid arguments to valk_sse_registry_init");
    return;
  }

  memset(registry, 0, sizeof(*registry));
  registry->aio_system = aio;
  registry->timer_interval_ms = 100;
  registry->timer_running = false;
  registry->streams = NULL;
  registry->stream_count = 0;

#ifdef VALK_METRICS_ENABLED
  // Initialize global baseline for modular metrics
  valk_metrics_baseline_init(&registry->global_baseline);
  registry->modular_delta_initialized = false;
#endif

  // Timer will start on first stream subscription
  // Once started, it runs forever until shutdown
  VALK_INFO("SSE registry: initialized (timer starts on first subscription)");
}

void valk_sse_registry_shutdown(valk_sse_stream_registry_t *registry) {
  if (!registry) {
    return;
  }

  VALK_INFO("SSE registry: shutting down (%zu streams)", registry->stream_count);

  // Stop timer first
  valk_sse_registry_timer_stop(registry);

  // Free all streams
  valk_sse_stream_entry_t *stream = registry->streams;
  while (stream) {
    valk_sse_stream_entry_t *next = stream->next;

    // Mark inactive
    atomic_store(&stream->active, false);

    // Free pending buffer
    free(stream->pending_data);

    // Free previous snapshot
    valk_mem_snapshot_free(&stream->prev_snapshot);

    // Free metrics baseline
#ifdef VALK_METRICS_ENABLED
    free(stream->metrics_baseline);
#endif

    free(stream);
    stream = next;
  }

  registry->streams = NULL;
  registry->stream_count = 0;

  // Free current snapshot
  valk_mem_snapshot_free(&registry->current_snapshot);

#ifdef VALK_METRICS_ENABLED
  // Free modular delta
  if (registry->modular_delta_initialized) {
    valk_delta_snapshot_free(&registry->modular_delta);
    registry->modular_delta_initialized = false;
  }
#endif

  VALK_INFO("SSE registry: shutdown complete");
}

// ============================================================================
// Helper: Push event to stream entry
// ============================================================================

static bool sse_push_to_entry(valk_sse_stream_entry_t *entry,
                               valk_mem_snapshot_t *snapshot,
                               valk_delta_snapshot_t *modular_delta) {
  if (!entry || !atomic_load(&entry->active) || !entry->session) {
    return false;
  }

  // Check if connection is closing - don't push to dying connections
  // This prevents race conditions during page refresh where the old connection
  // is closing but the timer fires before cleanup is complete
  if (valk_aio_http_connection_closing(entry->handle)) {
    VALK_INFO("SSE stream %d: INACTIVE - connection closing", entry->http2_stream_id);
    atomic_store(&entry->active, false);
    return false;
  }

  // Debug: log entry state before processing
  VALK_DEBUG("SSE push: stream_id=%lu http2_stream=%d first_sent=%d last_id=%lu pending=%zu/%zu",
             entry->stream_id, entry->http2_stream_id, entry->first_event_sent,
             entry->last_event_id, entry->pending_offset, entry->pending_len);

  // If we still have pending data that wasn't fully flushed (e.g., due to
  // TCP buffer exhaustion during backpressure), retry flushing instead of
  // skipping. We still return true so the handle gets added to flush list.
  if (entry->pending_data && entry->pending_offset < entry->pending_len) {
    // Resume the stream to tell nghttp2 we have data
    if (entry->session && atomic_load(&entry->active)) {
      int rv = nghttp2_session_resume_data(entry->session, entry->http2_stream_id);
      if (rv != 0 && rv != NGHTTP2_ERR_INVALID_ARGUMENT) {
        VALK_ERROR("Failed to resume HTTP/2 stream %d for retry: %s",
                   entry->http2_stream_id, nghttp2_strerror(rv));
        return false;
      }
      VALK_DEBUG("SSE stream %d: retrying flush of %zu pending bytes",
                 entry->http2_stream_id, entry->pending_len - entry->pending_offset);
      return true;  // Add to flush list so we retry sending
    }
    return false;
  }

  // Allocate or reuse pending buffer
  if (!entry->pending_data) {
    entry->pending_data = malloc(SSE_BUFFER_SIZE);
    if (!entry->pending_data) {
      VALK_ERROR("Failed to allocate SSE buffer for stream %d", entry->http2_stream_id);
      return false;
    }
    entry->pending_capacity = SSE_BUFFER_SIZE;
  }

  int len = 0;

  if (!entry->first_event_sent) {
    // First event: send full snapshot
    // Use next_id so we only update last_event_id if formatting succeeds
    uint64_t next_id = entry->last_event_id + 1;

    if (entry->type == VALK_SSE_SUB_DIAGNOSTICS) {
      len = valk_diag_snapshot_to_sse(snapshot, entry->aio_system,
                                      entry->pending_data, entry->pending_capacity,
                                      next_id);
    } else if (entry->type == VALK_SSE_SUB_MEMORY_ONLY) {
      len = valk_mem_snapshot_to_sse(snapshot, entry->pending_data,
                                     entry->pending_capacity, next_id);
    } else if (entry->type == VALK_SSE_SUB_METRICS_ONLY) {
#ifdef VALK_METRICS_ENABLED
      // Format metrics-only snapshot
      char *p = entry->pending_data;
      char *end = entry->pending_data + entry->pending_capacity;
      int n = snprintf(p, end - p, "event: metrics\nid: %lu\ndata: ", next_id);
      if (n > 0 && n < end - p) {
        p += n;
        size_t json_len = valk_metrics_v2_to_json(&g_metrics, p, end - p - 3);
        if (json_len > 0 && json_len < (size_t)(end - p - 3)) {
          p += json_len;
          n = snprintf(p, end - p, "\n\n");
          if (n > 0 && n < end - p) {
            p += n;
            len = p - entry->pending_data;
          }
        }
      }
#endif
    }

    if (len > 0) {
      entry->last_event_id = next_id;
      entry->first_event_sent = true;

#ifdef VALK_METRICS_ENABLED
      // Initialize previous metrics for delta tracking
      const valk_aio_metrics_t *aio_metrics = valk_aio_get_metrics(entry->aio_system);
      if (aio_metrics) {
        entry->prev_aio_metrics.bytes_sent = atomic_load(&aio_metrics->bytes_sent_total);
        entry->prev_aio_metrics.bytes_recv = atomic_load(&aio_metrics->bytes_recv_total);
        entry->prev_aio_metrics.requests_total = atomic_load(&aio_metrics->requests_total);
        entry->prev_aio_metrics.connections_total = atomic_load(&aio_metrics->connections_total);
      }

      // Initialize per-stream baseline
      if (!entry->metrics_baseline) {
        entry->metrics_baseline = malloc(sizeof(valk_metrics_baseline_t));
        if (entry->metrics_baseline) {
          valk_metrics_baseline_init(entry->metrics_baseline);
          valk_metrics_baseline_sync(entry->metrics_baseline, &g_metrics);
        }
      }
#endif

      // Store snapshot for next delta comparison
      valk_mem_snapshot_copy(&entry->prev_snapshot, snapshot);

      VALK_INFO("SSE[stream=%d]: FULL snapshot id=%lu (%d bytes)",
                entry->http2_stream_id, entry->last_event_id, len);
    }
  } else {
    // Subsequent events: send delta only
    if (entry->type == VALK_SSE_SUB_DIAGNOSTICS) {
      // Create a temporary connection structure for delta calculation
      valk_sse_diag_conn_t temp_conn = {
        .handle = entry->handle,
        .session = entry->session,
        .stream_id = entry->http2_stream_id,
        .aio_system = entry->aio_system,
        .prev_metrics = {
          .bytes_sent = entry->prev_aio_metrics.bytes_sent,
          .bytes_recv = entry->prev_aio_metrics.bytes_recv,
          .requests_total = entry->prev_aio_metrics.requests_total,
          .connections_total = entry->prev_aio_metrics.connections_total,
          .gc_cycles = entry->prev_aio_metrics.gc_cycles,
        }
      };

      // Use next_id to avoid incrementing last_event_id if no changes
      uint64_t next_id = entry->last_event_id + 1;
      len = valk_diag_delta_to_sse(snapshot, &entry->prev_snapshot, &temp_conn,
                                    entry->aio_system, modular_delta,
                                    entry->pending_data, entry->pending_capacity,
                                    next_id);
      // Only update last_event_id if we actually produced output
      if (len > 0) {
        entry->last_event_id = next_id;
      }

      // Update stored metrics (copy field-by-field due to different anonymous struct types)
      entry->prev_aio_metrics.bytes_sent = temp_conn.prev_metrics.bytes_sent;
      entry->prev_aio_metrics.bytes_recv = temp_conn.prev_metrics.bytes_recv;
      entry->prev_aio_metrics.requests_total = temp_conn.prev_metrics.requests_total;
      entry->prev_aio_metrics.connections_total = temp_conn.prev_metrics.connections_total;
      entry->prev_aio_metrics.gc_cycles = temp_conn.prev_metrics.gc_cycles;
    } else if (entry->type == VALK_SSE_SUB_MEMORY_ONLY) {
      // Memory-only delta (not implemented in existing code - just resend full)
      // Use next_id to avoid incrementing if we don't send
      uint64_t next_id = entry->last_event_id + 1;
      len = valk_mem_snapshot_to_sse(snapshot, entry->pending_data,
                                     entry->pending_capacity, next_id);
      if (len > 0) {
        entry->last_event_id = next_id;
      }
    } else if (entry->type == VALK_SSE_SUB_METRICS_ONLY) {
#ifdef VALK_METRICS_ENABLED
      // Metrics-only delta using per-stream baseline
      if (entry->metrics_baseline && modular_delta) {
        len = valk_delta_to_sse(modular_delta, entry->pending_data, entry->pending_capacity);
      }
#endif
    }

    if (len > 0) {
      // Update stored snapshot for next comparison
      valk_mem_snapshot_copy(&entry->prev_snapshot, snapshot);
      VALK_DEBUG("SSE[stream=%d]: sent delta (%d bytes)", entry->http2_stream_id, len);
    } else if (len == 0) {
      // No changes - don't send anything
      return false;
    }
  }

  if (len < 0) {
    VALK_ERROR("Failed to format SSE event for stream %d", entry->http2_stream_id);
    return false;
  }

  entry->pending_len = (size_t)len;
  entry->pending_offset = 0;

  // Always resume stream when we have data - resume_data is idempotent
  if (entry->session && atomic_load(&entry->active)) {
    // Re-check connection closing (state may have changed during data formatting)
    if (valk_aio_http_connection_closing(entry->handle)) {
      VALK_INFO("SSE stream %d: INACTIVE - connection closing (re-check)", entry->http2_stream_id);
      atomic_store(&entry->active, false);
      return false;
    }

    // Verify session is still valid
    if (!valk_aio_http_session_valid(entry->handle, entry->session)) {
      VALK_INFO("SSE stream %d: INACTIVE - session invalidated (entry->session=%p, handle->session=%p)",
                entry->http2_stream_id, (void*)entry->session, (void*)entry->handle);
      atomic_store(&entry->active, false);
      return false;
    }

    // Check if the stream is still valid
    void *stream_data = nghttp2_session_get_stream_user_data(entry->session, entry->http2_stream_id);
    if (stream_data == NULL) {
      VALK_INFO("SSE stream %d: INACTIVE - nghttp2 stream closed (user_data=NULL)", entry->http2_stream_id);
      atomic_store(&entry->active, false);
      return false;
    }

    int rv = nghttp2_session_resume_data(entry->session, entry->http2_stream_id);
    // NGHTTP2_ERR_INVALID_ARGUMENT means stream not deferred (already active) - that's fine
    if (rv != 0 && rv != NGHTTP2_ERR_INVALID_ARGUMENT) {
      VALK_ERROR("Failed to resume HTTP/2 stream %d: %s",
                 entry->http2_stream_id, nghttp2_strerror(rv));
      return false;
    }
  }

  return true;
}

// ============================================================================
// Timer Callback
// ============================================================================

static void sse_registry_timer_cb(uv_timer_t *timer) {
  valk_sse_stream_registry_t *registry = (valk_sse_stream_registry_t *)timer->data;

  if (!registry || registry->stream_count == 0) {
    return;
  }

  // Check if we're past the shutdown deadline
  if (registry->shutting_down) {
    uint64_t now = uv_hrtime() / 1000000;
    if (now >= registry->shutdown_deadline_ms) {
      VALK_INFO("SSE registry: shutdown deadline reached, force closing streams");
      valk_sse_registry_force_close_all(registry);
      return;
    }
  }

  // Check for idle timeouts
  valk_sse_registry_check_timeouts(registry);

  // Collect memory snapshot once for all streams
  valk_mem_snapshot_free(&registry->current_snapshot);
  valk_mem_snapshot_collect(&registry->current_snapshot, registry->aio_system);

  // Update event loop metrics from libuv (before collecting delta)
  valk_aio_update_loop_metrics(registry->aio_system);

  // Collect modular metrics delta once for all streams
#ifdef VALK_METRICS_ENABLED
  if (!registry->modular_delta_initialized) {
    valk_delta_snapshot_init(&registry->modular_delta);
    registry->modular_delta_initialized = true;
  }

  size_t modular_changes = valk_delta_snapshot_collect_stateless(
      &registry->modular_delta, &g_metrics, &registry->global_baseline);

  valk_delta_snapshot_t *modular_delta_ptr = modular_changes > 0 ? &registry->modular_delta : NULL;
#else
  valk_delta_snapshot_t *modular_delta_ptr = NULL;
#endif

  VALK_DEBUG("SSE registry: collected snapshot (%zu slabs, %zu modular changes)",
             registry->current_snapshot.slab_count,
             modular_delta_ptr ? modular_delta_ptr->delta_count : 0);

  // Push to each active stream, tracking unique handles that need flushing
  // Max 16 concurrent connections should be plenty for debug dashboard
  valk_aio_handle_t *handles_to_flush[16];
  size_t handle_count = 0;

  for (valk_sse_stream_entry_t *entry = registry->streams; entry; entry = entry->next) {
    if (!atomic_load(&entry->active)) {
      continue;
    }

    if (sse_push_to_entry(entry, &registry->current_snapshot, modular_delta_ptr)) {
      registry->events_pushed_total++;
      registry->bytes_pushed_total += entry->pending_len;

      // Touch activity timestamp on successful push
      entry->last_activity_ms = uv_hrtime() / 1000000;

      // Add handle to flush list if not already present
      bool found = false;
      for (size_t i = 0; i < handle_count; i++) {
        if (handles_to_flush[i] == entry->handle) {
          found = true;
          break;
        }
      }
      if (!found && handle_count < 16) {
        handles_to_flush[handle_count++] = entry->handle;
      }
    }
  }

  // Flush ALL connections that have streams with pending data
  for (size_t i = 0; i < handle_count; i++) {
    valk_http2_flush_pending(handles_to_flush[i]);
  }
}

// ============================================================================
// nghttp2 Data Provider Callback
// ============================================================================

static nghttp2_ssize sse_registry_data_read_callback(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data) {
  (void)session;
  (void)user_data;

  valk_sse_stream_entry_t *entry = (valk_sse_stream_entry_t *)source->ptr;

  if (!entry || !atomic_load(&entry->active)) {
    // Stream is closed, signal EOF
    VALK_INFO("SSE data_read: stream %d EOF (entry=%p, active=%d)",
              stream_id, (void*)entry, entry ? atomic_load(&entry->active) : -1);
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
    return 0;
  }

  // Check if we have data to send
  if (!entry->pending_data || entry->pending_offset >= entry->pending_len) {
    // No data available, defer until timer fires
    VALK_DEBUG("SSE data_read: stream %d DEFERRED (no data)", stream_id);
    return NGHTTP2_ERR_DEFERRED;
  }

  // Calculate how much to send
  size_t remaining = entry->pending_len - entry->pending_offset;
  size_t to_send = remaining < length ? remaining : length;

  memcpy(buf, entry->pending_data + entry->pending_offset, to_send);
  entry->pending_offset += to_send;

  // Don't set EOF - this is a streaming response
  // Don't set NO_COPY - we copied data into the provided buffer

  return (nghttp2_ssize)to_send;
}

// ============================================================================
// Stream Management
// ============================================================================

valk_sse_stream_entry_t* valk_sse_registry_subscribe(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle,
    nghttp2_session *session,
    int32_t stream_id,
    valk_sse_subscription_type_e type,
    nghttp2_data_provider2 *data_prd_out) {

  if (!registry || !handle || !session || !data_prd_out) {
    VALK_ERROR("Invalid arguments to valk_sse_registry_subscribe");
    return NULL;
  }

  // Create new stream entry
  valk_sse_stream_entry_t *entry = malloc(sizeof(valk_sse_stream_entry_t));
  if (!entry) {
    VALK_ERROR("Failed to allocate SSE stream entry");
    return NULL;
  }

  memset(entry, 0, sizeof(*entry));

  // Generate unique stream ID
  static _Atomic uint64_t next_id = 1;
  entry->stream_id = atomic_fetch_add(&next_id, 1);

  entry->type = type;
  entry->handle = handle;
  entry->aio_system = registry->aio_system;
  entry->session = session;
  entry->http2_stream_id = stream_id;
  atomic_store(&entry->active, true);
  atomic_store(&entry->being_removed, false);

  // Initialize activity tracking
  uint64_t now = uv_hrtime() / 1000000;
  entry->created_at_ms = now;
  entry->last_activity_ms = now;
  entry->idle_timeout_ms = 0;  // No timeout by default

  entry->first_event_sent = false;
  entry->last_event_id = 0;
  entry->pending_data = NULL;
  entry->pending_len = 0;
  entry->pending_offset = 0;
  entry->pending_capacity = 0;
  entry->metrics_baseline = NULL;

  // Add to doubly-linked list (prepend)
  entry->next = registry->streams;
  entry->prev = NULL;
  if (registry->streams) {
    registry->streams->prev = entry;
  }
  registry->streams = entry;
  registry->stream_count++;

  // Set up data provider for nghttp2
  data_prd_out->source.ptr = entry;
  data_prd_out->read_callback = sse_registry_data_read_callback;

  // Start timer on first subscription - once started, it runs forever
  if (!registry->timer_running) {
    valk_sse_registry_timer_start(registry);
  }

  VALK_INFO("SSE registry: stream %lu subscribed (http2_stream=%d, type=%d, total=%zu)",
            entry->stream_id, stream_id, type, registry->stream_count);

  return entry;
}

void valk_sse_registry_unsubscribe(valk_sse_stream_registry_t *registry,
                                    valk_sse_stream_entry_t *entry) {
  if (!registry || !entry) {
    return;
  }

  // Atomic double-removal guard
  bool expected = false;
  if (!atomic_compare_exchange_strong(&entry->being_removed, &expected, true)) {
    VALK_WARN("SSE registry: stream %lu already being removed", entry->stream_id);
    return;
  }

  VALK_INFO("SSE registry: unsubscribing stream %lu (http2_stream=%d)",
            entry->stream_id, entry->http2_stream_id);

  // Mark inactive
  atomic_store(&entry->active, false);

  // Remove from doubly-linked list
  if (entry->prev) {
    entry->prev->next = entry->next;
  } else {
    registry->streams = entry->next;
  }

  if (entry->next) {
    entry->next->prev = entry->prev;
  }

  registry->stream_count--;

  // Free resources
  free(entry->pending_data);
  valk_mem_snapshot_free(&entry->prev_snapshot);

#ifdef VALK_METRICS_ENABLED
  free(entry->metrics_baseline);
#endif

  free(entry);

  // Timer keeps running - no stop needed

  VALK_INFO("SSE registry: stream unsubscribed (remaining=%zu)", registry->stream_count);
}

size_t valk_sse_registry_unsubscribe_connection(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle) {

  if (!registry || !handle) {
    return 0;
  }

  VALK_INFO("SSE registry: unsubscribing all streams for handle %p", (void*)handle);

  // Find all streams for this handle
  size_t count = 0;
  valk_sse_stream_entry_t *entry = registry->streams;
  while (entry) {
    valk_sse_stream_entry_t *next = entry->next;
    if (entry->handle == handle) {
      valk_sse_registry_unsubscribe(registry, entry);
      count++;
    }
    entry = next;
  }
  return count;
}

valk_sse_stream_entry_t* valk_sse_registry_find_by_stream(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle,
    int32_t http2_stream_id) {
  if (!registry) {
    return NULL;
  }

  for (valk_sse_stream_entry_t *entry = registry->streams; entry; entry = entry->next) {
    if (entry->handle == handle && entry->http2_stream_id == http2_stream_id) {
      return entry;
    }
  }
  return NULL;
}

// ============================================================================
// Timer Control
// ============================================================================

static void on_timer_close(uv_handle_t *handle) {
  valk_sse_stream_registry_t *registry = (valk_sse_stream_registry_t *)handle->data;

  if (!registry) {
    VALK_WARN("SSE registry timer close callback: registry is NULL");
    return;
  }

  if (!registry->timer_handle) {
    VALK_WARN("SSE registry timer close callback: timer_handle is NULL");
    return;
  }

  VALK_DEBUG("SSE registry: timer closed, releasing handle");
  valk_aio_timer_free(registry->timer_handle);
  registry->timer_handle = NULL;
  registry->timer_running = false;
}

void valk_sse_registry_timer_start(valk_sse_stream_registry_t *registry) {
  if (!registry || !registry->aio_system) {
    VALK_ERROR("Invalid registry or AIO system");
    return;
  }

  if (registry->timer_running) {
    VALK_DEBUG("SSE registry: timer already running");
    return;
  }

  // Allocate timer handle from slab
  registry->timer_handle = valk_aio_timer_alloc(registry->aio_system);
  if (!registry->timer_handle) {
    VALK_ERROR("Failed to allocate SSE registry timer from handle slab");
    return;
  }

  valk_aio_timer_init(registry->timer_handle);
  valk_aio_timer_set_data(registry->timer_handle, registry);

  // Start timer with 100ms interval, first tick after 10ms
  valk_aio_timer_start(registry->timer_handle, 10, registry->timer_interval_ms,
                       sse_registry_timer_cb);

  registry->timer_running = true;

  VALK_INFO("SSE registry: timer started (interval=%lu ms)", registry->timer_interval_ms);
}

void valk_sse_registry_timer_stop(valk_sse_stream_registry_t *registry) {
  if (!registry) {
    return;
  }

  if (!registry->timer_running || !registry->timer_handle) {
    return;
  }

  VALK_INFO("SSE registry: stopping timer");

  valk_aio_timer_stop(registry->timer_handle);
  valk_aio_timer_close(registry->timer_handle, on_timer_close);
}

// ============================================================================
// Query API
// ============================================================================

size_t valk_sse_registry_stream_count(valk_sse_stream_registry_t *registry) {
  if (!registry) {
    return 0;
  }
  return registry->stream_count;
}

size_t valk_sse_registry_stats_json(valk_sse_stream_registry_t *registry, char *buf, size_t buf_size) {
  if (!registry || !buf || buf_size == 0) {
    return 0;
  }

  int n = snprintf(buf, buf_size,
                   "{\"stream_count\":%zu,\"timer_running\":%s,"
                   "\"events_pushed_total\":%" PRIu64 ",\"bytes_pushed_total\":%" PRIu64 ","
                   "\"streams_timed_out\":%" PRIu64 ",\"streams_cancelled\":%" PRIu64 ","
                   "\"shutting_down\":%s}",
                   registry->stream_count,
                   registry->timer_running ? "true" : "false",
                   registry->events_pushed_total,
                   registry->bytes_pushed_total,
                   registry->streams_timed_out,
                   registry->streams_cancelled,
                   registry->shutting_down ? "true" : "false");

  if (n < 0 || (size_t)n >= buf_size) {
    return 0;
  }

  return (size_t)n;
}

// ============================================================================
// Timeout Management
// ============================================================================

static uint64_t registry_get_current_time_ms(void) {
  return uv_hrtime() / 1000000;
}

void valk_sse_registry_set_idle_timeout(valk_sse_stream_entry_t *entry, uint64_t timeout_ms) {
  if (!entry) {
    return;
  }
  entry->idle_timeout_ms = timeout_ms;
  VALK_DEBUG("SSE registry: stream %lu idle timeout set to %" PRIu64 " ms",
             entry->stream_id, timeout_ms);
}

size_t valk_sse_registry_check_timeouts(valk_sse_stream_registry_t *registry) {
  if (!registry) {
    return 0;
  }

  uint64_t now = registry_get_current_time_ms();
  size_t timed_out = 0;

  valk_sse_stream_entry_t *entry = registry->streams;
  while (entry) {
    valk_sse_stream_entry_t *next = entry->next;

    if (atomic_load(&entry->active) && entry->idle_timeout_ms > 0) {
      uint64_t idle_time = now - entry->last_activity_ms;
      if (idle_time >= entry->idle_timeout_ms) {
        VALK_INFO("SSE registry: stream %" PRIu64 " timed out (idle for %" PRIu64 " ms)",
                  entry->stream_id, idle_time);

        registry->streams_timed_out++;
        valk_sse_registry_unsubscribe(registry, entry);
        timed_out++;
      }
    }

    entry = next;
  }

  return timed_out;
}

// ============================================================================
// Stream Cancellation
// ============================================================================

valk_sse_stream_entry_t *valk_sse_registry_find_by_id(valk_sse_stream_registry_t *registry, uint64_t stream_id) {
  if (!registry) {
    return NULL;
  }

  for (valk_sse_stream_entry_t *entry = registry->streams; entry; entry = entry->next) {
    if (entry->stream_id == stream_id) {
      return entry;
    }
  }
  return NULL;
}

int valk_sse_registry_cancel_stream(valk_sse_stream_registry_t *registry, uint64_t stream_id) {
  if (!registry) {
    return -1;
  }

  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_id(registry, stream_id);
  if (!entry) {
    VALK_WARN("SSE registry: cancel failed - stream %" PRIu64 " not found", stream_id);
    return -1;
  }

  if (!atomic_load(&entry->active)) {
    return 0;  // Already inactive
  }

  VALK_INFO("SSE registry: cancelling stream %" PRIu64 " (http2_stream=%d)",
            entry->stream_id, entry->http2_stream_id);

  // Submit RST_STREAM to HTTP/2 layer
  if (entry->session && entry->http2_stream_id > 0) {
    int rv = nghttp2_submit_rst_stream(entry->session, NGHTTP2_FLAG_NONE,
                                        entry->http2_stream_id, NGHTTP2_CANCEL);
    if (rv != 0) {
      VALK_WARN("SSE registry: failed to submit RST_STREAM for stream %" PRIu64 ": %s",
                entry->stream_id, nghttp2_strerror(rv));
    } else if (entry->handle) {
      valk_http2_flush_pending(entry->handle);
    }
  }

  registry->streams_cancelled++;
  valk_sse_registry_unsubscribe(registry, entry);

  return 0;
}

// ============================================================================
// Graceful Shutdown
// ============================================================================

bool valk_sse_registry_is_shutting_down(valk_sse_stream_registry_t *registry) {
  if (!registry) {
    return false;
  }
  return registry->shutting_down;
}

int valk_sse_registry_graceful_shutdown(valk_sse_stream_registry_t *registry, uint64_t drain_timeout_ms) {
  if (!registry) {
    return -1;
  }

  if (registry->shutting_down) {
    return 0;  // Already shutting down
  }

  VALK_INFO("SSE registry: initiating graceful shutdown (drain_timeout=%" PRIu64 " ms, streams=%zu)",
            drain_timeout_ms, registry->stream_count);

  registry->shutting_down = true;
  registry->shutdown_deadline_ms = registry_get_current_time_ms() + drain_timeout_ms;

  // For diagnostics streams, we just close them immediately since they don't have
  // pending events to drain (timer pushes are periodic, not queued)
  if (drain_timeout_ms == 0) {
    return (int)valk_sse_registry_force_close_all(registry);
  }

  return 0;
}

size_t valk_sse_registry_force_close_all(valk_sse_stream_registry_t *registry) {
  if (!registry) {
    return 0;
  }

  VALK_INFO("SSE registry: force closing all streams (%zu active)", registry->stream_count);

  size_t closed = 0;
  valk_sse_stream_entry_t *entry = registry->streams;

  while (entry) {
    valk_sse_stream_entry_t *next = entry->next;

    if (atomic_load(&entry->active)) {
      // Submit RST_STREAM
      if (entry->session && entry->http2_stream_id > 0) {
        nghttp2_submit_rst_stream(entry->session, NGHTTP2_FLAG_NONE,
                                   entry->http2_stream_id, NGHTTP2_NO_ERROR);
        if (entry->handle) {
          valk_http2_flush_pending(entry->handle);
        }
      }

      valk_sse_registry_unsubscribe(registry, entry);
      closed++;
    }

    entry = next;
  }

  registry->shutting_down = false;
  VALK_INFO("SSE registry: force closed %zu streams", closed);

  return closed;
}
