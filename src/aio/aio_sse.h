#ifndef VALK_AIO_SSE_H
#define VALK_AIO_SSE_H

#include "aio.h"
#include <nghttp2/nghttp2.h>
#include <stdbool.h>
#include <stdint.h>

// Forward declarations
typedef struct valk_sse_stream valk_sse_stream_t;
typedef struct valk_sse_event valk_sse_event_t;

// Forward declarations for Lisp types
struct valk_lval_t;
struct valk_lenv_t;

// SSE stream state
typedef enum {
  VALK_SSE_INIT,
  VALK_SSE_OPEN,
  VALK_SSE_CLOSING,
  VALK_SSE_CLOSED,
} valk_sse_state_e;

// SSE event structure (for queueing)
struct valk_sse_event {
  valk_sse_event_t *next;
  char *event_type;       // NULL for default "message" event
  char *data;             // Event data (JSON, text, etc.)
  size_t data_len;
  uint64_t id;            // Optional event ID for resumption
  uint32_t retry_ms;      // Optional retry hint (0 = not set)
};

// SSE stream context
struct valk_sse_stream {
  // Identity
  uint64_t id;
  valk_sse_state_e state;

  // HTTP/2 context
  valk_aio_handle_t *conn;
  nghttp2_session *session;
  int32_t stream_id;

  // Connection tracking (linked list of streams per connection)
  valk_sse_stream_t *next;

  // Event queue (producer-consumer)
  valk_sse_event_t *queue_head;
  valk_sse_event_t *queue_tail;
  size_t queue_len;
  size_t queue_max;           // Backpressure threshold

  // Pending write buffer
  char *pending_data;
  size_t pending_len;
  size_t pending_offset;
  size_t pending_capacity;

  // State tracking
  bool data_deferred;
  uint64_t last_event_id;
  uint64_t events_sent;
  uint64_t bytes_sent;

  // Activity tracking for idle timeout
  uint64_t created_at_ms;
  uint64_t last_activity_ms;
  uint64_t idle_timeout_ms;       // 0 = no timeout

  // Callbacks (optional, for C-level hooks)
  void (*on_drain)(valk_sse_stream_t *stream, void *user_data);
  void (*on_close)(valk_sse_stream_t *stream, void *user_data);
  void (*on_timeout)(valk_sse_stream_t *stream, void *user_data);
  void *user_data;

  // Lisp callbacks (stored as heap-allocated lvals)
  struct valk_lval_t *lisp_on_drain;
  struct valk_lval_t *lisp_on_close;
  struct valk_lval_t *lisp_on_timeout;
  struct valk_lenv_t *callback_env;
};

// Stream lifecycle
valk_sse_stream_t *valk_sse_stream_new(
    valk_aio_handle_t *conn,
    nghttp2_session *session,
    int32_t stream_id,
    nghttp2_data_provider2 *data_prd_out);

void valk_sse_stream_close(valk_sse_stream_t *stream);
void valk_sse_stream_free(valk_sse_stream_t *stream);

// Connection tracking (for cleanup on connection close)
// Implemented in aio_sse_conn_tracking.c
void valk_sse_stream_register(valk_sse_stream_t *stream);
void valk_sse_stream_unregister(valk_sse_stream_t *stream);
void valk_sse_close_all_streams(valk_aio_handle_t *conn);

// Event sending
int valk_sse_send(valk_sse_stream_t *stream, const char *data, size_t len);
int valk_sse_send_event(valk_sse_stream_t *stream, const char *event_type,
                        const char *data, size_t len, uint64_t id);
int valk_sse_send_retry(valk_sse_stream_t *stream, uint32_t retry_ms);

// Backpressure
bool valk_sse_is_writable(valk_sse_stream_t *stream);
size_t valk_sse_queue_len(valk_sse_stream_t *stream);

// Timeout Management
void valk_sse_set_idle_timeout(valk_sse_stream_t *stream, uint64_t timeout_ms);
void valk_sse_touch_activity(valk_sse_stream_t *stream);
bool valk_sse_is_idle_expired(valk_sse_stream_t *stream);

// Stream cancellation (RST_STREAM)
int valk_sse_stream_cancel(valk_sse_stream_t *stream, uint32_t error_code);

// Global stream management
typedef struct valk_sse_manager valk_sse_manager_t;

struct valk_sse_manager {
  valk_sse_stream_t *streams;       // Global list of all streams
  size_t stream_count;
  bool shutting_down;
  uint64_t shutdown_deadline_ms;
  void *aio_system;                 // valk_aio_system_t*
};

void valk_sse_manager_init(valk_sse_manager_t *mgr, void *aio_system);
void valk_sse_manager_shutdown(valk_sse_manager_t *mgr);
void valk_sse_manager_add(valk_sse_manager_t *mgr, valk_sse_stream_t *stream);
void valk_sse_manager_remove(valk_sse_manager_t *mgr, valk_sse_stream_t *stream);
valk_sse_stream_t *valk_sse_manager_find_by_id(valk_sse_manager_t *mgr, uint64_t id);
size_t valk_sse_manager_check_timeouts(valk_sse_manager_t *mgr);
int valk_sse_manager_graceful_shutdown(valk_sse_manager_t *mgr, uint64_t drain_timeout_ms);
size_t valk_sse_manager_force_close_all(valk_sse_manager_t *mgr);

// Get global manager (initialized by AIO system)
valk_sse_manager_t *valk_sse_get_manager(void);

// Lisp builtins registration
void valk_register_sse_builtins(struct valk_lenv_t *env);

#endif // VALK_AIO_SSE_H
