#include "collections.h"
#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif
#define _POSIX_C_SOURCE \
  200809L  // The fuck is this ? turns out sigaction and shit has to be enabled
           // separately in strict mode

#include <netinet/in.h>
#include <netdb.h>
#include <nghttp2/nghttp2.h>
#include <openssl/bio.h>
#include <openssl/conf.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <openssl/ssl3.h>
#include <openssl/tls1.h>
#include <signal.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>
#include <execinfo.h>

#include "aio.h"
#include "aio_ssl.h"
#include "aio_metrics.h"
#include "metrics.h"
#include "common.h"
#include "concurrency.h"
#include "parser.h"  // For valk_lval_t in HTTP queue
#include "memory.h"
#include "log.h"

#define MAKE_NV(NAME, VALUE, VALUELEN)                         \
  {                                                            \
      (uint8_t *)NAME, (uint8_t *)VALUE,     sizeof(NAME) - 1, \
      VALUELEN,        NGHTTP2_NV_FLAG_NONE,                   \
  }

#define MAKE_NV2(NAME, VALUE)                                    \
  {                                                              \
      (uint8_t *)NAME,   (uint8_t *)VALUE,     sizeof(NAME) - 1, \
      sizeof(VALUE) - 1, NGHTTP2_NV_FLAG_NONE,                   \
  }

#ifdef VALK_METRICS_ENABLED
// Per-server metric handles (cached at server creation)
typedef struct {
  valk_counter_t* requests_total;
  valk_counter_t* requests_success;        // status="2xx"
  valk_counter_t* requests_client_error;   // status="4xx"
  valk_counter_t* requests_server_error;   // status="5xx"
  valk_gauge_t* connections_active;
  valk_histogram_t* request_duration;
  valk_counter_t* bytes_sent;
  valk_counter_t* bytes_recv;
  valk_counter_t* overload_responses;
} valk_server_metrics_t;
#endif

// It houses requests to the event loop
enum {
  AIO_QUEUE_SIZE = 10,
  AIO_MAX_HANDLES = 2056,
  HTTP_MAX_SERVERS = 3,
  HTTP_MAX_CLIENTS = 3,
  HTTP_SLAB_ITEM_SIZE = (SSL3_RT_MAX_PACKET_SIZE * 2),
  HTTP_MAX_IO_REQUESTS = (1024),
  HTTP_MAX_CONNECTIONS = (10),
  // TODO(networking): Figure out a good initial value for this.
  HTTP_MAX_CONNECTION_HEAP = (1024000),
  HTTP_MAX_CONCURRENT_REQUESTS = (1024),
  HTTP_MAX_REQUEST_SIZE_BYTES = ((int)8e6),
  HTTP_MAX_RESPONSE_SIZE_BYTES = ((int)64e6),  // 64MB for large response tests
  // Per-stream arena configuration
  HTTP_STREAM_ARENA_SIZE = (67108864),        // 64MB per stream arena (generous for handler eval)
  HTTP_MAX_STREAMS_PER_CONNECTION = (128),    // Max concurrent streams per conn
  HTTP_STREAM_ARENA_POOL_SIZE = (64),         // Total stream arenas in pool (64 * 64MB = 4GB max)
};

// times 2 just for fun

// Singleton: only one AIO system can exist per process
// This prevents accidentally starting multiple event loops which causes race conditions
static valk_aio_system_t *global_aio_system = NULL;

// Global active AIO system (exported to aio.h for metrics access)
valk_aio_system_t *valk_aio_active_system = NULL;

#ifdef VALK_METRICS_ENABLED
// Global client connections gauge (initialized lazily)
static valk_gauge_t* client_connections_active = NULL;
#endif

static __thread valk_slab_t *tcp_buffer_slab;
static void __valk_http2_response_free(valk_arc_box *box);

// Forward declarations for backpressure functions (defined after valk_aio_http_conn)
static void __backpressure_list_add(struct valk_aio_http_conn *conn);
static void __backpressure_list_remove(struct valk_aio_http_conn *conn);
static void __backpressure_try_resume_one(void);
static void __uv_handle_closed_cb(uv_handle_t *handle);

typedef struct __http2_req_res_t {
  size_t streamid;
  valk_http2_request_t *req;
  valk_arc_box *res_box;
  valk_http2_response_t *res;
  valk_promise promise;
} __http2_req_res_t;

typedef struct __tcp_buffer_slab_item_t {
  uv_write_t req;
  uv_buf_t buf;
  struct valk_aio_http_conn *conn;  // Connection for write continuation
  char data[HTTP_SLAB_ITEM_SIZE];
} __tcp_buffer_slab_item_t;

typedef struct __http2_connect_req {
  valk_aio_system_t *sys;
  valk_aio_http2_client *client;
} __http2_connect_req;

typedef enum handle_kind_t {
  VALK_HNDL_EMPTY,
  VALK_HNDL_TCP,
  VALK_HNDL_TASK,
  VALK_HNDL_TIMER,  // For aio/delay async handles
  // VALK_FILE,
  // VALK_SIGNAL,
} handle_kind_t;

// ============================================================================
// Async Handle System (for composable async operations)
// ============================================================================
// The valk_async_handle_t struct and valk_async_status_t enum are defined in aio.h

// Extended handle data for libuv integration (internal to aio_uv.c)
typedef struct valk_async_handle_uv_data {
  union {
    uv_timer_t timer;
    // Future: uv_tcp_t, uv_fs_t, etc.
  } uv;
  valk_async_handle_t *handle;  // Back-pointer to the handle
} valk_async_handle_uv_data_t;

// Global handle ID counter (use atomic operations for thread safety)
static uint64_t g_async_handle_id = 0;

// Forward declarations for async handle functions
static valk_async_handle_t* valk_async_handle_new(uv_loop_t *loop, valk_lenv_t *env);
static void valk_async_handle_free(valk_async_handle_t *handle);
static void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
static void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
static bool valk_async_handle_cancel(valk_async_handle_t *handle);
static void valk_async_handle_add_child(valk_async_handle_t *parent, valk_async_handle_t *child);

typedef struct valk_aio_handle_t {
  handle_kind_t kind;
  valk_aio_handle_t *prev;
  valk_aio_handle_t *next;
  valk_aio_system_t *sys;
  void *arg;

  void (*onOpen)(valk_aio_handle_t *);
  void (*onClose)(valk_aio_handle_t *);

  union {
    uv_tcp_t tcp;
    uv_async_t task;
  } uv;
} valk_aio_handle_t;

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf);
void __alloc_callback(uv_handle_t *handle, size_t suggested_size,
                      uv_buf_t *buf) {
  UNUSED(handle);
  UNUSED(suggested_size);
  // TODO(networking): replace it with memory arena for the request
  valk_slab_item_t *item = valk_slab_aquire(tcp_buffer_slab);
  if (!item) {
    // Slab exhausted - return empty buffer, libuv will handle the error
    buf->base = NULL;
    buf->len = 0;
    VALK_ERROR("TCP buffer slab exhausted in alloc callback");
    return;
  }
  buf->base = (char *)item->data;  // start of payload region
  // Clamp to the configured slab payload size
  buf->len = HTTP_SLAB_ITEM_SIZE;
}

typedef struct valk_aio_task_new {
  void *arg;
  valk_promise promise;
  void (*callback)(valk_aio_system_t *, struct valk_aio_task_new *);
  valk_mem_allocator_t *allocator; // allocator used for this task
} valk_aio_task_new;

typedef struct __valk_request_client_pair_t {
  valk_aio_http2_client *client;
  valk_http2_request_t *req;
} __valk_request_client_pair_t;

typedef enum __aio_http_conn_e {
  VALK_CONN_INIT,
  VALK_CONN_ESTABLISHED,
  VALK_CONN_CLOSING,
  VALK_CONN_CLOSED
} __aio_http_conn_e;

typedef enum __aio_http_srv_e {
  VALK_SRV_INIT,
  VALK_SRV_LISTENING,
  VALK_SRV_CLOSING,
  VALK_SRV_CLOSED,
} __aio_http_srv_e;

typedef struct valk_aio_http_conn {
  __aio_http_conn_e state;
  struct valk_aio_http_conn *prev, *next;

  valk_aio_ssl_t ssl;
  nghttp2_session *session;
  valk_http2_handler_t *httpHandler;
  valk_aio_handle_t *handle;
  uv_connect_t req;
  valk_aio_http_server *server;
  int active_streams;
  int pending_write;  // Flag indicating more data to send after current write

  // Spillover buffer for nghttp2 frame data that couldn't fit in send buffer
  // nghttp2_session_mem_send2 returns data that must be consumed immediately
  uint8_t *spillover_data;
  size_t spillover_len;

  // Backpressure: true when we stopped reading due to buffer exhaustion
  bool backpressure;
  struct valk_aio_http_conn *backpressure_next;  // Next in backpressure list
  uint64_t backpressure_start_time;  // When backpressure was applied (for timeout)
} valk_aio_http_conn;

// Linked list of connections under backpressure (waiting for TCP buffers)
// Thread-local since event loop is single-threaded
static __thread struct valk_aio_http_conn *backpressure_list_head = NULL;
static __thread size_t backpressure_list_size = 0;
static __thread uv_timer_t *backpressure_timer = NULL;
#define BACKPRESSURE_LIST_MAX_SIZE 1000
#define BACKPRESSURE_CHECK_INTERVAL_MS 100  // Check every 100ms
#define BACKPRESSURE_TIMEOUT_MS 30000  // Close connections after 30s under backpressure

// Forward declaration for server request type (defined below)
typedef struct valk_http2_server_request valk_http2_server_request_t;

// Thread-local context for current HTTP request (used by aio/delay)
typedef struct {
  nghttp2_session *session;
  int32_t stream_id;
  valk_aio_http_conn *conn;
  valk_http2_server_request_t *req;
  valk_lenv_t *env;
} valk_http_request_ctx_t;

static __thread valk_http_request_ctx_t *current_request_ctx = NULL;

// Timer callback data for aio/delay
typedef struct {
  uv_timer_t timer;
  valk_lval_t *continuation;  // Lambda to call after delay
  nghttp2_session *session;
  int32_t stream_id;
  valk_aio_http_conn *conn;
  valk_mem_arena_t *stream_arena;
  valk_lenv_t *env;
} valk_delay_timer_t;

// Add connection to backpressure list
static void __backpressure_list_add(struct valk_aio_http_conn *conn) {
  if (conn->backpressure) return;  // Already in list

  // Check if list is at capacity - log warning
  // TODO(networking): Implement eviction policy when list reaches max size
  if (backpressure_list_size >= BACKPRESSURE_LIST_MAX_SIZE) {
    VALK_WARN("Backpressure list at maximum size (%zu), cannot add more connections",
              BACKPRESSURE_LIST_MAX_SIZE);
    return;  // Don't add to list if at capacity
  }

  conn->backpressure = true;
  conn->backpressure_start_time = uv_now(conn->handle->uv.tcp.loop);
  conn->backpressure_next = backpressure_list_head;
  backpressure_list_head = conn;
  backpressure_list_size++;
}

// Remove connection from backpressure list
static void __backpressure_list_remove(struct valk_aio_http_conn *conn) {
  if (!conn->backpressure) return;
  conn->backpressure = false;

  // Remove from list
  struct valk_aio_http_conn **pp = &backpressure_list_head;
  while (*pp) {
    if (*pp == conn) {
      *pp = conn->backpressure_next;
      conn->backpressure_next = NULL;
      backpressure_list_size--;
      return;
    }
    pp = &(*pp)->backpressure_next;
  }
}

// Minimum buffers needed per connection to safely resume reading
// (1 for input, 1 for output, plus margin for TLS/HTTP2 framing)
#define BUFFERS_PER_CONNECTION 4

// Try to resume backpressured connections based on available buffers
// Only resumes connections if we have enough buffer headroom to avoid
// immediate re-exhaustion
static void __backpressure_try_resume_one(void) {
  if (!backpressure_list_head) return;

  // Check available buffers - only resume if we have headroom
  size_t available = valk_slab_available(tcp_buffer_slab);
  size_t total = tcp_buffer_slab->numItems;
  float usage = 1.0f - ((float)available / total);

  // Adaptive resume threshold based on current pressure
  uint32_t min_buffers;
  if (usage < 0.5f) {
    // Low pressure: resume aggressively
    min_buffers = 2;
  } else if (usage < 0.75f) {
    // Medium pressure: normal threshold
    min_buffers = BUFFERS_PER_CONNECTION;
  } else {
    // High pressure: conservative threshold
    min_buffers = BUFFERS_PER_CONNECTION * 2;
  }

  if (available < min_buffers) {
    // Not enough buffers to safely resume - wait for more to free
    return;
  }

  // Calculate how many connections we can resume based on available buffers
  // Leave some buffer headroom (25%) for active connections
  size_t headroom = available / 4;
  size_t usable = available - headroom;
  size_t max_resume = usable / min_buffers;
  if (max_resume == 0) max_resume = 1;

  size_t resumed = 0;
  while (backpressure_list_head && resumed < max_resume) {
    struct valk_aio_http_conn *conn = backpressure_list_head;

    // Remove from list
    backpressure_list_head = conn->backpressure_next;
    conn->backpressure_next = NULL;
    conn->backpressure = false;
    backpressure_list_size--;

    // Resume reading if connection is still valid
    // Include VALK_CONN_INIT to resume connections that were mid-handshake
    // when backpressure was applied
    if (conn->state == VALK_CONN_ESTABLISHED || conn->state == VALK_CONN_INIT) {
      uv_read_start((uv_stream_t *)&conn->handle->uv.tcp,
                    __alloc_callback, __http_tcp_read_cb);
      resumed++;
    }
  }

  if (resumed > 0) {
    VALK_DEBUG("Resumed %zu backpressured connections (available buffers: %zu, usage: %.1f%%)",
               resumed, available, usage * 100);
  }
}

// Timer callback to periodically check for backpressure recovery
static void __backpressure_timer_cb(uv_timer_t *handle) {
  if (!backpressure_list_head) {
    // Stop timer if no more backpressured connections
    if (backpressure_timer) {
      VALK_DEBUG("Backpressure timer: all connections resumed, stopping timer");
      uv_timer_stop(backpressure_timer);
    }
    return;
  }

  uint64_t now = uv_now(handle->loop);
  size_t available = valk_slab_available(tcp_buffer_slab);
  size_t total = tcp_buffer_slab->numItems;
  VALK_DEBUG("Backpressure timer: %zu connections waiting, buffers %zu/%zu (%.1f%% used)",
             backpressure_list_size, total - available, total,
             (1.0f - (float)available / total) * 100);

  // First, close any timed-out connections to free resources
  struct valk_aio_http_conn **pp = &backpressure_list_head;
  while (*pp) {
    struct valk_aio_http_conn *conn = *pp;
    uint64_t elapsed = now - conn->backpressure_start_time;

    if (elapsed >= BACKPRESSURE_TIMEOUT_MS) {
      VALK_WARN("Backpressure timeout: closing connection after %llu ms",
                (unsigned long long)elapsed);

      // Remove from list
      *pp = conn->backpressure_next;
      conn->backpressure_next = NULL;
      conn->backpressure = false;
      backpressure_list_size--;

      // Close the connection
      if (conn->state != VALK_CONN_CLOSING && conn->state != VALK_CONN_CLOSED) {
        conn->state = VALK_CONN_CLOSING;
        uv_close((uv_handle_t *)&conn->handle->uv.tcp, __uv_handle_closed_cb);
      }
      // Don't advance pp, we already moved to next via *pp = conn->backpressure_next
    } else {
      pp = &(*pp)->backpressure_next;
    }
  }

  // Try to resume remaining connections
  __backpressure_try_resume_one();
}

// Start backpressure timer if not already running
static void __backpressure_timer_start(uv_loop_t *loop) {
  if (!backpressure_timer) {
    backpressure_timer = malloc(sizeof(uv_timer_t));
    if (!backpressure_timer) return;
    uv_timer_init(loop, backpressure_timer);
  }

  // Start/restart timer if we have backpressured connections
  if (backpressure_list_head && !uv_is_active((uv_handle_t *)backpressure_timer)) {
    uv_timer_start(backpressure_timer, __backpressure_timer_cb,
                   BACKPRESSURE_CHECK_INTERVAL_MS, BACKPRESSURE_CHECK_INTERVAL_MS);
  }
}

// Escape analysis: intern value to GC heap for cross-thread sharing
// Takes arena-allocated value, returns GC heap-allocated deep copy
static inline valk_lval_t* valk_http_intern_to_heap(valk_lval_t* arena_val) {
  valk_lval_t* heap_val;
  VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
    heap_val = valk_lval_copy(arena_val);
  }
  return heap_val;
}

// Server-side incoming request data (arena-allocated, per stream)
struct valk_http2_server_request {
  char *method;              // :method pseudo-header
  char *scheme;              // :scheme pseudo-header
  char *authority;           // :authority pseudo-header
  char *path;                // :path pseudo-header
  struct {
    struct valk_http2_header_t *items;
    size_t count;
    size_t capacity;
  } headers;                 // Regular headers
  uint8_t *body;             // Request body data
  size_t bodyLen;
  size_t bodyCapacity;
  valk_aio_http_conn *conn;  // Connection this request came from
  int32_t stream_id;         // HTTP/2 stream ID
  valk_mem_arena_t *stream_arena;       // Per-stream arena
  valk_slab_item_t *arena_slab_item;    // For releasing back to slab
#ifdef VALK_METRICS_ENABLED
  uint64_t start_time_us;    // Request start time for metrics
  uint64_t bytes_sent;       // Bytes sent in response
  uint64_t bytes_recv;       // Bytes received in request
  int status_code;           // HTTP status code for response (for new metrics)
#endif
};

// HTTP request item - event loop -> main thread
typedef struct {
  valk_lval_t* request;      // Request qexpr (GC heap)
  valk_lval_t* handler_fn;   // Handler lambda (GC heap)
  valk_aio_http_conn* conn;  // Connection handle
  int32_t stream_id;         // HTTP/2 stream ID
} valk_http_request_item_t;

// HTTP response item - main thread -> event loop
typedef struct {
  valk_lval_t* response;     // Response qexpr {status body headers}
  valk_aio_http_conn* conn;  // Connection to send on
  int32_t stream_id;         // Stream to respond to
} valk_http_response_item_t;

// Queue for cross-thread HTTP request/response communication
typedef struct {
  pthread_mutex_t request_mutex;
  pthread_cond_t request_ready;
  valk_http_request_item_t* request_items;
  size_t request_idx;
  size_t request_count;
  size_t request_capacity;

  pthread_mutex_t response_mutex;
  pthread_cond_t response_ready;
  valk_http_response_item_t* response_items;
  size_t response_idx;
  size_t response_count;
  size_t response_capacity;
} valk_http_queue_t;

typedef struct valk_aio_system {
  valk_aio_system_config_t config;  // Resolved configuration

  // everything  past this point only accessed inside of event loop
  uv_loop_t *eventloop;
  uv_thread_t loopThread;

  valk_aio_handle_t *stopperHandle;

  valk_slab_t *httpServers;
  valk_slab_t *httpClients;
  valk_slab_t *httpStreamArenas;    // Pool of per-stream arenas
  valk_slab_t *tcpBufferSlab;       // TCP buffer pool (for metrics access)

  valk_slab_t *handleSlab;
  valk_aio_handle_t liveHandles;

  bool shuttingDown;

  // HTTP request/response queues for Lisp handlers
  valk_http_queue_t http_queue;

#ifdef VALK_METRICS_ENABLED
  valk_aio_metrics_t metrics;
  valk_aio_system_stats_t system_stats;
#endif
} valk_aio_system_t;

typedef struct valk_aio_http_server {
  __aio_http_srv_e state;
  valk_aio_system_t *sys;
  SSL_CTX *ssl_ctx;
  valk_aio_handle_t *listener;
  char interface[200];
  int port;
  valk_http2_handler_t handler;
  valk_lval_t* lisp_handler_fn;  // Lisp lambda for request handling (GC heap)
  valk_lenv_t* sandbox_env;      // Sandbox env that shadows def (created once at startup)
  valk_http_server_config_t config;  // Server configuration
#ifdef VALK_METRICS_ENABLED
  valk_server_metrics_t metrics;
#endif
} valk_aio_http_server;

#ifdef VALK_METRICS_ENABLED
// Initialize server metrics with proper labels
static void server_metrics_init(valk_server_metrics_t* m,
                                 const char* name, int port) {
  char port_str[8];
  snprintf(port_str, sizeof(port_str), "%d", port);

  m->requests_total = valk_metric_counter("http_requests_total",
    "server", name, "port", port_str, NULL);

  m->requests_success = valk_metric_counter("http_requests_total",
    "server", name, "port", port_str, "status", "2xx", NULL);

  m->requests_client_error = valk_metric_counter("http_requests_total",
    "server", name, "port", port_str, "status", "4xx", NULL);

  m->requests_server_error = valk_metric_counter("http_requests_total",
    "server", name, "port", port_str, "status", "5xx", NULL);

  m->connections_active = valk_metric_gauge("http_connections_active",
    "server", name, "port", port_str, NULL);

  static const double latency_buckets[] = {
    0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0
  };
  m->request_duration = valk_metric_histogram("http_request_duration_seconds",
    latency_buckets, 12, "server", name, "port", port_str, NULL);

  m->bytes_sent = valk_metric_counter("http_bytes_sent_total",
    "server", name, "port", port_str, NULL);

  m->bytes_recv = valk_metric_counter("http_bytes_recv_total",
    "server", name, "port", port_str, NULL);

  m->overload_responses = valk_metric_counter("http_overload_responses_total",
    "server", name, "port", port_str, NULL);
}
#endif

static void __event_loop(void *arg) {
  valk_aio_system_t *sys = arg;
  valk_mem_init_malloc();
  VALK_DEBUG("Initializing UV event loop thread");
  // Slab for TCP buffers - must use sizeof the struct we overlay (which
  // includes uv_write_t + uv_buf_t + data buffer), not just the data size
  tcp_buffer_slab =
      valk_slab_new(sizeof(__tcp_buffer_slab_item_t), sys->config.tcp_buffer_pool_size);
  sys->tcpBufferSlab = tcp_buffer_slab;  // Store for metrics access
  VALK_INFO("Initialized %u TCP buffers (%zuKB each)",
            sys->config.tcp_buffer_pool_size, HTTP_SLAB_ITEM_SIZE / 1024);

  // Initialize per-stream arena pool
  // Each slab item contains: valk_mem_arena_t header + arena heap space
  sys->httpStreamArenas = valk_slab_new(
      sizeof(valk_mem_arena_t) + sys->config.arena_size,
      sys->config.arena_pool_size);
  if (!sys->httpStreamArenas) {
    VALK_ERROR("Failed to allocate stream arena slab");
    return;
  }
  VALK_INFO("Initialized %u stream arenas (%zuKB each)",
            sys->config.arena_pool_size, sys->config.arena_size / 1024);

  // Run the loop until stop is requested
  uv_run(sys->eventloop, UV_RUN_DEFAULT);

  // Drain pending close callbacks and timers cleanly. uv_stop only requests
  // the loop to stop; we still need to spin the loop to let close callbacks
  // run to completion.
  while (uv_loop_alive(sys->eventloop)) {
    uv_run(sys->eventloop, UV_RUN_NOWAIT);
  }

  // Clean up backpressure timer
  if (backpressure_timer) {
    uv_close((uv_handle_t *)backpressure_timer, (uv_close_cb)free);
    backpressure_timer = NULL;
  }

  valk_slab_free(tcp_buffer_slab);
  valk_slab_free(sys->httpStreamArenas);
}

static void __valk_aio_http2_on_disconnect(valk_aio_handle_t *handle) {
  VALK_DEBUG("HTTP/2 disconnect called");
  valk_aio_http_conn *conn = handle->arg;

  // Remove from backpressure list if present
  __backpressure_list_remove(conn);

  // Mark connection as closed to prevent any further operations
  conn->state = VALK_CONN_CLOSED;

  if (conn->httpHandler && conn->httpHandler->onDisconnect) {
    VALK_TRACE("HTTP/2 onDisconnect handler");
    conn->httpHandler->onDisconnect(conn->httpHandler->arg, conn);
  }

#ifdef VALK_METRICS_ENABLED
  // Record connection close (old metrics system)
  valk_aio_metrics_on_close(&handle->sys->metrics);
  // Decrement active connections gauge (new metrics system)
  if (conn->server) {
    // Server-side connection (incoming from client)
    valk_gauge_dec(conn->server->metrics.connections_active);
  } else {
    // Client-side connection (outgoing to server)
    valk_gauge_dec(client_connections_active);
  }
#endif

  // TODO Tear down http and ssl context's only through the slab... make sure
  // they dont escape into malloc

  valk_aio_ssl_free(&conn->ssl);
  nghttp2_session_del(conn->session);

  // Free spillover buffer if allocated
  if (conn->spillover_data) {
    free(conn->spillover_data);
    conn->spillover_data = NULL;
  }

  free(conn);
}

static void __uv_handle_closed_cb(uv_handle_t *handle) {
  // TODO(networking): Rename this to something more generic as it can be used
  // with any handle
  valk_aio_handle_t *hndl = handle->data;
  VALK_TRACE("UV handle closed %p", handle->data);
  if (hndl->onClose != nullptr) {
    VALK_TRACE("Calling onClose callback");
    hndl->onClose(hndl);
  }
  valk_dll_pop(hndl);  // remove this handle from live handles
  valk_slab_release_ptr(hndl->sys->handleSlab, hndl);  // finally release it
}

static void __aio_uv_walk_close(uv_handle_t *h, void *arg) {
  UNUSED(arg);
  if (!uv_is_closing(h)) {
    VALK_DEBUG("Closing open UV handle");
    uv_close(h, __uv_handle_closed_cb);
  }
}

static void __aio_uv_stop(uv_async_t *h) {
  // Just mark all handles for closing. The drain loop in __event_loop
  // (lines 208-210) will properly complete the shutdown by running until
  // all handles are closed.
  uv_walk(h->loop, __aio_uv_walk_close, NULL);
  // Call uv_stop to break out of UV_RUN_DEFAULT
  uv_stop(h->loop);
}

static int __http_on_header_callback(nghttp2_session *session,
                                     const nghttp2_frame *frame,
                                     const uint8_t *name, size_t namelen,
                                     const uint8_t *value, size_t valuelen,
                                     uint8_t flags, void *user_data) {
  UNUSED(flags);
  UNUSED(user_data);
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  VALK_TRACE("HDR: %.*s: %.*s", (int)namelen, name, (int)valuelen, value);

  // Get request attached to this stream
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

  if (!req) return 0;

#ifdef VALK_METRICS_ENABLED
  // Track received bytes for headers (name + value + overhead for ': ' and \r\n)
  req->bytes_recv += namelen + valuelen + 4;
#endif

  // Allocate strings on per-stream arena
  VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
    // Handle pseudo-headers
    if (namelen > 0 && name[0] == ':') {
      char *str = valk_mem_alloc(valuelen + 1);
      memcpy(str, value, valuelen);
      str[valuelen] = '\0';

      if (namelen == 7 && memcmp(name, ":method", 7) == 0) {
        req->method = str;
      } else if (namelen == 7 && memcmp(name, ":scheme", 7) == 0) {
        req->scheme = str;
      } else if (namelen == 10 && memcmp(name, ":authority", 10) == 0) {
        req->authority = str;
      } else if (namelen == 5 && memcmp(name, ":path", 5) == 0) {
        req->path = str;
      }
    } else {
      // Regular header - add to headers array
      if (req->headers.count >= req->headers.capacity) {
        size_t new_cap = req->headers.capacity == 0 ? 8 : req->headers.capacity * 2;
        struct valk_http2_header_t *new_items = valk_mem_alloc(
            new_cap * sizeof(struct valk_http2_header_t));
        if (req->headers.items) {
          memcpy(new_items, req->headers.items,
                 req->headers.count * sizeof(struct valk_http2_header_t));
        }
        req->headers.items = new_items;
        req->headers.capacity = new_cap;
      }

      struct valk_http2_header_t *h = &req->headers.items[req->headers.count++];
      h->name = valk_mem_alloc(namelen + 1);
      h->value = valk_mem_alloc(valuelen + 1);
      memcpy(h->name, name, namelen);
      memcpy(h->value, value, valuelen);
      h->name[namelen] = '\0';
      h->value[valuelen] = '\0';
      h->nameLen = namelen;
      h->valueLen = valuelen;
    }
  }

  return 0;  // success
}

// Forward declaration for overload response
static int __http_send_overload_response(nghttp2_session *session,
                                          int32_t stream_id,
                                          valk_aio_http_conn *conn);

static int __http_on_begin_headers_callback(nghttp2_session *session,
                                            const nghttp2_frame *frame,
                                            void *user_data) {
  valk_aio_http_conn *conn = (valk_aio_http_conn *)user_data;

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_DEBUG(">>> Received HTTP/2 request (stream_id=%d)",
               frame->hd.stream_id);

    // Track active streams for arena lifecycle
    conn->active_streams++;

#ifdef VALK_METRICS_ENABLED
    // Record stream start
    valk_aio_metrics_on_stream_start(&conn->server->sys->metrics);
#endif

    // Acquire per-stream arena from slab
    valk_slab_item_t *arena_item = valk_slab_aquire(conn->server->sys->httpStreamArenas);
    if (!arena_item) {
      // Pool exhausted - send 503 response instead of RST_STREAM
      VALK_WARN("Stream arena pool exhausted for stream %d, sending 503",
                frame->hd.stream_id);
      conn->active_streams--;

#ifdef VALK_METRICS_ENABLED
      // Track overflow in system stats
      atomic_fetch_add(&conn->server->sys->system_stats.arena_pool_overflow, 1);
      valk_counter_inc(conn->server->metrics.overload_responses);
#endif

      __http_send_overload_response(session, frame->hd.stream_id, conn);
      return 0;  // Success - we handled it with 503
    }

    valk_mem_arena_t *stream_arena = (valk_mem_arena_t *)arena_item->data;
    valk_mem_arena_init(stream_arena, conn->server->sys->config.arena_size);

#ifdef VALK_METRICS_ENABLED
    // Track arena acquisition
    valk_aio_system_stats_on_arena_acquire(&conn->server->sys->system_stats);
#endif

    // Allocate request object on STREAM arena
    valk_http2_server_request_t *req;
    VALK_WITH_ALLOC((valk_mem_allocator_t*)stream_arena) {
      req = valk_mem_alloc(sizeof(valk_http2_server_request_t));
      memset(req, 0, sizeof(valk_http2_server_request_t));
      req->conn = conn;
      req->stream_id = frame->hd.stream_id;
      req->stream_arena = stream_arena;
      req->arena_slab_item = arena_item;
#ifdef VALK_METRICS_ENABLED
      req->start_time_us = uv_hrtime() / 1000;  // Record start time
      req->bytes_sent = 0;
      req->bytes_recv = 0;
#endif
    }

    // Attach request to stream
    nghttp2_session_set_stream_user_data(session, frame->hd.stream_id, req);
  }
  return 0;
}

static int __http2_client_on_header_cb(nghttp2_session *session,
                                       const nghttp2_frame *frame,
                                       const uint8_t *name, size_t namelen,
                                       const uint8_t *value, size_t valuelen,
                                       uint8_t flags, void *user_data) {
  UNUSED(session);
  UNUSED(frame);
  UNUSED(flags);
  UNUSED(user_data);

  __http2_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

  if (reqres) {
    // Cache headers into the response object for later inspection
    if (namelen == 7 && memcmp(name, ":status", 7) == 0) {
      char *st = valk_mem_alloc(valuelen + 1);
      memcpy(st, value, valuelen);
      st[valuelen] = '\0';
      reqres->res->status = st;
    } else {
      struct valk_http2_header_t h = {0};
      h.name = valk_mem_alloc(namelen + 1);
      h.value = valk_mem_alloc(valuelen + 1);
      memcpy(h.name, name, namelen);
      memcpy(h.value, value, valuelen);
      h.name[namelen] = '\0';
      h.value[valuelen] = '\0';
      h.nameLen = namelen;
      h.valueLen = valuelen;
      da_add(&reqres->res->headers, h);
    }
  }
  return 0;  // success
}

// Forward declaration for write continuation
static void __http_continue_pending_send(struct valk_aio_http_conn *conn);

static void __http_tcp_on_write_cb(uv_write_t *handle, int status) {
  if (status) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Socket On Write error: %s \n", uv_strerror(status));
  }

  __tcp_buffer_slab_item_t *item =
      valk_container_of(handle, __tcp_buffer_slab_item_t, req);

  // Get connection reference before releasing the slab item
  struct valk_aio_http_conn *conn = item->conn;

  valk_slab_release_ptr(tcp_buffer_slab, item);

  // Buffer freed - try to resume a backpressured connection
  __backpressure_try_resume_one();

  // If write succeeded and there's pending data, continue sending
  if (status == 0 && conn && conn->pending_write) {
    __http_continue_pending_send(conn);
  }
}

// Struct to track body streaming state for large responses
typedef struct {
  const char *body;   // Body data pointer
  size_t body_len;    // Total body length
  size_t offset;      // Current offset (how much sent so far)
} http_body_source_t;

// Default 503 error page HTML
static const char valk_http_default_503_html[] =
  "<!DOCTYPE html>\n"
  "<html>\n"
  "<head>\n"
  "  <title>503 Service Unavailable</title>\n"
  "  <style>\n"
  "    body {\n"
  "      font-family: system-ui, -apple-system, sans-serif;\n"
  "      max-width: 600px;\n"
  "      margin: 100px auto;\n"
  "      padding: 20px;\n"
  "      text-align: center;\n"
  "      color: #333;\n"
  "    }\n"
  "    h1 {\n"
  "      font-size: 72px;\n"
  "      margin: 0;\n"
  "      color: #e53935;\n"
  "    }\n"
  "    p {\n"
  "      font-size: 18px;\n"
  "      color: #666;\n"
  "      margin-top: 20px;\n"
  "    }\n"
  "  </style>\n"
  "</head>\n"
  "<body>\n"
  "  <h1>503</h1>\n"
  "  <p>Server is temporarily at capacity.<br>Please try again shortly.</p>\n"
  "</body>\n"
  "</html>\n";

static const size_t valk_http_default_503_html_len = sizeof(valk_http_default_503_html) - 1;

// Thread-local body source for overload responses (event loop is single-threaded)
static _Thread_local http_body_source_t __overload_body_src;

static nghttp2_ssize __http_byte_body_cb(nghttp2_session *session,
                                         int32_t stream_id, uint8_t *buf,
                                         size_t length, uint32_t *data_flags,
                                         nghttp2_data_source *source,
                                         void *user_data) {
  UNUSED(session);
  UNUSED(stream_id);
  UNUSED(user_data);

  http_body_source_t *src = (http_body_source_t *)source->ptr;
  size_t remaining = src->body_len - src->offset;

  // Calculate how much to copy this chunk (min of remaining and buffer size)
  size_t to_copy = remaining < length ? remaining : length;

  // Copy the chunk
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memcpy(buf, src->body + src->offset, to_copy);
  src->offset += to_copy;

  // Mark EOF only when we've sent everything
  if (src->offset >= src->body_len) {
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
  }

  return (nghttp2_ssize)to_copy;
}

static int __demo_response(nghttp2_session *session, int stream_id) {
  /* Prepare some pseudo-headers: */
  const nghttp2_nv response_headers[] = {
      MAKE_NV2(":status", "200"),
      MAKE_NV2("content-type", "text/html; charset=utf-8"),
  };

  /* Allocate body source struct (static since this is a demo) */
  static http_body_source_t body_src;
  body_src.body = VALK_HTTP_MOTD;
  body_src.body_len = strlen(VALK_HTTP_MOTD);
  body_src.offset = 0;

  /* Send DATA frame */
  nghttp2_data_provider2 data_prd;
  data_prd.source.ptr = &body_src;
  data_prd.read_callback = __http_byte_body_cb;

  return nghttp2_submit_response2(
      session, stream_id, response_headers,
      sizeof(response_headers) / sizeof(response_headers[0]), &data_prd);
}

// Forward declaration for server config access
static int __http_send_overload_response(nghttp2_session *session,
                                          int32_t stream_id,
                                          valk_aio_http_conn *conn);

// Send HTTP 503 response for overload conditions
// Uses thread-local storage for body source (safe - event loop is single-threaded)
static int __http_send_overload_response(nghttp2_session *session,
                                          int32_t stream_id,
                                          valk_aio_http_conn *conn) {
  const char* body;
  size_t body_len;

  // Use pre-rendered custom body if available, otherwise default
  if (conn->server->config.error_503_body) {
    body = conn->server->config.error_503_body;
    body_len = conn->server->config.error_503_body_len;
  } else {
    body = valk_http_default_503_html;
    body_len = valk_http_default_503_html_len;
  }

  // Setup thread-local body source
  __overload_body_src.body = body;
  __overload_body_src.body_len = body_len;
  __overload_body_src.offset = 0;

  // Build response headers (stack allocation OK - nghttp2 copies them)
  nghttp2_nv headers[] = {
    MAKE_NV2(":status", "503"),
    MAKE_NV2("content-type", "text/html; charset=utf-8"),
    MAKE_NV2("retry-after", "1"),
  };

  // Submit response using nghttp2_data_provider2 (modern API)
  nghttp2_data_provider2 data_prd = {
    .source.ptr = &__overload_body_src,
    .read_callback = __http_byte_body_cb,
  };

  return nghttp2_submit_response2(session, stream_id, headers,
                                   sizeof(headers) / sizeof(headers[0]), &data_prd);
}

// Extract value for a keyword from qexpr like {:key "value" ...}
static valk_lval_t* __http_qexpr_get(valk_lval_t* qexpr, const char* key) {
  if (LVAL_TYPE(qexpr) != LVAL_QEXPR && LVAL_TYPE(qexpr) != LVAL_CONS) {
    return NULL;
  }

  // Iterate through the qexpr looking for the keyword
  valk_lval_t* curr = qexpr;
  while (!valk_lval_list_is_empty(curr)) {
    valk_lval_t* k = valk_lval_head(curr);
    curr = valk_lval_tail(curr);

    if (valk_lval_list_is_empty(curr)) break;

    valk_lval_t* v = valk_lval_head(curr);
    curr = valk_lval_tail(curr);

    // Check if key matches
    if (LVAL_TYPE(k) == LVAL_SYM && strcmp(k->str, key) == 0) {
      return v;
    }
  }

  return NULL;
}

// Send HTTP/2 response from Lisp qexpr {:status "200" :body "..." :headers {...}}
static int __http_send_response(nghttp2_session *session, int stream_id,
                                 valk_lval_t* response_qexpr, valk_mem_arena_t* arena) {
  // Extract status (default "200")
  const char* status = "200";
  valk_lval_t* status_val = __http_qexpr_get(response_qexpr, ":status");
  if (status_val && LVAL_TYPE(status_val) == LVAL_STR) {
    status = status_val->str;
  }

  // Extract body (default "")
  // For large bodies, we reference the original string directly instead of copying
  // to avoid arena overflow. The string is safe because the handler's return value
  // keeps it referenced in the GC heap for the duration of the response.
  const char* body = "";
  size_t body_len = 0;
  valk_lval_t* body_val = __http_qexpr_get(response_qexpr, ":body");
  if (body_val && LVAL_TYPE(body_val) == LVAL_STR) {
    body_len = strlen(body_val->str);
    // For bodies larger than 1MB, don't copy - reference directly from GC heap
    // This avoids arena overflow for large responses
    if (body_len > 1024 * 1024) {
      body = body_val->str;
    } else {
      // Small bodies: copy to arena so they remain valid when body callback is invoked
      VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
        char* body_copy = valk_mem_alloc(body_len + 1);
        memcpy(body_copy, body_val->str, body_len + 1);
        body = body_copy;
      }
    }
  }

#ifdef VALK_METRICS_ENABLED
  // Track bytes sent and status code for metrics
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (req) {
    req->bytes_sent = body_len;
    // Parse status code from string
    req->status_code = atoi(status);
  }
#endif

  // Extract content-type (default "text/plain; charset=utf-8")
  const char* content_type = "text/plain; charset=utf-8";
  valk_lval_t* ct_val = __http_qexpr_get(response_qexpr, ":content-type");
  if (ct_val && LVAL_TYPE(ct_val) == LVAL_STR) {
    content_type = ct_val->str;
  }

  // Build response headers on arena
  nghttp2_nv* headers;
  size_t header_count = 2; // :status and content-type

  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    headers = valk_mem_alloc(sizeof(nghttp2_nv) * header_count);
    headers[0] = (nghttp2_nv)MAKE_NV(":status", status, strlen(status));
    headers[1] = (nghttp2_nv)MAKE_NV("content-type", content_type, strlen(content_type));
  }

  // Setup data provider for body with streaming state
  http_body_source_t *body_src;
  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    body_src = valk_mem_alloc(sizeof(http_body_source_t));
    body_src->body = body;
    body_src->body_len = body_len;
    body_src->offset = 0;
  }

  nghttp2_data_provider2 data_prd;
  data_prd.source.ptr = (void*)body_src;
  data_prd.read_callback = __http_byte_body_cb;

  return nghttp2_submit_response2(session, stream_id, headers, header_count, &data_prd);
}

// Build Lisp qexpr from HTTP/2 request (on arena)
// Returns qexpr like: {:method "GET" :path "/" :headers {{name value}...} :body ""}
static valk_lval_t* __http_build_request_qexpr(valk_http2_server_request_t *req) {
  valk_lval_t *qexpr;

  VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
    // Build headers list (in reverse order, will be reversed by qcons)
    valk_lval_t *headers_list = valk_lval_nil();
    for (size_t i = req->headers.count; i > 0; i--) {
      valk_lval_t *pair_items[2] = {
        valk_lval_str((char*)req->headers.items[i-1].name),
        valk_lval_str((char*)req->headers.items[i-1].value)
      };
      valk_lval_t *pair = valk_lval_qlist(pair_items, 2);
      headers_list = valk_lval_qcons(pair, headers_list);
    }

    // Build main qexpr {... } in correct order
    valk_lval_t *items[8];
    size_t item_count = 0;

    // Add method and value
    items[item_count++] = valk_lval_sym(":method");
    items[item_count++] = valk_lval_str(req->method ? req->method : "GET");

    // Add path and value
    items[item_count++] = valk_lval_sym(":path");
    items[item_count++] = valk_lval_str(req->path ? req->path : "/");

    // Add authority if present
    if (req->authority) {
      items[item_count++] = valk_lval_sym(":authority");
      items[item_count++] = valk_lval_str(req->authority);
    }

    // Add headers and list
    items[item_count++] = valk_lval_sym(":headers");
    items[item_count++] = headers_list;

    // Add :body and value
    // items[item_count++] = valk_lval_sym(":body");
    // items[item_count++] = valk_lval_str(req->body && req->bodyLen > 0 ? (char*)req->body : "");

    qexpr = valk_lval_qlist(items, item_count);
  }

  return qexpr;
}

/* Called when a stream is closed (server-side).
 * Release per-stream arena immediately for instant memory reclamation.
 */
static int __http_server_on_stream_close_callback(nghttp2_session *session,
                                                  int32_t stream_id,
                                                  uint32_t error_code,
                                                  void *user_data) {
  UNUSED(error_code);
  valk_aio_http_conn *conn = (valk_aio_http_conn *)user_data;

  // Get request data to access stream arena
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data(session, stream_id);

  if (req && req->arena_slab_item) {
#ifdef VALK_METRICS_ENABLED
    // Record stream end metrics (old system)
    uint64_t end_time_us = uv_hrtime() / 1000;
    uint64_t duration_us = end_time_us - req->start_time_us;
    bool is_error = (error_code != NGHTTP2_NO_ERROR);
    // Add body length to bytes_recv (headers already tracked in on_header callback)
    uint64_t bytes_recv = req->bytes_recv + req->bodyLen;
    valk_aio_metrics_on_stream_end(&conn->server->sys->metrics, is_error,
                                     duration_us, req->bytes_sent, bytes_recv);

    // Record metrics with new system
    valk_server_metrics_t* m = &conn->server->metrics;

    // Increment total requests counter
    valk_counter_inc(m->requests_total);

    // Increment status-specific counter
    int status = req->status_code;
    if (status >= 200 && status < 300) {
      valk_counter_inc(m->requests_success);
    } else if (status >= 400 && status < 500) {
      valk_counter_inc(m->requests_client_error);
    } else if (status >= 500) {
      valk_counter_inc(m->requests_server_error);
    }

    // Record request duration
    double duration_sec = (double)duration_us / 1e6;
    valk_histogram_observe(m->request_duration, duration_sec);

    // Record bytes sent and received
    valk_counter_add(m->bytes_sent, req->bytes_sent);
    valk_counter_add(m->bytes_recv, bytes_recv);
#endif

    // Release stream arena back to slab (instant cleanup)
#ifdef VALK_METRICS_ENABLED
    valk_aio_system_stats_on_arena_release(&conn->server->sys->system_stats);
#endif
    valk_slab_release(conn->server->sys->httpStreamArenas, req->arena_slab_item);
    VALK_DEBUG("Stream %d closed, arena released", stream_id);
  }

  conn->active_streams--;
  VALK_DEBUG("%d active streams remaining", conn->active_streams);

  return 0;
}

/* Called when a frame is fully received. For a request, we might respond here.
 */
static int __http_on_frame_recv_callback(nghttp2_session *session,
                                         const nghttp2_frame *frame,
                                         void *user_data) {
  valk_aio_http_conn *conn = (valk_aio_http_conn *)user_data;

  if (frame->hd.type == NGHTTP2_GOAWAY) {
    VALK_DEBUG("Received GO AWAY frame");
    return 0;
  }

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    VALK_DEBUG(">>> Received complete HTTP/2 request (stream_id=%d)", frame->hd.stream_id);

    // Get request data attached to this stream
    valk_http2_server_request_t *req =
        nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

    if (!req) {
      VALK_WARN("No request data for stream %d", frame->hd.stream_id);
      return 0;
    }

    // Check if there's a Lisp handler
    if (conn->server && conn->server->lisp_handler_fn) {
      // Build request qexpr on stream arena
      valk_lval_t *arena_qexpr = __http_build_request_qexpr(req);

      // Call handler: (handler request)
      // Use pre-created sandbox env (shadows 'def') and stream arena for allocations
      valk_lval_t *handler = conn->server->lisp_handler_fn;
      valk_lenv_t *sandbox_env = conn->server->sandbox_env;
      valk_lval_t *response;

      // Set up request context for aio/delay
      valk_http_request_ctx_t req_ctx = {
        .session = session,
        .stream_id = frame->hd.stream_id,
        .conn = conn,
        .req = req,
        .env = sandbox_env
      };
      current_request_ctx = &req_ctx;

      VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
        valk_lval_t *args = valk_lval_cons(arena_qexpr, valk_lval_nil());
        response = valk_lval_eval_call(sandbox_env, handler, args);
      }

      // Clear request context
      current_request_ctx = NULL;

      // Check for deferred response (aio/delay was called - legacy pattern)
      if (LVAL_TYPE(response) == LVAL_SYM && strcmp(response->str, ":deferred") == 0) {
        // Response will be sent later by timer callback
        // Don't release stream arena yet - it's owned by the timer
        return 0;
      }

      // Check for LVAL_HANDLE return (new async pattern)
      // When handler returns a handle, we wait for it to complete
      if (LVAL_TYPE(response) == LVAL_HANDLE) {
        valk_async_handle_t *handle = response->async.handle;

        // Store HTTP context in the handle for sending response when complete
        handle->session = session;
        handle->stream_id = frame->hd.stream_id;
        handle->conn = conn;
        handle->stream_arena = (struct valk_mem_arena*)req->stream_arena;
        handle->env = sandbox_env;

        // If handle is already completed, send response immediately
        if (handle->status == VALK_ASYNC_COMPLETED) {
          valk_lval_t *result = handle->result;
          if (LVAL_TYPE(result) == LVAL_ERR) {
            VALK_WARN("Handle completed with error: %s", result->str);
            VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
              valk_lval_t* error_items[] = {
                valk_lval_sym(":status"), valk_lval_str("500"),
                valk_lval_sym(":body"), valk_lval_str(result->str)
              };
              valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
              __http_send_response(session, frame->hd.stream_id, error_resp, req->stream_arena);
            }
          } else {
            __http_send_response(session, frame->hd.stream_id, result, req->stream_arena);
          }
        } else if (handle->status == VALK_ASYNC_FAILED) {
          // Handle failed - send error response
          valk_lval_t *err = handle->error ? handle->error : valk_lval_err("Handle failed");
          VALK_WARN("Handle failed: %s", LVAL_TYPE(err) == LVAL_ERR ? err->str : "unknown error");
          VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
            const char *err_msg = LVAL_TYPE(err) == LVAL_ERR ? err->str : "Async operation failed";
            valk_lval_t* error_items[] = {
              valk_lval_sym(":status"), valk_lval_str("500"),
              valk_lval_sym(":body"), valk_lval_str(err_msg)
            };
            valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
            __http_send_response(session, frame->hd.stream_id, error_resp, req->stream_arena);
          }
        } else if (handle->status == VALK_ASYNC_CANCELLED) {
          // Handle was cancelled - don't send response (client likely disconnected)
          VALK_DEBUG("Handle cancelled, not sending response for stream %d", frame->hd.stream_id);
        } else {
          // Handle is still running - response will be sent when it completes
          // The completion callback will use the stored context to send response
          VALK_DEBUG("Handle pending/running, will send response when complete");
          return 0;  // Don't release arena yet
        }
        return 0;
      }

      // Send response based on handler result
      if (LVAL_TYPE(response) == LVAL_ERR) {
        VALK_WARN("Handler returned error: %s", response->str);
        // Send 500 error response
        VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
          valk_lval_t* error_items[] = {
            valk_lval_sym(":status"), valk_lval_str("500"),
            valk_lval_sym(":body"), valk_lval_str(response->str)
          };
          valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
          __http_send_response(session, frame->hd.stream_id, error_resp, req->stream_arena);
        }
      } else {
        // Send handler's response
        __http_send_response(session, frame->hd.stream_id, response, req->stream_arena);
      }
    } else {
      // Fall back to demo response
      VALK_DEBUG("No Lisp handler, using demo response");
      __demo_response(session, frame->hd.stream_id);
    }
  }

  return 0;
}

// Simple no-op callbacks for demo handler
static void __demo_on_connect(void *arg, valk_aio_http_conn *conn) {
  UNUSED(arg);
  UNUSED(conn);
}

static void __demo_on_disconnect(void *arg, valk_aio_http_conn *conn) {
  UNUSED(arg);
  UNUSED(conn);
}

static void __demo_on_header(void *arg, valk_aio_http_conn *conn, size_t stream,
                             char *name, char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

static void __demo_on_body(void *arg, valk_aio_http_conn *conn, size_t stream,
                           uint8_t flags, valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}

// Export a demo handler for testing
valk_http2_handler_t *valk_aio_http2_demo_handler(void) {
  static valk_http2_handler_t handler;
  static int initialized = 0;
  if (!initialized) {
    handler.arg = NULL;
    handler.onConnect = __demo_on_connect;
    handler.onDisconnect = __demo_on_disconnect;
    handler.onHeader = __demo_on_header;
    handler.onBody = __demo_on_body;
    initialized = 1;
  }
  return &handler;
}

// Returns true if there's more data pending to send (buffer was full)
static int __http2_flush_frames(valk_buffer_t *buf,
                                struct valk_aio_http_conn *conn) {
  const uint8_t *data;
  int has_pending = 0;

  // First, drain any spillover data from previous call
  if (conn->spillover_data && conn->spillover_len > 0) {
    size_t to_copy = conn->spillover_len;
    if (buf->count + to_copy > buf->capacity) {
      to_copy = buf->capacity - buf->count;
    }
    if (to_copy > 0) {
      valk_buffer_append(buf, conn->spillover_data, to_copy);
      if (to_copy < conn->spillover_len) {
        // Still have spillover remaining, shift it
        memmove(conn->spillover_data, conn->spillover_data + to_copy,
                conn->spillover_len - to_copy);
        conn->spillover_len -= to_copy;
        has_pending = 1;
        conn->pending_write = has_pending;
        return has_pending;
      } else {
        // Spillover fully consumed
        free(conn->spillover_data);
        conn->spillover_data = NULL;
        conn->spillover_len = 0;
      }
    } else {
      // Buffer already full
      has_pending = 1;
      conn->pending_write = has_pending;
      return has_pending;
    }
  }

  int len = 0;
  do {
    len = nghttp2_session_mem_send2(conn->session, &data);
    if (len < 0) {
      VALK_ERROR("nghttp2_session_mem_send2 error: %s", nghttp2_strerror((int)len));
    } else if (len) {
      // Check if we would overflow before appending
      if ((buf->count + (size_t)len) >= buf->capacity) {
        // Buffer full - store unconsumed data in spillover buffer
        // nghttp2 data pointer is only valid until next call, so we MUST copy it
        has_pending = 1;
        conn->spillover_data = malloc(len);
        if (conn->spillover_data) {
          memcpy(conn->spillover_data, data, len);
          conn->spillover_len = len;
          VALK_TRACE("Buffer full, saved %d bytes to spillover", len);
        } else {
          VALK_ERROR("Failed to allocate spillover buffer for %d bytes", len);
        }
        break;
      }

      valk_buffer_append(buf, (void *)data, len);

      VALK_TRACE("Buffered frame len=%ld count=%ld capacity=%ld", (long)len,
                 (long)buf->count, (long)buf->capacity);
    } else {
      VALK_TRACE("No data to send");
    }
  } while (len > 0);

  // Update connection's pending_write flag
  conn->pending_write = has_pending;
  return has_pending;
}

// Continue sending pending HTTP/2 frames after a write completes
// This is called from the write callback when there's more data to send
static void __http_continue_pending_send(struct valk_aio_http_conn *conn) {
  if (!conn || !conn->session || !SSL_is_init_finished(conn->ssl.ssl)) {
    return;
  }

  // Check if connection is closing
  if (uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
    return;
  }

  // Create buffers for frame data - use same size as main path
  char buf[HTTP_SLAB_ITEM_SIZE];
  memset(buf, 0, sizeof(buf));
  valk_buffer_t In = {
      .items = buf, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  valk_slab_item_t *slabItemRaw = valk_slab_aquire(tcp_buffer_slab);
  if (!slabItemRaw) {
    VALK_ERROR("TCP buffer slab exhausted in continue_pending_send");
    return;
  }
  __tcp_buffer_slab_item_t *slabItem = (void *)slabItemRaw->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  // Flush pending frames
  __http2_flush_frames(&In, conn);

  // Loop to handle all pending data (matches main path pattern)
  while (In.count > 0) {
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);

    if (Out.count > 0) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;
      slabItem->conn = conn;

      VALK_TRACE("Continuation send: %ld bytes (remaining: %zu, pending: %d)",
                 Out.count, In.count, conn->pending_write);
      uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
               &slabItem->buf, 1, __http_tcp_on_write_cb);

      // If there's more data to encrypt, get a new buffer
      if (In.count > 0) {
        valk_slab_item_t *newSlabRaw = valk_slab_aquire(tcp_buffer_slab);
        if (!newSlabRaw) {
          VALK_ERROR("TCP buffer slab exhausted in continue_pending_send loop");
          break;
        }
        slabItem = (void *)newSlabRaw->data;
        Out = (valk_buffer_t){
            .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};
      } else {
        slabItem = NULL;  // Mark as used
      }
    } else {
      VALK_WARN("SSL encrypt produced no output with %zu bytes remaining", In.count);
      break;
    }
  }

  // Final SSL flush - get any remaining encrypted data from BIO
  if (slabItem != NULL && In.count == 0) {
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);
    if (Out.count > 0) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;
      slabItem->conn = conn;
      VALK_TRACE("Final continuation flush: %ld bytes", Out.count);
      uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
               &slabItem->buf, 1, __http_tcp_on_write_cb);
      slabItem = NULL;
    }
  }

  // Release unused slab item if we didn't send anything
  if (slabItem != NULL) {
    valk_slab_release_ptr(tcp_buffer_slab, slabItem);
  }
}

static void __http_tcp_unencrypted_read_cb(void *arg,
                                           const valk_buffer_t *buf) {
  struct valk_aio_http_conn *conn = arg;

  // Feed data to nghttp2
  ssize_t rv = nghttp2_session_mem_recv2(
      conn->session, (const uint8_t *)buf->items, buf->count);
  if (rv < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("nghttp2_session_mem_recv error: %zd", rv);
    if (!uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
      conn->state = VALK_CONN_CLOSING;
      uv_close((uv_handle_t *)&conn->handle->uv.tcp, __uv_handle_closed_cb);
    }
  }
}

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf) {
  valk_aio_handle_t *hndl = stream->data;
  struct valk_aio_http_conn *conn = hndl->arg;

  // Early exit if connection is closing or closed - prevent use-after-free
  if (conn->state == VALK_CONN_CLOSING || conn->state == VALK_CONN_CLOSED) {
    valk_slab_release_ptr(tcp_buffer_slab, buf->base);
    return;
  }

  if (nread < 0) {
    bool is_eof = (nread == UV_EOF);

    if (is_eof && conn->ssl.ssl) {
      // Check for pending data in SSL before we do anything
      int ssl_pending = SSL_pending(conn->ssl.ssl);
      int bio_pending = (int)BIO_ctrl_pending(conn->ssl.read_bio);
      UNUSED(ssl_pending);
      UNUSED(bio_pending);
      // CRITICAL: Process any pending data in SSL BIO before closing
      // The final TLS close_notify alert may be waiting in the BIO
      valk_buffer_t In = {
          .items = buf->base,
          .count = 0,  // No new TCP data, but SSL BIO may have pending data
          .capacity = HTTP_SLAB_ITEM_SIZE
      };

      valk_slab_item_t *slabItemRaw = valk_slab_aquire(tcp_buffer_slab);
      if (!slabItemRaw) {
        VALK_ERROR("TCP buffer slab exhausted in EOF handling");
        valk_slab_release_ptr(tcp_buffer_slab, buf->base);
        return;
      }
      __tcp_buffer_slab_item_t *slabItem = (void *)slabItemRaw->data;

      valk_buffer_t Out = {
          .items = slabItem->data,
          .count = 0,
          .capacity = HTTP_SLAB_ITEM_SIZE
      };

      // Process pending SSL data (close_notify, final records, etc.)
      int ssl_err = valk_aio_ssl_on_read(&conn->ssl, &In, &Out, conn,
                                         __http_tcp_unencrypted_read_cb);

      // Send any pending encrypted response data
      if (!ssl_err && Out.count > 0) {
        slabItem->buf.base = Out.items;
        slabItem->buf.len = Out.count;
        slabItem->conn = conn;

        VALK_TRACE("Sending %ld bytes on EOF", Out.count);
        uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
                 &slabItem->buf, 1, __http_tcp_on_write_cb);
      } else {
        valk_slab_release_ptr(tcp_buffer_slab, slabItem);
      }
    }

    // Close the connection
    if (!uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
      conn->state = VALK_CONN_CLOSING;
      uv_close((uv_handle_t *)&conn->handle->uv.tcp, __uv_handle_closed_cb);
    }

    // Release the input buffer from alloc_callback (may be NULL if alloc failed)
    if (buf->base) {
      valk_slab_release_ptr(tcp_buffer_slab, buf->base);
    }
    return;
  }

  VALK_TRACE("Feeding data to OpenSSL %ld", nread);

  valk_buffer_t In = {
      .items = buf->base, .count = nread, .capacity = HTTP_SLAB_ITEM_SIZE};

  valk_slab_item_t *slabItemRaw = valk_slab_aquire(tcp_buffer_slab);
  if (!slabItemRaw) {
    // Apply backpressure: stop reading from this connection until buffers free up
    // This propagates TCP flow control to the client, slowing them down
    VALK_WARN("TCP buffer slab exhausted - applying backpressure on connection");

    // CRITICAL: Feed the incoming data to OpenSSL's BIO before stopping reads.
    // The BIO will buffer this data, preserving SSL record boundaries.
    // Without this, we'd drop encrypted bytes mid-record causing "bad record mac" errors.
    int n = BIO_write(conn->ssl.read_bio, buf->base, nread);
    if (n != nread) {
      VALK_ERROR("BIO_write during backpressure failed: wrote %d of %ld", n, nread);
    }

    uv_read_stop((uv_stream_t *)&conn->handle->uv.tcp);
    __backpressure_list_add(conn);

    // Start timer to periodically check for recovery
    __backpressure_timer_start(conn->handle->uv.tcp.loop);

#ifdef VALK_METRICS_ENABLED
    atomic_fetch_add(&conn->server->sys->system_stats.tcp_buffer_overflow, 1);
#endif

    valk_slab_release_ptr(tcp_buffer_slab, buf->base);
    // Try to resume another connection since we just freed a buffer
    __backpressure_try_resume_one();
    return;
  }
  __tcp_buffer_slab_item_t *slabItem = (void *)slabItemRaw->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  int err = valk_aio_ssl_on_read(&conn->ssl, &In, &Out, conn,
                                 __http_tcp_unencrypted_read_cb);

  // Only do this if ssl is established:
  if (!err) {
    // Mark connection as established once SSL handshake is complete
    if (conn->state == VALK_CONN_INIT && SSL_is_init_finished(conn->ssl.ssl)) {
      conn->state = VALK_CONN_ESTABLISHED;
    }
    // Flushies
    In.count = 0;
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memset(In.items, 0, In.capacity);
    __http2_flush_frames(&In, conn);

    // Encrypt the new data n stuff - loop to handle large responses
    // that may need multiple buffers
    while (In.count > 0) {
      valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);

      if (Out.count > 0) {
        slabItem->buf.base = Out.items;
        slabItem->buf.len = Out.count;
        slabItem->conn = conn;  // Store connection for continuation

        VALK_TRACE("Sending %ld bytes (remaining: %zu)", Out.count, In.count);
        uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
                 &slabItem->buf, 1, __http_tcp_on_write_cb);

        // If there's more data to encrypt, get a new buffer
        if (In.count > 0) {
          valk_slab_item_t *newSlabRaw = valk_slab_aquire(tcp_buffer_slab);
          if (!newSlabRaw) {
            VALK_ERROR("TCP buffer slab exhausted in encrypt loop");
            break;
          }
          slabItem = (void *)newSlabRaw->data;
          Out = (valk_buffer_t){
              .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};
        } else {
          // All data sent, mark slabItem as used
          slabItem = NULL;
        }
      } else {
        // No output but still have input - shouldn't happen, break to avoid infinite loop
        VALK_WARN("SSL encrypt produced no output with %zu bytes remaining", In.count);
        break;
      }
    }

    // Handle final encryption if we haven't sent anything yet
    if (slabItem != NULL && In.count == 0) {
      valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);
    }
  }

  int wantToSend = slabItem != NULL && Out.count > 0;
  if (wantToSend) {
    slabItem->buf.base = Out.items;
    slabItem->buf.len = Out.count;
    slabItem->conn = conn;  // Store connection for continuation

    VALK_TRACE("Sending final %ld bytes", Out.count);
    uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
             &slabItem->buf, 1, __http_tcp_on_write_cb);
  } else if (slabItem != NULL) {
    VALK_TRACE("Nothing to send: %d", wantToSend);
    valk_slab_release_ptr(tcp_buffer_slab, slabItem);
  }

  valk_slab_release_ptr(tcp_buffer_slab, In.items);
}

static int __http_send_server_connection_header(nghttp2_session *session, valk_aio_system_t *sys) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, sys->config.max_concurrent_streams}};
  int rv;

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  if (rv != 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

static int __http_send_client_connection_header(nghttp2_session *session, valk_aio_system_t *sys) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, sys->config.max_concurrent_streams}};
  int rv;
  VALK_DEBUG("[http2 Client] Sending connection frame");

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  if (rv != 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

// Close callback for load-shed rejected connections
static void __load_shed_close_cb(uv_handle_t *handle) {
  free(handle);
}

static void __http_server_accept_cb(uv_stream_t *stream, int status) {
  if (status < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "New connection error %s\n", uv_strerror(status));
    // error!
    return;
  }

  valk_aio_handle_t *hndl = stream->data;
  valk_aio_http_server *srv = hndl->arg;

  // Load shedding: check buffer pool usage before accepting
  size_t available = valk_slab_available(tcp_buffer_slab);
  size_t total = tcp_buffer_slab->numItems;
  float usage = 1.0f - ((float)available / total);

  // Get watermarks from config (use defaults if zero)
  float high_watermark = srv->sys->config.buffer_high_watermark;
  float critical_watermark = srv->sys->config.buffer_critical_watermark;
  if (high_watermark <= 0.0f) high_watermark = 0.85f;
  if (critical_watermark <= 0.0f) critical_watermark = 0.95f;

  // Critical: reject all new connections
  if (usage >= critical_watermark) {
    VALK_WARN("Load shedding: rejecting connection (buffer usage %.1f%% >= critical %.1f%%)",
              usage * 100, critical_watermark * 100);
#ifdef VALK_METRICS_ENABLED
    atomic_fetch_add(&srv->sys->system_stats.connections_rejected_load, 1);
#endif
    // Accept and immediately close to reject the connection
    // Must heap-allocate because uv_close is async
    uv_tcp_t *reject_tcp = malloc(sizeof(uv_tcp_t));
    if (reject_tcp) {
      uv_tcp_init(stream->loop, reject_tcp);
      if (uv_accept(stream, (uv_stream_t *)reject_tcp) == 0) {
        uv_close((uv_handle_t *)reject_tcp, __load_shed_close_cb);
      } else {
        free(reject_tcp);
      }
    }
    return;
  }

  // High watermark: probabilistic load shedding
  if (usage >= high_watermark) {
    // Linear probability from 0% at high_watermark to 100% at critical_watermark
    float shed_probability = (usage - high_watermark) / (critical_watermark - high_watermark);
    float random_val = (float)rand() / (float)RAND_MAX;
    if (random_val < shed_probability) {
      VALK_WARN("Load shedding: probabilistically rejecting connection (buffer usage %.1f%%, p=%.2f)",
                usage * 100, shed_probability);
#ifdef VALK_METRICS_ENABLED
      atomic_fetch_add(&srv->sys->system_stats.connections_rejected_load, 1);
#endif
      uv_tcp_t *reject_tcp = malloc(sizeof(uv_tcp_t));
      if (reject_tcp) {
        uv_tcp_init(stream->loop, reject_tcp);
        if (uv_accept(stream, (uv_stream_t *)reject_tcp) == 0) {
          uv_close((uv_handle_t *)reject_tcp, __load_shed_close_cb);
        } else {
          free(reject_tcp);
        }
      }
      return;
    }
  }

  struct valk_aio_http_conn *conn = malloc(sizeof(struct valk_aio_http_conn));
  if (!conn) {
    VALK_ERROR("Failed to allocate connection");
    return;
  }
  memset(conn, 0, sizeof(struct valk_aio_http_conn));
  conn->state = VALK_CONN_INIT;
  conn->server = srv;

  conn->handle =
      (valk_aio_handle_t *)valk_slab_aquire(srv->sys->handleSlab)->data;
  memset(conn->handle, 0, sizeof(valk_aio_handle_t));

  conn->handle->kind = VALK_HNDL_TCP;
  conn->handle->sys = srv->sys;
  conn->handle->arg = conn;
  // conn->handle->onClose = nullptr;
  conn->handle->onClose = __valk_aio_http2_on_disconnect;
  conn->handle->uv.tcp.data = conn->handle;

  conn->httpHandler = &srv->handler;

  valk_dll_insert_after(&srv->sys->liveHandles, conn->handle);

  uv_tcp_init(stream->loop, &conn->handle->uv.tcp);

  // dont need for now because we are using nghttp2 mem buffer for send
  // conn->send_buf.base = valk_mem_alloc(MAX_SEND_BYTES);
  int res = uv_accept(stream, (uv_stream_t *)&conn->handle->uv.tcp);

  if (!res) {
    // Get the client IP address
    struct sockaddr_storage client_addr;
    int addr_len = sizeof(client_addr);

    if (uv_tcp_getpeername(&conn->handle->uv.tcp,
                           (struct sockaddr *)&client_addr, &addr_len) == 0) {
      char ip[INET6_ADDRSTRLEN];
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      memset(ip, 0, sizeof(ip));
      uint16_t port = 0;
      if (client_addr.ss_family == AF_INET) {
        // IPv4
        struct sockaddr_in *addr4 = (struct sockaddr_in *)&client_addr;
        uv_ip4_name(addr4, ip, sizeof(ip));
        port = ntohs(addr4->sin_port);
      } else if (client_addr.ss_family == AF_INET6) {
        // IPv6
        struct sockaddr_in6 *addr6 = (struct sockaddr_in6 *)&client_addr;
        uv_ip6_name(addr6, ip, sizeof(ip));
        port = ntohs(addr6->sin6_port);
      }

      VALK_INFO("Accepted connection from %s:%d", ip, port);
    } else {
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      VALK_WARN("Could not get peer name");
    };

    static nghttp2_session_callbacks *callbacks = nullptr;
    if (!callbacks) {
      nghttp2_session_callbacks_new(&callbacks);
      nghttp2_session_callbacks_set_on_begin_headers_callback(
          callbacks, __http_on_begin_headers_callback);
      nghttp2_session_callbacks_set_on_header_callback(
          callbacks, __http_on_header_callback);
      nghttp2_session_callbacks_set_on_frame_recv_callback(
          callbacks, __http_on_frame_recv_callback);
      nghttp2_session_callbacks_set_on_stream_close_callback(
          callbacks, __http_server_on_stream_close_callback);
    }

    nghttp2_session_server_new3(&conn->session, callbacks, conn, nullptr,
                                nullptr);
    valk_aio_ssl_accept(&conn->ssl, srv->ssl_ctx);

    // Send settings to the client
    __http_send_server_connection_header(conn->session, srv->sys);

    //  TODO(networking): Maybe i should call this on the first read?
    if (conn->httpHandler && conn->httpHandler->onConnect) {
      conn->httpHandler->onConnect(conn->httpHandler->arg, conn);
    }

#ifdef VALK_METRICS_ENABLED
    // Record successful connection (old metrics system)
    valk_aio_metrics_on_connection(&srv->sys->metrics, true);
    // Increment active connections gauge (new metrics system)
    valk_gauge_inc(srv->metrics.connections_active);
#endif

    // start the connection off by listening, (SSL expects client to send first)
    uv_read_start((uv_stream_t *)&conn->handle->uv.tcp, __alloc_callback,
                  __http_tcp_read_cb);
  } else {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_WARN("Accept error: %s", uv_strerror(res));

#ifdef VALK_METRICS_ENABLED
    // Record failed connection
    valk_aio_metrics_on_connection(&srv->sys->metrics, false);
#endif

    // Only close if not already closing
    if (!uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
      conn->state = VALK_CONN_CLOSING;
      uv_close((uv_handle_t *)&conn->handle->uv.tcp, __uv_handle_closed_cb);
    }
    free(conn);
  }
}
static void __http_shutdown_cb(valk_aio_handle_t *hndl) {
  UNUSED(hndl);
  VALK_INFO("TODO: shutdown the server cleanly");
}

static void __http_listen_cb(valk_aio_system_t *sys,
                             struct valk_aio_task_new *task) {
  int r;
  struct sockaddr_in addr;
  // We accept the transfer of ownership for box here
  // therefore we dont aquire it, but are responsible for releasing it
  valk_arc_box *box = task->arg;

  valk_aio_http_server *srv = box->item;
  // Initialize the listener handle
  srv->listener = (void *)valk_slab_aquire(sys->handleSlab)->data;

  memset(srv->listener, 0, sizeof(valk_aio_handle_t));
  srv->listener->kind = VALK_HNDL_TCP;
  srv->listener->sys = sys;
  srv->listener->arg = srv;
  srv->listener->onClose = __http_shutdown_cb;
  srv->listener->uv.tcp.data = srv->listener;

  r = uv_tcp_init(srv->sys->eventloop, &srv->listener->uv.tcp);
  uv_tcp_nodelay(&srv->listener->uv.tcp, 1);

  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Tcp init error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on TcpInit");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  r = uv_ip4_addr(srv->interface, srv->port, &addr);
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Get addr error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Addr");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }
#ifdef __linux__
  r = uv_tcp_bind(&srv->listener->uv.tcp, (const struct sockaddr *)&addr,
                  UV_TCP_REUSEPORT);
#else
  r = uv_tcp_bind(&srv->listener->uv.tcp, (const struct sockaddr *)&addr, 0);
#endif
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Bind error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Bind");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  r = uv_listen((uv_stream_t *)&srv->listener->uv.tcp, 128,
                __http_server_accept_cb);
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Listen error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Listening");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  VALK_INFO("Listening on %s:%d", srv->interface, srv->port);

#ifdef VALK_METRICS_ENABLED
  // Initialize server metrics
  server_metrics_init(&srv->metrics, srv->interface, srv->port);
  // Track server start in system stats
  valk_aio_system_stats_on_server_start(&sys->system_stats);
#endif

  valk_promise_respond(&task->promise, box);
  valk_dll_insert_after(&sys->liveHandles, srv->listener);
  valk_arc_release(box);
}

static int __alpn_select_proto_cb(SSL *ssl, const unsigned char **out,
                                  unsigned char *outlen,
                                  const unsigned char *in, unsigned int inlen,
                                  void *arg) {
  UNUSED(ssl);
  UNUSED(arg);

  int rv;
  rv = nghttp2_select_alpn(out, outlen, in, inlen);
  if (rv == -1) {
    return SSL_TLSEXT_ERR_NOACK;
  }
  return SSL_TLSEXT_ERR_OK;
}

static void __uv_task_close_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  valk_aio_task_new *task = hndl->arg;

  // Release the future reference held by the task
  valk_arc_release(task->promise.item);

  // Free using the original allocator captured at allocation time
  valk_mem_allocator_free(task->allocator, task);

  // Now release the handle
  valk_dll_pop(hndl);
  valk_slab_release_ptr(hndl->sys->handleSlab, hndl);
}

static void __uv_task_cb_new(uv_async_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  valk_aio_task_new *task = hndl->arg;

  task->callback(hndl->sys, task);

  // Close the UV handle - cleanup will happen in the close callback
  uv_close((uv_handle_t *)&hndl->uv.task, __uv_task_close_cb);
}

static void __uv_exec_task(valk_aio_system_t *sys, valk_aio_task_new *task) {
  valk_aio_handle_t *hndl =
      (valk_aio_handle_t *)valk_slab_aquire(sys->handleSlab)->data;
  memset(hndl, 0, sizeof(valk_aio_handle_t));
  hndl->kind = VALK_HNDL_TASK;
  hndl->sys = sys;
  hndl->arg = task;
  hndl->uv.task.data = hndl;

  uv_async_init(sys->eventloop, &hndl->uv.task, __uv_task_cb_new);
  valk_dll_insert_after(&sys->liveHandles, hndl);

  uv_async_send(&hndl->uv.task);
}

static void __valk_aio_http2_server_free(valk_arc_box *box) {
  printf("FREERDOM\n");
  valk_aio_http_server *srv = box->item;
#ifdef VALK_METRICS_ENABLED
  // Track server stop in system stats
  valk_aio_system_stats_on_server_stop(&srv->sys->system_stats);
#endif
  SSL_CTX_free(srv->ssl_ctx);
  valk_mem_allocator_free(box->allocator, box);
}

// static void __no_free(void *arg) { UNUSED(arg); }
valk_future *valk_aio_http2_listen(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler) {
  return valk_aio_http2_listen_with_config(sys, interface, port, keyfile, certfile,
                                            handler, lisp_handler, NULL);
}

// HTTP/2 server listen with configuration
valk_future *valk_aio_http2_listen_with_config(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler,
                                   valk_http_server_config_t *config) {
  valk_arc_box *box = (valk_arc_box *)valk_slab_aquire(sys->httpServers)->data;
  valk_future *res = valk_future_new();

  valk_aio_http_server *srv;
  {
    valk_arc_box_init(box, VALK_SUC, sizeof(valk_aio_http_server));

    box->allocator = (valk_mem_allocator_t *)sys->httpServers;
    box->free = __valk_aio_http2_server_free;

    srv = box->item;
    memset(srv, 0, sizeof(valk_aio_http_server));
    srv->sys = sys;

    strncpy(srv->interface, interface, 200);
    srv->port = port;
    if (handler) {
      srv->handler = *handler;
    }
    srv->lisp_handler_fn = (valk_lval_t*)lisp_handler;
    if (lisp_handler) {
      srv->sandbox_env = valk_lenv_sandboxed(((valk_lval_t*)lisp_handler)->fun.env);
    }

    // Apply config if provided, otherwise use defaults
    if (config) {
      srv->config = *config;
    } else {
      srv->config = valk_http_server_config_default();
    }

    valk_aio_ssl_server_init(&srv->ssl_ctx, keyfile, certfile);
    SSL_CTX_set_alpn_select_cb(srv->ssl_ctx, __alpn_select_proto_cb, NULL);
  }

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  task->arg = box;
  task->promise.item = res;
  valk_arc_retain(res);
  task->callback = __http_listen_cb;

  __uv_exec_task(sys, task);

  return res;
}

void valk_aio_http2_server_set_handler(valk_aio_http_server *srv, void *handler_fn) {
  srv->lisp_handler_fn = (valk_lval_t*)handler_fn;
  // Create sandbox env once - wraps handler's captured env to shadow 'def'
  if (handler_fn) {
    srv->sandbox_env = valk_lenv_sandboxed(((valk_lval_t*)handler_fn)->fun.env);
  }
}

//// HTTP2 CLIENT

typedef struct valk_aio_http2_client {
  valk_aio_system_t *sys;
  SSL_CTX *ssl_ctx;
  // TODO(networking):  connections could be pooled
  valk_aio_http_conn *connection;
  char interface[200];
  int port;
  // Hostname used for TLS SNI and HTTP/2 authority defaults
  char hostname[200];
  // Totally internal, totally unneccessary, but i wanna avoid a tuple
  valk_promise _promise;
} valk_aio_http2_client;

static int __http_client_on_frame_recv_callback(nghttp2_session *session,
                                                const nghttp2_frame *frame,
                                                void *user_data) {
  UNUSED(session);
  UNUSED(user_data);

  VALK_TRACE("on_recv callback");

  switch (frame->hd.type) {
    case NGHTTP2_HEADERS:
      break;
    case NGHTTP2_RST_STREAM:
      VALK_INFO("C <--- S (RST_STREAM) stream=%d error=%d", frame->hd.stream_id,
               frame->rst_stream.error_code);
      break;
    case NGHTTP2_GOAWAY:
      VALK_INFO("C <--- S (GOAWAY) %d", frame->hd.stream_id);
      VALK_INFO("Client received GOAWAY");
      break;
  }

  return 0;
}

static int __http_client_on_stream_close_callback(nghttp2_session *session,
                                                  int32_t stream_id,
                                                  uint32_t error_code,
                                                  void *user_data) {
  UNUSED(user_data);
  __http2_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (reqres) {
    if (error_code != NGHTTP2_NO_ERROR) {
      // Stream was reset or closed with an error - reject the promise
      char errmsg[256];
      snprintf(errmsg, sizeof(errmsg), "HTTP/2 stream error: %s (code=%u)",
               nghttp2_http2_strerror(error_code), error_code);
      valk_arc_box *err = valk_arc_box_err(errmsg);
      valk_promise_respond(&reqres->promise, err);
      valk_arc_release(err);
    } else {
      // Normal close - resolve with the response (even if no DATA arrived)
      valk_arc_box *box = reqres->res_box;
      valk_promise_respond(&reqres->promise, box);
    }
    valk_arc_release(reqres->promise.item);
    // Free the reqres struct itself
    valk_mem_free(reqres);
  }
  return 0;
}

static int __http_on_data_chunk_recv_callback(nghttp2_session *session,
                                              uint8_t flags, int32_t stream_id,
                                              const uint8_t *data, size_t len,
                                              void *user_data) {
  (void)flags;
  (void)user_data;

  __http2_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, stream_id);

  if (reqres) {
    VALK_INFO("C <--- S (DATA chunk) len=%lu", (unsigned long)len);
    size_t offset = reqres->res->bodyLen;
    VALK_ASSERT((offset + len) < reqres->res->bodyCapacity,
                "Response was too big %ld > %ld", offset + len,
                reqres->res->bodyCapacity);
    // Append into body buffer
    memcpy((char *)reqres->res->body + offset, data, len);
    reqres->res->bodyLen = offset + len;
    ((char *)reqres->res->body)[reqres->res->bodyLen] = '\0';
  }

  return 0;
}

static void __uv_http2_connect_cb(uv_connect_t *req, int status) {
  valk_arc_box *box = req->data;
  // TODO(networking): assert that its a succefull box
  valk_aio_http2_client *client = box->item;
  valk_arc_retain(box);

  if (status < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Client Connection err: %s\n", uv_strerror(status));
    valk_arc_box *err = valk_arc_box_err("Client Connection err");
    valk_promise_respond(&client->_promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }

  printf("Gurr we connected\n");

#ifdef VALK_METRICS_ENABLED
  // Initialize client connections gauge lazily
  if (!client_connections_active) {
    client_connections_active = valk_metric_gauge("http_connections_active",
      "role", "client", NULL);
  }
  valk_gauge_inc(client_connections_active);
#endif

  valk_slab_item_t *slabItemRaw = valk_slab_aquire(tcp_buffer_slab);
  if (!slabItemRaw) {
    VALK_ERROR("TCP buffer slab exhausted in client connect");
    return;
  }
  __tcp_buffer_slab_item_t *slabItem = (void *)slabItemRaw->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  static nghttp2_session_callbacks *callbacks = nullptr;
  if (!callbacks) {
    nghttp2_session_callbacks_new(&callbacks);
    /*

      nghttp2_session_callbacks_set_on_frame_recv_callback(callbacks,
                                                           on_frame_recv_callback);

      nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
        callbacks, on_data_chunk_recv_callback);

      nghttp2_session_callbacks_set_on_stream_close_callback(
        callbacks, on_stream_close_callback);

      nghttp2_session_callbacks_set_on_header_callback(callbacks,
                                                       on_header_callback);

      nghttp2_session_callbacks_set_on_begin_headers_callback(
        callbacks, on_begin_headers_callback);
          */

    // nghttp2_session_callbacks_set_on_begin_headers_callback(
    //     callbacks, __http_on_begin_headers_callback);
    nghttp2_session_callbacks_set_on_header_callback(
        callbacks, __http2_client_on_header_cb);
    nghttp2_session_callbacks_set_on_frame_recv_callback(
        callbacks, __http_client_on_frame_recv_callback);

    nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
        callbacks, __http_on_data_chunk_recv_callback);
    nghttp2_session_callbacks_set_on_stream_close_callback(
        callbacks, __http_client_on_stream_close_callback);
  }

  nghttp2_session_client_new(&client->connection->session, callbacks, client);

  __http_send_client_connection_header(client->connection->session, client->sys);

  valk_aio_ssl_client_init(&client->ssl_ctx);
  SSL_CTX_set_alpn_protos(client->ssl_ctx, (const unsigned char *)"\x02h2", 3);

  valk_aio_ssl_connect(&client->connection->ssl, client->ssl_ctx);
  const char *sni = (client->hostname[0] != '\0') ? client->hostname : "localhost";
  SSL_set_tlsext_host_name(client->connection->ssl.ssl, sni);

  valk_aio_ssl_handshake(&client->connection->ssl, &Out);

  int wantToSend = Out.count > 0;
  if (wantToSend) {
    slabItem->buf.base = Out.items;
    slabItem->buf.len = Out.count;

    printf("[Client] Sending %ld bytes\n", Out.count);
    uv_write(&slabItem->req, (uv_stream_t *)&client->connection->handle->uv.tcp,
             &slabItem->buf, 1, __http_tcp_on_write_cb);
  } else {
    valk_slab_release_ptr(tcp_buffer_slab, slabItem);
  }

  // After handshake, flush any pending HTTP/2 frames (client preface, SETTINGS,
  // or requests submitted before handshake completion).
  if (SSL_is_init_finished(client->connection->ssl.ssl)) {
    char inbuf[SSL3_RT_MAX_PACKET_SIZE];
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memset(inbuf, 0, sizeof(inbuf));
    valk_buffer_t In = {
        .items = inbuf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

    valk_slab_item_t *slab2Raw = valk_slab_aquire(tcp_buffer_slab);
    if (!slab2Raw) {
      VALK_ERROR("TCP buffer slab exhausted in client read flush");
      return;
    }
    __tcp_buffer_slab_item_t *slab2 = (void *)slab2Raw->data;
    valk_buffer_t Out2 = {.items = slab2->data,
                          .count = 0,
                          .capacity = SSL3_RT_MAX_PACKET_SIZE};

    __http2_flush_frames(&In, client->connection);
    valk_aio_ssl_encrypt(&client->connection->ssl, &In, &Out2);

    if (Out2.count > 0) {
      slab2->buf.base = Out2.items;
      slab2->buf.len = Out2.count;
      uv_write(&slab2->req, (uv_stream_t *)&client->connection->handle->uv.tcp,
               &slab2->buf, 1, __http_tcp_on_write_cb);
    } else {
      valk_slab_release_ptr(tcp_buffer_slab, slab2);
    }
  }

  uv_read_start((uv_stream_t *)&client->connection->handle->uv.tcp,
                __alloc_callback, __http_tcp_read_cb);

  printf("Finished initializing client %p\n", (void *)client);

  // Shits connected but not fully established, it will buffer any requests tho
  // releases the promise
  valk_promise_respond(&client->_promise, box);
  valk_arc_release(box);
}

static void __aio_client_connect_cb(valk_aio_system_t *sys,
                                    valk_aio_task_new *task) {
  int r;
  struct sockaddr_in addr;

  valk_arc_box *box = task->arg;
  valk_aio_http2_client *client = box->item;

  client->connection = malloc(sizeof(valk_aio_http_conn));
  VALK_ASSERT(client->connection != NULL,
              "Client connection must be allocated");
  memset(client->connection, 0, sizeof(valk_aio_http_conn));
  client->connection->state = VALK_CONN_INIT;

  client->connection->handle =
      (valk_aio_handle_t *)valk_slab_aquire(sys->handleSlab)->data;
  memset(client->connection->handle, 0, sizeof(valk_aio_handle_t));

  client->connection->handle->kind = VALK_HNDL_TCP;
  client->connection->handle->sys = sys;
  client->connection->handle->arg = client->connection;
  // client->connection->handle->onClose = nullptr;
  client->connection->handle->onClose = __valk_aio_http2_on_disconnect;
  client->connection->handle->uv.tcp.data = client->connection->handle;

  // activate the handle
  valk_dll_insert_after(&sys->liveHandles, client->connection->handle);

  r = uv_tcp_init(sys->eventloop, &client->connection->handle->uv.tcp);

  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "TcpInit err: %s \n", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("TcpInit err");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }

  uv_tcp_nodelay(&client->connection->handle->uv.tcp, 1);

  // Try numeric IPv4 first; if it fails, resolve hostname.
  r = uv_ip4_addr(client->interface, client->port, &addr);
  if (r) {
    struct addrinfo hints, *res = NULL;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    char portstr[16];
    snprintf(portstr, sizeof portstr, "%d", client->port);
    int gai = getaddrinfo(client->interface, portstr, &hints, &res);
    if (gai == 0 && res) {
      memcpy(&addr, res->ai_addr, sizeof(struct sockaddr_in));
      freeaddrinfo(res);
    } else {
      if (res) freeaddrinfo(res);
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      fprintf(stderr, "Addr resolve err: %s\n", gai_strerror(gai));
      valk_arc_box *err = valk_arc_box_err("Addr err");
      valk_promise_respond(&task->promise, err);
      valk_arc_release(err);
      valk_arc_release(box);
      return;
    }
  }

  client->connection->req.data = box;
  client->_promise = task->promise;
  uv_tcp_connect(&client->connection->req, &client->connection->handle->uv.tcp,
                 (const struct sockaddr *)&addr, __uv_http2_connect_cb);
}

static void __valk_aio_http2_client_free(valk_arc_box *box) {
  printf("FREERDOM2 -> the client edition\n");
  valk_aio_http2_client *client = box->item;
  SSL_CTX_free(client->ssl_ctx);
  valk_mem_allocator_free(box->allocator, box);
}

valk_future *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                         const char *ip, const int port,
                                         const char *hostname) {

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  valk_future *res = valk_future_new();
  valk_arc_box *box = valk_arc_box_new(VALK_SUC, sizeof(valk_aio_http2_client));
  box->free = __valk_aio_http2_client_free;

  task->arg = box;
  memset(box->item, 0, sizeof(valk_aio_http2_client));

  valk_aio_http2_client *client = box->item;
  // Store IP for uv connect
  strncpy(client->interface, ip, sizeof(client->interface) - 1);
  client->interface[sizeof(client->interface) - 1] = '\0';
  // Store hostname for SNI
  if (hostname) {
    strncpy(client->hostname, hostname, sizeof(client->hostname) - 1);
    client->hostname[sizeof(client->hostname) - 1] = '\0';
  } else {
    client->hostname[0] = '\0';
  }
  client->sys = sys;
  client->port = port;

  task->promise.item = res;
  valk_arc_retain(res);
  task->callback = __aio_client_connect_cb;

  VALK_DEBUG("Initializing client %p", (void *)client);
  __uv_exec_task(sys, task);

  return res;
}

valk_future *valk_aio_http2_connect(valk_aio_system_t *sys,
                                    const char *interface, const int port,
                                    const char *certfile) {
  UNUSED(certfile);
  // Backward-compatible connect that uses provided interface and defaults SNI
  return valk_aio_http2_connect_host(sys, interface, port, "localhost");
}

static void __http2_submit_demo_request_cb(valk_aio_system_t *sys,
                                           struct valk_aio_task_new *task) {
  UNUSED(sys);

  valk_arc_box *box = task->arg;
  valk_aio_http2_client *client = box->item;

  VALK_DEBUG("Constructing request on client %p", (void *)client);
  valk_aio_http_conn *conn = client->connection;

  int32_t stream_id;
  // http2_stream_data *stream_data = session_data->stream_data;
  // const char *uri = "local/";
  // const struct http_parser_url *u = stream_data->u;

  nghttp2_nv hdrs[] = {MAKE_NV2(":method", "GET"), MAKE_NV2(":scheme", "https"),
                       MAKE_NV2(":authority", "google.com"),
                       // stream_data->authoritylen),
                       MAKE_NV2(":path", "/")};
  // fprintf(stderr, "Request headers:\n");
  // print_headers(stderr, hdrs, ARRLEN(hdrs));

  // TODO(networking): Allocating this promise here temporarily, ideally need to
  // be passing a request object with a promise on it
  valk_promise *prom = valk_mem_alloc(sizeof(valk_promise));
  // valk_mem_free(sizeof(valk_promise)); in callback to nghttp2 recv
  *prom = task->promise;  // copy this shit

  stream_id =
      nghttp2_submit_request2(conn->session, nullptr, hdrs,
                              sizeof(hdrs) / sizeof(hdrs[0]), nullptr, prom);

  if (stream_id < 0) {
    VALK_ERROR("Could not submit HTTP request: %s", nghttp2_strerror(stream_id));
    valk_arc_box *err = valk_arc_box_err("Could not submit HTTP request");
    valk_promise_respond(prom, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_mem_free(prom);
    return;
  }

  VALK_INFO("Submitted request stream_id=%d", stream_id);

  char buf[SSL3_RT_MAX_PACKET_SIZE];
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memset(buf, 0, sizeof(buf));
  valk_buffer_t In = {
      .items = buf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};
  valk_slab_item_t *slabItemRaw = valk_slab_aquire(tcp_buffer_slab);
  if (!slabItemRaw) {
    VALK_ERROR("TCP buffer slab exhausted in submit request");
    return;
  }
  __tcp_buffer_slab_item_t *slabItem = (void *)slabItemRaw->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  // Only write stuff if ssl is established
  if (SSL_is_init_finished(client->connection->ssl.ssl)) {
    __http2_flush_frames(&In, conn);

    // Encrypt the new data n stuff
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);

    int wantToSend = Out.count > 0;
    if (wantToSend) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;

      printf("Sending %ld bytes\n", Out.count);
      uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
               &slabItem->buf, 1, __http_tcp_on_write_cb);
    } else {
      printf("Nothing to send %d \n", wantToSend);
      valk_slab_release_ptr(tcp_buffer_slab, slabItem);
    }
  }

  valk_arc_release(box);
  // return stream_id;
}

static valk_future *__http2_submit_demo_request(valk_aio_system_t *sys,
                                                valk_arc_box *client) {
  valk_future *res = valk_future_new();
  valk_arc_retain(client);
  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  task->arg = client;
  valk_arc_retain(res);
  task->promise.item = res;
  task->callback = __http2_submit_demo_request_cb;

  // valk_arc_release(client); in callback
  // valk_arc_release(res); in resolve
  __uv_exec_task(sys, task);
  return res;
}

char *valk_client_demo(valk_aio_system_t *sys, const char *domain,
                       const char *port) {
  UNUSED(port);
  // Demo: connect to Google over HTTP/2 TLS using a known IPv4 and SNI
  (void)domain; // future: parse/use
  valk_future *fut =
      valk_aio_http2_connect_host(sys, "142.250.191.78", 443, "google.com");
  printf("Arc count of fut : %ld\n", fut->refcount);
  valk_arc_box *client = valk_future_await(fut);
  printf("Arc count of fut : %ld\n", fut->refcount);
  // valk_arc_release(fut);
  // printf("Arc count of fut : %d\n", fut->refcount);

  VALK_ASSERT(client->type == VALK_SUC, "Error creating client: %s",
              (char *)client->item);

  // valk_arc_trace_report_print(fut);
  valk_arc_release(fut);

  fut = __http2_submit_demo_request(sys, client);
  valk_arc_box *response = valk_future_await(fut);
  // future release is gonna eat that shit for breakfast
  valk_arc_retain(response);
  valk_arc_release(fut);
  // valk_arc_trace_report_print(fut);
  // valk_arc_trace_report_print(response);

  VALK_ASSERT(response->type == VALK_SUC, "Error from the response: %s",
              (char *)response->item);

  printf("Got response %s\n", (char *)response->item);
  char *res = strdup(response->item);

  valk_arc_release(response);
  valk_arc_release(client);

  return res;
}

static void __valk_aio_http2_request_send_cb(valk_aio_system_t *sys,
                                             struct valk_aio_task_new *task) {
  UNUSED(sys);
  __valk_request_client_pair_t *pair = task->arg;

  // TODO(networking): Allocating this promise here temporarily, ideally need
  // to be passing a request object with a promise on it
  // the reason its not done on the arena, is because it will be freed by a
  // callback
  valk_aio_http2_client *client = pair->client;
  VALK_INFO("Client ready: %s:%d", client->interface, client->port);
  VALK_DEBUG("req: %s%s", pair->req->authority, pair->req->path);

  VALK_DEBUG("Constructing request on client %p", (void *)client);
  valk_aio_http_conn *conn = client->connection;

  // Allocate request/response context using malloc (event loop thread allocator)
  __http2_req_res_t *reqres = valk_mem_alloc(sizeof(__http2_req_res_t));
  reqres->req = pair->req;
  reqres->promise = task->promise;

  // Allocate and initialize response using malloc allocator
  // (must match event loop thread where headers/body will be populated)
  valk_arc_box *box =
      valk_arc_box_new(VALK_SUC, sizeof(valk_http2_response_t));
  box->free = __valk_http2_response_free;

  reqres->res_box = box;
  reqres->res = box->item;
  memset(reqres->res, 0, sizeof(valk_http2_response_t));
  da_init(&reqres->res->headers);

  // For client responses, use a generous 64MB limit (responses are fully buffered)
  // This is separate from server-side max_request_body_size since client may receive
  // large responses from external servers
  size_t client_response_limit = 64 * 1024 * 1024;
  reqres->res->body = valk_mem_alloc(client_response_limit);
  reqres->res->bodyLen = 0;
  reqres->res->bodyCapacity = client_response_limit;

  VALK_TRACE("Box: %p, item: %p", (void*)box, reqres->res);

  // Build HTTP/2 headers from request (use request allocator for reading)
  VALK_WITH_ALLOC(pair->req->allocator) {
    // HTTP/2 requires these 4 pseudo-headers
    const size_t NUM_PSEUDO_HEADERS = 4;
    size_t hdrCount = pair->req->headers.count + NUM_PSEUDO_HEADERS;
    struct valk_http2_header_t *phds = pair->req->headers.items;

    nghttp2_nv hdrs[hdrCount];

    hdrs[0].name = (uint8_t *)":method";
    hdrs[0].value = (uint8_t *)pair->req->method;
    hdrs[0].namelen = sizeof(":method") - 1;
    hdrs[0].valuelen = strlen(pair->req->method);
    hdrs[0].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[1].name = (uint8_t *)":scheme";
    hdrs[1].value = (uint8_t *)pair->req->scheme;
    hdrs[1].namelen = sizeof(":scheme") - 1;
    hdrs[1].valuelen = strlen(pair->req->scheme);
    hdrs[1].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[2].name = (uint8_t *)":authority";
    hdrs[2].value = (uint8_t *)pair->req->authority;
    hdrs[2].namelen = sizeof(":authority") - 1;
    hdrs[2].valuelen = strlen(pair->req->authority);
    hdrs[2].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[3].name = (uint8_t *)":path";
    hdrs[3].value = (uint8_t *)pair->req->path;
    hdrs[3].namelen = sizeof(":path") - 1;
    hdrs[3].valuelen = strlen(pair->req->path);
    hdrs[3].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    // Add custom headers from the request
    for (size_t i = 0; i < pair->req->headers.count; ++i) {
      hdrs[NUM_PSEUDO_HEADERS + i].name = phds[i].name;
      hdrs[NUM_PSEUDO_HEADERS + i].value = phds[i].value;
      hdrs[NUM_PSEUDO_HEADERS + i].namelen = phds[i].nameLen;
      hdrs[NUM_PSEUDO_HEADERS + i].valuelen = phds[i].valueLen;
      hdrs[NUM_PSEUDO_HEADERS + i].flags =
          NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;
    }

    reqres->streamid = nghttp2_submit_request2(conn->session, nullptr, hdrs,
                                               hdrCount, nullptr, reqres);

    if (reqres->streamid < 0) {
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      VALK_ERROR("Could not submit HTTP request: %s",
                 nghttp2_strerror(reqres->streamid));
      valk_arc_box *err = valk_arc_box_err("Could not submit HTTP request");
      valk_promise_respond(&task->promise, err);
      valk_arc_release(err);
      // valk_arc_release(task->promise.item);
      return;
    }

    reqres->res->stream_id = reqres->streamid;
    VALK_INFO("Submitted request stream_id=%ld", reqres->streamid);
  }

  // Not request allocated... its connection allocated. Event though technically
  // the buffer could be part of the request maybe
  char buf[SSL3_RT_MAX_PACKET_SIZE];
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memset(buf, 0, sizeof(buf));
  valk_buffer_t In = {
      .items = buf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};
  valk_slab_item_t *slabItemRaw = valk_slab_aquire(tcp_buffer_slab);
  if (!slabItemRaw) {
    VALK_ERROR("TCP buffer slab exhausted in submit data");
    return;
  }
  __tcp_buffer_slab_item_t *slabItem = (void *)slabItemRaw->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  // Only write stuff if ssl is established
  if (SSL_is_init_finished(client->connection->ssl.ssl)) {
    __http2_flush_frames(&In, conn);

    // Encrypt the new data n stuff
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);

    int wantToSend = Out.count > 0;
    if (wantToSend) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;

      printf("Sending %ld bytes\n", Out.count);
      uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
               &slabItem->buf, 1, __http_tcp_on_write_cb);
    } else {
      printf("Nothing to send %d \n", wantToSend);
      valk_slab_release_ptr(tcp_buffer_slab, slabItem);
    }
  }
}

valk_future *valk_aio_http2_request_send(valk_http2_request_t *req,
                                         valk_aio_http2_client *client) {
  printf("Client's ready to go : %s: %d :: %p\n", client->interface,
         client->port, (void *)client);
  valk_future *res;
  valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)client->sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  task->allocator = (valk_mem_allocator_t *)client->sys->handleSlab;

  VALK_WITH_ALLOC(req->allocator) {
    res = valk_future_new();
    __valk_request_client_pair_t *pair =
        valk_mem_alloc(sizeof(__valk_request_client_pair_t));

    pair->client = client;
    pair->req = req;

    task->arg = pair;
    task->promise.item = res;
    valk_arc_retain(res);
    task->callback = __valk_aio_http2_request_send_cb;
    printf("Client's NOT ready to go : %s: %d :: %p :: %p\n",
           pair->client->interface, pair->client->port, (void *)pair->client,
           (void *)__valk_aio_http2_request_send_cb);
  }
  __uv_exec_task(client->sys, task);
  return res;
}

//
const char *valk_aio_system_config_validate(const valk_aio_system_config_t *cfg) {
  // Hard limits
  if (cfg->max_connections < 1 || cfg->max_connections > 100000)
    return "max_connections must be between 1 and 100,000";

  if (cfg->max_concurrent_streams < 1 || cfg->max_concurrent_streams > 1000)
    return "max_concurrent_streams must be between 1 and 1,000";

  if (cfg->tcp_buffer_pool_size < 16 || cfg->tcp_buffer_pool_size > 1000000)
    return "tcp_buffer_pool_size must be between 16 and 1,000,000";

  if (cfg->arena_pool_size < 1 || cfg->arena_pool_size > 10000)
    return "arena_pool_size must be between 1 and 10,000";

  if (cfg->arena_size < (1 << 20) || cfg->arena_size > (256ULL << 20))
    return "arena_size must be between 1MB and 256MB";

  if (cfg->max_request_body_size < (1 << 10) || cfg->max_request_body_size > (1ULL << 30))
    return "max_request_body_size must be between 1KB and 1GB";

  if (cfg->queue_capacity < 16 || cfg->queue_capacity > 100000)
    return "queue_capacity must be between 16 and 100,000";

  // Relationship validations
  if (cfg->tcp_buffer_pool_size < cfg->max_connections)
    return "tcp_buffer_pool_size must be >= max_connections";

  if (cfg->arena_pool_size < cfg->max_connections / 10)
    return "arena_pool_size must be >= max_connections / 10";

  return NULL; // Valid
}

int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg) {
  // Set defaults for primary parameters
  if (cfg->max_connections == 0) cfg->max_connections = 100;
  if (cfg->max_concurrent_streams == 0) cfg->max_concurrent_streams = 100;

  // Derive dependent values (new formulas based on research)
  if (cfg->tcp_buffer_pool_size == 0) {
    uint32_t stream_overhead = cfg->max_concurrent_streams / 8;
    cfg->tcp_buffer_pool_size = cfg->max_connections * (2 + stream_overhead);
  }

  if (cfg->arena_pool_size == 0)
    cfg->arena_pool_size = cfg->max_connections * 2;

  if (cfg->arena_size == 0)
    cfg->arena_size = 64 * 1024 * 1024;

  if (cfg->max_request_body_size == 0)
    cfg->max_request_body_size = 8 * 1024 * 1024;

  if (cfg->queue_capacity == 0)
    cfg->queue_capacity = cfg->max_connections * 2;

  // Backpressure defaults
  if (cfg->buffer_high_watermark == 0.0f)
    cfg->buffer_high_watermark = 0.85f;

  if (cfg->buffer_critical_watermark == 0.0f)
    cfg->buffer_critical_watermark = 0.95f;

  if (cfg->min_buffers_per_conn == 0)
    cfg->min_buffers_per_conn = BUFFERS_PER_CONNECTION;

  // Validate watermarks
  if (cfg->buffer_high_watermark >= cfg->buffer_critical_watermark) {
    fprintf(stderr, "AIO config error: buffer_high_watermark must be < buffer_critical_watermark\n");
    return -1;
  }

  // Validate
  const char *err = valk_aio_system_config_validate(cfg);
  if (err) {
    fprintf(stderr, "AIO config error: %s\n", err);
    return -1;
  }

  return 0;
}

valk_aio_system_t *valk_aio_start() {
  return valk_aio_start_with_config(NULL);
}

valk_aio_system_t *valk_aio_start_with_config(valk_aio_system_config_t *config) {
  // Singleton guard: check if AIO system is already running
  if (global_aio_system != NULL) {
    VALK_WARN("AIO system already started - returning existing instance. "
              "Multiple AIO systems are not supported and can cause race conditions.");
    return global_aio_system;
  }

  // Resolve configuration
  valk_aio_system_config_t resolved;
  if (config) {
    resolved = *config;
  } else {
    resolved = valk_aio_system_config_default();
  }

  if (valk_aio_system_config_resolve(&resolved) != 0) {
    return NULL;
  }

  // On linux definitely turn sigpipe off
  // Otherwise ''hit crashes.
  // When the socket dissapears a write may be queued in the event loop
  // In that case we just want to do proper error handling without the
  // signal
  // Simpler portable ignore of SIGPIPE to avoid crashes on broken pipe
  signal(SIGPIPE, SIG_IGN);

  valk_aio_system_t *sys = valk_mem_alloc(sizeof(valk_aio_system_t));
  sys->config = resolved;  // Store resolved configuration
  global_aio_system = sys;  // Store singleton reference
  valk_aio_active_system = sys;  // Export for metrics access

  valk_aio_ssl_start();

  sys->eventloop = uv_default_loop();

  // Enable metrics collection on event loop
  #ifdef VALK_METRICS_ENABLED
  int rc = uv_loop_configure(sys->eventloop, UV_METRICS_IDLE_TIME);
  if (rc != 0) {
    VALK_WARN("Failed to enable loop metrics: %s", uv_strerror(rc));
  }
  #endif

  sys->liveHandles.kind = VALK_HNDL_EMPTY;
  memset(&sys->liveHandles, 0, sizeof(valk_aio_handle_t));

  // Allocate AIO slabs with malloc allocator (not GC heap)
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    sys->httpServers = valk_slab_new(
        sizeof(valk_arc_box) + sizeof(valk_aio_http_server), HTTP_MAX_SERVERS);
    sys->httpClients = valk_slab_new(
        sizeof(valk_arc_box) + sizeof(valk_aio_http2_client), HTTP_MAX_CLIENTS);
    sys->handleSlab = valk_slab_new(sizeof(valk_aio_handle_t), AIO_MAX_HANDLES);
  }

  // Initialize HTTP request/response queues for Lisp handlers
  sys->http_queue.request_items = malloc(sizeof(valk_http_request_item_t) * sys->config.queue_capacity);
  sys->http_queue.request_idx = 0;
  sys->http_queue.request_count = 0;
  sys->http_queue.request_capacity = sys->config.queue_capacity;
  pthread_mutex_init(&sys->http_queue.request_mutex, NULL);
  pthread_cond_init(&sys->http_queue.request_ready, NULL);

  sys->http_queue.response_items = malloc(sizeof(valk_http_response_item_t) * sys->config.queue_capacity);
  sys->http_queue.response_idx = 0;
  sys->http_queue.response_count = 0;
  sys->http_queue.response_capacity = sys->config.queue_capacity;
  pthread_mutex_init(&sys->http_queue.response_mutex, NULL);
  pthread_cond_init(&sys->http_queue.response_ready, NULL);

#ifdef VALK_METRICS_ENABLED
  // Initialize global modular metrics system (once)
  static bool metrics_initialized = false;
  if (!metrics_initialized) {
    valk_metrics_init();
    metrics_initialized = true;
  }
  // Initialize AIO-specific metrics
  valk_aio_metrics_init(&sys->metrics);
  // Initialize AIO system stats with pool sizes
  valk_aio_system_stats_init(&sys->system_stats,
                              sys->config.arena_pool_size,  // arenas_total
                              sys->config.tcp_buffer_pool_size);  // tcp_buffers_total
#endif

  // printf("Aquiring stopper\n");
  sys->stopperHandle = (valk_aio_handle_t *)valk_slab_aquire(sys->handleSlab)->data;
  memset(sys->stopperHandle, 0, sizeof(valk_aio_handle_t));
  sys->stopperHandle->kind = VALK_HNDL_TASK;
  sys->stopperHandle->sys = sys;
  sys->stopperHandle->uv.task.data = sys->stopperHandle;
  uv_async_init(sys->eventloop, &sys->stopperHandle->uv.task, __aio_uv_stop);
  valk_dll_insert_after(&sys->liveHandles, sys->stopperHandle);

  int status = uv_thread_create(&sys->loopThread, __event_loop, sys);
  if (status) {
    perror("pthread_create");
  }
  return sys;
}

void valk_aio_stop(valk_aio_system_t *sys) {
  uv_async_send(&sys->stopperHandle->uv.task);
  // printf("Processing the stopper\n");
  // fflush(stdout);
  uv_thread_join(&sys->loopThread);
  // printf("AFTER the Processing the stopper\n");
  // fflush(stdout);
  // while (UV_EBUSY == uv_loop_close(sys->eventloop)) {
  // };
  // TODO(networking): need to properly free the system too
  // Slabs were allocated with malloc allocator, so free with malloc allocator
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    valk_slab_free(sys->httpServers);
    valk_slab_free(sys->httpClients);
    valk_slab_free(sys->handleSlab);
  }

  // Reset singleton so AIO can be restarted if needed
  if (global_aio_system == sys) {
    global_aio_system = NULL;
  }
  if (valk_aio_active_system == sys) {
    valk_aio_active_system = NULL;
  }

  // printf("Freeing sys\n");
  // fflush(stdout);
  valk_mem_free(sys);
  // printf("Done freeing\n");
  // fflush(stdout);
}

#ifdef VALK_METRICS_ENABLED
// Get metrics from AIO system
valk_aio_metrics_t* valk_aio_get_metrics(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return &sys->metrics;
}

// Get system stats from AIO system
valk_aio_system_stats_t* valk_aio_get_system_stats(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return &sys->system_stats;
}

// Update queue stats from HTTP queue (call before rendering metrics)
void valk_aio_update_queue_stats(valk_aio_system_t* sys) {
  if (!sys) return;

  // Calculate pending requests (items written - items consumed)
  pthread_mutex_lock(&sys->http_queue.request_mutex);
  size_t pending_requests = sys->http_queue.request_count - sys->http_queue.request_idx;
  pthread_mutex_unlock(&sys->http_queue.request_mutex);

  // Calculate pending responses (items written - items consumed)
  pthread_mutex_lock(&sys->http_queue.response_mutex);
  size_t pending_responses = sys->http_queue.response_count - sys->http_queue.response_idx;
  pthread_mutex_unlock(&sys->http_queue.response_mutex);

  // Update the atomic stats
  valk_aio_system_stats_update_queue(&sys->system_stats, pending_requests, pending_responses);

  // Update buffer pool stats (calculate used from available)
  if (sys->tcpBufferSlab) {
    size_t available = valk_slab_available(sys->tcpBufferSlab);
    size_t total = sys->config.tcp_buffer_pool_size;
    size_t used = (available <= total) ? (total - available) : 0;
    atomic_store(&sys->system_stats.tcp_buffers_used, used);
  }

  // Update arena pool stats
  if (sys->httpStreamArenas) {
    size_t available = valk_slab_available(sys->httpStreamArenas);
    size_t total = sys->config.arena_pool_size;
    size_t used = (available <= total) ? (total - available) : 0;
    atomic_store(&sys->system_stats.arenas_used, used);
  }
}
#endif

// Get event loop from AIO system
uv_loop_t* valk_aio_get_event_loop(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return sys->eventloop;
}

// Timer callback for aio/delay - called when timer fires
static void __delay_timer_cb(uv_timer_t *handle) {
  valk_delay_timer_t *timer_data = (valk_delay_timer_t *)handle->data;
  VALK_INFO("aio/delay timer fired for stream %d", timer_data->stream_id);

  // Call the continuation lambda
  if (timer_data->continuation && timer_data->env) {
    valk_lval_t *response;
    VALK_WITH_ALLOC((valk_mem_allocator_t*)timer_data->stream_arena) {
      // Call continuation with no arguments: (continuation)
      valk_lval_t *args = valk_lval_nil();
      response = valk_lval_eval_call(timer_data->env, timer_data->continuation, args);
    }

    VALK_INFO("aio/delay continuation returned type %d", LVAL_TYPE(response));

    // Send the response
    if (LVAL_TYPE(response) == LVAL_ERR) {
      VALK_WARN("Delay continuation returned error: %s", response->str);
      VALK_WITH_ALLOC((valk_mem_allocator_t*)timer_data->stream_arena) {
        valk_lval_t* error_items[] = {
          valk_lval_sym(":status"), valk_lval_str("500"),
          valk_lval_sym(":body"), valk_lval_str(response->str)
        };
        valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
        __http_send_response(timer_data->session, timer_data->stream_id,
                             error_resp, timer_data->stream_arena);
      }
    } else {
      VALK_INFO("aio/delay sending response for stream %d", timer_data->stream_id);
      __http_send_response(timer_data->session, timer_data->stream_id,
                           response, timer_data->stream_arena);
    }

    // Flush the queued HTTP/2 frames to the wire
    // __http_send_response only queues the response in nghttp2's session,
    // we need to explicitly flush it since we're outside the normal read callback flow
    __http_continue_pending_send(timer_data->conn);
  } else {
    VALK_WARN("aio/delay timer fired but no continuation or env");
  }

  // Stop and close the timer
  uv_timer_stop(handle);
  uv_close((uv_handle_t *)handle, NULL);
  free(timer_data);
}

// aio/delay implementation - schedules a timer and calls continuation after delay
// Returns a special "deferred" symbol to indicate response will be sent later
valk_lval_t* valk_aio_delay(valk_aio_system_t* sys, uint64_t delay_ms,
                            valk_lval_t* continuation, valk_lenv_t* env) {
  UNUSED(env);
  VALK_INFO("aio/delay called with delay_ms=%lu", (unsigned long)delay_ms);

  // Check if we're in a request context
  if (!current_request_ctx) {
    VALK_WARN("aio/delay called outside request context");
    return valk_lval_err("aio/delay can only be used within an HTTP request handler");
  }

  // Allocate timer data
  valk_delay_timer_t *timer_data = malloc(sizeof(valk_delay_timer_t));
  if (!timer_data) {
    return valk_lval_err("Failed to allocate timer");
  }

  // Copy continuation using malloc allocator so it survives arena reset
  // Note: We use malloc allocator since event loop thread doesn't have GC heap
  valk_lval_t *heap_continuation;
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    heap_continuation = valk_lval_copy(continuation);
  }

  // Store context
  timer_data->continuation = heap_continuation;
  timer_data->session = current_request_ctx->session;
  timer_data->stream_id = current_request_ctx->stream_id;
  timer_data->conn = current_request_ctx->conn;
  timer_data->stream_arena = current_request_ctx->req->stream_arena;
  timer_data->env = current_request_ctx->env;
  timer_data->timer.data = timer_data;

  // Initialize and start timer on the event loop
  uv_loop_t *loop = sys->eventloop;
  int r = uv_timer_init(loop, &timer_data->timer);
  VALK_INFO("uv_timer_init returned %d", r);
  r = uv_timer_start(&timer_data->timer, __delay_timer_cb, delay_ms, 0);
  VALK_INFO("uv_timer_start returned %d for stream %d", r, timer_data->stream_id);

  // Return special "deferred" symbol to indicate async response
  return valk_lval_sym(":deferred");
}

// ============================================================================
// aio/sleep - Timer that returns a handle (no callback)
// ============================================================================
// Usage: (aio/sleep ms) -> handle that completes with nil after ms milliseconds
//
// This is the handle-based equivalent of aio/delay. Instead of taking a
// callback, it returns a handle that can be composed with aio/then.
//
// Example:
//   (aio/then (aio/sleep 2000) (\ {_} {:status "200" :body "done"}))

static void __sleep_timer_cb(uv_timer_t *timer_handle) {
  valk_async_handle_uv_data_t *data = (valk_async_handle_uv_data_t *)timer_handle->data;
  valk_async_handle_t *async_handle = data->handle;

  // Complete with nil value
  valk_lval_t *result = valk_lval_nil();
  valk_async_handle_complete(async_handle, result);

  // Cleanup timer
  uv_timer_stop(timer_handle);
  uv_close((uv_handle_t *)timer_handle, NULL);
}

static valk_lval_t* valk_builtin_aio_sleep(valk_lenv_t* e, valk_lval_t* a) {
  // Validate: (aio/sleep ms)
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/sleep: expected 1 argument (ms)");
  }
  valk_lval_t *ms_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ms_arg) != LVAL_NUM) {
    return valk_lval_err("aio/sleep: expected number argument");
  }

  uint64_t delay_ms = (uint64_t)ms_arg->num;

  // Get event loop - prefer current request context, fall back to global AIO system
  // The fallback is needed for aio/sleep calls inside aio/then callbacks where
  // the HTTP request context is no longer set
  uv_loop_t *loop = NULL;
  if (current_request_ctx) {
    valk_aio_system_t *sys = current_request_ctx->conn->server->sys;
    loop = sys->eventloop;
  } else if (global_aio_system) {
    loop = global_aio_system->eventloop;
  } else {
    return valk_lval_err("aio/sleep requires an active AIO system");
  }

  // Create async handle
  // Note: We don't set HTTP context on inner handles like aio/sleep - only the
  // outermost handle returned to the HTTP handler should have HTTP context.
  // The HTTP handler will set context on that handle, and propagation will
  // route the response through it.
  valk_async_handle_t *async_handle = valk_async_handle_new(loop, e);

  // Allocate timer data
  valk_async_handle_uv_data_t *timer_data = malloc(sizeof(valk_async_handle_uv_data_t));
  timer_data->handle = async_handle;
  timer_data->uv.timer.data = timer_data;

  async_handle->uv_handle_ptr = timer_data;
  async_handle->status = VALK_ASYNC_RUNNING;

  // Initialize and start timer
  uv_timer_init(loop, &timer_data->uv.timer);
  uv_timer_start(&timer_data->uv.timer, __sleep_timer_cb, delay_ms, 0);

  VALK_INFO("aio/sleep started: %lu ms, handle id=%lu", delay_ms, async_handle->id);

  return valk_lval_handle(async_handle);
}

// ============================================================================
// aio/let - Monadic let-bindings for async operations
// ============================================================================
//
// Syntax: (aio/let bindings body)
//   bindings: q-expr of ((var1 expr1) (var2 expr2) :then (var3 expr3) ...)
//   body: expression to evaluate with all bindings in scope
//
// Behavior:
//   - Bindings in same group (before :then) run in PARALLEL via aio/all
//   - Groups separated by :then run SEQUENTIALLY
//   - Body evaluates after all bindings complete
//
// Example:
//   (aio/let {((user (fetch-user id))
//             (settings (fetch-settings id))
//             :then
//             (posts (fetch-posts (user :id))))}
//     {:user user :settings settings :posts posts})

// Helper: Check if lval is the :then barrier keyword
static inline bool is_then_barrier(valk_lval_t *item) {
  return LVAL_TYPE(item) == LVAL_SYM && strcmp(item->str, ":then") == 0;
}

// Binding group for parallel execution
typedef struct {
  valk_lval_t **bindings;  // Array of (var expr) pairs
  size_t count;
  size_t capacity;
} aio_let_group_t;

// Parsed binding groups
typedef struct {
  aio_let_group_t *groups;
  size_t count;
  size_t capacity;
} aio_let_parsed_t;

static aio_let_parsed_t* aio_let_parse_bindings(valk_lval_t *bindings) {
  aio_let_parsed_t *result = malloc(sizeof(aio_let_parsed_t));
  result->groups = malloc(sizeof(aio_let_group_t) * 16);
  result->count = 1;
  result->capacity = 16;

  // Initialize first group
  aio_let_group_t *current = &result->groups[0];
  current->bindings = malloc(sizeof(valk_lval_t*) * 32);
  current->count = 0;
  current->capacity = 32;

  // The bindings argument is a QEXPR containing the bindings list
  // For syntax: (aio/let {((a expr1) (b expr2) :then (c expr3))} body)
  // bindings = {((a expr1) (b expr2) :then (c expr3))}
  // We need to get the inner list and iterate over it
  valk_lval_t *curr = bindings;

  // If bindings is a QEXPR with one element that is a list, unwrap it
  if (LVAL_TYPE(bindings) == LVAL_QEXPR && !valk_lval_list_is_empty(bindings)) {
    valk_lval_t *first = bindings->cons.head;
    if (LVAL_TYPE(first) == LVAL_CONS || LVAL_TYPE(first) == LVAL_QEXPR) {
      // The first element is a list - this is our bindings list
      curr = first;
    }
  }

  // Walk bindings list - both CONS and QEXPR use cons.head/cons.tail
  while ((LVAL_TYPE(curr) == LVAL_CONS || LVAL_TYPE(curr) == LVAL_QEXPR) &&
         !valk_lval_list_is_empty(curr)) {
    valk_lval_t *item = curr->cons.head;

    if (is_then_barrier(item)) {
      // Start new group (only if current has bindings)
      if (current->count > 0) {
        result->count++;
        if (result->count >= result->capacity) {
          result->capacity *= 2;
          result->groups = realloc(result->groups,
                                   sizeof(aio_let_group_t) * result->capacity);
        }
        current = &result->groups[result->count - 1];
        current->bindings = malloc(sizeof(valk_lval_t*) * 32);
        current->count = 0;
        current->capacity = 32;
      }
    } else {
      // Add binding to current group
      if (current->count >= current->capacity) {
        current->capacity *= 2;
        current->bindings = realloc(current->bindings,
                                    sizeof(valk_lval_t*) * current->capacity);
      }
      current->bindings[current->count++] = item;
    }

    curr = curr->cons.tail;
  }

  return result;
}

static void aio_let_free_parsed(aio_let_parsed_t *parsed) {
  for (size_t i = 0; i < parsed->count; i++) {
    free(parsed->groups[i].bindings);
  }
  free(parsed->groups);
  free(parsed);
}

// Generate code for a single group of bindings
// Returns: (aio/then (aio/all exprs) (\ {results} (def vars) inner))
static valk_lval_t* aio_let_gen_group(valk_lenv_t *env,
                                       aio_let_group_t *group,
                                       valk_lval_t *inner) {
  if (group->count == 0) {
    return inner;
  }

  if (group->count == 1) {
    // Single binding: (aio/then expr (\ {var} inner))
    valk_lval_t *binding = group->bindings[0];
    valk_lval_t *var = valk_lval_list_nth(binding, 0);
    valk_lval_t *expr = valk_lval_list_nth(binding, 1);

    // Build: (aio/then expr (\ {var} inner))
    // formals = {var}
    valk_lval_t *formals = valk_lval_qcons(valk_lval_copy(var), valk_lval_nil());

    valk_lval_t *lambda = valk_lval_lambda(env, formals, inner);

    valk_lval_t *then_call = valk_lval_cons(
      valk_lval_sym("aio/then"),
      valk_lval_cons(valk_lval_copy(expr),
        valk_lval_cons(lambda, valk_lval_nil())));

    return then_call;
  }

  // Multiple bindings: use aio/all for parallel execution
  // Build: (aio/then (aio/all (list e1 e2 ...)) (\ {_results} (= {v1} (nth _results 0)) ... inner))

  // Build expression list for aio/all
  valk_lval_t *expr_list = valk_lval_nil();
  for (int i = group->count - 1; i >= 0; i--) {
    valk_lval_t *binding = group->bindings[i];
    valk_lval_t *expr = valk_lval_list_nth(binding, 1);
    expr_list = valk_lval_cons(valk_lval_copy(expr), expr_list);
  }

  // (list e1 e2 ...)
  valk_lval_t *list_call = valk_lval_cons(valk_lval_sym("list"), expr_list);

  // (aio/all (list ...))
  valk_lval_t *all_call = valk_lval_cons(
    valk_lval_sym("aio/all"),
    valk_lval_cons(list_call, valk_lval_nil()));

  // Build lambda body: (do (= {v1} (nth _results 0)) (= {v2} (nth _results 1)) ... inner)
  valk_lval_t *body = valk_lval_cons(valk_lval_sym("do"), valk_lval_nil());
  valk_lval_t *body_tail = body;

  for (size_t i = 0; i < group->count; i++) {
    valk_lval_t *binding = group->bindings[i];
    valk_lval_t *var = valk_lval_list_nth(binding, 0);

    // (= {var} (nth _results (i+1)))  -- nth is 1-based in prelude
    // var_qexpr = {var}
    valk_lval_t *var_qexpr = valk_lval_qcons(valk_lval_copy(var), valk_lval_nil());

    valk_lval_t *nth_call = valk_lval_cons(
      valk_lval_sym("nth"),
      valk_lval_cons(valk_lval_num(i + 1),  // 1-based indexing
        valk_lval_cons(valk_lval_sym("_results"), valk_lval_nil())));

    valk_lval_t *assign = valk_lval_cons(
      valk_lval_sym("="),
      valk_lval_cons(var_qexpr,
        valk_lval_cons(nth_call, valk_lval_nil())));

    body_tail->cons.tail = valk_lval_cons(assign, valk_lval_nil());
    body_tail = body_tail->cons.tail;
  }

  // Add inner expression at end
  body_tail->cons.tail = valk_lval_cons(inner, valk_lval_nil());

  // Build lambda: (\ {_results} body)
  // formals = {_results}
  valk_lval_t *formals = valk_lval_qcons(valk_lval_sym("_results"), valk_lval_nil());
  valk_lval_t *lambda = valk_lval_lambda(env, formals, body);

  // (aio/then (aio/all ...) lambda)
  valk_lval_t *then_call = valk_lval_cons(
    valk_lval_sym("aio/then"),
    valk_lval_cons(all_call,
      valk_lval_cons(lambda, valk_lval_nil())));

  return then_call;
}

static valk_lval_t* valk_builtin_aio_let(valk_lenv_t* e, valk_lval_t* a) {
  // aio/let receives: (bindings body)
  // bindings is a QEXPR of binding pairs + :then barriers
  // body is also a QEXPR to prevent premature evaluation

  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/let: expected 2 arguments (bindings body)");
  }

  valk_lval_t *bindings = valk_lval_list_nth(a, 0);
  valk_lval_t *body = valk_lval_list_nth(a, 1);

  // Parse bindings into groups separated by :then
  aio_let_parsed_t *parsed = aio_let_parse_bindings(bindings);

  if (parsed->count == 0 || (parsed->count == 1 && parsed->groups[0].count == 0)) {
    aio_let_free_parsed(parsed);
    // No bindings - wrap body in aio/pure and evaluate
    valk_lval_t *evaled_body = valk_lval_eval(e, valk_lval_copy(body));
    valk_lval_t *pure_call = valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(evaled_body, valk_lval_nil()));
    return valk_lval_eval(e, pure_call);
  }

  // Build nested aio/then chain from innermost (body) outward
  // Work backwards: last group wraps body, previous groups wrap that, etc.
  valk_lval_t *result = valk_lval_cons(
    valk_lval_sym("aio/pure"),
    valk_lval_cons(valk_lval_copy(body), valk_lval_nil()));

  for (int g = parsed->count - 1; g >= 0; g--) {
    result = aio_let_gen_group(e, &parsed->groups[g], result);
  }

  aio_let_free_parsed(parsed);

  // Evaluate the generated code
  return valk_lval_eval(e, result);
}

// ============================================================================
// aio/do - Monadic do-notation for async operations with interleaved effects
// ============================================================================
//
// Syntax: (aio/do stmt1 stmt2 ... final-expr)
//   Each stmt can be:
//     - A regular expression (executed for side effects, result discarded)
//     - (<- var expr) - Bind async result to var, then continue
//   The final expression is the result.
//
// Example:
//   (aio/do
//     (println "Before sleep 1")
//     (<- step1 (aio/sleep 1000))
//     (println "After sleep 1, before sleep 2")
//     (<- step2 (aio/sleep 1000))
//     (println "After sleep 2")
//     {:status "200" :body "done"})
//
// Transforms to:
//   (do
//     (println "Before sleep 1")
//     (aio/then (aio/sleep 1000) (\ {step1}
//       (do
//         (println "After sleep 1, before sleep 2")
//         (aio/then (aio/sleep 1000) (\ {step2}
//           (do
//             (println "After sleep 2")
//             (aio/pure {:status "200" :body "done"}))))))))

// Helper: Check if expression is (<- var expr) form
static inline bool is_bind_form(valk_lval_t *expr) {
  if (LVAL_TYPE(expr) != LVAL_CONS && LVAL_TYPE(expr) != LVAL_QEXPR) return false;
  if (valk_lval_list_is_empty(expr)) return false;
  valk_lval_t *head = expr->cons.head;
  return LVAL_TYPE(head) == LVAL_SYM && strcmp(head->str, "<-") == 0;
}

// Recursively build the aio/do chain from statements
// stmts is a list (curr...rest), we process curr and recurse on rest
static valk_lval_t* aio_do_build_chain(valk_lenv_t *env, valk_lval_t *stmts) {
  if (valk_lval_list_is_empty(stmts)) {
    // No statements - return nil wrapped in aio/pure
    return valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(valk_lval_nil(), valk_lval_nil()));
  }

  valk_lval_t *curr = stmts->cons.head;
  valk_lval_t *rest = stmts->cons.tail;

  // Check if this is the last statement
  bool is_last = valk_lval_list_is_empty(rest);

  if (is_bind_form(curr)) {
    // (<- var expr) form
    // Extract var and expr from (<- var expr)
    valk_lval_t *var = valk_lval_list_nth(curr, 1);
    valk_lval_t *expr = valk_lval_list_nth(curr, 2);

    if (is_last) {
      // Last statement is a bind - just return the expression directly
      // (it's async and its result becomes the overall result)
      return valk_lval_copy(expr);
    }

    // Build continuation: (aio/then expr (\ {var} <rest>))
    valk_lval_t *continuation = aio_do_build_chain(env, rest);

    // formals = {var}
    valk_lval_t *formals = valk_lval_qcons(valk_lval_copy(var), valk_lval_nil());
    valk_lval_t *lambda = valk_lval_lambda(env, formals, continuation);

    return valk_lval_cons(
      valk_lval_sym("aio/then"),
      valk_lval_cons(valk_lval_copy(expr),
        valk_lval_cons(lambda, valk_lval_nil())));
  } else {
    // Regular expression (side effect)
    if (is_last) {
      // Last statement - wrap in aio/pure
      return valk_lval_cons(
        valk_lval_sym("aio/pure"),
        valk_lval_cons(valk_lval_copy(curr), valk_lval_nil()));
    }

    // Not last - execute this, then continue with rest
    // Build: (do curr (aio/then (aio/pure nil) (\ {_} <rest>)))
    // Actually simpler: since sync exprs are immediate, we can collect them
    // into a (do ...) block until we hit the next async bind or end

    // Collect consecutive sync expressions
    valk_lval_t *sync_exprs = valk_lval_nil();
    sync_exprs = valk_lval_cons(valk_lval_copy(curr), sync_exprs);

    valk_lval_t *remaining = rest;
    while (!valk_lval_list_is_empty(remaining) && !is_bind_form(remaining->cons.head)) {
      valk_lval_t *next = remaining->cons.head;
      remaining = remaining->cons.tail;

      if (valk_lval_list_is_empty(remaining)) {
        // This is the last statement (sync) - add to sync_exprs, then wrap result
        sync_exprs = valk_lval_cons(valk_lval_copy(next), sync_exprs);
        break;
      }
      sync_exprs = valk_lval_cons(valk_lval_copy(next), sync_exprs);
    }

    // Reverse sync_exprs to get correct order
    valk_lval_t *reversed = valk_lval_nil();
    while (!valk_lval_list_is_empty(sync_exprs)) {
      reversed = valk_lval_cons(sync_exprs->cons.head, reversed);
      sync_exprs = sync_exprs->cons.tail;
    }

    if (valk_lval_list_is_empty(remaining)) {
      // All remaining statements were sync - wrap last in aio/pure
      // Build: (do expr1 expr2 ... (aio/pure last-expr))
      valk_lval_t *do_body = valk_lval_cons(valk_lval_sym("do"), valk_lval_nil());
      valk_lval_t *do_tail = do_body;

      valk_lval_t *rev_curr = reversed;
      valk_lval_t *last_sync = NULL;
      while (!valk_lval_list_is_empty(rev_curr)) {
        if (valk_lval_list_is_empty(rev_curr->cons.tail)) {
          // This is the last one
          last_sync = rev_curr->cons.head;
        } else {
          do_tail->cons.tail = valk_lval_cons(valk_lval_copy(rev_curr->cons.head), valk_lval_nil());
          do_tail = do_tail->cons.tail;
        }
        rev_curr = rev_curr->cons.tail;
      }

      // Wrap last in aio/pure
      valk_lval_t *pure_last = valk_lval_cons(
        valk_lval_sym("aio/pure"),
        valk_lval_cons(valk_lval_copy(last_sync), valk_lval_nil()));
      do_tail->cons.tail = valk_lval_cons(pure_last, valk_lval_nil());

      return do_body;
    } else {
      // There's a bind form in remaining - build continuation
      // Build: (do expr1 expr2 ... <continuation>)
      valk_lval_t *continuation = aio_do_build_chain(env, remaining);

      valk_lval_t *do_body = valk_lval_cons(valk_lval_sym("do"), valk_lval_nil());
      valk_lval_t *do_tail = do_body;

      valk_lval_t *rev_curr = reversed;
      while (!valk_lval_list_is_empty(rev_curr)) {
        do_tail->cons.tail = valk_lval_cons(valk_lval_copy(rev_curr->cons.head), valk_lval_nil());
        do_tail = do_tail->cons.tail;
        rev_curr = rev_curr->cons.tail;
      }

      do_tail->cons.tail = valk_lval_cons(continuation, valk_lval_nil());
      return do_body;
    }
  }
}

static valk_lval_t* valk_builtin_aio_do(valk_lenv_t* e, valk_lval_t* a) {
  // aio/do receives all statements as arguments (unevaluated - it's a special form)
  // Actually, aio/do needs to be a macro/special form that doesn't evaluate args
  // For now, it receives a QEXPR containing the statements

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/do: expected 1 argument (qexpr of statements)");
  }

  valk_lval_t *stmts = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(stmts) != LVAL_QEXPR) {
    return valk_lval_err("aio/do: argument must be a qexpr {stmt1 stmt2 ...}");
  }

  if (valk_lval_list_is_empty(stmts)) {
    // Empty do block - return aio/pure nil
    valk_lval_t *pure = valk_lval_cons(
      valk_lval_sym("aio/pure"),
      valk_lval_cons(valk_lval_nil(), valk_lval_nil()));
    return valk_lval_eval(e, pure);
  }

  // Build the chain of operations
  valk_lval_t *chain = aio_do_build_chain(e, stmts);

  // Evaluate the generated code
  return valk_lval_eval(e, chain);
}

// Get/set current request context (for aio/delay to access)
valk_http_request_ctx_t* valk_http_get_request_ctx(void) {
  return current_request_ctx;
}

void valk_http_set_request_ctx(valk_http_request_ctx_t* ctx) {
  current_request_ctx = ctx;
}

// reference code for openssl setup
//
static void __valk_http2_response_free(valk_arc_box *box) {
  valk_http2_response_t *res = box->item;
  if (res) {
    if (res->body) free(res->body);
    if (res->status) free((void *)res->status);
    if (res->headers.items) {
      for (size_t i = 0; i < res->headers.count; ++i) {
        if (res->headers.items[i].name) free(res->headers.items[i].name);
        if (res->headers.items[i].value) free(res->headers.items[i].value);
      }
      free(res->headers.items);
    }
  }
  valk_mem_allocator_free(box->allocator, box);
}
// https://github.com/darrenjs/openssl_examples

// ============================================================================
// Async Handle Implementation
// ============================================================================

// Forward declaration for completion propagation (defined in Phase 2 section)
static void valk_async_propagate_completion(valk_async_handle_t *source);

// Forward declarations for aio/all parent notification
// (Implementations are after valk_builtin_aio_all)
#define VALK_ALL_CTX_MAGIC_EARLY 0xA11C7821
static void valk_async_notify_all_parent(valk_async_handle_t *child);

// Send HTTP response from a completed handle (if it has HTTP context)
static void valk_async_send_http_response(valk_async_handle_t *handle) {
  // Check if this handle has HTTP context attached
  if (!handle->session || handle->stream_id == 0 || !handle->conn) {
    return;  // No HTTP context - nothing to send
  }

  nghttp2_session *session = (nghttp2_session*)handle->session;
  int32_t stream_id = handle->stream_id;
  struct valk_aio_http_conn *conn = handle->conn;
  valk_mem_arena_t *arena = (valk_mem_arena_t*)handle->stream_arena;

  if (handle->status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *result = handle->result;
    if (LVAL_TYPE(result) == LVAL_ERR) {
      VALK_WARN("Handle completed with error for stream %d: %s", stream_id, result->str);
      VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
        valk_lval_t* error_items[] = {
          valk_lval_sym(":status"), valk_lval_str("500"),
          valk_lval_sym(":body"), valk_lval_str(result->str)
        };
        valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
        __http_send_response(session, stream_id, error_resp, arena);
      }
    } else {
      VALK_INFO("Sending async response for stream %d", stream_id);
      __http_send_response(session, stream_id, result, arena);
    }
    __http_continue_pending_send(conn);
  } else if (handle->status == VALK_ASYNC_FAILED) {
    valk_lval_t *err = handle->error ? handle->error : valk_lval_err("Async operation failed");
    VALK_WARN("Handle failed for stream %d: %s",
              stream_id, LVAL_TYPE(err) == LVAL_ERR ? err->str : "unknown");
    VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
      const char *err_msg = LVAL_TYPE(err) == LVAL_ERR ? err->str : "Async operation failed";
      valk_lval_t* error_items[] = {
        valk_lval_sym(":status"), valk_lval_str("500"),
        valk_lval_sym(":body"), valk_lval_str(err_msg)
      };
      valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
      __http_send_response(session, stream_id, error_resp, arena);
    }
    __http_continue_pending_send(conn);
  }
  // For CANCELLED, don't send anything (client disconnected)
}

// Create a new async handle
static valk_async_handle_t* valk_async_handle_new(uv_loop_t *loop, valk_lenv_t *env) {
  valk_async_handle_t *handle = malloc(sizeof(valk_async_handle_t));
  if (!handle) return NULL;

  memset(handle, 0, sizeof(valk_async_handle_t));
  handle->id = __atomic_fetch_add(&g_async_handle_id, 1, __ATOMIC_RELAXED);
  handle->status = VALK_ASYNC_PENDING;
  __atomic_store_n(&handle->cancel_requested, 0, __ATOMIC_RELAXED);
  handle->loop = loop;
  handle->env = env;
  handle->allocator = &valk_malloc_allocator;

  return handle;
}

// Free an async handle and its resources
static void valk_async_handle_free(valk_async_handle_t *handle) {
  if (!handle) return;

  // Free children array
  if (handle->children.items) {
    free(handle->children.items);
  }

  free(handle);
}

// Mark handle as completed with a result
static void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result) {
  if (!handle) return;
  if (handle->status != VALK_ASYNC_PENDING && handle->status != VALK_ASYNC_RUNNING) {
    return;  // Already in terminal state
  }

  handle->status = VALK_ASYNC_COMPLETED;
  handle->result = result;

  // Call on_complete callback if registered (for direct callbacks, not chaining)
  // Note: For aio/then chaining, on_complete stores the transform function
  // and is handled by valk_async_propagate_completion instead
  if (handle->on_complete && handle->env && handle->stream_arena) {
    VALK_WITH_ALLOC((valk_mem_allocator_t*)handle->stream_arena) {
      valk_lval_t *args = valk_lval_cons(result, valk_lval_nil());
      valk_lval_eval_call(handle->env, handle->on_complete, args);
    }
  }

  // Notify aio/all parent if this handle is a child of one
  valk_async_notify_all_parent(handle);

  // Send HTTP response if this handle has HTTP context attached
  valk_async_send_http_response(handle);

  // Propagate completion to chained handles (aio/then, aio/catch, etc.)
  valk_async_propagate_completion(handle);
}

// Mark handle as failed with an error
static void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error) {
  if (!handle) return;
  if (handle->status != VALK_ASYNC_PENDING && handle->status != VALK_ASYNC_RUNNING) {
    return;  // Already in terminal state
  }

  handle->status = VALK_ASYNC_FAILED;
  handle->error = error;

  // Call on_error callback if registered (for direct callbacks)
  if (handle->on_error && handle->env && handle->stream_arena) {
    VALK_WITH_ALLOC((valk_mem_allocator_t*)handle->stream_arena) {
      valk_lval_t *args = valk_lval_cons(error, valk_lval_nil());
      valk_lval_eval_call(handle->env, handle->on_error, args);
    }
  }

  // Notify aio/all parent if this handle is a child of one
  valk_async_notify_all_parent(handle);

  // Send HTTP error response if this handle has HTTP context attached
  valk_async_send_http_response(handle);

  // Propagate failure to chained handles
  valk_async_propagate_completion(handle);
}

// Request cancellation of a handle
// Returns true if cancellation was requested, false if already in terminal state
static bool valk_async_handle_cancel(valk_async_handle_t *handle) {
  if (!handle) return false;
  if (handle->status != VALK_ASYNC_PENDING && handle->status != VALK_ASYNC_RUNNING) {
    return false;  // Already in terminal state
  }

  // Set atomic cancel flag
  __atomic_store_n(&handle->cancel_requested, 1, __ATOMIC_RELEASE);

  // If it's a timer, stop it
  if (handle->status == VALK_ASYNC_RUNNING && handle->uv_handle_ptr) {
    valk_async_handle_uv_data_t *uv_data = handle->uv_handle_ptr;
    uv_timer_stop(&uv_data->uv.timer);
  }

  handle->status = VALK_ASYNC_CANCELLED;

  // Call on_cancel callback if registered
  if (handle->on_cancel && handle->env) {
    VALK_WITH_ALLOC((valk_mem_allocator_t*)handle->stream_arena) {
      valk_lval_t *args = valk_lval_nil();
      valk_lval_eval_call(handle->env, handle->on_cancel, args);
    }
  }

  // Cancel all children
  for (size_t i = 0; i < handle->children.count; i++) {
    valk_async_handle_cancel(handle->children.items[i]);
  }

  return true;
}

// Add a child handle to a parent (for structured cancellation)
static void valk_async_handle_add_child(valk_async_handle_t *parent, valk_async_handle_t *child) {
  if (!parent || !child) return;

  child->parent = parent;

  // Grow children array if needed
  if (parent->children.count >= parent->children.capacity) {
    size_t new_cap = parent->children.capacity == 0 ? 4 : parent->children.capacity * 2;
    valk_async_handle_t **new_items = realloc(parent->children.items,
                                               new_cap * sizeof(valk_async_handle_t*));
    if (!new_items) return;  // Allocation failed
    parent->children.items = new_items;
    parent->children.capacity = new_cap;
  }

  parent->children.items[parent->children.count++] = child;
}

// Convert status enum to symbol for Lisp
static valk_lval_t* valk_async_status_to_sym(valk_async_status_t status) {
  switch (status) {
    case VALK_ASYNC_PENDING:   return valk_lval_sym(":pending");
    case VALK_ASYNC_RUNNING:   return valk_lval_sym(":running");
    case VALK_ASYNC_COMPLETED: return valk_lval_sym(":completed");
    case VALK_ASYNC_FAILED:    return valk_lval_sym(":failed");
    case VALK_ASYNC_CANCELLED: return valk_lval_sym(":cancelled");
    default:                   return valk_lval_sym(":unknown");
  }
}

// ============================================================================
// LVAL_HANDLE Constructor
// ============================================================================

valk_lval_t *valk_lval_handle(valk_async_handle_t *handle) {
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_HANDLE | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  res->origin_allocator = valk_thread_ctx.allocator;
  res->gc_next = NULL;
  res->async.handle = handle;
  return res;
}

// ============================================================================
// Async Handle Builtins
// ============================================================================

// aio/cancel: (aio/cancel handle) -> bool
// Request cancellation of an async handle
static valk_lval_t* valk_builtin_aio_cancel(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/cancel: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/cancel: expected handle argument");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;
  bool cancelled = valk_async_handle_cancel(handle);

  return valk_lval_sym(cancelled ? ":true" : ":false");
}

// aio/cancelled?: (aio/cancelled? handle) -> bool
// Check if an async handle has been cancelled
static valk_lval_t* valk_builtin_aio_cancelled(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/cancelled?: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/cancelled?: expected handle argument");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;
  bool cancelled = handle->status == VALK_ASYNC_CANCELLED ||
                   __atomic_load_n(&handle->cancel_requested, __ATOMIC_ACQUIRE);

  return valk_lval_sym(cancelled ? ":true" : ":false");
}

// aio/status: (aio/status handle) -> symbol
// Get the current status of an async handle
static valk_lval_t* valk_builtin_aio_status(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/status: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/status: expected handle argument");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;
  return valk_async_status_to_sym(handle->status);
}

// aio/pure: (aio/pure value) -> handle
// Create an immediately completed handle with the given value
static valk_lval_t* valk_builtin_aio_pure(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/pure: expected 1 argument");
  }
  valk_lval_t *value = valk_lval_list_nth(a, 0);

  // Create a handle that's already completed
  valk_async_handle_t *handle = valk_async_handle_new(NULL, e);
  if (!handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  handle->status = VALK_ASYNC_COMPLETED;
  handle->result = value;

  return valk_lval_handle(handle);
}

// aio/fail: (aio/fail error) -> handle
// Create an immediately failed handle with the given error
static valk_lval_t* valk_builtin_aio_fail(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/fail: expected 1 argument");
  }
  valk_lval_t *error = valk_lval_list_nth(a, 0);

  // Create a handle that's already failed
  valk_async_handle_t *handle = valk_async_handle_new(NULL, e);
  if (!handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  handle->status = VALK_ASYNC_FAILED;
  handle->error = error;

  return valk_lval_handle(handle);
}

// ============================================================================
// Composition Builtins (Phase 2)
// ============================================================================

// aio/then: (aio/then source-handle fn) -> handle
// Chain: when source completes, call fn with result, return new handle
static valk_lval_t* valk_builtin_aio_then(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/then: expected 2 arguments (handle fn)");
  }
  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/then: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/then: second argument must be a function");
  }

  valk_async_handle_t *source = source_lval->async.handle;

  // Create the result handle
  valk_async_handle_t *result = valk_async_handle_new(source->loop, e);
  if (!result) {
    return valk_lval_err("Failed to allocate async handle");
  }

  // If source is already completed, run the transform immediately
  if (source->status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *args = valk_lval_cons(source->result, valk_lval_nil());
    valk_lval_t *transformed = valk_lval_eval_call(e, fn, args);
    if (LVAL_TYPE(transformed) == LVAL_ERR) {
      result->status = VALK_ASYNC_FAILED;
      result->error = transformed;
    } else if (LVAL_TYPE(transformed) == LVAL_HANDLE) {
      // fn returned a handle - chain to it
      valk_async_handle_t *inner = transformed->async.handle;
      if (inner->status == VALK_ASYNC_COMPLETED) {
        result->status = VALK_ASYNC_COMPLETED;
        result->result = inner->result;
      } else if (inner->status == VALK_ASYNC_FAILED) {
        result->status = VALK_ASYNC_FAILED;
        result->error = inner->error;
      } else {
        // Inner handle still running - register callbacks to forward
        result->status = VALK_ASYNC_RUNNING;
        inner->on_complete = valk_lval_lambda(e,
          valk_lval_qcons(valk_lval_sym("x"), valk_lval_nil()),
          valk_lval_nil());  // Placeholder - completion forwarded below
        valk_async_handle_add_child(result, inner);
      }
    } else {
      result->status = VALK_ASYNC_COMPLETED;
      result->result = transformed;
    }
    return valk_lval_handle(result);
  }

  // If source already failed, propagate error
  if (source->status == VALK_ASYNC_FAILED) {
    result->status = VALK_ASYNC_FAILED;
    result->error = source->error;
    return valk_lval_handle(result);
  }

  // If source already cancelled, propagate
  if (source->status == VALK_ASYNC_CANCELLED) {
    result->status = VALK_ASYNC_CANCELLED;
    return valk_lval_handle(result);
  }

  // Source is still pending/running - set up chaining
  // The result handle will be notified when source completes via propagation
  result->status = VALK_ASYNC_RUNNING;
  result->env = e;
  result->on_complete = fn;  // Store transform function - called when source completes
  result->on_error = NULL;   // Errors propagate without transformation
  result->parent = source;   // Mark as waiting on source

  // Add result as child of source for:
  // 1. Cancellation propagation (if source cancelled, cancel result)
  // 2. Completion propagation (valk_async_propagate_completion handles this)
  valk_async_handle_add_child(source, result);

  return valk_lval_handle(result);
}

// Modified completion propagation - called after source completes
// Propagates to chained children (aio/then handles)
static void valk_async_propagate_completion(valk_async_handle_t *source) {
  if (!source) return;

  for (size_t i = 0; i < source->children.count; i++) {
    valk_async_handle_t *child = source->children.items[i];
    // Check if child is a "then" handle (waiting on us)
    if (child->status == VALK_ASYNC_RUNNING && child->parent == source) {
      // Child is waiting for our result
      if (source->status == VALK_ASYNC_COMPLETED) {
        // Call child's transform function with our result
        if (child->on_complete && child->env) {
          valk_lval_t *args = valk_lval_cons(source->result, valk_lval_nil());
          valk_lval_t *transformed = valk_lval_eval_call(child->env, child->on_complete, args);
          if (LVAL_TYPE(transformed) == LVAL_ERR) {
            child->status = VALK_ASYNC_FAILED;
            child->error = transformed;
          } else if (LVAL_TYPE(transformed) == LVAL_HANDLE) {
            // Transform returned a handle - need to chain further
            valk_async_handle_t *inner = transformed->async.handle;
            if (inner->status == VALK_ASYNC_COMPLETED) {
              child->status = VALK_ASYNC_COMPLETED;
              child->result = inner->result;
            } else if (inner->status == VALK_ASYNC_FAILED) {
              child->status = VALK_ASYNC_FAILED;
              child->error = inner->error;
            } else if (inner->status == VALK_ASYNC_CANCELLED) {
              child->status = VALK_ASYNC_CANCELLED;
            } else {
              // Inner still running - link child to inner
              valk_async_handle_add_child(inner, child);
              child->parent = inner;
              // IMPORTANT: Clear the transform function - we already called it
              // and now we're waiting for inner. If we don't clear this, when
              // inner completes and propagates to child, it will call on_complete
              // again, creating an infinite loop.
              child->on_complete = NULL;
              // Transfer HTTP context from child to inner, so the inner can
              // eventually send the HTTP response when it completes
              if (child->session && !inner->session) {
                inner->session = child->session;
                inner->stream_id = child->stream_id;
                inner->conn = child->conn;
                inner->stream_arena = child->stream_arena;
                inner->env = child->env;
                // Clear child's HTTP context so it doesn't try to send response
                child->session = NULL;
                child->stream_id = 0;
                child->conn = NULL;
              }
              // child stays RUNNING, will complete when inner does
              continue;
            }
          } else {
            child->status = VALK_ASYNC_COMPLETED;
            child->result = transformed;
          }
        } else {
          // No transform, just forward result
          child->status = VALK_ASYNC_COMPLETED;
          child->result = source->result;
        }
        // Send HTTP response if this handle has HTTP context
        valk_async_send_http_response(child);
        // Recursively propagate to child's dependents
        valk_async_propagate_completion(child);
      } else if (source->status == VALK_ASYNC_FAILED) {
        // Check if child has error handler (for aio/catch)
        if (child->on_error && child->env) {
          valk_lval_t *args = valk_lval_cons(source->error, valk_lval_nil());
          valk_lval_t *recovered = valk_lval_eval_call(child->env, child->on_error, args);
          if (LVAL_TYPE(recovered) == LVAL_ERR) {
            child->status = VALK_ASYNC_FAILED;
            child->error = recovered;
          } else {
            child->status = VALK_ASYNC_COMPLETED;
            child->result = recovered;
          }
        } else {
          // Propagate failure
          child->status = VALK_ASYNC_FAILED;
          child->error = source->error;
        }
        // Send HTTP response if this handle has HTTP context
        valk_async_send_http_response(child);
        valk_async_propagate_completion(child);
      }
    }
  }
}

// aio/catch: (aio/catch source-handle fn) -> handle
// Handle errors: if source fails, call fn with error
static valk_lval_t* valk_builtin_aio_catch(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/catch: expected 2 arguments (handle fn)");
  }
  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/catch: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/catch: second argument must be a function");
  }

  valk_async_handle_t *source = source_lval->async.handle;

  // Create the result handle
  valk_async_handle_t *catch_handle = valk_async_handle_new(source->loop, e);
  if (!catch_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  // If source already completed successfully, pass through
  if (source->status == VALK_ASYNC_COMPLETED) {
    catch_handle->status = VALK_ASYNC_COMPLETED;
    catch_handle->result = source->result;
    return valk_lval_handle(catch_handle);
  }

  // If source already failed, run the error handler
  if (source->status == VALK_ASYNC_FAILED) {
    valk_lval_t *args = valk_lval_cons(source->error, valk_lval_nil());
    valk_lval_t *recovered = valk_lval_eval_call(e, fn, args);
    if (LVAL_TYPE(recovered) == LVAL_ERR) {
      catch_handle->status = VALK_ASYNC_FAILED;
      catch_handle->error = recovered;
    } else {
      catch_handle->status = VALK_ASYNC_COMPLETED;
      catch_handle->result = recovered;
    }
    return valk_lval_handle(catch_handle);
  }

  // If source cancelled, propagate
  if (source->status == VALK_ASYNC_CANCELLED) {
    catch_handle->status = VALK_ASYNC_CANCELLED;
    return valk_lval_handle(catch_handle);
  }

  // Source still running - register for notification
  catch_handle->status = VALK_ASYNC_RUNNING;
  catch_handle->env = e;
  catch_handle->on_complete = NULL;  // Pass through on success
  catch_handle->on_error = fn;       // Handle errors
  catch_handle->parent = source;

  valk_async_handle_add_child(source, catch_handle);

  return valk_lval_handle(catch_handle);
}

// aio/finally: (aio/finally source-handle fn) -> handle
// Always run cleanup fn, regardless of success/failure/cancel
static valk_lval_t* valk_builtin_aio_finally(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/finally: expected 2 arguments (handle fn)");
  }
  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/finally: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/finally: second argument must be a function");
  }

  valk_async_handle_t *source = source_lval->async.handle;

  // Create the result handle
  valk_async_handle_t *finally_handle = valk_async_handle_new(source->loop, e);
  if (!finally_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  // If source already in terminal state, run cleanup now and preserve outcome
  if (source->status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);  // Run cleanup, ignore result
    finally_handle->status = VALK_ASYNC_COMPLETED;
    finally_handle->result = source->result;
    return valk_lval_handle(finally_handle);
  }
  if (source->status == VALK_ASYNC_FAILED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);  // Run cleanup, ignore result
    finally_handle->status = VALK_ASYNC_FAILED;
    finally_handle->error = source->error;
    return valk_lval_handle(finally_handle);
  }
  if (source->status == VALK_ASYNC_CANCELLED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);  // Run cleanup, ignore result
    finally_handle->status = VALK_ASYNC_CANCELLED;
    return valk_lval_handle(finally_handle);
  }

  // Source still running - register for notification
  finally_handle->status = VALK_ASYNC_RUNNING;
  finally_handle->env = e;
  finally_handle->on_cancel = fn;  // Store cleanup function here (used for finally)
  finally_handle->parent = source;

  valk_async_handle_add_child(source, finally_handle);

  return valk_lval_handle(finally_handle);
}

// Magic marker to identify aio/all contexts
#define VALK_ALL_CTX_MAGIC 0xA11C7821

// Context for aio/all
typedef struct {
  uint32_t magic;                       // Magic marker to identify this context
  valk_async_handle_t *all_handle;
  valk_lval_t **results;
  valk_async_handle_t **handles;        // Array of child handles for index lookup
  size_t total;
  size_t completed;
  bool failed;
  valk_lval_t *first_error;
} valk_all_ctx_t;

// Forward declaration for parent notification
static void valk_async_all_child_completed(valk_async_handle_t *child);
static void valk_async_all_child_failed(valk_async_handle_t *child, valk_lval_t *error);

// aio/all: (aio/all handles-list) -> handle
// Wait for all handles to complete, return list of results
static valk_lval_t* valk_builtin_aio_all(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/all: expected 1 argument (list of handles)");
  }
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  // Count handles and validate
  size_t count = 0;
  valk_lval_t *iter = handles_list;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/all: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/all: all elements must be handles");
    }
    count++;
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    // Empty list - return immediately completed handle with empty list
    valk_async_handle_t *result = valk_async_handle_new(NULL, e);
    result->status = VALK_ASYNC_COMPLETED;
    result->result = valk_lval_nil();
    return valk_lval_handle(result);
  }

  // Create the all_handle
  valk_async_handle_t *all_handle = valk_async_handle_new(NULL, e);
  if (!all_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  // Allocate results array
  valk_lval_t **results = calloc(count, sizeof(valk_lval_t*));
  if (!results) {
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate results array");
  }

  // Check all handles and collect results
  size_t completed = 0;
  bool any_pending = false;
  bool any_failed = false;
  valk_lval_t *first_error = NULL;

  iter = handles_list;
  for (size_t i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;

    if (handle->status == VALK_ASYNC_COMPLETED) {
      results[i] = handle->result;
      completed++;
    } else if (handle->status == VALK_ASYNC_FAILED) {
      any_failed = true;
      if (!first_error) first_error = handle->error;
    } else if (handle->status == VALK_ASYNC_CANCELLED) {
      any_failed = true;
      if (!first_error) first_error = valk_lval_err("cancelled");
    } else {
      any_pending = true;
      // Get event loop from first pending handle
      if (!all_handle->loop && handle->loop) {
        all_handle->loop = handle->loop;
      }
    }
    iter = valk_lval_tail(iter);
  }

  // If any failed, fail immediately and cancel others
  if (any_failed) {
    free(results);
    all_handle->status = VALK_ASYNC_FAILED;
    all_handle->error = first_error;

    // Cancel any pending handles
    iter = handles_list;
    for (size_t i = 0; i < count; i++) {
      valk_lval_t *h = valk_lval_head(iter);
      valk_async_handle_t *handle = h->async.handle;
      if (handle->status == VALK_ASYNC_PENDING || handle->status == VALK_ASYNC_RUNNING) {
        valk_async_handle_cancel(handle);
      }
      iter = valk_lval_tail(iter);
    }
    return valk_lval_handle(all_handle);
  }

  // If all completed, return results immediately
  if (!any_pending) {
    // Build result list
    valk_lval_t *result_list = valk_lval_nil();
    for (size_t i = count; i > 0; i--) {
      result_list = valk_lval_cons(results[i-1], result_list);
    }
    free(results);
    all_handle->status = VALK_ASYNC_COMPLETED;
    all_handle->result = result_list;
    return valk_lval_handle(all_handle);
  }

  // Some handles still pending - set up tracking
  all_handle->status = VALK_ASYNC_RUNNING;
  all_handle->env = e;

  // Allocate handles array for index lookup
  valk_async_handle_t **handles = calloc(count, sizeof(valk_async_handle_t*));
  if (!handles) {
    free(results);
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate handles array");
  }

  // Store results array in handle (hacky: use uv_handle_ptr)
  valk_all_ctx_t *ctx = malloc(sizeof(valk_all_ctx_t));
  if (!ctx) {
    free(results);
    free(handles);
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate all context");
  }
  ctx->magic = VALK_ALL_CTX_MAGIC;
  ctx->all_handle = all_handle;
  ctx->results = results;
  ctx->handles = handles;
  ctx->total = count;
  ctx->completed = completed;
  ctx->failed = false;
  ctx->first_error = NULL;
  all_handle->uv_handle_ptr = ctx;

  // Link all source handles as children and populate handles array
  iter = handles_list;
  for (size_t i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    handles[i] = handle;
    valk_async_handle_add_child(all_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(all_handle);
}

// Helper: Check if a handle's parent is an aio/all context
static inline valk_all_ctx_t* valk_async_get_all_ctx(valk_async_handle_t *handle) {
  if (!handle || !handle->parent) return NULL;
  valk_async_handle_t *parent = handle->parent;
  if (!parent->uv_handle_ptr) return NULL;
  valk_all_ctx_t *ctx = (valk_all_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_ALL_CTX_MAGIC) return NULL;
  return ctx;
}

// Find the index of a child handle in the aio/all context
static inline ssize_t valk_async_all_find_index(valk_all_ctx_t *ctx, valk_async_handle_t *child) {
  for (size_t i = 0; i < ctx->total; i++) {
    if (ctx->handles[i] == child) return (ssize_t)i;
  }
  return -1;
}

// Called when a child of aio/all completes successfully
static void valk_async_all_child_completed(valk_async_handle_t *child) {
  valk_all_ctx_t *ctx = valk_async_get_all_ctx(child);
  if (!ctx) return;
  if (ctx->failed) return;  // Already failed, ignore further completions

  // Find our index in the handles array
  ssize_t idx = valk_async_all_find_index(ctx, child);
  if (idx < 0) return;

  // Store result at our index
  ctx->results[idx] = child->result;
  ctx->completed++;

  // Check if all children have completed
  if (ctx->completed == ctx->total) {
    // Build result list
    valk_lval_t *result_list = valk_lval_nil();
    for (size_t i = ctx->total; i > 0; i--) {
      result_list = valk_lval_cons(ctx->results[i-1], result_list);
    }

    // Complete the all_handle
    ctx->all_handle->status = VALK_ASYNC_COMPLETED;
    ctx->all_handle->result = result_list;

    // Send HTTP response if the all_handle has HTTP context
    valk_async_send_http_response(ctx->all_handle);

    // Propagate to any dependents of all_handle (e.g., aio/then chained on it)
    valk_async_propagate_completion(ctx->all_handle);
  }
}

// Called when a child of aio/all fails
static void valk_async_all_child_failed(valk_async_handle_t *child, valk_lval_t *error) {
  valk_all_ctx_t *ctx = valk_async_get_all_ctx(child);
  if (!ctx) return;
  if (ctx->failed) return;  // Already failed

  ctx->failed = true;
  ctx->first_error = error;

  // Fail the all_handle immediately
  ctx->all_handle->status = VALK_ASYNC_FAILED;
  ctx->all_handle->error = error;

  // Cancel all other pending children
  for (size_t i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    if (h != child && (h->status == VALK_ASYNC_PENDING || h->status == VALK_ASYNC_RUNNING)) {
      valk_async_handle_cancel(h);
    }
  }

  // Send HTTP response if the all_handle has HTTP context
  valk_async_send_http_response(ctx->all_handle);

  // Propagate to any dependents
  valk_async_propagate_completion(ctx->all_handle);
}

// Unified parent notification function called from valk_async_handle_complete/fail
// This checks if the handle's parent is an aio/all context and notifies it
static void valk_async_notify_all_parent(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  // Check magic to see if this is an aio/all context
  // Note: We use VALK_ALL_CTX_MAGIC_EARLY which is defined before this function
  uint32_t *magic_ptr = (uint32_t*)parent->uv_handle_ptr;
  if (*magic_ptr != VALK_ALL_CTX_MAGIC_EARLY) return;

  // It's an aio/all parent - dispatch based on child status
  if (child->status == VALK_ASYNC_COMPLETED) {
    valk_async_all_child_completed(child);
  } else if (child->status == VALK_ASYNC_FAILED) {
    valk_async_all_child_failed(child, child->error);
  }
  // Note: CANCELLED is not handled - the parent will fail eventually if needed
}

// aio/race: (aio/race handles-list) -> handle
// Return first handle to complete (success or failure)
static valk_lval_t* valk_builtin_aio_race(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/race: expected 1 argument (list of handles)");
  }
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  // Validate and find first completed
  size_t count = 0;
  valk_async_handle_t *first_done = NULL;
  valk_lval_t *iter = handles_list;

  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/race: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/race: all elements must be handles");
    }
    valk_async_handle_t *handle = h->async.handle;
    count++;

    // Check if this one is already done
    if (!first_done && (handle->status == VALK_ASYNC_COMPLETED ||
                        handle->status == VALK_ASYNC_FAILED)) {
      first_done = handle;
    }
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    return valk_lval_err("aio/race: cannot race empty list");
  }

  // Create race handle
  valk_async_handle_t *race_handle = valk_async_handle_new(NULL, e);
  if (!race_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  // If we have a winner already, complete immediately and cancel others
  if (first_done) {
    if (first_done->status == VALK_ASYNC_COMPLETED) {
      race_handle->status = VALK_ASYNC_COMPLETED;
      race_handle->result = first_done->result;
    } else {
      race_handle->status = VALK_ASYNC_FAILED;
      race_handle->error = first_done->error;
    }

    // Cancel all other handles
    iter = handles_list;
    while (LVAL_TYPE(iter) != LVAL_NIL) {
      valk_lval_t *h = valk_lval_head(iter);
      valk_async_handle_t *handle = h->async.handle;
      if (handle != first_done &&
          (handle->status == VALK_ASYNC_PENDING || handle->status == VALK_ASYNC_RUNNING)) {
        valk_async_handle_cancel(handle);
      }
      iter = valk_lval_tail(iter);
    }
    return valk_lval_handle(race_handle);
  }

  // All handles still pending - set up race
  race_handle->status = VALK_ASYNC_RUNNING;
  race_handle->env = e;

  // Get event loop from first handle
  iter = handles_list;
  if (LVAL_TYPE(iter) != LVAL_NIL) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    race_handle->loop = handle->loop;
  }

  // Link all source handles as children
  iter = handles_list;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    valk_async_handle_add_child(race_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(race_handle);
}

// aio/any: (aio/any handles-list) -> handle
// Return first handle to succeed (ignore failures until all fail)
static valk_lval_t* valk_builtin_aio_any(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/any: expected 1 argument (list of handles)");
  }
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  // Count and validate
  size_t count = 0;
  size_t failed_count = 0;
  valk_async_handle_t *first_success = NULL;
  valk_lval_t *last_error = NULL;
  valk_lval_t *iter = handles_list;

  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/any: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/any: all elements must be handles");
    }
    valk_async_handle_t *handle = h->async.handle;
    count++;

    if (handle->status == VALK_ASYNC_COMPLETED && !first_success) {
      first_success = handle;
    } else if (handle->status == VALK_ASYNC_FAILED ||
               handle->status == VALK_ASYNC_CANCELLED) {
      failed_count++;
      last_error = handle->error ? handle->error : valk_lval_err("cancelled");
    }
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    return valk_lval_err("aio/any: cannot use with empty list");
  }

  // Create any handle
  valk_async_handle_t *any_handle = valk_async_handle_new(NULL, e);
  if (!any_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  // If we have a success, complete immediately and cancel others
  if (first_success) {
    any_handle->status = VALK_ASYNC_COMPLETED;
    any_handle->result = first_success->result;

    // Cancel remaining
    iter = handles_list;
    while (LVAL_TYPE(iter) != LVAL_NIL) {
      valk_lval_t *h = valk_lval_head(iter);
      valk_async_handle_t *handle = h->async.handle;
      if (handle != first_success &&
          (handle->status == VALK_ASYNC_PENDING || handle->status == VALK_ASYNC_RUNNING)) {
        valk_async_handle_cancel(handle);
      }
      iter = valk_lval_tail(iter);
    }
    return valk_lval_handle(any_handle);
  }

  // If all failed, fail with last error
  if (failed_count == count) {
    any_handle->status = VALK_ASYNC_FAILED;
    any_handle->error = last_error;
    return valk_lval_handle(any_handle);
  }

  // Some handles still pending
  any_handle->status = VALK_ASYNC_RUNNING;
  any_handle->env = e;

  // Get event loop from first pending handle
  iter = handles_list;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    if (handle->loop) {
      any_handle->loop = handle->loop;
      break;
    }
    iter = valk_lval_tail(iter);
  }

  // Link all source handles as children
  iter = handles_list;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    valk_async_handle_add_child(any_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(any_handle);
}

// aio/on-cancel: (aio/on-cancel handle fn) -> handle
// Register a callback to run if handle is cancelled
static valk_lval_t* valk_builtin_aio_on_cancel(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/on-cancel: expected 2 arguments (handle fn)");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/on-cancel: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/on-cancel: second argument must be a function");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;

  // If already cancelled, run callback immediately
  if (handle->status == VALK_ASYNC_CANCELLED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);
    return handle_lval;
  }

  // Register the callback
  handle->on_cancel = fn;
  if (!handle->env) handle->env = e;

  return handle_lval;
}

// ============================================================================
// Resource Safety Builtins (Phase 3)
// ============================================================================

// aio/bracket: (aio/bracket acquire release use) -> handle
// Safe resource management: acquire, use, ALWAYS release
// - acquire: handle that produces a resource
// - release: (\ {resource} ...) called ALWAYS after use completes/fails/cancels
// - use: (\ {resource} ...) the main operation
static valk_lval_t* valk_builtin_aio_bracket(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 3) {
    return valk_lval_err("aio/bracket: expected 3 arguments (acquire release use)");
  }
  valk_lval_t *acquire_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *release_fn = valk_lval_list_nth(a, 1);
  valk_lval_t *use_fn = valk_lval_list_nth(a, 2);

  if (LVAL_TYPE(acquire_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/bracket: first argument must be a handle");
  }
  if (LVAL_TYPE(release_fn) != LVAL_FUN) {
    return valk_lval_err("aio/bracket: second argument must be a function");
  }
  if (LVAL_TYPE(use_fn) != LVAL_FUN) {
    return valk_lval_err("aio/bracket: third argument must be a function");
  }

  valk_async_handle_t *acquire = acquire_lval->async.handle;

  // Create the bracket handle
  valk_async_handle_t *bracket_handle = valk_async_handle_new(acquire->loop, e);
  if (!bracket_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }

  // If acquire already completed, run use immediately
  if (acquire->status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *resource = acquire->result;

    // Call use with resource
    valk_lval_t *use_args = valk_lval_cons(resource, valk_lval_nil());
    valk_lval_t *use_result = valk_lval_eval_call(e, use_fn, use_args);

    // Check if use returned a handle
    if (LVAL_TYPE(use_result) == LVAL_HANDLE) {
      valk_async_handle_t *use_handle = use_result->async.handle;

      // Wait for use handle to complete, then run release
      if (use_handle->status == VALK_ASYNC_COMPLETED ||
          use_handle->status == VALK_ASYNC_FAILED ||
          use_handle->status == VALK_ASYNC_CANCELLED) {
        // Use already done - run release now
        valk_lval_t *release_args = valk_lval_cons(resource, valk_lval_nil());
        valk_lval_eval_call(e, release_fn, release_args);  // Ignore release result

        if (use_handle->status == VALK_ASYNC_COMPLETED) {
          bracket_handle->status = VALK_ASYNC_COMPLETED;
          bracket_handle->result = use_handle->result;
        } else if (use_handle->status == VALK_ASYNC_FAILED) {
          bracket_handle->status = VALK_ASYNC_FAILED;
          bracket_handle->error = use_handle->error;
        } else {
          bracket_handle->status = VALK_ASYNC_CANCELLED;
        }
      } else {
        // Use handle still running - set up finally for release
        bracket_handle->status = VALK_ASYNC_RUNNING;
        bracket_handle->env = e;
        bracket_handle->parent = use_handle;

        // Store release_fn and resource for later
        // We use on_cancel to store the release function
        // and uv_handle_ptr to store the resource
        bracket_handle->on_cancel = release_fn;
        bracket_handle->result = resource;  // Temporarily store resource here

        valk_async_handle_add_child(use_handle, bracket_handle);
      }
    } else if (LVAL_TYPE(use_result) == LVAL_ERR) {
      // Use failed synchronously - run release and propagate error
      valk_lval_t *release_args = valk_lval_cons(resource, valk_lval_nil());
      valk_lval_eval_call(e, release_fn, release_args);

      bracket_handle->status = VALK_ASYNC_FAILED;
      bracket_handle->error = use_result;
    } else {
      // Use returned a non-handle value - run release and complete
      valk_lval_t *release_args = valk_lval_cons(resource, valk_lval_nil());
      valk_lval_eval_call(e, release_fn, release_args);

      bracket_handle->status = VALK_ASYNC_COMPLETED;
      bracket_handle->result = use_result;
    }

    return valk_lval_handle(bracket_handle);
  }

  // If acquire failed, fail immediately (no release needed)
  if (acquire->status == VALK_ASYNC_FAILED) {
    bracket_handle->status = VALK_ASYNC_FAILED;
    bracket_handle->error = acquire->error;
    return valk_lval_handle(bracket_handle);
  }

  // If acquire cancelled, cancel bracket (no release needed)
  if (acquire->status == VALK_ASYNC_CANCELLED) {
    bracket_handle->status = VALK_ASYNC_CANCELLED;
    return valk_lval_handle(bracket_handle);
  }

  // Acquire still running - set up continuation
  bracket_handle->status = VALK_ASYNC_RUNNING;
  bracket_handle->env = e;

  // Store use_fn in on_complete and release_fn in on_cancel
  // When acquire completes, propagation will call on_complete (use_fn)
  // Then we need to ensure release is called after use completes
  bracket_handle->on_complete = use_fn;
  bracket_handle->on_cancel = release_fn;
  bracket_handle->parent = acquire;

  valk_async_handle_add_child(acquire, bracket_handle);

  return valk_lval_handle(bracket_handle);
}

// aio/scope: (aio/scope fn) -> handle
// Creates a cancellation scope. All handles created inside fn are children of this scope.
// fn receives a scope parameter that can be used to track child handles
static valk_lval_t* valk_builtin_aio_scope(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/scope: expected 1 argument (fn)");
  }
  valk_lval_t *fn = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/scope: argument must be a function");
  }

  // Create the scope handle
  valk_async_handle_t *scope_handle = valk_async_handle_new(NULL, e);
  if (!scope_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  scope_handle->status = VALK_ASYNC_RUNNING;
  scope_handle->env = e;

  // Create an lval for the scope handle to pass to fn
  valk_lval_t *scope_lval = valk_lval_handle(scope_handle);

  // Call fn with the scope handle
  // User can use this to manually add children if needed
  valk_lval_t *args = valk_lval_cons(scope_lval, valk_lval_nil());
  valk_lval_t *result = valk_lval_eval_call(e, fn, args);

  // Check what fn returned
  if (LVAL_TYPE(result) == LVAL_ERR) {
    scope_handle->status = VALK_ASYNC_FAILED;
    scope_handle->error = result;
    return scope_lval;
  }

  if (LVAL_TYPE(result) == LVAL_HANDLE) {
    // fn returned a handle - scope waits for that handle
    valk_async_handle_t *inner = result->async.handle;

    // Add inner as child of scope
    valk_async_handle_add_child(scope_handle, inner);

    if (inner->status == VALK_ASYNC_COMPLETED) {
      scope_handle->status = VALK_ASYNC_COMPLETED;
      scope_handle->result = inner->result;
    } else if (inner->status == VALK_ASYNC_FAILED) {
      scope_handle->status = VALK_ASYNC_FAILED;
      scope_handle->error = inner->error;
    } else if (inner->status == VALK_ASYNC_CANCELLED) {
      scope_handle->status = VALK_ASYNC_CANCELLED;
    } else {
      // Inner still running - scope stays running
      scope_handle->parent = inner;  // Wait on inner
      inner->on_complete = NULL;  // Use propagation
    }
    return scope_lval;
  }

  // fn returned a regular value - scope completes immediately
  scope_handle->status = VALK_ASYNC_COMPLETED;
  scope_handle->result = result;
  return scope_lval;
}

// Register the async handle builtins
void valk_register_async_handle_builtins(valk_lenv_t *env) {
  // Core operations (Phase 1)
  valk_lenv_put_builtin(env, "aio/cancel", valk_builtin_aio_cancel);
  valk_lenv_put_builtin(env, "aio/cancelled?", valk_builtin_aio_cancelled);
  valk_lenv_put_builtin(env, "aio/status", valk_builtin_aio_status);
  valk_lenv_put_builtin(env, "aio/pure", valk_builtin_aio_pure);
  valk_lenv_put_builtin(env, "aio/fail", valk_builtin_aio_fail);

  // Composition operations (Phase 2)
  valk_lenv_put_builtin(env, "aio/then", valk_builtin_aio_then);
  valk_lenv_put_builtin(env, "aio/catch", valk_builtin_aio_catch);
  valk_lenv_put_builtin(env, "aio/finally", valk_builtin_aio_finally);
  valk_lenv_put_builtin(env, "aio/all", valk_builtin_aio_all);
  valk_lenv_put_builtin(env, "aio/race", valk_builtin_aio_race);
  valk_lenv_put_builtin(env, "aio/any", valk_builtin_aio_any);
  valk_lenv_put_builtin(env, "aio/on-cancel", valk_builtin_aio_on_cancel);

  // Timer and monadic operations
  valk_lenv_put_builtin(env, "aio/sleep", valk_builtin_aio_sleep);
  valk_lenv_put_builtin(env, "aio/let", valk_builtin_aio_let);
  valk_lenv_put_builtin(env, "aio/do", valk_builtin_aio_do);

  // Resource safety operations (Phase 3)
  valk_lenv_put_builtin(env, "aio/bracket", valk_builtin_aio_bracket);
  valk_lenv_put_builtin(env, "aio/scope", valk_builtin_aio_scope);
}
