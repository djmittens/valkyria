#pragma once

#include <stddef.h>
#include <stdatomic.h>
#include "concurrency.h"
#include "memory.h"
#include "aio_types.h"

#define VALK_HTTP_MOTD "<!DOCTYPE html><html><head><meta charset=\"UTF-8\"><title>Valkyria HTTP/2 Server</title><style>body{font-family:system-ui,sans-serif;max-width:800px;margin:80px auto;padding:0 20px;background:#0a0e27;color:#e0e0e0}h1{color:#00d9ff;font-size:3em;margin-bottom:0.2em}p{font-size:1.2em;line-height:1.6;color:#b0b0b0}code{background:#1a1e3a;padding:2px 8px;border-radius:4px;color:#00d9ff}</style></head><body><h1>\u269C Valkyria</h1><p>Valhalla's Treasure - HTTP/2 Server</p><p>This is a <code>Valkyria Lisp</code> web server running on nghttp2 with TLS.</p><p style=\"margin-top:40px;font-size:0.9em;opacity:0.7\">Server is operational and ready to handle requests.</p></body></html>"

// Forward declarations for libuv types
typedef struct uv_timer_s uv_timer_t;
typedef struct uv_handle_s uv_handle_t;

// Forward declarations for parser.h types
struct valk_lval_t;
struct valk_lenv_t;
struct valk_mem_arena;

// Async handle - represents an in-flight async operation
// This is the main structure for composable async operations.
//
// The async system is decoupled from specific I/O layers (HTTP, files, etc).
// Each layer registers callbacks to handle completion and detect cancellation.
//
// Lifecycle: Reference counted. Call valk_async_handle_ref() to keep alive,
// valk_async_handle_unref() when done. Cleanup callbacks run when refcount hits 0.
//
// Concurrency: The status field is atomic to handle races between cancel and
// complete. State transitions use compare-exchange: first to CAS wins.
struct valk_async_handle_t {
  u64 id;
  _Atomic valk_async_status_t status;

  _Atomic int cancel_requested;

  void *uv_handle_ptr;
  struct valk_aio_system *sys;

  struct valk_lval_t *on_complete;
  struct valk_lval_t *on_error;
  struct valk_lval_t *on_cancel;
  struct valk_lenv_t *env;

  struct valk_lval_t *result;
  struct valk_lval_t *error;

  valk_mem_allocator_t *allocator;

  valk_async_done_fn on_done;
  void *on_done_ctx;

  valk_async_is_closed_fn is_closed;
  void *is_closed_ctx;

  struct valk_async_handle_t *parent;
  struct {
    struct valk_async_handle_t **items;
    u64 count;
    u64 capacity;
  } children;

  struct valk_async_handle_t *prev;
  struct valk_async_handle_t *next;

  _Atomic u32 refcount;

  struct {
    valk_async_cleanup_fn fn;
    void *ctx;
  } *cleanup_callbacks;
  u32 cleanup_count;
  u32 cleanup_capacity;
};

valk_async_handle_t *valk_async_handle_ref(valk_async_handle_t *handle);
void valk_async_handle_unref(valk_async_handle_t *handle);
u32 valk_async_handle_refcount(valk_async_handle_t *handle);
void valk_async_handle_on_cleanup(valk_async_handle_t *handle,
                                   valk_async_cleanup_fn fn, void *ctx);

static inline bool valk_async_handle_is_cancelled(valk_async_handle_t *handle) {
  if (!handle) return false;
  return atomic_load_explicit(&handle->cancel_requested, memory_order_acquire) != 0;
}

static inline valk_async_status_t valk_async_handle_get_status(valk_async_handle_t *handle) {
  if (!handle) return VALK_ASYNC_CANCELLED;
  return atomic_load_explicit(&handle->status, memory_order_acquire);
}

static inline bool valk_async_handle_try_transition(
    valk_async_handle_t *handle,
    valk_async_status_t expected,
    valk_async_status_t desired) {
  if (!handle) return false;
  return atomic_compare_exchange_strong_explicit(
      &handle->status, &expected, desired,
      memory_order_acq_rel, memory_order_acquire);
}

static inline bool valk_async_handle_is_terminal(valk_async_status_t status) {
  return status == VALK_ASYNC_COMPLETED ||
         status == VALK_ASYNC_FAILED ||
         status == VALK_ASYNC_CANCELLED;
}

void valk_register_async_handle_builtins(struct valk_lenv_t *env);

// HTTP/2 client request implementation (called from parser.c builtin)
struct valk_lval_t *valk_http2_client_request_impl(struct valk_lenv_t *e,
                                                    valk_aio_system_t *sys,
                                                    const char *host, int port,
                                                    const char *path,
                                                    struct valk_lval_t *callback);

// HTTP/2 client request with custom headers
struct valk_lval_t *valk_http2_client_request_with_headers_impl(struct valk_lenv_t *e,
                                                    valk_aio_system_t *sys,
                                                    const char *host, int port,
                                                    const char *path,
                                                    struct valk_lval_t *headers,
                                                    struct valk_lval_t *callback);

// Top-level timer scheduling (no HTTP context required)
struct valk_lval_t *valk_aio_schedule(valk_aio_system_t *sys, u64 delay_ms,
                                       struct valk_lval_t *callback,
                                       struct valk_lenv_t *env);

// Repeating interval timer - callback returns :stop to cancel
struct valk_lval_t *valk_aio_interval(valk_aio_system_t *sys, u64 interval_ms,
                                       struct valk_lval_t *callback,
                                       struct valk_lenv_t *env);

typedef struct valk_http2_request_t {
  valk_mem_allocator_t *allocator;
  char *method;
  char *scheme;
  char *authority;
  char *path;
  struct {
    struct valk_http2_header_t *items;
    u64 count;
    u64 capacity;
  } headers;
  void *ctx;
  u8 *body;
  u64 bodyLen;
  u64 bodyCapacity;
} valk_http2_request_t;

typedef struct valk_http2_response_t {
  i32 stream_id;

  valk_mem_allocator_t *allocator;
  valk_http2_request_t *req;
  const char *status;
  struct {
    struct valk_http2_header_t *items;
    u64 count;
    u64 capacity;
  } headers;

  bool headersReceived;
  bool bodyReceived;

  u8 *body;
  u64 bodyLen;
  u64 bodyCapacity;

  valk_promise _promise;
} valk_http2_response_t;

valk_aio_system_t *valk_aio_start();

/// @brief Start AIO system with custom configuration
/// @param config System configuration (nullptr for defaults)
/// @return AIO system handle
valk_aio_system_t *valk_aio_start_with_config(valk_aio_system_config_t *config);

/// @brief Resolve derived values (called automatically by valk_aio_start_with_config)
/// Fills in any 0-valued fields with derived/default values
/// Returns 0 on success, -1 on validation failure
int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg);

/// @brief Validate configuration
/// Returns nullptr on success, or error message on failure
const char *valk_aio_system_config_validate(const valk_aio_system_config_t *cfg);

void valk_aio_stop(valk_aio_system_t *sys);

/// @brief Check if the AIO system is shutting down
bool valk_aio_is_shutting_down(valk_aio_system_t *sys);

/// @brief Wait for shutdown to complete and cleanup resources
void valk_aio_wait_for_shutdown(valk_aio_system_t *sys);

/// @brief Wake all AIO event loops for GC synchronization
/// Called by the GC coordinator when requesting stop-the-world
void valk_aio_wake_all_for_gc(void);

typedef struct {
  void *arg;
  void (*onConnect)(void *arg, valk_aio_handle_t *);
  void (*onDisconnect)(void *arg, valk_aio_handle_t *);
  void (*onHeader)(void *arg, valk_aio_handle_t *, u64 stream, char *name,
                   char *value);
  void (*onBody)(void *arg, valk_aio_handle_t *, u64 stream, u8 flags,
                 valk_buffer_t *buf);
} valk_http2_handler_t;

// System configuration for AIO pools
typedef struct valk_aio_system_config {
  // PRIMARY TUNING PARAMETERS
  u32 max_connections;          // Default: 100
  u32 max_concurrent_streams;   // Default: 100 (per connection, sent via SETTINGS)

  // CAPACITY LIMITS
  u32 max_handles;              // Default: 2056
  u32 max_servers;              // Default: 8
  u32 max_clients;              // Default: 8
  u32 max_connections_per_client; // Default: 2 (connections per HTTP/2 client)
  u32 max_timers;               // Default: max_handles / 4

  // DERIVED SETTINGS (set to 0 for auto-calculation)
  u32 tcp_buffer_pool_size;     // Auto: 2 × total_connections
  u32 arena_pool_size;          // Auto: max_connections × 2
  u32 queue_capacity;           // Auto: max_connections × 2

  // MEMORY SIZING
  u64   arena_size;               // Default: 64MB per arena
  u64   max_request_body_size;    // Default: 8MB (required - requests are buffered)

  // THREAD ONBOARDING
  void (*thread_onboard_fn)(void);  // Function to call when event loop thread starts

  // BACKPRESSURE SETTINGS
  float    buffer_high_watermark;     // Default: 0.85 (85%) - start load shedding
  float    buffer_critical_watermark; // Default: 0.95 (95%) - reject all new conns
  u32 min_buffers_per_conn;      // Default: 4 (BUFFERS_PER_CONNECTION)

  // BACKPRESSURE TIMING
  u32 backpressure_list_max;     // Default: 1000
  u32 backpressure_timeout_ms;   // Default: 30000 (30s)

  // CONNECTION TIMEOUT SETTINGS
  u32 connection_idle_timeout_ms;  // Default: 60000 (60s) - close idle connections
  u32 maintenance_interval_ms;     // Default: 1000 (1s) - timer for timeout checks
} valk_aio_system_config_t;

// Default system configuration
static inline valk_aio_system_config_t valk_aio_system_config_default(void) {
  return (valk_aio_system_config_t){0};
}

// Server configuration for HTTP/2 server behavior
typedef struct valk_http_server_config {
  u64      max_response_body_size;  // Default: 64MB (Lisp API limit, not C runtime)
  const char* error_503_body;          // Pre-rendered overload response
  u64      error_503_body_len;

  // SSE CONFIGURATION
  u64      sse_buffer_size;         // Default: 64KB (pending write buffer per stream)
  u32    sse_queue_max;           // Default: 1000 (event queue depth)
} valk_http_server_config_t;

// Default server configuration
static inline valk_http_server_config_t valk_http_server_config_default(void) {
  return (valk_http_server_config_t){
    .max_response_body_size = 64 * 1024 * 1024,  // 64MB
    .error_503_body = nullptr,
    .error_503_body_len = 0,
    .sse_buffer_size = 64 * 1024,   // 64KB
    .sse_queue_max = 1000,
  };
}

// Client configuration for HTTP/2 client behavior
typedef struct valk_http_client_config {
  u32 max_concurrent_streams;     // Default: 100
  u64   max_response_body_size;     // Default: 64MB
  u32 connect_timeout_ms;         // Default: 30000 (30s)
  u32 request_timeout_ms;         // Default: 60000 (60s)

  // Connection pooling (future use)
  u32 max_idle_connections;       // Default: 0 (no pooling)
  u32 keepalive_ms;               // Default: 0 (close after use)
} valk_http_client_config_t;

// Default client configuration
static inline valk_http_client_config_t valk_http_client_config_default(void) {
  return (valk_http_client_config_t){
    .max_concurrent_streams = 100,
    .max_response_body_size = 64 * 1024 * 1024,  // 64MB
    .connect_timeout_ms = 30000,
    .request_timeout_ms = 60000,
    .max_idle_connections = 0,
    .keepalive_ms = 0,
  };
}

// ============================================================================
// Configuration Presets
// ============================================================================

// Demo profile: low resource usage, good for demos and development
// Ratios: arena_pool_size >= max_concurrent_streams * 3 (handles 3 full connections)
static inline valk_aio_system_config_t valk_aio_config_demo(void) {
  return (valk_aio_system_config_t){
    .max_connections = 8,
    .max_concurrent_streams = 8,        // 8 streams/conn × 8 conns = 64 max
    .max_handles = 128,
    .max_servers = 3,
    .max_clients = 3,
    .arena_size = 4 * 1024 * 1024,      // 4MB per arena
    .arena_pool_size = 24,              // 24 × 4MB = 96MB (3x a full connection)
    .max_request_body_size = 1 * 1024 * 1024,  // 1MB
    .backpressure_list_max = 50,
    .backpressure_timeout_ms = 30000,
  };
}

// Production profile: high capacity for production deployments
// Memory: 1000 arenas × 4MB = 4GB (reasonable for production server)
// Capacity: 100 conns × 100 streams = 10,000 max concurrent, 1000 arenas = 10 saturated conns
static inline valk_aio_system_config_t valk_aio_config_production(void) {
  return (valk_aio_system_config_t){
    .max_connections = 100,
    .max_concurrent_streams = 100,      // RFC 7540 minimum, good balance
    .max_handles = 4096,
    .max_servers = 8,
    .max_clients = 8,
    .arena_size = 4 * 1024 * 1024,      // 4MB (sufficient for most requests)
    .arena_pool_size = 1000,            // 4GB total, handles 10 saturated connections
    .max_request_body_size = 8 * 1024 * 1024,  // 8MB
    .backpressure_list_max = 5000,
    .backpressure_timeout_ms = 30000,
  };
}

// Minimal profile: embedded systems and testing
// Memory: 12 arenas × 1MB = 12MB total
// Capacity: 4 conns × 4 streams = 16 max concurrent, 12 arenas = 3 saturated conns
static inline valk_aio_system_config_t valk_aio_config_minimal(void) {
  return (valk_aio_system_config_t){
    .max_connections = 4,
    .max_concurrent_streams = 4,        // Low streams to match small arena pool
    .max_handles = 64,
    .max_servers = 1,
    .max_clients = 1,
    .arena_size = 1 * 1024 * 1024,      // 1MB
    .arena_pool_size = 12,              // 12MB total, handles 3 saturated connections
    .max_request_body_size = 256 * 1024,  // 256KB
    .backpressure_list_max = 16,
    .backpressure_timeout_ms = 10000,
  };
}

// High-throughput API profile: maximum requests per second, small payloads
// Memory: 2000 arenas × 1MB = 2GB total
// Capacity: 50 conns × 256 streams = 12,800 max concurrent
static inline valk_aio_system_config_t valk_aio_config_api(void) {
  return (valk_aio_system_config_t){
    .max_connections = 50,
    .max_concurrent_streams = 256,      // High multiplexing for APIs
    .max_handles = 2048,
    .max_servers = 4,
    .max_clients = 4,
    .arena_size = 1 * 1024 * 1024,      // 1MB (small API payloads)
    .arena_pool_size = 2000,            // 2GB total
    .max_request_body_size = 1 * 1024 * 1024,  // 1MB
    .backpressure_list_max = 2000,
    .backpressure_timeout_ms = 15000,   // Faster timeout for APIs
  };
}

// Large payload profile: file uploads and downloads
// Memory: 64 arenas × 64MB = 4GB total
// Capacity: 20 conns × 16 streams = 320 max concurrent (but large payloads)
static inline valk_aio_system_config_t valk_aio_config_large_payload(void) {
  return (valk_aio_system_config_t){
    .max_connections = 20,
    .max_concurrent_streams = 16,       // Fewer streams for large payloads
    .max_handles = 512,
    .max_servers = 4,
    .max_clients = 4,
    .arena_size = 64 * 1024 * 1024,     // 64MB for large files
    .arena_pool_size = 64,              // 4GB total
    .max_request_body_size = 128 * 1024 * 1024,  // 128MB uploads
    .backpressure_list_max = 100,
    .backpressure_timeout_ms = 60000,   // Longer timeout for large transfers
  };
}

// Demo server config: smaller buffers for demos
static inline valk_http_server_config_t valk_http_server_config_demo(void) {
  return (valk_http_server_config_t){
    .max_response_body_size = 8 * 1024 * 1024,  // 8MB
    .error_503_body = nullptr,
    .error_503_body_len = 0,
    .sse_buffer_size = 32 * 1024,   // 32KB
    .sse_queue_max = 100,
  };
}

///
/// @brief start a new htt2 listening server on a port
///
/// @param[out] srv the server that will be running
/// @param[in] sys the aio system that will run the server
/// @return returns an async handle that resolves to the server ref
///
valk_async_handle_t *valk_aio_http2_listen(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler);

/// @brief Start HTTP/2 server with custom configuration
/// @param[in] sys the aio system that will run the server
/// @param[in] interface the interface to bind to (e.g., "0.0.0.0")
/// @param[in] port the port number to listen on
/// @param[in] keyfile path to TLS private key file
/// @param[in] certfile path to TLS certificate file
/// @param[in] handler C function handler (optional, can be nullptr)
/// @param[in] lisp_handler Lisp function handler (optional, can be nullptr)
/// @param[in] config server configuration (optional, uses defaults if nullptr)
/// @return returns an async handle that resolves to the server ref
valk_async_handle_t *valk_aio_http2_listen_with_config(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler,
                                   valk_http_server_config_t *config);

/// @brief Set a Lisp handler function for HTTP/2 requests
/// @param srv The HTTP/2 server
/// @param handler_fn Lisp lambda (GC heap allocated) with signature (lambda {req k} ...)
void valk_aio_http2_server_set_handler(valk_aio_http_server *srv, void *handler_fn);

/// @brief Get the actual bound port (useful when listening on port 0)
/// @param srv The HTTP/2 server
/// @return The actual port number the server is listening on
int valk_aio_http2_server_get_port(valk_aio_http_server *srv);

/// @brief Extract the server from a server ref lval (unwraps arc_box)
/// @param server_ref LVAL_REF containing the server arc_box
/// @return The HTTP/2 server pointer
valk_aio_http_server* valk_aio_http2_server_from_ref(struct valk_lval_t *server_ref);

/// @brief Get port from a server ref lval (convenience wrapper)
/// @param server_ref LVAL_REF containing the server arc_box
/// @return The actual port number the server is listening on
int valk_aio_http2_server_get_port_from_ref(struct valk_lval_t *server_ref);

/// @brief Gracefully stop an HTTP/2 server
/// @param srv The HTTP/2 server to stop
/// @param box The arc_box containing the server (for ref counting)
/// @return Async handle that completes when server is stopped
valk_async_handle_t *valk_aio_http2_stop(valk_aio_http_server *srv,
                                         struct valk_arc_box *box);

///
/// @return returns an async handle that completes with the client
///
valk_async_handle_t *valk_aio_http2_connect(valk_aio_system_t *sys,
                                             const char *interface, const int port,
                                             const char *certfile);

// Connect to an IP with an explicit SNI/hostname used for TLS and HTTP/2.
// Returns an async handle that completes with the client.
valk_async_handle_t *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                                  const char *ip, const int port,
                                                  const char *hostname);

valk_async_handle_t *valk_aio_http2_request_send(valk_http2_request_t *req,
                                                  valk_aio_http2_client *client);

#ifdef VALK_METRICS_ENABLED
#include "aio_metrics.h"
#include "gc.h"

// Get metrics from AIO system (returns nullptr if metrics not enabled)
valk_aio_metrics_t* valk_aio_get_metrics(valk_aio_system_t* sys);

// Get system stats from AIO system (returns nullptr if metrics not enabled)
valk_aio_system_stats_t* valk_aio_get_system_stats(valk_aio_system_t* sys);

// Get HTTP clients registry from AIO system (returns nullptr if metrics not enabled)
valk_http_clients_registry_t* valk_aio_get_http_clients_registry(valk_aio_system_t* sys);

// Update queue stats from HTTP queue (call before rendering metrics)
void valk_aio_update_queue_stats(valk_aio_system_t* sys);

// Get GC heap from AIO system (returns nullptr if metrics not enabled)
valk_gc_malloc_heap_t* valk_aio_get_gc_heap(valk_aio_system_t* sys);

// Get scratch arena from AIO system (for diagnostics, returns nullptr if not available)
valk_mem_arena_t* valk_aio_get_scratch_arena(valk_aio_system_t* sys);

// ============================================================================
// Connection Diagnostics Types (for SSE memory diagnostics)
// ============================================================================

// Handle types for dashboard visualization (mirrors internal handle_kind_t)
typedef enum {
  VALK_DIAG_HNDL_EMPTY = 0,     // Slot not allocated
  VALK_DIAG_HNDL_TCP,           // TCP server listener
  VALK_DIAG_HNDL_TASK,          // Async task handle
  VALK_DIAG_HNDL_TIMER,         // Timer handle (aio/delay)
  VALK_DIAG_HNDL_HTTP_CONN,     // HTTP/2 connection (server or client)
} valk_diag_handle_kind_e;

// Connection states for dashboard visualization (only for HTTP_CONN handles)
typedef enum {
  VALK_DIAG_CONN_FREE = 0,      // Slot not allocated
  VALK_DIAG_CONN_CONNECTING,    // TCP handshake in progress
  VALK_DIAG_CONN_ACTIVE,        // Processing request/response
  VALK_DIAG_CONN_IDLE,          // Pooled, awaiting reuse
  VALK_DIAG_CONN_CLOSING,       // Graceful shutdown
} valk_diag_conn_state_e;

// Per-handle diagnostics metadata
typedef struct {
  valk_diag_conn_state_e state;
  u16 owner_idx;          // Index into owner registry (server/client ID)
  u64 state_change_time;  // Timestamp of last state change (ms since epoch)
} valk_handle_diag_t;

// Owner registry for server/client attribution (defined in aio_uv.c)
typedef struct valk_owner_entry valk_owner_entry_t;
typedef struct valk_owner_registry valk_owner_registry_t;

// Owner registry API
u16 valk_owner_register(valk_aio_system_t *sys, const char *name, u8 type, void *ptr);
const char* valk_owner_get_name(valk_aio_system_t *sys, u16 idx);
u64 valk_owner_get_count(valk_aio_system_t *sys);

// Get slab allocators for memory diagnostics
valk_slab_t* valk_aio_get_tcp_buffer_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_handle_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_stream_arenas_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_http_servers_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_http_clients_slab(valk_aio_system_t* sys);

// Get diagnostics for a handle at a given slab slot index
// Returns false if slot is invalid or not an HTTP connection handle
bool valk_aio_get_handle_diag(valk_aio_system_t* sys, u64 slot_idx,
                               valk_handle_diag_t* out_diag);

// Get the kind of handle at a given slab slot index
// Returns VALK_DIAG_HNDL_EMPTY if slot is invalid or free
valk_diag_handle_kind_e valk_aio_get_handle_kind(valk_aio_system_t* sys, u64 slot_idx);

// Timer handle management (allocates from handle slab)
valk_aio_handle_t* valk_aio_timer_alloc(valk_aio_system_t* sys);
void valk_aio_timer_init(valk_aio_handle_t* handle);
void valk_aio_timer_start(valk_aio_handle_t* handle, u64 timeout_ms, u64 repeat_ms,
                           void (*callback)(uv_timer_t*));
void valk_aio_timer_stop(valk_aio_handle_t* handle);
void valk_aio_timer_close(valk_aio_handle_t* handle, void (*close_cb)(uv_handle_t*));
void valk_aio_timer_set_data(valk_aio_handle_t* handle, void* data);
void valk_aio_timer_free(valk_aio_handle_t* handle);
#endif

// Get the event loop from AIO system (returns nullptr if no loop available)
struct uv_loop_s* valk_aio_get_event_loop(valk_aio_system_t* sys);

// Update event loop metrics from libuv (reads loop counters and updates modular metrics)
// Should be called periodically (e.g., from SSE timer) to keep metrics current
void valk_aio_update_loop_metrics(valk_aio_system_t* sys);

// Get the system name (for metrics/dashboard)
const char* valk_aio_get_name(valk_aio_system_t* sys);

// Set the system name (for metrics/dashboard)
void valk_aio_set_name(valk_aio_system_t* sys, const char* name);

// Forward declarations for Lisp types (defined in parser.h)
struct valk_lval_t;
struct valk_lenv_t;

// Check if connection is closing
bool valk_aio_http_connection_closing(valk_aio_handle_t* handle);

// Check if HTTP/2 session is valid for given handle
bool valk_aio_http_session_valid(valk_aio_handle_t* handle, void* session);

// Reset an HTTP/2 stream with the given error code (for testing client stream error handling)
// Returns 0 on success, -1 on failure
int valk_http2_stream_reset(valk_aio_handle_t* conn, i32 stream_id, u32 error_code);

// Submit GOAWAY frame (for testing client GOAWAY handling)
// Returns 0 on success, -1 on failure
int valk_http2_submit_goaway(valk_aio_handle_t* conn, u32 error_code);

// Flush pending HTTP/2 frames (for testing - ensures RST_STREAM is sent immediately)
void valk_http2_flush_pending(valk_aio_handle_t* conn);

// HTTP request accessor builtins registration
void valk_register_http_request_builtins(struct valk_lenv_t* env);
