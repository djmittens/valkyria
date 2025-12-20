#pragma once

#include <stddef.h>
#include "concurrency.h"
#include "memory.h"

#define VALK_HTTP_MOTD "<!DOCTYPE html><html><head><meta charset=\"UTF-8\"><title>Valkyria HTTP/2 Server</title><style>body{font-family:system-ui,sans-serif;max-width:800px;margin:80px auto;padding:0 20px;background:#0a0e27;color:#e0e0e0}h1{color:#00d9ff;font-size:3em;margin-bottom:0.2em}p{font-size:1.2em;line-height:1.6;color:#b0b0b0}code{background:#1a1e3a;padding:2px 8px;border-radius:4px;color:#00d9ff}</style></head><body><h1>\u269C Valkyria</h1><p>Valhalla's Treasure - HTTP/2 Server</p><p>This is a <code>Valkyria Lisp</code> web server running on nghttp2 with TLS.</p><p style=\"margin-top:40px;font-size:0.9em;opacity:0.7\">Server is operational and ready to handle requests.</p></body></html>"

typedef struct valk_aio_system valk_aio_system_t;
typedef struct valk_aio_system_config valk_aio_system_config_t;

typedef struct valk_aio_http_server valk_aio_http_server;
typedef struct valk_aio_http2_client valk_aio_http2_client;
typedef struct valk_aio_handle_t valk_aio_handle_t;
typedef struct valk_async_handle_t valk_async_handle_t;

// Forward declarations for libuv types
typedef struct uv_timer_s uv_timer_t;
typedef struct uv_handle_s uv_handle_t;

// Forward declarations for parser.h types
struct valk_lval_t;
struct valk_lenv_t;
struct valk_mem_arena;

// ============================================================================
// Async Handle Status
// ============================================================================

typedef enum valk_async_status_t {
  VALK_ASYNC_PENDING,     // Created but not started
  VALK_ASYNC_RUNNING,     // Operation in progress
  VALK_ASYNC_COMPLETED,   // Finished successfully
  VALK_ASYNC_FAILED,      // Finished with error
  VALK_ASYNC_CANCELLED,   // Cancelled before completion
} valk_async_status_t;

// Callback types for async handle completion notification
typedef void (*valk_async_done_fn)(struct valk_async_handle_t *handle, void *ctx);
typedef bool (*valk_async_is_closed_fn)(void *ctx);

// Async handle - represents an in-flight async operation
// This is the main structure for composable async operations.
//
// The async system is decoupled from specific I/O layers (HTTP, files, etc).
// Each layer registers callbacks to handle completion and detect cancellation.
struct valk_async_handle_t {
  // Identity
  uint64_t id;
  valk_async_status_t status;

  // Cancellation (use atomic operations on this field)
  int cancel_requested;

  // libuv integration (opaque - actual uv handles are in aio_uv.c)
  void *uv_handle_ptr;
  void *loop;

  // Transform callbacks (Lisp lambdas for aio/then, aio/catch, etc.)
  struct valk_lval_t *on_complete;       // (\ {result} ...) - transform on success
  struct valk_lval_t *on_error;          // (\ {error} ...) - transform on error
  struct valk_lval_t *on_cancel;         // (\ {} ...) - cleanup on cancel
  struct valk_lenv_t *env;               // Environment for callback evaluation

  // Result storage
  struct valk_lval_t *result;            // Success value (or nil)
  struct valk_lval_t *error;             // Error value (or nil)

  // Memory management - allocator for transform function execution
  // Set by the I/O layer: HTTP uses stream arena, others use malloc
  valk_mem_allocator_t *allocator;

  // Generic completion callback - called when handle reaches terminal state
  // This replaces HTTP-specific response sending. Each I/O layer registers
  // its own callback (e.g., HTTP sends response, file I/O closes fd, etc.)
  valk_async_done_fn on_done;
  void *on_done_ctx;

  // Connection/resource closed detection - called to check if the underlying
  // resource is still valid (e.g., HTTP connection closed, file closed, etc.)
  // If NULL, resource is assumed to be always valid.
  valk_async_is_closed_fn is_closed;
  void *is_closed_ctx;

  // Structured cancellation (parent/child hierarchy)
  struct valk_async_handle_t *parent;
  struct {
    struct valk_async_handle_t **items;
    size_t count;
    size_t capacity;
  } children;

  // Linked list for handle tracking
  struct valk_async_handle_t *prev;
  struct valk_async_handle_t *next;
};

// Register async handle builtins
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
struct valk_lval_t *valk_aio_schedule(valk_aio_system_t *sys, uint64_t delay_ms,
                                       struct valk_lval_t *callback,
                                       struct valk_lenv_t *env);

struct valk_http2_header_t {
  uint8_t *name;
  uint8_t *value;
  size_t nameLen;
  size_t valueLen;
};

typedef struct valk_http2_request_t {
  valk_mem_allocator_t *allocator;
  char *method;
  char *scheme;
  char *authority;
  char *path;
  struct {
    struct valk_http2_header_t *items;
    size_t count;
    size_t capacity;
  } headers;
  void *ctx;
  uint8_t *body;
  size_t bodyLen;
  size_t bodyCapacity;
} valk_http2_request_t;

typedef struct valk_http2_response_t {
  int32_t stream_id;

  // valk_mem_arena_t *arena;
  valk_http2_request_t *req;
  const char *status;
  struct {
    struct valk_http2_header_t *items;
    size_t count;
    size_t capacity;
  } headers;

  bool headersReceived;
  bool bodyReceived;

  uint8_t *body;
  size_t bodyLen;
  size_t bodyCapacity;

  valk_promise _promise;
} valk_http2_response_t;

valk_aio_system_t *valk_aio_start();

/// @brief Start AIO system with custom configuration
/// @param config System configuration (NULL for defaults)
/// @return AIO system handle
valk_aio_system_t *valk_aio_start_with_config(valk_aio_system_config_t *config);

/// @brief Resolve derived values (called automatically by valk_aio_start_with_config)
/// Fills in any 0-valued fields with derived/default values
/// Returns 0 on success, -1 on validation failure
int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg);

/// @brief Validate configuration
/// Returns NULL on success, or error message on failure
const char *valk_aio_system_config_validate(const valk_aio_system_config_t *cfg);

void valk_aio_stop(valk_aio_system_t *sys);

/// @brief Check if the AIO system is shutting down
bool valk_aio_is_shutting_down(valk_aio_system_t *sys);

/// @brief Wait for shutdown to complete and cleanup resources
void valk_aio_wait_for_shutdown(valk_aio_system_t *sys);

valk_future *valk_aio_read_file(valk_aio_system_t *sys, const char *filename);

typedef struct {
  void *arg;
  void (*onConnect)(void *arg, valk_aio_handle_t *);
  void (*onDisconnect)(void *arg, valk_aio_handle_t *);
  void (*onHeader)(void *arg, valk_aio_handle_t *, size_t stream, char *name,
                   char *value);
  void (*onBody)(void *arg, valk_aio_handle_t *, size_t stream, uint8_t flags,
                 valk_buffer_t *buf);
} valk_http2_handler_t;

// System configuration for AIO pools
typedef struct valk_aio_system_config {
  // PRIMARY TUNING PARAMETERS
  uint32_t max_connections;          // Default: 100
  uint32_t max_concurrent_streams;   // Default: 100 (per connection, sent via SETTINGS)

  // CAPACITY LIMITS
  uint32_t max_handles;              // Default: 2056
  uint32_t max_servers;              // Default: 8
  uint32_t max_clients;              // Default: 8

  // DERIVED SETTINGS (set to 0 for auto-calculation)
  uint32_t tcp_buffer_pool_size;     // Auto: max_connections × (2 + streams/8)
  uint32_t arena_pool_size;          // Auto: max_connections × 2
  uint32_t queue_capacity;           // Auto: max_connections × 2

  // MEMORY SIZING
  size_t   arena_size;               // Default: 64MB per arena
  size_t   max_request_body_size;    // Default: 8MB (required - requests are buffered)

  // BACKPRESSURE SETTINGS
  float    buffer_high_watermark;     // Default: 0.85 (85%) - start load shedding
  float    buffer_critical_watermark; // Default: 0.95 (95%) - reject all new conns
  uint32_t min_buffers_per_conn;      // Default: 4 (BUFFERS_PER_CONNECTION)

  // BACKPRESSURE TIMING
  uint32_t backpressure_list_max;     // Default: 1000
  uint32_t backpressure_timeout_ms;   // Default: 30000 (30s)
  uint32_t pending_stream_pool_size;  // Default: 64
} valk_aio_system_config_t;

// Default system configuration
static inline valk_aio_system_config_t valk_aio_system_config_default(void) {
  return (valk_aio_system_config_t){0};
}

// Server configuration for HTTP/2 server behavior
typedef struct valk_http_server_config {
  size_t      max_response_body_size;  // Default: 64MB (Lisp API limit, not C runtime)
  const char* error_503_body;          // Pre-rendered overload response
  size_t      error_503_body_len;

  // SSE CONFIGURATION
  size_t      sse_buffer_size;         // Default: 64KB (pending write buffer per stream)
  uint32_t    sse_queue_max;           // Default: 1000 (event queue depth)
} valk_http_server_config_t;

// Default server configuration
static inline valk_http_server_config_t valk_http_server_config_default(void) {
  return (valk_http_server_config_t){
    .max_response_body_size = 64 * 1024 * 1024,  // 64MB
    .error_503_body = NULL,
    .error_503_body_len = 0,
    .sse_buffer_size = 64 * 1024,   // 64KB
    .sse_queue_max = 1000,
  };
}

// Client configuration for HTTP/2 client behavior
typedef struct valk_http_client_config {
  uint32_t max_concurrent_streams;     // Default: 100
  size_t   max_response_body_size;     // Default: 64MB
  uint32_t connect_timeout_ms;         // Default: 30000 (30s)
  uint32_t request_timeout_ms;         // Default: 60000 (60s)

  // Connection pooling (future use)
  uint32_t max_idle_connections;       // Default: 0 (no pooling)
  uint32_t keepalive_ms;               // Default: 0 (close after use)
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
    .pending_stream_pool_size = 24,
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
    .pending_stream_pool_size = 200,    // 20% overflow capacity
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
    .pending_stream_pool_size = 4,
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
    .pending_stream_pool_size = 500,    // 25% overflow
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
    .pending_stream_pool_size = 32,
  };
}

// Demo server config: smaller buffers for demos
static inline valk_http_server_config_t valk_http_server_config_demo(void) {
  return (valk_http_server_config_t){
    .max_response_body_size = 8 * 1024 * 1024,  // 8MB
    .error_503_body = NULL,
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
/// @return returns a future with a boxed `valk_aio_http2_server`
///
valk_future *valk_aio_http2_listen(valk_aio_system_t *sys,
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
/// @param[in] handler C function handler (optional, can be NULL)
/// @param[in] lisp_handler Lisp function handler (optional, can be NULL)
/// @param[in] config server configuration (optional, uses defaults if NULL)
/// @return returns a future with a boxed `valk_aio_http2_server`
valk_future *valk_aio_http2_listen_with_config(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler,
                                   valk_http_server_config_t *config);

/// @brief Set a Lisp handler function for HTTP/2 requests
/// @param srv The HTTP/2 server
/// @param handler_fn Lisp lambda (GC heap allocated) with signature (lambda {req k} ...)
void valk_aio_http2_server_set_handler(valk_aio_http_server *srv, void *handler_fn);

/// @return returns a future with a boxed `unit`
///
valk_future *valk_aio_http2_shutdown(valk_aio_http_server *srv);

///
/// @return returns a future with a boxed `valk_aio_http2_client`
///
valk_future *valk_aio_http2_connect(valk_aio_system_t *sys,
                                    const char *interface, const int port,
                                    const char *certfile);

// Connect to an IP with an explicit SNI/hostname used for TLS and HTTP/2.
// Returns a future with a boxed `valk_aio_http2_client`.
valk_future *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                         const char *ip, const int port,
                                         const char *hostname);

valk_future *valk_aio_http2_request_send(valk_http2_request_t *req,
                                         valk_aio_http2_client *client);

#ifdef VALK_METRICS_ENABLED
#include "aio_metrics.h"
#include "gc.h"

// Forward declaration for SSE stream registry (defined in aio_sse_stream_registry.h)
typedef struct valk_sse_stream_registry valk_sse_stream_registry_t;

// Get metrics from AIO system (returns NULL if metrics not enabled)
valk_aio_metrics_t* valk_aio_get_metrics(valk_aio_system_t* sys);

// Get system stats from AIO system (returns NULL if metrics not enabled)
valk_aio_system_stats_t* valk_aio_get_system_stats(valk_aio_system_t* sys);

// Get HTTP clients registry from AIO system (returns NULL if metrics not enabled)
valk_http_clients_registry_t* valk_aio_get_http_clients_registry(valk_aio_system_t* sys);

// Update queue stats from HTTP queue (call before rendering metrics)
void valk_aio_update_queue_stats(valk_aio_system_t* sys);

// Get GC heap from AIO system (returns NULL if metrics not enabled)
valk_gc_malloc_heap_t* valk_aio_get_gc_heap(valk_aio_system_t* sys);

// Get scratch arena from AIO system (for diagnostics, returns NULL if not available)
valk_mem_arena_t* valk_aio_get_scratch_arena(valk_aio_system_t* sys);

// Get SSE stream registry from AIO system (returns NULL if metrics not enabled)
valk_sse_stream_registry_t* valk_aio_get_sse_registry(valk_aio_system_t* sys);

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
  uint16_t owner_idx;          // Index into owner registry (server/client ID)
  uint64_t state_change_time;  // Timestamp of last state change (ms since epoch)
} valk_handle_diag_t;

// Owner registry for server/client attribution (defined in aio_uv.c)
typedef struct valk_owner_entry valk_owner_entry_t;
typedef struct valk_owner_registry valk_owner_registry_t;

// Owner registry API
uint16_t valk_owner_register(valk_aio_system_t *sys, const char *name, uint8_t type, void *ptr);
const char* valk_owner_get_name(valk_aio_system_t *sys, uint16_t idx);
size_t valk_owner_get_count(valk_aio_system_t *sys);

// Get slab allocators for memory diagnostics
valk_slab_t* valk_aio_get_tcp_buffer_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_handle_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_stream_arenas_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_http_servers_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_http_clients_slab(valk_aio_system_t* sys);

// Get diagnostics for a handle at a given slab slot index
// Returns false if slot is invalid or not an HTTP connection handle
bool valk_aio_get_handle_diag(valk_aio_system_t* sys, size_t slot_idx,
                               valk_handle_diag_t* out_diag);

// Get the kind of handle at a given slab slot index
// Returns VALK_DIAG_HNDL_EMPTY if slot is invalid or free
valk_diag_handle_kind_e valk_aio_get_handle_kind(valk_aio_system_t* sys, size_t slot_idx);

// Timer handle management (allocates from handle slab)
valk_aio_handle_t* valk_aio_timer_alloc(valk_aio_system_t* sys);
void valk_aio_timer_init(valk_aio_handle_t* handle);
void valk_aio_timer_start(valk_aio_handle_t* handle, uint64_t timeout_ms, uint64_t repeat_ms,
                           void (*callback)(uv_timer_t*));
void valk_aio_timer_stop(valk_aio_handle_t* handle);
void valk_aio_timer_close(valk_aio_handle_t* handle, void (*close_cb)(uv_handle_t*));
void valk_aio_timer_set_data(valk_aio_handle_t* handle, void* data);
void valk_aio_timer_free(valk_aio_handle_t* handle);
#endif

// Get the event loop from AIO system (returns NULL if no loop available)
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

// Async delay - schedules callback after delay_ms milliseconds
// Must be called from within an HTTP request handler
// Returns :deferred symbol on success to indicate async response
struct valk_lval_t* valk_aio_delay(valk_aio_system_t* sys, uint64_t delay_ms,
                                    struct valk_lval_t* continuation, struct valk_lenv_t* env);

// Global active AIO system (set by valk_aio_start, cleared by valk_aio_stop)
extern valk_aio_system_t* valk_aio_active_system;

// ============================================================================
// Test Helpers - Functions exposed for unit testing internal state
// ============================================================================

// Get current backpressure list size
size_t valk_aio_test_get_backpressure_list_size(void);

// Get pending stream queue count
size_t valk_aio_test_get_pending_stream_count(void);

// Force trigger backpressure timer callback (for testing timeout logic)
void valk_aio_test_trigger_backpressure_timer(valk_aio_system_t* sys);

// Check if a connection is in the backpressure list
bool valk_aio_test_is_connection_backpressured(valk_aio_handle_t* conn);

// Close all SSE streams on a connection (exposed for testing cleanup paths)
void valk_sse_close_all_streams(valk_aio_handle_t* conn);

// SSE state accessors (used by SSE diagnostics module)
bool valk_aio_http_connection_closing(valk_aio_handle_t* handle);
struct valk_sse_diag_state;
struct valk_sse_diag_state* valk_aio_get_sse_state(valk_aio_handle_t* handle);
void valk_aio_set_sse_state(valk_aio_handle_t* handle, struct valk_sse_diag_state* state);

// Set backpressure list size directly (for testing limit behavior)
void valk_aio_test_set_backpressure_list_size(size_t size);

// Trigger backpressure resume logic
void valk_aio_test_backpressure_try_resume(void);

// Add/remove connection from backpressure list (for testing)
void valk_aio_test_add_to_backpressure_list(valk_aio_handle_t* conn);
void valk_aio_test_remove_from_backpressure_list(valk_aio_handle_t* conn);

// Pending stream test helpers
// Create a mock pending stream and add to queue (returns opaque pointer for removal)
void* valk_aio_test_create_pending_stream(valk_aio_system_t* sys);
// Simulate client RST_STREAM by removing pending stream from queue
void valk_aio_test_remove_pending_stream(valk_aio_system_t* sys, void* pending_stream);
// Get pending stream queue head (for verification)
void* valk_aio_test_get_pending_stream_head(void);
// Add a header to a pending stream (for testing header copy path)
bool valk_aio_test_pending_stream_add_header(void* pending_stream, const char* name, const char* value);

// TCP buffer slab test helpers
// Exhaust TCP buffer slab by acquiring all items (returns count acquired)
size_t valk_aio_test_exhaust_tcp_buffers(valk_aio_system_t* sys);
// Release all held TCP buffer test items
void valk_aio_test_release_tcp_buffers(valk_aio_system_t* sys);
// Simulate EOF on a connection (triggers EOF handling path)
void valk_aio_test_simulate_eof(valk_aio_handle_t* conn);
// Get connection handle from HTTP2 client
valk_aio_handle_t* valk_aio_test_get_client_connection(valk_aio_http2_client* client);
