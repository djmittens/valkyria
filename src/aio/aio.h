#pragma once

#include <stddef.h>
#include <stdatomic.h>
#include "memory.h"
#include "async_handle.h"
#include "aio_types.h"
#include "aio_config.h"

#define VALK_HTTP_MOTD "<!DOCTYPE html><html><head><meta charset=\"UTF-8\"><title>Valkyria HTTP/2 Server</title><style>body{font-family:system-ui,sans-serif;max-width:800px;margin:80px auto;padding:0 20px;background:#0a0e27;color:#e0e0e0}h1{color:#00d9ff;font-size:3em;margin-bottom:0.2em}p{font-size:1.2em;line-height:1.6;color:#b0b0b0}code{background:#1a1e3a;padding:2px 8px;border-radius:4px;color:#00d9ff}</style></head><body><h1>\u269C Valkyria</h1><p>Valhalla's Treasure - HTTP/2 Server</p><p>This is a <code>Valkyria Lisp</code> web server running on nghttp2 with TLS.</p><p style=\"margin-top:40px;font-size:0.9em;opacity:0.7\">Server is operational and ready to handle requests.</p></body></html>"

// Forward declarations for libuv types
typedef struct uv_timer_s uv_timer_t;
typedef struct uv_handle_s uv_handle_t;

valk_async_handle_t *valk_async_handle_new(struct valk_aio_system *sys, struct valk_lenv_t *env);
valk_async_handle_t *valk_async_handle_new_in_region(struct valk_aio_system *sys, struct valk_lenv_t *env, struct valk_region *region);
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

void valk_async_propagate_region(valk_async_handle_t *handle, struct valk_region *region, struct valk_lenv_t *env);
void valk_async_propagate_context(valk_async_handle_t *handle, struct valk_region *region, struct valk_lenv_t *env, struct valk_request_ctx *request_ctx);

// HTTP/2 client request implementation (called from parser.c builtin)
struct valk_lval_t *valk_http2_client_request_impl(struct valk_lenv_t *e,
                                                    valk_aio_system_t *sys,
                                                    const char *host, int port,
                                                    const char *path);

// HTTP/2 client request with custom headers
struct valk_lval_t *valk_http2_client_request_with_headers_impl(struct valk_lenv_t *e,
                                                    valk_aio_system_t *sys,
                                                    const char *host, int port,
                                                    const char *path,
                                                    struct valk_lval_t *headers);

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
  struct valk_region *region;
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

/// @brief Free the AIO system struct (called after wait_for_shutdown)
void valk_aio_destroy(valk_aio_system_t *sys);


typedef struct {
  void *arg;
  void (*onConnect)(void *arg, valk_aio_handle_t *);
  void (*onDisconnect)(void *arg, valk_aio_handle_t *);
  void (*onHeader)(void *arg, valk_aio_handle_t *, u64 stream, char *name,
                   char *value);
  void (*onBody)(void *arg, valk_aio_handle_t *, u64 stream, u8 flags,
                 valk_buffer_t *buf);
} valk_http2_handler_t;

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

/// @brief Check if the server has been stopped or is stopping
/// @param srv The HTTP/2 server
/// @return true if the server is stopped or stopping
bool valk_aio_http2_server_is_stopped(valk_aio_http_server *srv);

/// @brief Extract the server from a server ref lval
/// @param server_ref LVAL_REF containing the server pointer
/// @return The HTTP/2 server pointer
valk_aio_http_server* valk_aio_http2_server_from_ref(struct valk_lval_t *server_ref);

/// @brief Get port from a server ref lval (convenience wrapper)
/// @param server_ref LVAL_REF containing the server arc
/// @return The actual port number the server is listening on
int valk_aio_http2_server_get_port_from_ref(struct valk_lval_t *server_ref);

/// @brief Gracefully stop an HTTP/2 server
/// @param srv The HTTP/2 server to stop
/// @return Async handle that completes when server is stopped
valk_async_handle_t *valk_aio_http2_stop(valk_aio_http_server *srv);

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

valk_async_handle_t *valk_aio_http2_connect_host_with_done(valk_aio_system_t *sys,
                                                            const char *ip, const int port,
                                                            const char *hostname,
                                                            valk_async_done_fn on_done,
                                                            void *on_done_ctx);

valk_async_handle_t *valk_aio_http2_request_send(valk_http2_request_t *req,
                                                    valk_aio_http2_client *client);

valk_async_handle_t *valk_aio_http2_request_send_with_done(valk_http2_request_t *req,
                                                            valk_aio_http2_client *client,
                                                            valk_async_done_fn on_done,
                                                            void *on_done_ctx);

#include "aio_metrics.h"
#include "gc.h"

// Update queue stats from HTTP queue (call before rendering metrics)
void valk_aio_update_queue_stats(valk_aio_system_t* sys);

// Get GC heap from AIO system
valk_gc_heap_t* valk_aio_get_gc_heap(valk_aio_system_t* sys);

// Get scratch arena from AIO system (for diagnostics)
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
