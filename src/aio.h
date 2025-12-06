#pragma once

// #include <unistd.h>

#include <stddef.h>
#include "concurrency.h"
#include "memory.h"

#define VALK_HTTP_MOTD "<!DOCTYPE html><html><head><meta charset=\"UTF-8\"><title>Valkyria HTTP/2 Server</title><style>body{font-family:system-ui,sans-serif;max-width:800px;margin:80px auto;padding:0 20px;background:#0a0e27;color:#e0e0e0}h1{color:#00d9ff;font-size:3em;margin-bottom:0.2em}p{font-size:1.2em;line-height:1.6;color:#b0b0b0}code{background:#1a1e3a;padding:2px 8px;border-radius:4px;color:#00d9ff}</style></head><body><h1>\u269C Valkyria</h1><p>Valhalla's Treasure - HTTP/2 Server</p><p>This is a <code>Valkyria Lisp</code> web server running on nghttp2 with TLS.</p><p style=\"margin-top:40px;font-size:0.9em;opacity:0.7\">Server is operational and ready to handle requests.</p></body></html>"

// Host TO Network Short
/* void htons(void); */
/**/
/* // Host TO Network Long */
/* void htonl(void); */
/**/
/* // Network TO Host Short */
/* void ntohs(void); */
/**/
/* // Network TO Host Long */
/* void ntohl(void); */

typedef struct valk_aio_system valk_aio_system_t;
typedef struct valk_aio_system_config valk_aio_system_config_t;
typedef struct valk_aio_http_conn valk_aio_http_conn;

typedef struct valk_aio_http_server valk_aio_http_server;
typedef struct valk_aio_http2_client valk_aio_http2_client;
typedef struct valk_aio_handle_t valk_aio_handle_t;

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

char *valk_client_demo(valk_aio_system_t *sys, const char *domain,
                       const char *port);

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

valk_future *valk_aio_read_file(valk_aio_system_t *sys, const char *filename);

typedef struct {
  void *arg;
  void (*onConnect)(void *arg, valk_aio_http_conn *);
  void (*onDisconnect)(void *arg, valk_aio_http_conn *);
  void (*onHeader)(void *arg, valk_aio_http_conn *, size_t stream, char *name,
                   char *value);
  void (*onBody)(void *arg, valk_aio_http_conn *, size_t stream, uint8_t flags,
                 valk_buffer_t *buf);
} valk_http2_handler_t;

// System configuration for AIO pools
typedef struct valk_aio_system_config {
  // PRIMARY TUNING PARAMETERS
  uint32_t max_connections;          // Default: 100
  uint32_t max_concurrent_streams;   // Default: 100 (per connection, sent via SETTINGS)

  // DERIVED SETTINGS (set to 0 for auto-calculation)
  uint32_t tcp_buffer_pool_size;     // Auto: max_connections × (2 + streams/8)
  uint32_t arena_pool_size;          // Auto: max_connections × 2
  uint32_t queue_capacity;           // Auto: max_connections × 2

  // MEMORY SIZING
  size_t   arena_size;               // Default: 64MB per arena
  size_t   max_request_body_size;    // Default: 8MB (required - requests are buffered)
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
} valk_http_server_config_t;

// Default server configuration
static inline valk_http_server_config_t valk_http_server_config_default(void) {
  return (valk_http_server_config_t){
    .max_response_body_size = 64 * 1024 * 1024,  // 64MB
    .error_503_body = NULL,
    .error_503_body_len = 0,
  };
}

///
/// @brief start a new htt2 listening server on a port
///
/// Hey *THis* is not **Sparta**
/// @param[out] srv the server that will be running
/// @param[in] sys the aio system that will run the shit
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

/// @brief Get a demo HTTP/2 handler that returns "Hello from Valk!"
/// @return Pointer to a static demo handler
valk_http2_handler_t *valk_aio_http2_demo_handler(void);

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

// Get metrics from AIO system (returns NULL if metrics not enabled)
valk_aio_metrics_t* valk_aio_get_metrics(valk_aio_system_t* sys);

// Get system stats from AIO system (returns NULL if metrics not enabled)
valk_aio_system_stats_t* valk_aio_get_system_stats(valk_aio_system_t* sys);

// Update queue stats from HTTP queue (call before rendering metrics)
void valk_aio_update_queue_stats(valk_aio_system_t* sys);
#endif

// Get the event loop from AIO system (returns NULL if no loop available)
struct uv_loop_s* valk_aio_get_event_loop(valk_aio_system_t* sys);

// Global active AIO system (set by valk_aio_start, cleared by valk_aio_stop)
extern valk_aio_system_t* valk_aio_active_system;
