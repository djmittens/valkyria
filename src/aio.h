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
                                   valk_http2_handler_t *handler);

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
