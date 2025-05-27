#pragma once

#include <unistd.h>

#include "concurrency.h"
#include "memory.h"

#define VALK_HTTP_MOTD "<h1>Valkyria, valhallas treasure</h1>"

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
} valk_http2_request_t;

typedef struct valk_http2_response_t {
  // valk_mem_arena_t *arena;
  valk_http2_request_t *req;
  const char *status;
  struct {
    struct valk_http2_header_t *items;
    size_t count;
    size_t capacity;
  } headers;

  uint8_t *body;
  size_t bodyLen;
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

/// @return returns a future with a boxed `unit`
///
valk_future *valk_aio_http2_shutdown(valk_aio_http_server *srv);

///
/// @return returns a future with a boxed `valk_aio_http2_client`
///
valk_future *valk_aio_http2_connect(valk_aio_system_t *sys,
                                    const char *interface, const int port,
                                    const char *certfile);


valk_future *valk_aio_http2_request_send(valk_http2_request_t *req,
                                         valk_aio_http2_client *client);
