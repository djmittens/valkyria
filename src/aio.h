#pragma once

#include "concurrency.h"
#include "memory.h"
#include <unistd.h>

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

typedef struct valk_aio_system valk_aio_system;
typedef struct valk_aio_socket valk_aio_socket;

typedef struct valk_aio_http_server valk_aio_http_server;
typedef struct valk_aio_http2_client valk_aio_http2_client;
typedef struct valk_aio_http_conn valk_aio_http_conn;

char *valk_client_demo(valk_aio_system *sys, const char *domain,
                       const char *port);

valk_aio_system *valk_aio_start();
void valk_aio_stop(valk_aio_system *sys);

valk_future *valk_aio_read_file(valk_aio_system *sys, const char *filename);

typedef struct {
  char *body;
} valk_http_request_t;

typedef struct {
  char *body;
} valk_http_response_t;

typedef struct {
  void *arg;
  void (*onConnect)(void *, valk_aio_http_conn *);
  void (*onDisconnect)(void *, valk_aio_http_conn *);
  void (*onHeaders)(void *, valk_aio_http_conn *, size_t stream, char *names,
                    char *values, size_t num);
  void (*onBody)(void *, valk_aio_http_conn *, size_t stream, uint8_t flags,
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
valk_future *valk_aio_http2_listen(valk_aio_system *sys, const char *interface,
                                   const int port, const char *keyfile,
                                   const char *certfile,
                                   valk_http2_handler_t handler);

///
/// @return returns a future with a boxed `valk_aio_http2_client`
///
valk_future *valk_aio_http2_connect(valk_aio_system *sys, const char *interface,
                                    const int port, const char *certfile);

void valk_aio_hangup(valk_aio_socket *socket);
