#pragma once

#include "concurrency.h"
#include <unistd.h>

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

void valk_server_demo(void);

char *valk_client_demo(const char *domain, const char *port);

typedef struct valk_aio_system valk_aio_system;
typedef struct valk_aio_socket valk_aio_socket;

typedef struct valk_aio_http_server valk_aio_http_server;

void valk_aio_start(valk_aio_system *sys);
void valk_aio_stop(valk_aio_system *sys);

valk_future *valk_aio_read_file(valk_aio_system *sys, const char *filename);

typedef struct {
  char *body;
} valk_http_request_t;

typedef struct {
  char *body;
} valk_http_response_t;

void valk_aio_http_listen(valk_aio_http_server *srv, valk_aio_system *sys,
                          const char *interface, const int port);

void valk_aio_hangup(valk_aio_socket *socket);
