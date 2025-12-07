#pragma once
#include "aio.h"
#include <stdint.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <unistd.h>

typedef struct {
  int connectedCount;
  int disconnectedCount;
} valk_srv_state_t;

// Get an available port by binding to port 0 and reading the assigned port
static inline int get_available_port(void) {
  int sock = socket(AF_INET, SOCK_STREAM, 0);
  if (sock < 0) return -1;

  struct sockaddr_in addr = {
    .sin_family = AF_INET,
    .sin_addr.s_addr = INADDR_ANY,
    .sin_port = 0,
  };

  if (bind(sock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
    close(sock);
    return -1;
  }

  socklen_t len = sizeof(addr);
  if (getsockname(sock, (struct sockaddr *)&addr, &len) < 0) {
    close(sock);
    return -1;
  }

  int port = ntohs(addr.sin_port);
  close(sock);
  return port;
}

void cb_onConnect(void *arg, valk_aio_handle_t *);
void cb_onDisconnect(void *arg, valk_aio_handle_t *);
void cb_onHeader(void *arg, valk_aio_handle_t *, size_t stream, char *name,
                 char *value);
void cb_onBody(void *arg, valk_aio_handle_t *, size_t stream, uint8_t flags,
               valk_buffer_t *buf);
