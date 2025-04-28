#pragma once
#include "aio.h"
#include <stdint.h>

typedef struct {
  int connectedCount;
  int disconnectedCount;
} valk_srv_state_t;

void cb_onConnect(void *arg, valk_aio_http_conn *);
void cb_onDisconnect(void *arg, valk_aio_http_conn *);
void cb_onHeader(void *arg, valk_aio_http_conn *, size_t stream, char *name,
                 char *value);
void cb_onBody(void *arg, valk_aio_http_conn *, size_t stream, uint8_t flags,
               valk_buffer_t *buf);
