#pragma once

#include "common.h"
#include <stdbool.h>

typedef enum __aio_http_conn_e {
  VALK_CONN_INIT,
  VALK_CONN_HANDSHAKING,
  VALK_CONN_ESTABLISHED,
  VALK_CONN_GOAWAY_SENT,
  VALK_CONN_DRAINING,
  VALK_CONN_CLOSING,
  VALK_CONN_CLOSED,
  VALK_CONN_ERROR,
} __aio_http_conn_e;

typedef enum valk_conn_event {
  VALK_CONN_EVT_START_HANDSHAKE,
  VALK_CONN_EVT_HANDSHAKE_COMPLETE,
  VALK_CONN_EVT_HANDSHAKE_FAILED,
  VALK_CONN_EVT_SEND_GOAWAY,
  VALK_CONN_EVT_GOAWAY_ACKED,
  VALK_CONN_EVT_STREAMS_DRAINED,
  VALK_CONN_EVT_CLOSE,
  VALK_CONN_EVT_CLOSED,
  VALK_CONN_EVT_ERROR,
  VALK_CONN_EVT_TIMEOUT,
} valk_conn_event_e;

struct valk_aio_handle_t;

bool valk_conn_transition(struct valk_aio_handle_t *conn, valk_conn_event_e event);

const char *valk_conn_state_str(__aio_http_conn_e state);
const char *valk_conn_event_str(valk_conn_event_e event);

static inline bool valk_conn_is_closing_or_closed(__aio_http_conn_e state) {
  return state == VALK_CONN_CLOSING ||
         state == VALK_CONN_CLOSED ||
         state == VALK_CONN_DRAINING ||
         state == VALK_CONN_GOAWAY_SENT ||
         state == VALK_CONN_ERROR;
}

static inline void valk_conn_init_state(struct valk_aio_handle_t *conn) {
  extern void __valk_conn_set_init_state(struct valk_aio_handle_t *conn);
  __valk_conn_set_init_state(conn);
}
