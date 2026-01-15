#include "aio_internal.h"
#include "log.h"

// LCOV_EXCL_BR_START - FSM switch statements have defensive default cases
static valk_diag_conn_state_e __conn_state_to_diag(__aio_http_conn_e state) {
  switch (state) {
    case VALK_CONN_INIT:
    case VALK_CONN_HANDSHAKING:
      return VALK_DIAG_CONN_CONNECTING;
    case VALK_CONN_ESTABLISHED:
      return VALK_DIAG_CONN_ACTIVE;
    case VALK_CONN_GOAWAY_SENT:
    case VALK_CONN_DRAINING:
    case VALK_CONN_CLOSING:
      return VALK_DIAG_CONN_CLOSING;
    case VALK_CONN_CLOSED:
    case VALK_CONN_ERROR:
      return VALK_DIAG_CONN_FREE;
  }
  return VALK_DIAG_CONN_FREE;
}

static const char *STATE_NAMES[] = {
  [VALK_CONN_INIT] = "INIT",
  [VALK_CONN_HANDSHAKING] = "HANDSHAKING",
  [VALK_CONN_ESTABLISHED] = "ESTABLISHED",
  [VALK_CONN_GOAWAY_SENT] = "GOAWAY_SENT",
  [VALK_CONN_DRAINING] = "DRAINING",
  [VALK_CONN_CLOSING] = "CLOSING",
  [VALK_CONN_CLOSED] = "CLOSED",
  [VALK_CONN_ERROR] = "ERROR",
};

static const char *EVENT_NAMES[] = {
  [VALK_CONN_EVT_START_HANDSHAKE] = "START_HANDSHAKE",
  [VALK_CONN_EVT_HANDSHAKE_COMPLETE] = "HANDSHAKE_COMPLETE",
  [VALK_CONN_EVT_HANDSHAKE_FAILED] = "HANDSHAKE_FAILED",
  [VALK_CONN_EVT_SEND_GOAWAY] = "SEND_GOAWAY",
  [VALK_CONN_EVT_GOAWAY_ACKED] = "GOAWAY_ACKED",
  [VALK_CONN_EVT_STREAMS_DRAINED] = "STREAMS_DRAINED",
  [VALK_CONN_EVT_CLOSE] = "CLOSE",
  [VALK_CONN_EVT_CLOSED] = "CLOSED",
  [VALK_CONN_EVT_ERROR] = "ERROR",
  [VALK_CONN_EVT_TIMEOUT] = "TIMEOUT",
};

const char *valk_conn_state_str(__aio_http_conn_e state) {
  if (state < 0 || state > VALK_CONN_ERROR) return "UNKNOWN";
  return STATE_NAMES[state];
}

const char *valk_conn_event_str(valk_conn_event_e event) {
  if (event < 0 || event > VALK_CONN_EVT_TIMEOUT) return "UNKNOWN";
  return EVENT_NAMES[event];
}

static __aio_http_conn_e __next_state(__aio_http_conn_e current, valk_conn_event_e event) {
  switch (current) {
    case VALK_CONN_INIT:
      switch (event) {
        case VALK_CONN_EVT_START_HANDSHAKE: return VALK_CONN_HANDSHAKING;
        case VALK_CONN_EVT_HANDSHAKE_COMPLETE: return VALK_CONN_ESTABLISHED;
        case VALK_CONN_EVT_CLOSE: return VALK_CONN_CLOSING;
        case VALK_CONN_EVT_ERROR: return VALK_CONN_ERROR;
        default: return current;
      }

    case VALK_CONN_HANDSHAKING:
      switch (event) {
        case VALK_CONN_EVT_HANDSHAKE_COMPLETE: return VALK_CONN_ESTABLISHED;
        case VALK_CONN_EVT_HANDSHAKE_FAILED: return VALK_CONN_ERROR;
        case VALK_CONN_EVT_CLOSE: return VALK_CONN_CLOSING;
        case VALK_CONN_EVT_ERROR: return VALK_CONN_ERROR;
        case VALK_CONN_EVT_TIMEOUT: return VALK_CONN_CLOSING;
        default: return current;
      }

    case VALK_CONN_ESTABLISHED:
      switch (event) {
        case VALK_CONN_EVT_SEND_GOAWAY: return VALK_CONN_GOAWAY_SENT;
        case VALK_CONN_EVT_CLOSE: return VALK_CONN_CLOSING;
        case VALK_CONN_EVT_ERROR: return VALK_CONN_ERROR;
        case VALK_CONN_EVT_TIMEOUT: return VALK_CONN_CLOSING;
        default: return current;
      }

    case VALK_CONN_GOAWAY_SENT:
      switch (event) {
        case VALK_CONN_EVT_GOAWAY_ACKED: return VALK_CONN_DRAINING;
        case VALK_CONN_EVT_STREAMS_DRAINED: return VALK_CONN_CLOSING;
        case VALK_CONN_EVT_CLOSE: return VALK_CONN_CLOSING;
        case VALK_CONN_EVT_ERROR: return VALK_CONN_ERROR;
        case VALK_CONN_EVT_TIMEOUT: return VALK_CONN_CLOSING;
        default: return current;
      }

    case VALK_CONN_DRAINING:
      switch (event) {
        case VALK_CONN_EVT_STREAMS_DRAINED: return VALK_CONN_CLOSING;
        case VALK_CONN_EVT_CLOSE: return VALK_CONN_CLOSING;
        case VALK_CONN_EVT_ERROR: return VALK_CONN_ERROR;
        case VALK_CONN_EVT_TIMEOUT: return VALK_CONN_CLOSING;
        default: return current;
      }

    case VALK_CONN_CLOSING:
      switch (event) {
        case VALK_CONN_EVT_CLOSED: return VALK_CONN_CLOSED;
        default: return current;
      }

    case VALK_CONN_CLOSED:
      return current;

    case VALK_CONN_ERROR:
      switch (event) {
        case VALK_CONN_EVT_CLOSE: return VALK_CONN_CLOSING;
        case VALK_CONN_EVT_CLOSED: return VALK_CONN_CLOSED;
        default: return current;
      }
  }
  return current;
}
// LCOV_EXCL_BR_STOP

void __valk_conn_set_init_state(valk_aio_handle_t *conn) {
  if (!conn) return; // LCOV_EXCL_BR_LINE
  conn->http.state = VALK_CONN_INIT;
  conn->http.diag.state = __conn_state_to_diag(VALK_CONN_INIT);
  conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
  VALK_DEBUG("FSM: initialized to INIT state");
}

static void on_enter_goaway_sent(__attribute__((unused)) valk_aio_handle_t *conn) {
  VALK_INFO("FSM: entering GOAWAY_SENT - first GOAWAY sent, waiting for drain");
}

static void on_enter_draining(__attribute__((unused)) valk_aio_handle_t *conn) {
  VALK_INFO("FSM: entering DRAINING - second GOAWAY sent, waiting for streams to close");
}

static void __on_enter_state(valk_aio_handle_t *conn, __aio_http_conn_e state) {
  switch (state) {
    case VALK_CONN_GOAWAY_SENT:
      on_enter_goaway_sent(conn);
      break;
    case VALK_CONN_DRAINING:
      on_enter_draining(conn);
      break;
    default:
      break;
  }
}

bool valk_conn_transition(valk_aio_handle_t *conn, valk_conn_event_e event) {
  if (!conn) return false; // LCOV_EXCL_BR_LINE

  __aio_http_conn_e old_state = conn->http.state;
  __aio_http_conn_e new_state = __next_state(old_state, event);

  if (new_state == old_state) {
    VALK_DEBUG("FSM: %s + %s = (no change)",
               valk_conn_state_str(old_state), valk_conn_event_str(event));
    return false;
  }

  VALK_INFO("FSM: %s + %s -> %s",
            valk_conn_state_str(old_state), valk_conn_event_str(event),
            valk_conn_state_str(new_state));

  conn->http.state = new_state;
  __on_enter_state(conn, new_state);

  conn->http.diag.state = __conn_state_to_diag(new_state);
  conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);

  return true;
}
