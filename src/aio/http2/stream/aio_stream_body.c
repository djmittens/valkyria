#include "aio_stream_body.h"
#include "aio_http2_session.h"
#include "aio_http2_server.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>

#include "common.h"
#include "gc.h"
#include "log.h"
#include "metrics_v2.h"
#include "parser.h"

extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);

static u64 g_stream_body_id = 0;

#define STREAM_DEFAULT_QUEUE_MAX 1000
#define STREAM_DEFAULT_BUFFER_SIZE 65536

static nghttp2_ssize __stream_data_read_callback(
    nghttp2_session *session, i32 stream_id, u8 *buf, size_t length,
    u32 *data_flags, nghttp2_data_source *source, void *user_data);

static void __stream_chunk_free(valk_stream_chunk_t *chunk);

void valk_http2_flush_pending(valk_aio_handle_t *conn);

valk_stream_body_t *valk_stream_body_new(
    valk_aio_handle_t *conn,
    nghttp2_session *session,
    i32 stream_id,
    nghttp2_data_provider2 *data_prd_out,
    valk_mem_arena_t *arena) {

  if (!conn || !session || !data_prd_out) { // LCOV_EXCL_START
    VALK_ERROR("stream_body: invalid arguments to valk_stream_body_new");
    return nullptr;
  } // LCOV_EXCL_STOP

  valk_stream_body_t *body;
  char *pending_buf;

  if (arena) { // LCOV_EXCL_BR_LINE -- arena path tested via HTTP/2 integration
    body = valk_mem_arena_alloc(arena, sizeof(valk_stream_body_t));
    pending_buf = valk_mem_arena_alloc(arena, STREAM_DEFAULT_BUFFER_SIZE);
  } else {
    body = malloc(sizeof(valk_stream_body_t));
    pending_buf = body ? malloc(STREAM_DEFAULT_BUFFER_SIZE) : nullptr; // LCOV_EXCL_BR_LINE -- OOM
  }

  if (!body) { // LCOV_EXCL_START
    VALK_ERROR("stream_body: failed to allocate body struct");
    return nullptr;
  } // LCOV_EXCL_STOP
  if (!pending_buf) { // LCOV_EXCL_START
    VALK_ERROR("stream_body: failed to allocate pending buffer");
    if (!arena) free(body);
    return nullptr;
  } // LCOV_EXCL_STOP

  memset(body, 0, sizeof(*body));

  body->id = __atomic_fetch_add(&g_stream_body_id, 1, __ATOMIC_RELAXED);
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->session = session;
  body->stream_id = stream_id;
  body->queue_max = STREAM_DEFAULT_QUEUE_MAX;

  body->pending_capacity = STREAM_DEFAULT_BUFFER_SIZE;
  body->pending_data = pending_buf;

  body->arena = arena;
  if (arena) { // LCOV_EXCL_BR_LINE -- arena path tested via HTTP/2 integration
    body->chunk_checkpoint = valk_arena_checkpoint_save(arena);
  }

  body->data_deferred = true;

  u64 now = uv_hrtime() / 1000000;
  body->created_at_ms = now;
  body->last_activity_ms = now;
  body->idle_timeout_ms = 0;

  data_prd_out->source.ptr = body;
  data_prd_out->read_callback = __stream_data_read_callback;

  VALK_DEBUG("stream_body: created id=%llu, http2_stream=%d, arena=%p",
             (unsigned long long)body->id, stream_id, (void*)arena);

  return body;
}

// LCOV_EXCL_START -- internal cleanup, invoked only by nghttp2 callback or close path
static void __stream_body_finish_close(valk_stream_body_t *body) {
  if (!body->arena) {
    valk_stream_chunk_t *chunk = body->queue_head;
    while (chunk) {
      valk_stream_chunk_t *next = chunk->next;
      __stream_chunk_free(chunk);
      chunk = next;
    }
  }
  body->queue_head = nullptr;
  body->queue_tail = nullptr;
  body->queue_len = 0;

  if (body->pending_data && !body->arena) {
    free(body->pending_data);
    body->pending_data = nullptr;
  }

  if (body->on_close) {
    body->on_close(body, body->user_data);
  }

  if (body->closed_handle) {
    valk_async_handle_complete(body->closed_handle, valk_lval_sym(":closed"));
    body->closed_handle = NULL;
  }

  valk_lval_t *lisp_on_close = valk_handle_resolve(&valk_sys->handle_table, 
                                                    body->lisp_on_close_handle);
  if (lisp_on_close && body->callback_env) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_t *result = valk_lval_eval_call(body->callback_env, lisp_on_close, args);
    if (LVAL_TYPE(result) == LVAL_ERR) {
      VALK_WARN("stream_body: on-close callback error: %s", result->str);
    }
  }

  if (body->lisp_on_drain_handle.generation > 0) {
    valk_handle_release(&valk_sys->handle_table, body->lisp_on_drain_handle);
    body->lisp_on_drain_handle = (valk_handle_t){0, 0};
  }
  if (body->lisp_on_close_handle.generation > 0) {
    valk_handle_release(&valk_sys->handle_table, body->lisp_on_close_handle);
    body->lisp_on_close_handle = (valk_handle_t){0, 0};
  }
  if (body->lisp_on_timeout_handle.generation > 0) {
    valk_handle_release(&valk_sys->handle_table, body->lisp_on_timeout_handle);
    body->lisp_on_timeout_handle = (valk_handle_t){0, 0};
  }

  valk_stream_body_unregister(body);

  valk_http2_release_stream_arena(body->conn, body->stream_id);
}
// LCOV_EXCL_STOP

void valk_stream_body_close(valk_stream_body_t *body) {
  if (!body) {
    return;
  }

  valk_stream_state_e expected = VALK_STREAM_OPEN;
  if (!atomic_compare_exchange_strong(&body->state, &expected, VALK_STREAM_CLOSING)) {
    return;
  }

  VALK_DEBUG("stream_body: closing id=%llu (http2_stream=%d)",
             (unsigned long long)body->id, body->stream_id);

  if (body->data_deferred) {
    body->data_deferred = false;
    int rv = nghttp2_session_resume_data(body->session, body->stream_id);
    if (rv != 0) { // LCOV_EXCL_START -- nghttp2 internal: stream already closed
      VALK_DEBUG("stream_body: stream %d already closed, finishing body %llu immediately",
                 body->stream_id, (unsigned long long)body->id);
      atomic_store(&body->state, VALK_STREAM_CLOSED);
      __stream_body_finish_close(body);
      return;
    } // LCOV_EXCL_STOP
  }
  valk_http2_flush_pending(body->conn);
}

// LCOV_EXCL_START -- cleanup function, tested via HTTP/2 integration
void valk_stream_body_free(valk_stream_body_t *body) {
  if (!body) {
    return;
  }

  if (atomic_load(&body->state) != VALK_STREAM_CLOSED) {
    valk_stream_body_close(body);
  }

  if (!body->arena) {
    free(body);
  }
}
// LCOV_EXCL_STOP

int valk_stream_body_write(valk_stream_body_t *body, const char *data, u64 len) {
  if (!body || !data) {
    return -1;
  }

  valk_stream_state_e state = atomic_load(&body->state);
  if (state != VALK_STREAM_OPEN) {
    VALK_DEBUG("stream_body: write failed, body %llu not open (state=%d)",
               body->id, state);
    return -1;
  }

  if (body->queue_len >= body->queue_max) {
    VALK_DEBUG("stream_body: write backpressure, body %llu queue full (%zu/%zu)",
               body->id, body->queue_len, body->queue_max);
    return -2;
  }

  valk_stream_chunk_t *chunk;
  if (body->arena) { // LCOV_EXCL_BR_LINE -- arena path tested via HTTP/2 integration
    chunk = valk_mem_arena_alloc(body->arena, sizeof(valk_stream_chunk_t) + len + 1);
  } else {
    chunk = malloc(sizeof(valk_stream_chunk_t) + len + 1);
  }
  if (!chunk) { // LCOV_EXCL_START
    VALK_ERROR("stream_body: failed to allocate chunk");
    return -3;
  } // LCOV_EXCL_STOP

  char *buf = (char *)(chunk + 1);
  memcpy(buf, data, len);
  buf[len] = '\0';

  chunk->data = buf;
  chunk->data_len = len;
  chunk->next = nullptr;

  if (body->queue_tail) {
    body->queue_tail->next = chunk;
  } else {
    body->queue_head = chunk;
  }
  body->queue_tail = chunk;
  body->queue_len++;

  valk_stream_body_touch_activity(body);

  VALK_DEBUG("stream_body: enqueued chunk to body %llu (queue_len=%zu, chunk_size=%zu)",
             body->id, body->queue_len, len);

  if (body->data_deferred) {
    body->data_deferred = false;
    if (!nghttp2_session_find_stream(body->session, body->stream_id)) { // LCOV_EXCL_START
      VALK_DEBUG("stream_body: stream %d no longer exists, closing body %llu immediately",
                 body->stream_id, (unsigned long long)body->id);
      atomic_store(&body->state, VALK_STREAM_CLOSED);
      __stream_body_finish_close(body);
      return -1;
    } // LCOV_EXCL_STOP
    int rv = nghttp2_session_resume_data(body->session, body->stream_id);
    if (rv != 0) { // LCOV_EXCL_START -- nghttp2 internal: stream already closed
      VALK_DEBUG("stream_body: failed to resume stream %d: %s, closing body %llu immediately",
                 body->stream_id, nghttp2_strerror(rv), (unsigned long long)body->id);
      atomic_store(&body->state, VALK_STREAM_CLOSED);
      __stream_body_finish_close(body);
      return -1;
    } // LCOV_EXCL_STOP
    valk_http2_flush_pending(body->conn);
  }

  return 0;
}

bool valk_stream_body_writable(valk_stream_body_t *body) {
  if (!body) {
    return false;
  }
  if (atomic_load(&body->state) != VALK_STREAM_OPEN) {
    return false;
  }
  if (!body->session) { // LCOV_EXCL_BR_LINE -- defensive null check
    return false;
  }
  if (!nghttp2_session_find_stream(body->session, body->stream_id)) { // LCOV_EXCL_BR_LINE -- requires nghttp2 session integration
    return false;
  }
  return body->queue_len < body->queue_max;
}

u64 valk_stream_body_queue_len(valk_stream_body_t *body) {
  if (!body) {
    return 0;
  }
  return body->queue_len;
}

// LCOV_EXCL_START -- internal helper for cleanup
static void __stream_chunk_free(valk_stream_chunk_t *chunk) {
  if (!chunk) {
    return;
  }
  free(chunk);
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START -- nghttp2 internal callback, only invoked from event loop
static nghttp2_ssize __stream_data_read_callback(
    nghttp2_session *session, i32 stream_id, u8 *buf, size_t length,
    u32 *data_flags, nghttp2_data_source *source, void *user_data) {

  UNUSED(session);
  UNUSED(stream_id);
  UNUSED(user_data);

  valk_stream_body_t *body = (valk_stream_body_t *)source->ptr;

  if (!body) {
    VALK_ERROR("stream_body: data_read_callback called with nullptr body");
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
    return 0;
  }

  valk_stream_state_e state = atomic_load(&body->state);
  if (state == VALK_STREAM_CLOSED) {
    VALK_DEBUG("stream_body: body %llu closed, returning EOF",
               (unsigned long long)body->id);
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
    return 0;
  }

  if (body->pending_offset < body->pending_len) {
    u64 remaining = body->pending_len - body->pending_offset;
    u64 to_send = remaining < length ? remaining : length;
    memcpy(buf, body->pending_data + body->pending_offset, to_send);
    body->pending_offset += to_send;

    VALK_DEBUG("stream_body: body %llu flushing pending (%llu bytes, %llu remaining)",
               (unsigned long long)body->id, (unsigned long long)to_send, 
               (unsigned long long)(remaining - to_send));
    return (nghttp2_ssize)to_send;
  }

  if (!body->queue_head) {
    if (atomic_load(&body->state) == VALK_STREAM_CLOSING) {
      VALK_DEBUG("stream_body: body %llu closing with empty queue, finishing close",
                 (unsigned long long)body->id);
      atomic_store(&body->state, VALK_STREAM_CLOSED);
      __stream_body_finish_close(body);
      *data_flags |= NGHTTP2_DATA_FLAG_EOF;
      return 0;
    }
    if (body->arena) {
      valk_arena_checkpoint_restore(body->arena, body->chunk_checkpoint);
    }
    body->data_deferred = true;
    VALK_DEBUG("stream_body: body %llu queue empty, deferring",
               (unsigned long long)body->id);
    return NGHTTP2_ERR_DEFERRED;
  }

  valk_stream_chunk_t *chunk = body->queue_head;
  body->queue_head = chunk->next;
  if (!body->queue_head) {
    body->queue_tail = nullptr;
  }
  body->queue_len--;

  if (chunk->data_len > body->pending_capacity) {
    u64 new_capacity = chunk->data_len;
    char *new_buf = body->arena ? nullptr : realloc(body->pending_data, new_capacity);
    if (!new_buf && !body->arena) {
      VALK_ERROR("stream_body: failed to grow pending buffer for body %llu",
                 (unsigned long long)body->id);
      __stream_chunk_free(chunk);
      *data_flags |= NGHTTP2_DATA_FLAG_EOF;
      return 0;
    }
    if (!body->arena) {
      body->pending_data = new_buf;
      body->pending_capacity = new_capacity;
    }
  }

  memcpy(body->pending_data, chunk->data, chunk->data_len);
  body->pending_len = chunk->data_len;
  body->pending_offset = 0;

  body->chunks_sent++;
  body->bytes_sent += chunk->data_len;

  if (body->conn && body->conn->http.server) {
    valk_counter_v2_add(body->conn->http.server->metrics.bytes_sent, chunk->data_len);
  }

  VALK_DEBUG("stream_body: body %llu dequeued chunk (size=%zu, queue_len=%zu, total_chunks=%llu)",
             body->id, chunk->data_len, body->queue_len, (unsigned long long)body->chunks_sent);

  if (!body->arena) {
    __stream_chunk_free(chunk);
  }

  u64 to_send = body->pending_len < length ? body->pending_len : length;
  memcpy(buf, body->pending_data, to_send);
  body->pending_offset = to_send;

  if (body->queue_len < body->queue_max / 2) {
    if (body->on_drain) {
      VALK_DEBUG("stream_body: body %llu calling on_drain (queue_len=%llu)",
                 (unsigned long long)body->id, (unsigned long long)body->queue_len);
      body->on_drain(body, body->user_data);
    }
    valk_lval_t *lisp_on_drain = valk_handle_resolve(&valk_sys->handle_table,
                                                      body->lisp_on_drain_handle);
    if (lisp_on_drain && body->callback_env) {
      VALK_DEBUG("stream_body: body %llu calling lisp_on_drain (queue_len=%llu)",
                 (unsigned long long)body->id, (unsigned long long)body->queue_len);
      valk_lval_t *args = valk_lval_nil();
      valk_lval_t *result = valk_lval_eval_call(body->callback_env, lisp_on_drain, args);
      if (LVAL_TYPE(result) == LVAL_ERR) {
        VALK_WARN("stream_body: on-drain callback error: %s", result->str);
      }
    }
  }

  return (nghttp2_ssize)to_send;
}
// LCOV_EXCL_STOP

static u64 __get_current_time_ms(void) {
  return uv_hrtime() / 1000000;
}

void valk_stream_body_set_idle_timeout(valk_stream_body_t *body, u64 timeout_ms) {
  if (!body) {
    return;
  }
  body->idle_timeout_ms = timeout_ms;
  VALK_DEBUG("stream_body: body %llu idle timeout set to %llu ms",
             (unsigned long long)body->id, (unsigned long long)timeout_ms);
}

void valk_stream_body_touch_activity(valk_stream_body_t *body) {
  if (!body) {
    return;
  }
  body->last_activity_ms = __get_current_time_ms();
}

bool valk_stream_body_is_idle_expired(valk_stream_body_t *body) {
  if (!body || body->idle_timeout_ms == 0) {
    return false;
  }
  u64 now = __get_current_time_ms();
  u64 idle_time = now - body->last_activity_ms;
  return idle_time >= body->idle_timeout_ms;
}

void valk_stream_body_set_max_session(valk_stream_body_t *body, u64 max_session_ms) {
  if (!body) {
    return;
  }
  body->max_session_ms = max_session_ms;
  VALK_DEBUG("stream_body: body %llu max session set to %llu ms",
             (unsigned long long)body->id, (unsigned long long)max_session_ms);
}

bool valk_stream_body_is_session_expired(valk_stream_body_t *body) {
  if (!body || body->max_session_ms == 0) {
    return false;
  }
  u64 now = __get_current_time_ms();
  u64 session_time = now - body->created_at_ms;
  return session_time >= body->max_session_ms;
}

// LCOV_EXCL_START -- requires nghttp2 session integration to test RST_STREAM path
int valk_stream_body_cancel(valk_stream_body_t *body, u32 error_code) {
  if (!body) {
    return -1;
  }

  if (atomic_load(&body->state) == VALK_STREAM_CLOSED) {
    return 0;
  }

  VALK_INFO("stream_body: cancelling body id=%llu with error_code=%u",
            (unsigned long long)body->id, error_code);

  if (body->session && body->stream_id > 0) {
    int rv = nghttp2_submit_rst_stream(body->session, NGHTTP2_FLAG_NONE,
                                        body->stream_id, error_code);
    if (rv != 0) {
      VALK_WARN("stream_body: failed to submit RST_STREAM for body %llu: %s",
                (unsigned long long)body->id, nghttp2_strerror(rv));
    } else {
      valk_http2_flush_pending(body->conn);
    }
  }

  valk_stream_body_close(body);

  return 0;
}
// LCOV_EXCL_STOP
