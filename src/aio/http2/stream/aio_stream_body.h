#ifndef VALK_AIO_STREAM_BODY_H
#define VALK_AIO_STREAM_BODY_H

#include "aio.h"
#include "memory.h"
#include "gc.h"
#include <nghttp2/nghttp2.h>
#include <stdbool.h>

typedef struct valk_stream_body valk_stream_body_t;
typedef struct valk_stream_chunk valk_stream_chunk_t;

struct valk_lval_t;
struct valk_lenv_t;

typedef enum {
  VALK_STREAM_OPEN,
  VALK_STREAM_CLOSING,
  VALK_STREAM_CLOSED,
} valk_stream_state_e;

struct valk_stream_chunk {
  valk_stream_chunk_t *next;
  char *data;
  u64 data_len;
};

struct valk_stream_body {
  u64 id;
  _Atomic valk_stream_state_e state;

  valk_aio_handle_t *conn;
  nghttp2_session *session;
  i32 stream_id;

  valk_stream_body_t *next;

  valk_stream_chunk_t *queue_head;
  valk_stream_chunk_t *queue_tail;
  u64 queue_len;
  u64 queue_max;

  char *pending_data;
  u64 pending_len;
  u64 pending_offset;
  u64 pending_capacity;

  valk_mem_arena_t *arena;
  valk_arena_checkpoint_t chunk_checkpoint;

  bool data_deferred;
  u64 bytes_sent;
  u64 chunks_sent;

  u64 created_at_ms;
  u64 last_activity_ms;
  u64 idle_timeout_ms;
  u64 max_session_ms;

  void (*on_drain)(valk_stream_body_t *body, void *user_data);
  void (*on_close)(valk_stream_body_t *body, void *user_data);
  void (*on_timeout)(valk_stream_body_t *body, void *user_data);
  void *user_data;

  valk_handle_t lisp_on_drain_handle;
  valk_handle_t lisp_on_close_handle;
  valk_handle_t lisp_on_timeout_handle;
  struct valk_lenv_t *callback_env;

  struct valk_async_handle_t *closed_handle;
};

valk_stream_body_t *valk_stream_body_new(
    valk_aio_handle_t *conn,
    nghttp2_session *session,
    i32 stream_id,
    nghttp2_data_provider2 *data_prd_out,
    valk_mem_arena_t *arena);

void valk_stream_body_close(valk_stream_body_t *body);
void valk_stream_body_free(valk_stream_body_t *body);

void valk_stream_body_register(valk_stream_body_t *body);
void valk_stream_body_unregister(valk_stream_body_t *body);
void valk_stream_body_close_by_stream_id(valk_aio_handle_t *conn, i32 stream_id);
void valk_stream_body_close_all(valk_aio_handle_t *conn);
u64 valk_stream_body_get_bytes_sent(valk_aio_handle_t *conn, i32 stream_id);
bool valk_stream_body_exists_for_stream(valk_aio_handle_t *conn, i32 stream_id);

int valk_stream_body_write(valk_stream_body_t *body, const char *data, u64 len);

bool valk_stream_body_writable(valk_stream_body_t *body);
u64 valk_stream_body_queue_len(valk_stream_body_t *body);

void valk_stream_body_set_idle_timeout(valk_stream_body_t *body, u64 timeout_ms);
void valk_stream_body_set_max_session(valk_stream_body_t *body, u64 max_session_ms);
void valk_stream_body_touch_activity(valk_stream_body_t *body);
bool valk_stream_body_is_idle_expired(valk_stream_body_t *body);
bool valk_stream_body_is_session_expired(valk_stream_body_t *body);

int valk_stream_body_cancel(valk_stream_body_t *body, u32 error_code);

void valk_stream_body_check_orphaned(valk_aio_handle_t *conn);

void valk_register_stream_builtins(struct valk_lenv_t *env);

#endif
