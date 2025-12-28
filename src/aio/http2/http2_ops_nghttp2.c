#include "http2_ops.h"
#include <nghttp2/nghttp2.h>
#include <stdlib.h>
#include <string.h>

struct valk_http2_session {
  nghttp2_session *ng;
  valk_http2_callbacks_t cbs;
  void *user_data;
};

static int __on_begin_headers_cb(__attribute__((unused)) nghttp2_session *session,
                                  const nghttp2_frame *frame,
                                  void *user_data) {
  valk_http2_session_t *s = user_data;
  if (s->cbs.on_begin_headers) {
    return s->cbs.on_begin_headers(s, frame->hd.stream_id, s->cbs.user_data);
  }
  return 0;
}

static int __on_header_cb(nghttp2_session *session,
                          const nghttp2_frame *frame,
                          const u8 *name, size_t namelen,
                          const u8 *value, size_t valuelen,
                          u8 flags, void *user_data) {
  (void)session;
  (void)flags;
  valk_http2_session_t *s = user_data;
  if (s->cbs.on_header) {
    valk_http2_header_t hdr = {
      .name = name,
      .name_len = namelen,
      .value = value,
      .value_len = valuelen,
    };
    return s->cbs.on_header(s, frame->hd.stream_id, &hdr, s->cbs.user_data);
  }
  return 0;
}

static int __on_data_chunk_cb(nghttp2_session *session, u8 flags,
                               i32 stream_id, const u8 *data,
                               size_t len, void *user_data) {
  (void)session;
  (void)flags;
  valk_http2_session_t *s = user_data;
  if (s->cbs.on_data) {
    return s->cbs.on_data(s, stream_id, data, len, s->cbs.user_data);
  }
  return 0;
}

static int __on_stream_close_cb(nghttp2_session *session, i32 stream_id,
                                 u32 error_code, void *user_data) {
  (void)session;
  valk_http2_session_t *s = user_data;
  if (s->cbs.on_stream_close) {
    return s->cbs.on_stream_close(s, stream_id, error_code, s->cbs.user_data);
  }
  return 0;
}

static int __on_frame_send_cb(nghttp2_session *session,
                               const nghttp2_frame *frame,
                               void *user_data) {
  (void)session;
  valk_http2_session_t *s = user_data;
  if (s->cbs.on_frame_send) {
    return s->cbs.on_frame_send(s, frame->hd.stream_id, frame->hd.type, s->cbs.user_data);
  }
  return 0;
}

static int __on_frame_recv_cb(nghttp2_session *session,
                               const nghttp2_frame *frame,
                               void *user_data) {
  (void)session;
  valk_http2_session_t *s = user_data;
  if (s->cbs.on_frame_recv) {
    return s->cbs.on_frame_recv(s, frame->hd.stream_id, frame->hd.type,
                                 frame->hd.flags, s->cbs.user_data);
  }
  return 0;
}

typedef struct {
  valk_http2_session_t *session;
  valk_http2_data_read_cb read_cb;
  void *source;
} __data_provider_ctx_t;

static ssize_t __data_read_wrapper(nghttp2_session *ng_session __attribute__((unused)),
                                    i32 stream_id,
                                    u8 *buf, size_t length,
                                    u32 *data_flags,
                                    nghttp2_data_source *source,
                                    void *user_data __attribute__((unused))) {
  __data_provider_ctx_t *ctx = source->ptr;
  return ctx->read_cb(ctx->session, stream_id, buf, length, data_flags, ctx->source);
}

static nghttp2_session_callbacks *__create_ng_callbacks(void) {
  nghttp2_session_callbacks *cbs;
  nghttp2_session_callbacks_new(&cbs);
  nghttp2_session_callbacks_set_on_begin_headers_callback(cbs, __on_begin_headers_cb);
  nghttp2_session_callbacks_set_on_header_callback(cbs, __on_header_cb);
  nghttp2_session_callbacks_set_on_data_chunk_recv_callback(cbs, __on_data_chunk_cb);
  nghttp2_session_callbacks_set_on_stream_close_callback(cbs, __on_stream_close_cb);
  nghttp2_session_callbacks_set_on_frame_send_callback(cbs, __on_frame_send_cb);
  nghttp2_session_callbacks_set_on_frame_recv_callback(cbs, __on_frame_recv_cb);
  return cbs;
}

static valk_http2_session_t *server_session_new(const valk_http2_callbacks_t *cbs,
                                                 void *user_data) {
  valk_http2_session_t *s = malloc(sizeof(valk_http2_session_t));
  if (!s) return nullptr;

  if (cbs) {
    s->cbs = *cbs;
  } else {
    memset(&s->cbs, 0, sizeof(s->cbs));
  }
  s->user_data = user_data;

  nghttp2_session_callbacks *ng_cbs = __create_ng_callbacks();
  int rv = nghttp2_session_server_new(&s->ng, ng_cbs, s);
  nghttp2_session_callbacks_del(ng_cbs);

  if (rv != 0) {
    free(s);
    return nullptr;
  }

  return s;
}

static valk_http2_session_t *client_session_new(const valk_http2_callbacks_t *cbs,
                                                 void *user_data) {
  valk_http2_session_t *s = malloc(sizeof(valk_http2_session_t));
  if (!s) return nullptr;

  if (cbs) {
    s->cbs = *cbs;
  } else {
    memset(&s->cbs, 0, sizeof(s->cbs));
  }
  s->user_data = user_data;

  nghttp2_session_callbacks *ng_cbs = __create_ng_callbacks();
  int rv = nghttp2_session_client_new(&s->ng, ng_cbs, s);
  nghttp2_session_callbacks_del(ng_cbs);

  if (rv != 0) {
    free(s);
    return nullptr;
  }

  return s;
}

static void session_del(valk_http2_session_t *session) {
  if (!session) return;
  nghttp2_session_del(session->ng);
  free(session);
}

static ssize_t session_recv(valk_http2_session_t *session, const u8 *data, u64 len) {
  return nghttp2_session_mem_recv(session->ng, data, len);
}

static ssize_t session_send(valk_http2_session_t *session, const u8 **data) {
  return nghttp2_session_mem_send(session->ng, data);
}

static bool session_want_write(valk_http2_session_t *session) {
  return nghttp2_session_want_write(session->ng) != 0;
}

static bool session_want_read(valk_http2_session_t *session) {
  return nghttp2_session_want_read(session->ng) != 0;
}

static void *stream_get_user_data(valk_http2_session_t *session, i32 stream_id) {
  return nghttp2_session_get_stream_user_data(session->ng, stream_id);
}

static int stream_set_user_data(valk_http2_session_t *session, i32 stream_id, void *data) {
  return nghttp2_session_set_stream_user_data(session->ng, stream_id, data);
}

static int stream_resume_data(valk_http2_session_t *session, i32 stream_id) {
  return nghttp2_session_resume_data(session->ng, stream_id);
}

static int submit_settings(valk_http2_session_t *session, const void *settings, u64 count) {
  return nghttp2_submit_settings(session->ng, NGHTTP2_FLAG_NONE,
                                  (const nghttp2_settings_entry *)settings, count);
}

static int submit_response(valk_http2_session_t *session, i32 stream_id,
                           const valk_http2_header_t *headers, u64 nheaders,
                           const valk_http2_data_provider_t *data_prd) {
  nghttp2_nv *nv = malloc(sizeof(nghttp2_nv) * nheaders);
  if (!nv) return -1;

  for (u64 i = 0; i < nheaders; i++) {
    nv[i].name = (u8 *)headers[i].name;
    nv[i].namelen = headers[i].name_len;
    nv[i].value = (u8 *)headers[i].value;
    nv[i].valuelen = headers[i].value_len;
    nv[i].flags = NGHTTP2_NV_FLAG_NONE;
  }

  nghttp2_data_provider2 ng_prd = {0};
  __data_provider_ctx_t *ctx = nullptr;
  if (data_prd) {
    ctx = malloc(sizeof(__data_provider_ctx_t));
    if (!ctx) { free(nv); return -1; }
    ctx->session = session;
    ctx->read_cb = data_prd->read_callback;
    ctx->source = data_prd->source;
    ng_prd.source.ptr = ctx;
    ng_prd.read_callback = __data_read_wrapper;
  }

  int rv = nghttp2_submit_response2(session->ng, stream_id, nv, nheaders,
                                     data_prd ? &ng_prd : nullptr);
  free(nv);
  return rv;
}

static i32 submit_request(valk_http2_session_t *session,
                              const valk_http2_header_t *headers, u64 nheaders,
                              const valk_http2_data_provider_t *data_prd) {
  nghttp2_nv *nv = malloc(sizeof(nghttp2_nv) * nheaders);
  if (!nv) return -1;

  for (u64 i = 0; i < nheaders; i++) {
    nv[i].name = (u8 *)headers[i].name;
    nv[i].namelen = headers[i].name_len;
    nv[i].value = (u8 *)headers[i].value;
    nv[i].valuelen = headers[i].value_len;
    nv[i].flags = NGHTTP2_NV_FLAG_NONE;
  }

  nghttp2_data_provider2 ng_prd = {0};
  __data_provider_ctx_t *ctx = nullptr;
  if (data_prd) {
    ctx = malloc(sizeof(__data_provider_ctx_t));
    if (!ctx) { free(nv); return -1; }
    ctx->session = session;
    ctx->read_cb = data_prd->read_callback;
    ctx->source = data_prd->source;
    ng_prd.source.ptr = ctx;
    ng_prd.read_callback = __data_read_wrapper;
  }

  i32 rv = nghttp2_submit_request2(session->ng, nullptr, nv, nheaders,
                                        data_prd ? &ng_prd : nullptr, nullptr);
  free(nv);
  return rv;
}

static int submit_rst_stream(valk_http2_session_t *session, i32 stream_id, u32 error) {
  return nghttp2_submit_rst_stream(session->ng, NGHTTP2_FLAG_NONE, stream_id, error);
}

static int submit_goaway(valk_http2_session_t *session, u32 error, const char *msg) {
  u64 msg_len = msg ? strlen(msg) : 0;
  return nghttp2_submit_goaway(session->ng, NGHTTP2_FLAG_NONE, 0, error,
                                (const u8 *)msg, msg_len);
}

static const char *h2_strerror(int error_code) {
  return nghttp2_strerror(error_code);
}

const valk_http2_ops_t valk_http2_ops_nghttp2 = {
  .server_session_new = server_session_new,
  .client_session_new = client_session_new,
  .session_del = session_del,
  .session_recv = session_recv,
  .session_send = session_send,
  .session_want_write = session_want_write,
  .session_want_read = session_want_read,
  .stream_get_user_data = stream_get_user_data,
  .stream_set_user_data = stream_set_user_data,
  .stream_resume_data = stream_resume_data,
  .submit_settings = submit_settings,
  .submit_response = submit_response,
  .submit_request = submit_request,
  .submit_rst_stream = submit_rst_stream,
  .submit_goaway = submit_goaway,
  .strerror = h2_strerror,
};
