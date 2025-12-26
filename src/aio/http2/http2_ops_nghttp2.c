#include "http2_ops.h"
#include <nghttp2/nghttp2.h>
#include <stdlib.h>
#include <string.h>

struct valk_http2_session {
  nghttp2_session *ng;
  valk_http2_callbacks_t cbs;
  void *user_data;
};

static int __on_begin_headers_cb(nghttp2_session *session,
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
                          const uint8_t *name, size_t namelen,
                          const uint8_t *value, size_t valuelen,
                          uint8_t flags, void *user_data) {
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

static int __on_data_chunk_cb(nghttp2_session *session, uint8_t flags,
                               int32_t stream_id, const uint8_t *data,
                               size_t len, void *user_data) {
  (void)session;
  (void)flags;
  valk_http2_session_t *s = user_data;
  if (s->cbs.on_data) {
    return s->cbs.on_data(s, stream_id, data, len, s->cbs.user_data);
  }
  return 0;
}

static int __on_stream_close_cb(nghttp2_session *session, int32_t stream_id,
                                 uint32_t error_code, void *user_data) {
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

static ssize_t session_recv(valk_http2_session_t *session, const uint8_t *data, size_t len) {
  return nghttp2_session_mem_recv(session->ng, data, len);
}

static ssize_t session_send(valk_http2_session_t *session, const uint8_t **data) {
  return nghttp2_session_mem_send(session->ng, data);
}

static bool session_want_write(valk_http2_session_t *session) {
  return nghttp2_session_want_write(session->ng) != 0;
}

static bool session_want_read(valk_http2_session_t *session) {
  return nghttp2_session_want_read(session->ng) != 0;
}

static void *stream_get_user_data(valk_http2_session_t *session, int32_t stream_id) {
  return nghttp2_session_get_stream_user_data(session->ng, stream_id);
}

static int stream_set_user_data(valk_http2_session_t *session, int32_t stream_id, void *data) {
  return nghttp2_session_set_stream_user_data(session->ng, stream_id, data);
}

static int stream_resume_data(valk_http2_session_t *session, int32_t stream_id) {
  return nghttp2_session_resume_data(session->ng, stream_id);
}

static int submit_settings(valk_http2_session_t *session, const void *settings, size_t count) {
  return nghttp2_submit_settings(session->ng, NGHTTP2_FLAG_NONE,
                                  (const nghttp2_settings_entry *)settings, count);
}

static int submit_response(valk_http2_session_t *session, int32_t stream_id,
                           const valk_http2_header_t *headers, size_t nheaders,
                           const valk_http2_data_provider_t *data_prd) {
  nghttp2_nv *nv = malloc(sizeof(nghttp2_nv) * nheaders);
  if (!nv) return -1;

  for (size_t i = 0; i < nheaders; i++) {
    nv[i].name = (uint8_t *)headers[i].name;
    nv[i].namelen = headers[i].name_len;
    nv[i].value = (uint8_t *)headers[i].value;
    nv[i].valuelen = headers[i].value_len;
    nv[i].flags = NGHTTP2_NV_FLAG_NONE;
  }

  nghttp2_data_provider2 ng_prd = {0};
  if (data_prd) {
    ng_prd.source.ptr = data_prd->source;
    ng_prd.read_callback = (nghttp2_data_source_read_callback2)data_prd->read_callback;
  }

  int rv = nghttp2_submit_response2(session->ng, stream_id, nv, nheaders,
                                     data_prd ? &ng_prd : nullptr);
  free(nv);
  return rv;
}

static int32_t submit_request(valk_http2_session_t *session,
                              const valk_http2_header_t *headers, size_t nheaders,
                              const valk_http2_data_provider_t *data_prd) {
  nghttp2_nv *nv = malloc(sizeof(nghttp2_nv) * nheaders);
  if (!nv) return -1;

  for (size_t i = 0; i < nheaders; i++) {
    nv[i].name = (uint8_t *)headers[i].name;
    nv[i].namelen = headers[i].name_len;
    nv[i].value = (uint8_t *)headers[i].value;
    nv[i].valuelen = headers[i].value_len;
    nv[i].flags = NGHTTP2_NV_FLAG_NONE;
  }

  nghttp2_data_provider2 ng_prd = {0};
  if (data_prd) {
    ng_prd.source.ptr = data_prd->source;
    ng_prd.read_callback = (nghttp2_data_source_read_callback2)data_prd->read_callback;
  }

  int32_t rv = nghttp2_submit_request2(session->ng, nullptr, nv, nheaders,
                                        data_prd ? &ng_prd : nullptr, nullptr);
  free(nv);
  return rv;
}

static int submit_rst_stream(valk_http2_session_t *session, int32_t stream_id, uint32_t error) {
  return nghttp2_submit_rst_stream(session->ng, NGHTTP2_FLAG_NONE, stream_id, error);
}

static int submit_goaway(valk_http2_session_t *session, uint32_t error, const char *msg) {
  size_t msg_len = msg ? strlen(msg) : 0;
  return nghttp2_submit_goaway(session->ng, NGHTTP2_FLAG_NONE, 0, error,
                                (const uint8_t *)msg, msg_len);
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
