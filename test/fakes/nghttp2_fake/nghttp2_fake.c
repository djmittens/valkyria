#include "nghttp2_fake.h"
#include "nghttp2_fake_control.h"
#include <stdlib.h>
#include <string.h>

typedef struct fake_stream {
  int32_t id;
  void *user_data;
  bool closed;
  
  int status_code;
  nghttp2_nv *response_headers;
  size_t response_nheaders;
  uint8_t *response_body;
  size_t response_body_len;
  size_t response_body_cap;
  
  struct fake_stream *next;
} fake_stream_t;

struct nghttp2_session_callbacks {
  nghttp2_on_begin_headers_callback on_begin_headers;
  nghttp2_on_header_callback on_header;
  nghttp2_on_data_chunk_recv_callback on_data_chunk_recv;
  nghttp2_on_stream_close_callback on_stream_close;
  nghttp2_on_frame_send_callback on_frame_send;
  nghttp2_on_frame_recv_callback on_frame_recv;
  nghttp2_send_callback send;
  nghttp2_recv_callback recv;
};

struct nghttp2_session {
  nghttp2_session_callbacks cbs;
  void *user_data;
  bool is_server;
  int32_t next_stream_id;
  fake_stream_t *streams;
  bool want_write;
};

struct nghttp2_option {
  int no_auto_window_update;
  uint32_t peer_max_concurrent_streams;
};

int nghttp2_session_callbacks_new(nghttp2_session_callbacks **cbs_ptr) {
  *cbs_ptr = calloc(1, sizeof(nghttp2_session_callbacks));
  return *cbs_ptr ? 0 : -1;
}

void nghttp2_session_callbacks_del(nghttp2_session_callbacks *cbs) {
  free(cbs);
}

void nghttp2_session_callbacks_set_on_begin_headers_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_begin_headers_callback cb) {
  cbs->on_begin_headers = cb;
}

void nghttp2_session_callbacks_set_on_header_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_header_callback cb) {
  cbs->on_header = cb;
}

void nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_data_chunk_recv_callback cb) {
  cbs->on_data_chunk_recv = cb;
}

void nghttp2_session_callbacks_set_on_stream_close_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_stream_close_callback cb) {
  cbs->on_stream_close = cb;
}

void nghttp2_session_callbacks_set_on_frame_send_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_frame_send_callback cb) {
  cbs->on_frame_send = cb;
}

void nghttp2_session_callbacks_set_on_frame_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_frame_recv_callback cb) {
  cbs->on_frame_recv = cb;
}

void nghttp2_session_callbacks_set_send_callback(
    nghttp2_session_callbacks *cbs, nghttp2_send_callback cb) {
  cbs->send = cb;
}

void nghttp2_session_callbacks_set_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_recv_callback cb) {
  cbs->recv = cb;
}

int nghttp2_option_new(nghttp2_option **option_ptr) {
  *option_ptr = calloc(1, sizeof(nghttp2_option));
  return *option_ptr ? 0 : -1;
}

void nghttp2_option_del(nghttp2_option *option) {
  free(option);
}

void nghttp2_option_set_no_auto_window_update(nghttp2_option *option, int val) {
  option->no_auto_window_update = val;
}

void nghttp2_option_set_peer_max_concurrent_streams(nghttp2_option *option, uint32_t val) {
  option->peer_max_concurrent_streams = val;
}

int nghttp2_session_server_new(nghttp2_session **session_ptr,
                                const nghttp2_session_callbacks *callbacks,
                                void *user_data) {
  return nghttp2_session_server_new2(session_ptr, callbacks, user_data, NULL);
}

int nghttp2_session_server_new2(nghttp2_session **session_ptr,
                                 const nghttp2_session_callbacks *callbacks,
                                 void *user_data,
                                 const nghttp2_option *option) {
  (void)option;
  nghttp2_session *s = calloc(1, sizeof(nghttp2_session));
  if (!s) return -1;
  
  if (callbacks) s->cbs = *callbacks;
  s->user_data = user_data;
  s->is_server = true;
  s->next_stream_id = 1;
  
  *session_ptr = s;
  return 0;
}

int nghttp2_session_server_new3(nghttp2_session **session_ptr,
                                 const nghttp2_session_callbacks *callbacks,
                                 void *user_data,
                                 const nghttp2_option *option,
                                 nghttp2_mem *mem) {
  (void)mem;
  return nghttp2_session_server_new2(session_ptr, callbacks, user_data, option);
}

int nghttp2_session_client_new(nghttp2_session **session_ptr,
                                const nghttp2_session_callbacks *callbacks,
                                void *user_data) {
  return nghttp2_session_client_new2(session_ptr, callbacks, user_data, NULL);
}

int nghttp2_session_client_new2(nghttp2_session **session_ptr,
                                 const nghttp2_session_callbacks *callbacks,
                                 void *user_data,
                                 const nghttp2_option *option) {
  (void)option;
  nghttp2_session *s = calloc(1, sizeof(nghttp2_session));
  if (!s) return -1;
  
  if (callbacks) s->cbs = *callbacks;
  s->user_data = user_data;
  s->is_server = false;
  s->next_stream_id = 1;
  
  *session_ptr = s;
  return 0;
}

void nghttp2_session_del(nghttp2_session *session) {
  if (!session) return;
  
  fake_stream_t *s = session->streams;
  while (s) {
    fake_stream_t *next = s->next;
    free(s->response_headers);
    free(s->response_body);
    free(s);
    s = next;
  }
  free(session);
}

static fake_stream_t *find_stream(nghttp2_session *session, int32_t stream_id) {
  fake_stream_t *s = session->streams;
  while (s) {
    if (s->id == stream_id) return s;
    s = s->next;
  }
  return NULL;
}

static fake_stream_t *create_stream(nghttp2_session *session, int32_t stream_id) {
  fake_stream_t *s = calloc(1, sizeof(fake_stream_t));
  if (!s) return NULL;
  s->id = stream_id;
  s->next = session->streams;
  session->streams = s;
  return s;
}

ssize_t nghttp2_session_mem_recv(nghttp2_session *session,
                                  const uint8_t *in, size_t inlen) {
  (void)session;
  (void)in;
  return (ssize_t)inlen;
}

ssize_t nghttp2_session_mem_send(nghttp2_session *session,
                                  const uint8_t **data_ptr) {
  (void)session;
  *data_ptr = NULL;
  return 0;
}

int nghttp2_session_send(nghttp2_session *session) {
  (void)session;
  return 0;
}

int nghttp2_session_recv(nghttp2_session *session) {
  (void)session;
  return 0;
}

int nghttp2_session_want_write(nghttp2_session *session) {
  return session->want_write ? 1 : 0;
}

int nghttp2_session_want_read(nghttp2_session *session) {
  (void)session;
  return 1;
}

void *nghttp2_session_get_stream_user_data(nghttp2_session *session, int32_t stream_id) {
  fake_stream_t *s = find_stream(session, stream_id);
  return s ? s->user_data : NULL;
}

int nghttp2_session_set_stream_user_data(nghttp2_session *session, int32_t stream_id,
                                          void *user_data) {
  fake_stream_t *s = find_stream(session, stream_id);
  if (!s) {
    s = create_stream(session, stream_id);
    if (!s) return -1;
  }
  s->user_data = user_data;
  return 0;
}

int nghttp2_session_resume_data(nghttp2_session *session, int32_t stream_id) {
  (void)session;
  (void)stream_id;
  return 0;
}

int nghttp2_session_consume(nghttp2_session *session, int32_t stream_id, size_t size) {
  (void)session;
  (void)stream_id;
  (void)size;
  return 0;
}

int nghttp2_session_consume_connection(nghttp2_session *session, size_t size) {
  (void)session;
  (void)size;
  return 0;
}

int nghttp2_submit_settings(nghttp2_session *session, uint8_t flags,
                            const nghttp2_settings_entry *iv, size_t niv) {
  (void)session;
  (void)flags;
  (void)iv;
  (void)niv;
  return 0;
}

int nghttp2_submit_response2(nghttp2_session *session, int32_t stream_id,
                             const nghttp2_nv *nva, size_t nvlen,
                             const nghttp2_data_provider2 *data_prd) {
  fake_stream_t *s = find_stream(session, stream_id);
  if (!s) {
    s = create_stream(session, stream_id);
    if (!s) return -1;
  }
  
  s->response_headers = malloc(sizeof(nghttp2_nv) * nvlen);
  if (s->response_headers) {
    memcpy(s->response_headers, nva, sizeof(nghttp2_nv) * nvlen);
    s->response_nheaders = nvlen;
  }
  
  for (size_t i = 0; i < nvlen; i++) {
    if (nva[i].namelen == 7 && memcmp(nva[i].name, ":status", 7) == 0) {
      char buf[8] = {0};
      size_t len = nva[i].valuelen < 7 ? nva[i].valuelen : 7;
      memcpy(buf, nva[i].value, len);
      s->status_code = atoi(buf);
      break;
    }
  }
  
  if (data_prd && data_prd->read_callback) {
    uint8_t buf[4096];
    uint32_t flags = 0;
    ssize_t nread;
    
    while ((nread = data_prd->read_callback(session, stream_id, buf, sizeof(buf),
                                             &flags, (nghttp2_data_source *)&data_prd->source,
                                             session->user_data)) > 0) {
      size_t new_len = s->response_body_len + (size_t)nread;
      if (new_len > s->response_body_cap) {
        size_t new_cap = s->response_body_cap == 0 ? 4096 : s->response_body_cap * 2;
        while (new_cap < new_len) new_cap *= 2;
        s->response_body = realloc(s->response_body, new_cap);
        s->response_body_cap = new_cap;
      }
      memcpy(s->response_body + s->response_body_len, buf, (size_t)nread);
      s->response_body_len += (size_t)nread;
      
      if (flags & NGHTTP2_DATA_FLAG_EOF) break;
    }
  }
  
  session->want_write = true;
  return 0;
}

int nghttp2_submit_response(nghttp2_session *session, int32_t stream_id,
                            const nghttp2_nv *nva, size_t nvlen,
                            const nghttp2_data_provider *data_prd) {
  nghttp2_data_provider2 dp2 = {0};
  if (data_prd) {
    dp2.source = data_prd->source;
    dp2.read_callback = (nghttp2_data_source_read_callback2)data_prd->read_callback;
  }
  return nghttp2_submit_response2(session, stream_id, nva, nvlen, 
                                   data_prd ? &dp2 : NULL);
}

int32_t nghttp2_submit_request2(nghttp2_session *session,
                                 const void *pri_spec,
                                 const nghttp2_nv *nva, size_t nvlen,
                                 const nghttp2_data_provider2 *data_prd,
                                 void *stream_user_data) {
  (void)pri_spec;
  (void)data_prd;
  
  int32_t stream_id = session->next_stream_id;
  session->next_stream_id += 2;
  
  fake_stream_t *s = create_stream(session, stream_id);
  if (!s) return -1;
  
  s->user_data = stream_user_data;
  s->response_headers = malloc(sizeof(nghttp2_nv) * nvlen);
  if (s->response_headers) {
    memcpy(s->response_headers, nva, sizeof(nghttp2_nv) * nvlen);
    s->response_nheaders = nvlen;
  }
  
  return stream_id;
}

int32_t nghttp2_submit_request(nghttp2_session *session,
                                const void *pri_spec,
                                const nghttp2_nv *nva, size_t nvlen,
                                const nghttp2_data_provider *data_prd,
                                void *stream_user_data) {
  nghttp2_data_provider2 dp2 = {0};
  if (data_prd) {
    dp2.source = data_prd->source;
    dp2.read_callback = (nghttp2_data_source_read_callback2)data_prd->read_callback;
  }
  return nghttp2_submit_request2(session, pri_spec, nva, nvlen,
                                  data_prd ? &dp2 : NULL, stream_user_data);
}

int nghttp2_submit_rst_stream(nghttp2_session *session, uint8_t flags,
                               int32_t stream_id, uint32_t error_code) {
  (void)flags;
  (void)error_code;
  
  fake_stream_t *s = find_stream(session, stream_id);
  if (s) s->closed = true;
  return 0;
}

int nghttp2_submit_goaway(nghttp2_session *session, uint8_t flags,
                           int32_t last_stream_id, uint32_t error_code,
                           const uint8_t *opaque_data, size_t opaque_data_len) {
  (void)session;
  (void)flags;
  (void)last_stream_id;
  (void)error_code;
  (void)opaque_data;
  (void)opaque_data_len;
  return 0;
}

const char *nghttp2_strerror(int lib_error_code) {
  (void)lib_error_code;
  return "fake error";
}

int32_t nghttp2_fake_inject_request(nghttp2_session *session,
                                     const char *method,
                                     const char *path,
                                     const nghttp2_nv *extra_headers,
                                     size_t nextra,
                                     const uint8_t *body,
                                     size_t body_len) {
  int32_t stream_id = session->next_stream_id;
  session->next_stream_id += 2;
  
  create_stream(session, stream_id);
  
  nghttp2_frame frame = {0};
  frame.hd.stream_id = stream_id;
  frame.hd.type = NGHTTP2_HEADERS;
  
  if (session->cbs.on_begin_headers) {
    session->cbs.on_begin_headers(session, &frame, session->user_data);
  }
  
  if (session->cbs.on_header) {
    session->cbs.on_header(session, &frame,
                           (uint8_t *)":method", 7,
                           (uint8_t *)method, strlen(method),
                           0, session->user_data);
    session->cbs.on_header(session, &frame,
                           (uint8_t *)":path", 5,
                           (uint8_t *)path, strlen(path),
                           0, session->user_data);
    session->cbs.on_header(session, &frame,
                           (uint8_t *)":scheme", 7,
                           (uint8_t *)"https", 5,
                           0, session->user_data);
    
    for (size_t i = 0; i < nextra; i++) {
      session->cbs.on_header(session, &frame,
                             extra_headers[i].name, extra_headers[i].namelen,
                             extra_headers[i].value, extra_headers[i].valuelen,
                             0, session->user_data);
    }
  }
  
  if (body && body_len > 0 && session->cbs.on_data_chunk_recv) {
    session->cbs.on_data_chunk_recv(session, 0, stream_id, body, body_len,
                                     session->user_data);
  }
  
  if (session->cbs.on_frame_recv) {
    frame.hd.flags = NGHTTP2_FLAG_END_HEADERS;
    if (!body || body_len == 0) {
      frame.hd.flags |= NGHTTP2_FLAG_END_STREAM;
    }
    session->cbs.on_frame_recv(session, &frame, session->user_data);
    
    if (body && body_len > 0) {
      frame.hd.type = NGHTTP2_DATA;
      frame.hd.flags = NGHTTP2_FLAG_END_STREAM;
      session->cbs.on_frame_recv(session, &frame, session->user_data);
    }
  }
  
  return stream_id;
}

bool nghttp2_fake_get_response(nghttp2_session *session, int32_t stream_id,
                                nghttp2_fake_response_t *response) {
  fake_stream_t *s = find_stream(session, stream_id);
  if (!s || s->status_code == 0) return false;
  
  response->status_code = s->status_code;
  response->headers = s->response_headers;
  response->nheaders = s->response_nheaders;
  response->body = s->response_body;
  response->body_len = s->response_body_len;
  response->closed = s->closed;
  
  return true;
}

size_t nghttp2_fake_stream_count(nghttp2_session *session) {
  size_t count = 0;
  fake_stream_t *s = session->streams;
  while (s) {
    count++;
    s = s->next;
  }
  return count;
}

bool nghttp2_fake_stream_exists(nghttp2_session *session, int32_t stream_id) {
  return find_stream(session, stream_id) != NULL;
}

int nghttp2_fake_process_pending(nghttp2_session *session) {
  (void)session;
  return 0;
}

void nghttp2_fake_reset(nghttp2_session *session) {
  fake_stream_t *s = session->streams;
  while (s) {
    fake_stream_t *next = s->next;
    free(s->response_headers);
    free(s->response_body);
    free(s);
    s = next;
  }
  session->streams = NULL;
  session->next_stream_id = session->is_server ? 2 : 1;
  session->want_write = false;
}
