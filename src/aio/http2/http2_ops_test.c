#include "http2_ops.h"
#include <stdlib.h>
#include <string.h>

struct valk_http2_session {
  bool is_server;
  valk_http2_callbacks_t cbs;
  void *user_data;
  valk_test_http2_stream_t *streams;
  int32_t next_stream_id;
};

static valk_test_http2_stream_t *__find_stream(valk_http2_session_t *session, int32_t stream_id) {
  valk_test_http2_stream_t *s = session->streams;
  while (s) {
    if (s->id == stream_id) return s;
    s = s->next;
  }
  return nullptr;
}

static valk_test_http2_stream_t *__create_stream(valk_http2_session_t *session, int32_t stream_id) {
  valk_test_http2_stream_t *s = malloc(sizeof(valk_test_http2_stream_t));
  if (!s) return nullptr;
  memset(s, 0, sizeof(*s));
  s->id = stream_id;
  s->next = session->streams;
  session->streams = s;
  return s;
}

static valk_http2_session_t *test_server_session_new(const valk_http2_callbacks_t *cbs,
                                                      void *user_data) {
  valk_http2_session_t *s = malloc(sizeof(valk_http2_session_t));
  if (!s) return nullptr;
  memset(s, 0, sizeof(*s));
  s->is_server = true;
  if (cbs) s->cbs = *cbs;
  s->user_data = user_data;
  s->next_stream_id = 1;
  return s;
}

static valk_http2_session_t *test_client_session_new(const valk_http2_callbacks_t *cbs,
                                                      void *user_data) {
  valk_http2_session_t *s = malloc(sizeof(valk_http2_session_t));
  if (!s) return nullptr;
  memset(s, 0, sizeof(*s));
  s->is_server = false;
  if (cbs) s->cbs = *cbs;
  s->user_data = user_data;
  s->next_stream_id = 1;
  return s;
}

static void test_session_del(valk_http2_session_t *session) {
  if (!session) return;
  valk_test_http2_stream_t *s = session->streams;
  while (s) {
    valk_test_http2_stream_t *next = s->next;
    free(s->headers);
    free(s->body);
    free(s);
    s = next;
  }
  free(session);
}

static ssize_t test_session_recv(valk_http2_session_t *session, const uint8_t *data, size_t len) {
  (void)session;
  (void)data;
  return (ssize_t)len;
}

static ssize_t test_session_send(valk_http2_session_t *session, const uint8_t **data) {
  (void)session;
  *data = nullptr;
  return 0;
}

static bool test_session_want_write(valk_http2_session_t *session) {
  (void)session;
  return false;
}

static bool test_session_want_read(valk_http2_session_t *session) {
  (void)session;
  return true;
}

static void *test_stream_get_user_data(valk_http2_session_t *session, int32_t stream_id) {
  valk_test_http2_stream_t *s = __find_stream(session, stream_id);
  return s ? s->user_data : nullptr;
}

static int test_stream_set_user_data(valk_http2_session_t *session, int32_t stream_id, void *data) {
  valk_test_http2_stream_t *s = __find_stream(session, stream_id);
  if (!s) {
    s = __create_stream(session, stream_id);
    if (!s) return -1;
  }
  s->user_data = data;
  return 0;
}

static int test_stream_resume_data(valk_http2_session_t *session, int32_t stream_id) {
  (void)session;
  (void)stream_id;
  return 0;
}

static int test_submit_settings(valk_http2_session_t *session, const void *settings, size_t count) {
  (void)session;
  (void)settings;
  (void)count;
  return 0;
}

static int test_submit_response(valk_http2_session_t *session, int32_t stream_id,
                                 const valk_http2_header_t *headers, size_t nheaders,
                                 const valk_http2_data_provider_t *data_prd) {
  valk_test_http2_stream_t *s = __find_stream(session, stream_id);
  if (!s) {
    s = __create_stream(session, stream_id);
    if (!s) return -1;
  }

  if (nheaders > 0) {
    s->headers = malloc(sizeof(valk_http2_header_t) * nheaders);
    if (s->headers) {
      memcpy(s->headers, headers, sizeof(valk_http2_header_t) * nheaders);
      s->header_count = nheaders;
      s->header_cap = nheaders;
    }

    for (size_t i = 0; i < nheaders; i++) {
      if (headers[i].name_len == 7 && memcmp(headers[i].name, ":status", 7) == 0) {
        char status_buf[8] = {0};
        size_t copy_len = headers[i].value_len < 7 ? headers[i].value_len : 7;
        memcpy(status_buf, headers[i].value, copy_len);
        s->status_code = atoi(status_buf);
        break;
      }
    }
  }

  if (data_prd && data_prd->read_callback) {
    uint8_t buf[4096];
    uint32_t flags = 0;
    ssize_t nread;
    
    while ((nread = data_prd->read_callback(session, stream_id, buf, sizeof(buf),
                                             &flags, data_prd->source)) > 0) {
      size_t new_len = s->body_len + (size_t)nread;
      if (new_len > s->body_cap) {
        size_t new_cap = s->body_cap == 0 ? 4096 : s->body_cap * 2;
        while (new_cap < new_len) new_cap *= 2;
        uint8_t *new_body = realloc(s->body, new_cap);
        if (!new_body) return -1;
        s->body = new_body;
        s->body_cap = new_cap;
      }
      memcpy(s->body + s->body_len, buf, (size_t)nread);
      s->body_len += (size_t)nread;
      
      if (flags & VALK_HTTP2_DATA_FLAG_EOF) break;
    }
  }

  s->response_sent = true;
  return 0;
}

static int32_t test_submit_request(valk_http2_session_t *session,
                                    const valk_http2_header_t *headers, size_t nheaders,
                                    const valk_http2_data_provider_t *data_prd) {
  int32_t stream_id = session->next_stream_id;
  session->next_stream_id += 2;

  valk_test_http2_stream_t *s = __create_stream(session, stream_id);
  if (!s) return -1;

  if (nheaders > 0) {
    s->headers = malloc(sizeof(valk_http2_header_t) * nheaders);
    if (s->headers) {
      memcpy(s->headers, headers, sizeof(valk_http2_header_t) * nheaders);
      s->header_count = nheaders;
    }
  }

  if (data_prd && data_prd->read_callback) {
    uint8_t buf[4096];
    uint32_t flags = 0;
    ssize_t nread;
    
    while ((nread = data_prd->read_callback(session, stream_id, buf, sizeof(buf),
                                             &flags, data_prd->source)) > 0) {
      size_t new_len = s->body_len + (size_t)nread;
      if (new_len > s->body_cap) {
        size_t new_cap = s->body_cap == 0 ? 4096 : s->body_cap * 2;
        while (new_cap < new_len) new_cap *= 2;
        uint8_t *new_body = realloc(s->body, new_cap);
        if (!new_body) return -1;
        s->body = new_body;
        s->body_cap = new_cap;
      }
      memcpy(s->body + s->body_len, buf, (size_t)nread);
      s->body_len += (size_t)nread;
      
      if (flags & VALK_HTTP2_DATA_FLAG_EOF) break;
    }
  }

  return stream_id;
}

static int test_submit_rst_stream(valk_http2_session_t *session, int32_t stream_id, uint32_t error) {
  (void)error;
  valk_test_http2_stream_t *s = __find_stream(session, stream_id);
  if (s) s->closed = true;
  return 0;
}

static int test_submit_goaway(valk_http2_session_t *session, uint32_t error, const char *msg) {
  (void)session;
  (void)error;
  (void)msg;
  return 0;
}

static const char *test_strerror(int error_code) {
  (void)error_code;
  return "test error";
}

const valk_http2_ops_t valk_http2_ops_test = {
  .server_session_new = test_server_session_new,
  .client_session_new = test_client_session_new,
  .session_del = test_session_del,
  .session_recv = test_session_recv,
  .session_send = test_session_send,
  .session_want_write = test_session_want_write,
  .session_want_read = test_session_want_read,
  .stream_get_user_data = test_stream_get_user_data,
  .stream_set_user_data = test_stream_set_user_data,
  .stream_resume_data = test_stream_resume_data,
  .submit_settings = test_submit_settings,
  .submit_response = test_submit_response,
  .submit_request = test_submit_request,
  .submit_rst_stream = test_submit_rst_stream,
  .submit_goaway = test_submit_goaway,
  .strerror = test_strerror,
};

int32_t valk_test_http2_inject_request(valk_http2_session_t *session,
                                        const char *method,
                                        const char *path,
                                        const valk_http2_header_t *headers,
                                        size_t nheaders,
                                        const uint8_t *body,
                                        size_t body_len) {
  int32_t stream_id = session->next_stream_id;
  session->next_stream_id += 2;

  if (session->cbs.on_begin_headers) {
    session->cbs.on_begin_headers(session, stream_id, session->cbs.user_data);
  }

  if (session->cbs.on_header) {
    valk_http2_header_t method_hdr = {
      .name = (const uint8_t *)":method",
      .name_len = 7,
      .value = (const uint8_t *)method,
      .value_len = strlen(method),
    };
    session->cbs.on_header(session, stream_id, &method_hdr, session->cbs.user_data);

    valk_http2_header_t path_hdr = {
      .name = (const uint8_t *)":path",
      .name_len = 5,
      .value = (const uint8_t *)path,
      .value_len = strlen(path),
    };
    session->cbs.on_header(session, stream_id, &path_hdr, session->cbs.user_data);

    for (size_t i = 0; i < nheaders; i++) {
      session->cbs.on_header(session, stream_id, &headers[i], session->cbs.user_data);
    }
  }

  if (body && body_len > 0 && session->cbs.on_data) {
    session->cbs.on_data(session, stream_id, body, body_len, session->cbs.user_data);
  }

  return stream_id;
}

bool valk_test_http2_get_response(valk_http2_session_t *session,
                                   int32_t stream_id,
                                   int *status,
                                   valk_http2_header_t **headers,
                                   size_t *nheaders,
                                   uint8_t **body,
                                   size_t *body_len) {
  valk_test_http2_stream_t *s = __find_stream(session, stream_id);
  if (!s || !s->response_sent) return false;

  if (status) *status = s->status_code;
  if (headers) *headers = s->headers;
  if (nheaders) *nheaders = s->header_count;
  if (body) *body = s->body;
  if (body_len) *body_len = s->body_len;

  return true;
}
