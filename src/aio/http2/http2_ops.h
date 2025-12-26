#pragma once

#include "http2_types.h"

typedef struct valk_http2_callbacks {
  void *user_data;

  int (*on_begin_headers)(valk_http2_session_t *session, int32_t stream_id,
                          void *user_data);
  int (*on_header)(valk_http2_session_t *session, int32_t stream_id,
                   const valk_http2_header_t *header, void *user_data);
  int (*on_data)(valk_http2_session_t *session, int32_t stream_id,
                 const uint8_t *data, size_t len, void *user_data);
  int (*on_stream_close)(valk_http2_session_t *session, int32_t stream_id,
                         uint32_t error_code, void *user_data);
  int (*on_frame_send)(valk_http2_session_t *session, int32_t stream_id,
                       uint8_t frame_type, void *user_data);
  int (*on_frame_recv)(valk_http2_session_t *session, int32_t stream_id,
                       uint8_t frame_type, uint8_t flags, void *user_data);
} valk_http2_callbacks_t;

typedef struct valk_http2_ops {
  valk_http2_session_t *(*server_session_new)(const valk_http2_callbacks_t *cbs,
                                               void *user_data);
  valk_http2_session_t *(*client_session_new)(const valk_http2_callbacks_t *cbs,
                                               void *user_data);
  void (*session_del)(valk_http2_session_t *session);

  ssize_t (*session_recv)(valk_http2_session_t *session, const uint8_t *data, size_t len);
  ssize_t (*session_send)(valk_http2_session_t *session, const uint8_t **data);
  bool (*session_want_write)(valk_http2_session_t *session);
  bool (*session_want_read)(valk_http2_session_t *session);

  void *(*stream_get_user_data)(valk_http2_session_t *session, int32_t stream_id);
  int (*stream_set_user_data)(valk_http2_session_t *session, int32_t stream_id, void *data);
  int (*stream_resume_data)(valk_http2_session_t *session, int32_t stream_id);

  int (*submit_settings)(valk_http2_session_t *session, const void *settings, size_t count);
  int (*submit_response)(valk_http2_session_t *session, int32_t stream_id,
                         const valk_http2_header_t *headers, size_t nheaders,
                         const valk_http2_data_provider_t *data_prd);
  int32_t (*submit_request)(valk_http2_session_t *session,
                            const valk_http2_header_t *headers, size_t nheaders,
                            const valk_http2_data_provider_t *data_prd);
  int (*submit_rst_stream)(valk_http2_session_t *session, int32_t stream_id, uint32_t error);
  int (*submit_goaway)(valk_http2_session_t *session, uint32_t error, const char *msg);

  const char *(*strerror)(int error_code);
} valk_http2_ops_t;

extern const valk_http2_ops_t valk_http2_ops_nghttp2;
extern const valk_http2_ops_t valk_http2_ops_test;

typedef struct valk_test_http2_stream {
  int32_t id;
  void *user_data;
  bool closed;

  valk_http2_header_t *headers;
  size_t header_count;
  size_t header_cap;

  uint8_t *body;
  size_t body_len;
  size_t body_cap;

  int status_code;
  bool response_sent;

  struct valk_test_http2_stream *next;
} valk_test_http2_stream_t;

int32_t valk_test_http2_inject_request(valk_http2_session_t *session,
                                        const char *method,
                                        const char *path,
                                        const valk_http2_header_t *headers,
                                        size_t nheaders,
                                        const uint8_t *body,
                                        size_t body_len);

bool valk_test_http2_get_response(valk_http2_session_t *session,
                                   int32_t stream_id,
                                   int *status,
                                   valk_http2_header_t **headers,
                                   size_t *nheaders,
                                   uint8_t **body,
                                   size_t *body_len);
