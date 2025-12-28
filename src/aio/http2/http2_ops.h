#pragma once

#include "http2_types.h"

typedef struct valk_http2_callbacks {
  void *user_data;

  int (*on_begin_headers)(valk_http2_session_t *session, i32 stream_id,
                          void *user_data);
  int (*on_header)(valk_http2_session_t *session, i32 stream_id,
                   const valk_http2_header_t *header, void *user_data);
  int (*on_data)(valk_http2_session_t *session, i32 stream_id,
                 const u8 *data, u64 len, void *user_data);
  int (*on_stream_close)(valk_http2_session_t *session, i32 stream_id,
                         u32 error_code, void *user_data);
  int (*on_frame_send)(valk_http2_session_t *session, i32 stream_id,
                       u8 frame_type, void *user_data);
  int (*on_frame_recv)(valk_http2_session_t *session, i32 stream_id,
                       u8 frame_type, u8 flags, void *user_data);
} valk_http2_callbacks_t;

typedef struct valk_http2_ops {
  valk_http2_session_t *(*server_session_new)(const valk_http2_callbacks_t *cbs,
                                               void *user_data);
  valk_http2_session_t *(*client_session_new)(const valk_http2_callbacks_t *cbs,
                                               void *user_data);
  void (*session_del)(valk_http2_session_t *session);

  ssize_t (*session_recv)(valk_http2_session_t *session, const u8 *data, u64 len);
  ssize_t (*session_send)(valk_http2_session_t *session, const u8 **data);
  bool (*session_want_write)(valk_http2_session_t *session);
  bool (*session_want_read)(valk_http2_session_t *session);

  void *(*stream_get_user_data)(valk_http2_session_t *session, i32 stream_id);
  int (*stream_set_user_data)(valk_http2_session_t *session, i32 stream_id, void *data);
  int (*stream_resume_data)(valk_http2_session_t *session, i32 stream_id);

  int (*submit_settings)(valk_http2_session_t *session, const void *settings, u64 count);
  int (*submit_response)(valk_http2_session_t *session, i32 stream_id,
                         const valk_http2_header_t *headers, u64 nheaders,
                         const valk_http2_data_provider_t *data_prd);
  i32 (*submit_request)(valk_http2_session_t *session,
                            const valk_http2_header_t *headers, u64 nheaders,
                            const valk_http2_data_provider_t *data_prd);
  int (*submit_rst_stream)(valk_http2_session_t *session, i32 stream_id, u32 error);
  int (*submit_goaway)(valk_http2_session_t *session, u32 error, const char *msg);

  const char *(*strerror)(int error_code);
} valk_http2_ops_t;

extern const valk_http2_ops_t valk_http2_ops_nghttp2;
extern const valk_http2_ops_t valk_http2_ops_test;

typedef struct valk_test_http2_stream {
  i32 id;
  void *user_data;
  bool closed;

  valk_http2_header_t *headers;
  u64 header_count;
  u64 header_cap;

  u8 *body;
  u64 body_len;
  u64 body_cap;

  int status_code;
  bool response_sent;

  struct valk_test_http2_stream *next;
} valk_test_http2_stream_t;

i32 valk_test_http2_inject_request(valk_http2_session_t *session,
                                        const char *method,
                                        const char *path,
                                        const valk_http2_header_t *headers,
                                        u64 nheaders,
                                        const u8 *body,
                                        u64 body_len);

bool valk_test_http2_get_response(valk_http2_session_t *session,
                                   i32 stream_id,
                                   int *status,
                                   valk_http2_header_t **headers,
                                   u64 *nheaders,
                                   u8 **body,
                                   u64 *body_len);
