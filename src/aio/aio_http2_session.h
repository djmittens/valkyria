#pragma once

#include "aio_internal.h"

int valk_http2_on_header_callback(nghttp2_session *session,
                                  const nghttp2_frame *frame,
                                  const uint8_t *name, size_t namelen,
                                  const uint8_t *value, size_t valuelen,
                                  uint8_t flags, void *user_data);

int valk_http2_on_begin_headers_callback(nghttp2_session *session,
                                         const nghttp2_frame *frame,
                                         void *user_data);

int valk_http2_client_on_header_cb(nghttp2_session *session,
                                   const nghttp2_frame *frame,
                                   const uint8_t *name, size_t namelen,
                                   const uint8_t *value, size_t valuelen,
                                   uint8_t flags, void *user_data);

nghttp2_ssize valk_http2_byte_body_cb(nghttp2_session *session,
                                      int32_t stream_id, uint8_t *buf,
                                      size_t length, uint32_t *data_flags,
                                      nghttp2_data_source *source,
                                      void *user_data);

int valk_http2_send_overload_response(nghttp2_session *session,
                                      int32_t stream_id,
                                      valk_aio_handle_t *conn);

valk_lval_t* valk_http2_qexpr_get(valk_lval_t* qexpr, const char* key);

int valk_http2_send_response(nghttp2_session *session, int stream_id,
                             valk_lval_t* response_qexpr, 
                             valk_mem_arena_t* arena);

valk_lval_t* valk_http2_build_request_qexpr(valk_http2_server_request_t *req);

int valk_http2_server_on_frame_send_callback(nghttp2_session *session,
                                             const nghttp2_frame *frame,
                                             void *user_data);

int valk_http2_server_on_stream_close_callback(nghttp2_session *session,
                                               int32_t stream_id,
                                               uint32_t error_code,
                                               void *user_data);

int valk_http2_on_frame_recv_callback(nghttp2_session *session,
                                      const nghttp2_frame *frame,
                                      void *user_data);

int valk_http2_client_on_frame_recv_callback(nghttp2_session *session,
                                             const nghttp2_frame *frame,
                                             void *user_data);

int valk_http2_client_on_stream_close_callback(nghttp2_session *session,
                                               int32_t stream_id,
                                               uint32_t error_code,
                                               void *user_data);

int valk_http2_on_data_chunk_recv_callback(nghttp2_session *session,
                                           uint8_t flags, int32_t stream_id,
                                           const uint8_t *data, size_t len,
                                           void *user_data);
