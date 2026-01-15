#pragma once
#include "types.h"

#include "aio_internal.h"

int valk_http2_on_header_callback(nghttp2_session *session,
                                  const nghttp2_frame *frame,
                                  const u8 *name, size_t namelen,
                                  const u8 *value, size_t valuelen,
                                  u8 flags, void *user_data);

int valk_http2_on_begin_headers_callback(nghttp2_session *session,
                                         const nghttp2_frame *frame,
                                         void *user_data);

int valk_http2_client_on_header_cb(nghttp2_session *session,
                                   const nghttp2_frame *frame,
                                   const u8 *name, size_t namelen,
                                   const u8 *value, size_t valuelen,
                                   u8 flags, void *user_data);

nghttp2_ssize valk_http2_byte_body_cb(nghttp2_session *session,
                                      i32 stream_id, u8 *buf,
                                      size_t length, u32 *data_flags,
                                      nghttp2_data_source *source,
                                      void *user_data);

int valk_http2_send_overload_response(nghttp2_session *session,
                                      i32 stream_id,
                                      valk_aio_handle_t *conn);

valk_lval_t* valk_http2_qexpr_get(valk_lval_t* qexpr, const char* key);

int valk_http2_send_response(nghttp2_session *session, int stream_id,
                             valk_lval_t* response_qexpr, 
                             valk_mem_arena_t* arena);

int valk_http2_server_on_frame_send_callback(nghttp2_session *session,
                                             const nghttp2_frame *frame,
                                             void *user_data);

int valk_http2_server_on_stream_close_callback(nghttp2_session *session,
                                               i32 stream_id,
                                               u32 error_code,
                                               void *user_data);

int valk_http2_on_frame_recv_callback(nghttp2_session *session,
                                      const nghttp2_frame *frame,
                                      void *user_data);

int valk_http2_client_on_frame_recv_callback(nghttp2_session *session,
                                             const nghttp2_frame *frame,
                                             void *user_data);

int valk_http2_client_on_stream_close_callback(nghttp2_session *session,
                                               i32 stream_id,
                                               u32 error_code,
                                               void *user_data);

int valk_http2_on_data_chunk_recv_callback(nghttp2_session *session,
                                           u8 flags, i32 stream_id,
                                           const u8 *data, size_t len,
                                           void *user_data);

void valk_http2_release_stream_arena(valk_aio_handle_t *conn, i32 stream_id);
