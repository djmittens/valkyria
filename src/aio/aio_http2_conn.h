#pragma once
#include "types.h"

#include "aio_internal.h"

void valk_http2_conn_on_disconnect(valk_aio_handle_t *handle);

bool valk_http2_conn_write_buf_acquire(valk_aio_handle_t *conn);
u8 *valk_http2_conn_write_buf_data(valk_aio_handle_t *conn);
u64 valk_http2_conn_write_buf_available(valk_aio_handle_t *conn);
bool valk_http2_conn_write_buf_writable(valk_aio_handle_t *conn);
u64 valk_http2_conn_write_buf_append(valk_aio_handle_t *conn, const u8 *data, u64 len);
int valk_http2_conn_write_buf_flush(valk_aio_handle_t *conn);

void valk_http2_conn_alloc_callback(uv_handle_t *handle, u64 suggested_size, uv_buf_t *buf);
void valk_http2_conn_tcp_read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf);
void valk_http2_conn_tcp_read_impl(valk_aio_handle_t *conn, ssize_t nread, const void *buf_base);
void valk_http2_conn_handle_closed_cb(uv_handle_t *handle);

u64 valk_http2_flush_frames(valk_buffer_t *buf, valk_aio_handle_t *conn);

void valk_http2_backpressure_try_resume_one(valk_aio_system_t *sys);

int valk_http2_send_server_connection_header(nghttp2_session *session, valk_aio_system_t *sys);
int valk_http2_send_client_connection_header(nghttp2_session *session, valk_aio_system_t *sys);
