#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sys/types.h>

typedef struct nghttp2_session nghttp2_session;
typedef struct nghttp2_session_callbacks nghttp2_session_callbacks;
typedef struct nghttp2_option nghttp2_option;
typedef struct nghttp2_mem nghttp2_mem;

#define NGHTTP2_ERR_WOULDBLOCK (-504)
#define NGHTTP2_ERR_CALLBACK_FAILURE (-902)
#define NGHTTP2_ERR_DEFERRED (-508)

#define NGHTTP2_DATA 0
#define NGHTTP2_HEADERS 1
#define NGHTTP2_PRIORITY 2
#define NGHTTP2_RST_STREAM 3
#define NGHTTP2_SETTINGS 4
#define NGHTTP2_PUSH_PROMISE 5
#define NGHTTP2_PING 6
#define NGHTTP2_GOAWAY 7
#define NGHTTP2_WINDOW_UPDATE 8
#define NGHTTP2_CONTINUATION 9

#define NGHTTP2_FLAG_NONE 0
#define NGHTTP2_FLAG_END_STREAM 0x01
#define NGHTTP2_FLAG_END_HEADERS 0x04
#define NGHTTP2_FLAG_ACK 0x01
#define NGHTTP2_FLAG_PADDED 0x08

#define NGHTTP2_NV_FLAG_NONE 0
#define NGHTTP2_NV_FLAG_NO_INDEX 0x01
#define NGHTTP2_NV_FLAG_NO_COPY_NAME 0x02
#define NGHTTP2_NV_FLAG_NO_COPY_VALUE 0x04

#define NGHTTP2_DATA_FLAG_NONE 0
#define NGHTTP2_DATA_FLAG_EOF 0x01
#define NGHTTP2_DATA_FLAG_NO_END_STREAM 0x02
#define NGHTTP2_DATA_FLAG_NO_COPY 0x04

#define NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS 0x03

typedef struct {
  uint8_t *name;
  uint8_t *value;
  size_t namelen;
  size_t valuelen;
  uint8_t flags;
} nghttp2_nv;

typedef struct {
  size_t length;
  int32_t stream_id;
  uint8_t type;
  uint8_t flags;
  uint8_t reserved;
} nghttp2_frame_hd;

typedef struct {
  nghttp2_frame_hd hd;
} nghttp2_frame;

typedef struct {
  union {
    int fd;
    void *ptr;
  } source;
} nghttp2_data_source;

typedef ssize_t (*nghttp2_data_source_read_callback)(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data);

typedef ssize_t (*nghttp2_data_source_read_callback2)(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data);

typedef struct {
  nghttp2_data_source source;
  nghttp2_data_source_read_callback read_callback;
} nghttp2_data_provider;

typedef struct {
  nghttp2_data_source source;
  nghttp2_data_source_read_callback2 read_callback;
} nghttp2_data_provider2;

typedef int (*nghttp2_on_begin_headers_callback)(
    nghttp2_session *session, const nghttp2_frame *frame, void *user_data);

typedef int (*nghttp2_on_header_callback)(
    nghttp2_session *session, const nghttp2_frame *frame,
    const uint8_t *name, size_t namelen,
    const uint8_t *value, size_t valuelen,
    uint8_t flags, void *user_data);

typedef int (*nghttp2_on_data_chunk_recv_callback)(
    nghttp2_session *session, uint8_t flags, int32_t stream_id,
    const uint8_t *data, size_t len, void *user_data);

typedef int (*nghttp2_on_stream_close_callback)(
    nghttp2_session *session, int32_t stream_id, uint32_t error_code,
    void *user_data);

typedef int (*nghttp2_on_frame_send_callback)(
    nghttp2_session *session, const nghttp2_frame *frame, void *user_data);

typedef int (*nghttp2_on_frame_recv_callback)(
    nghttp2_session *session, const nghttp2_frame *frame, void *user_data);

typedef ssize_t (*nghttp2_send_callback)(
    nghttp2_session *session, const uint8_t *data, size_t length,
    int flags, void *user_data);

typedef ssize_t (*nghttp2_recv_callback)(
    nghttp2_session *session, uint8_t *buf, size_t length,
    int flags, void *user_data);

int nghttp2_session_callbacks_new(nghttp2_session_callbacks **callbacks_ptr);
void nghttp2_session_callbacks_del(nghttp2_session_callbacks *callbacks);

void nghttp2_session_callbacks_set_on_begin_headers_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_begin_headers_callback cb);
void nghttp2_session_callbacks_set_on_header_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_header_callback cb);
void nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_data_chunk_recv_callback cb);
void nghttp2_session_callbacks_set_on_stream_close_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_stream_close_callback cb);
void nghttp2_session_callbacks_set_on_frame_send_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_frame_send_callback cb);
void nghttp2_session_callbacks_set_on_frame_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_frame_recv_callback cb);
void nghttp2_session_callbacks_set_send_callback(
    nghttp2_session_callbacks *cbs, nghttp2_send_callback cb);
void nghttp2_session_callbacks_set_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_recv_callback cb);

int nghttp2_option_new(nghttp2_option **option_ptr);
void nghttp2_option_del(nghttp2_option *option);
void nghttp2_option_set_no_auto_window_update(nghttp2_option *option, int val);
void nghttp2_option_set_peer_max_concurrent_streams(nghttp2_option *option, uint32_t val);

int nghttp2_session_server_new(nghttp2_session **session_ptr,
                                const nghttp2_session_callbacks *callbacks,
                                void *user_data);
int nghttp2_session_server_new2(nghttp2_session **session_ptr,
                                 const nghttp2_session_callbacks *callbacks,
                                 void *user_data,
                                 const nghttp2_option *option);
int nghttp2_session_server_new3(nghttp2_session **session_ptr,
                                 const nghttp2_session_callbacks *callbacks,
                                 void *user_data,
                                 const nghttp2_option *option,
                                 nghttp2_mem *mem);
int nghttp2_session_client_new(nghttp2_session **session_ptr,
                                const nghttp2_session_callbacks *callbacks,
                                void *user_data);
int nghttp2_session_client_new2(nghttp2_session **session_ptr,
                                 const nghttp2_session_callbacks *callbacks,
                                 void *user_data,
                                 const nghttp2_option *option);
void nghttp2_session_del(nghttp2_session *session);

ssize_t nghttp2_session_mem_recv(nghttp2_session *session,
                                  const uint8_t *in, size_t inlen);
ssize_t nghttp2_session_mem_send(nghttp2_session *session,
                                  const uint8_t **data_ptr);
int nghttp2_session_send(nghttp2_session *session);
int nghttp2_session_recv(nghttp2_session *session);
int nghttp2_session_want_write(nghttp2_session *session);
int nghttp2_session_want_read(nghttp2_session *session);

void *nghttp2_session_get_stream_user_data(nghttp2_session *session,
                                            int32_t stream_id);
int nghttp2_session_set_stream_user_data(nghttp2_session *session,
                                          int32_t stream_id, void *user_data);
int nghttp2_session_resume_data(nghttp2_session *session, int32_t stream_id);
int nghttp2_session_consume(nghttp2_session *session, int32_t stream_id, size_t size);
int nghttp2_session_consume_connection(nghttp2_session *session, size_t size);

typedef struct {
  int32_t settings_id;
  uint32_t value;
} nghttp2_settings_entry;

int nghttp2_submit_settings(nghttp2_session *session, uint8_t flags,
                            const nghttp2_settings_entry *iv, size_t niv);
int nghttp2_submit_response(nghttp2_session *session, int32_t stream_id,
                            const nghttp2_nv *nva, size_t nvlen,
                            const nghttp2_data_provider *data_prd);
int nghttp2_submit_response2(nghttp2_session *session, int32_t stream_id,
                             const nghttp2_nv *nva, size_t nvlen,
                             const nghttp2_data_provider2 *data_prd);
int32_t nghttp2_submit_request(nghttp2_session *session,
                                const void *pri_spec,
                                const nghttp2_nv *nva, size_t nvlen,
                                const nghttp2_data_provider *data_prd,
                                void *stream_user_data);
int32_t nghttp2_submit_request2(nghttp2_session *session,
                                 const void *pri_spec,
                                 const nghttp2_nv *nva, size_t nvlen,
                                 const nghttp2_data_provider2 *data_prd,
                                 void *stream_user_data);
int nghttp2_submit_rst_stream(nghttp2_session *session, uint8_t flags,
                               int32_t stream_id, uint32_t error_code);
int nghttp2_submit_goaway(nghttp2_session *session, uint8_t flags,
                           int32_t last_stream_id, uint32_t error_code,
                           const uint8_t *opaque_data, size_t opaque_data_len);

const char *nghttp2_strerror(int lib_error_code);
