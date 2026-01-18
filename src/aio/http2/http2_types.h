#pragma once

#include <stddef.h>
#include <sys/types.h>
#include "types.h"

typedef struct valk_http2_session valk_http2_session_t;

typedef struct valk_http2_header {
  const u8 *name;
  u64 name_len;
  const u8 *value;
  u64 value_len;
} valk_http2_header_t;

typedef struct valk_http2_data_provider valk_http2_data_provider_t;

typedef enum {
  VALK_HTTP2_DATA_FLAG_NONE = 0,
  VALK_HTTP2_DATA_FLAG_EOF = 1,
  VALK_HTTP2_DATA_FLAG_NO_END_STREAM = 2,
  VALK_HTTP2_DATA_FLAG_NO_COPY = 4,
} valk_http2_data_flags_e;

typedef enum {
  VALK_HTTP2_FRAME_DATA = 0,
  VALK_HTTP2_FRAME_HEADERS = 1,
  VALK_HTTP2_FRAME_PRIORITY = 2,
  VALK_HTTP2_FRAME_RST_STREAM = 3,
  VALK_HTTP2_FRAME_SETTINGS = 4,
  VALK_HTTP2_FRAME_PUSH_PROMISE = 5,
  VALK_HTTP2_FRAME_PING = 6,
  VALK_HTTP2_FRAME_GOAWAY = 7,
  VALK_HTTP2_FRAME_WINDOW_UPDATE = 8,
  VALK_HTTP2_FRAME_CONTINUATION = 9,
} valk_http2_frame_type_e;

typedef enum {
  VALK_HTTP2_HCAT_REQUEST = 0,
  VALK_HTTP2_HCAT_RESPONSE = 1,
  VALK_HTTP2_HCAT_PUSH_RESPONSE = 2,
  VALK_HTTP2_HCAT_HEADERS = 3,
} valk_http2_headers_cat_e;

typedef enum {
  VALK_HTTP2_FLAG_NONE = 0x00,
  VALK_HTTP2_FLAG_END_STREAM = 0x01,
  VALK_HTTP2_FLAG_END_HEADERS = 0x04,
  VALK_HTTP2_FLAG_ACK = 0x01,
  VALK_HTTP2_FLAG_PADDED = 0x08,
  VALK_HTTP2_FLAG_PRIORITY = 0x20,
} valk_http2_flag_e;

typedef enum {
  VALK_HTTP2_NO_ERROR = 0,
  VALK_HTTP2_PROTOCOL_ERROR = 1,
  VALK_HTTP2_INTERNAL_ERROR = 2,
  VALK_HTTP2_FLOW_CONTROL_ERROR = 3,
  VALK_HTTP2_SETTINGS_TIMEOUT = 4,
  VALK_HTTP2_STREAM_CLOSED = 5,
  VALK_HTTP2_FRAME_SIZE_ERROR = 6,
  VALK_HTTP2_REFUSED_STREAM = 7,
  VALK_HTTP2_CANCEL = 8,
  VALK_HTTP2_COMPRESSION_ERROR = 9,
  VALK_HTTP2_CONNECT_ERROR = 10,
  VALK_HTTP2_ENHANCE_YOUR_CALM = 11,
  VALK_HTTP2_INADEQUATE_SECURITY = 12,
  VALK_HTTP2_HTTP_1_1_REQUIRED = 13,
} valk_http2_error_code_e;

typedef enum {
  VALK_HTTP2_ERR_NOMEM = -901,
  VALK_HTTP2_ERR_CALLBACK_FAILURE = -902,
  VALK_HTTP2_ERR_BAD_CLIENT_MAGIC = -903,
  VALK_HTTP2_ERR_FLOODED = -904,
} valk_http2_lib_error_e;

typedef ssize_t (*valk_http2_data_read_cb)(valk_http2_session_t *session,
                                           i32 stream_id,
                                           u8 *buf, u64 len,
                                           u32 *flags, void *source);

struct valk_http2_data_provider {
  void *source;
  valk_http2_data_read_cb read_callback;
};
