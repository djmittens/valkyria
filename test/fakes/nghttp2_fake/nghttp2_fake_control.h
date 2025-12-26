#pragma once

#include "nghttp2_fake.h"
#include <stdbool.h>

int32_t nghttp2_fake_inject_request(nghttp2_session *session,
                                     const char *method,
                                     const char *path,
                                     const nghttp2_nv *extra_headers,
                                     size_t nextra,
                                     const uint8_t *body,
                                     size_t body_len);

typedef struct {
  int status_code;
  nghttp2_nv *headers;
  size_t nheaders;
  uint8_t *body;
  size_t body_len;
  bool closed;
} nghttp2_fake_response_t;

bool nghttp2_fake_get_response(nghttp2_session *session, int32_t stream_id,
                                nghttp2_fake_response_t *response);

int nghttp2_fake_process_pending(nghttp2_session *session);

size_t nghttp2_fake_stream_count(nghttp2_session *session);
bool nghttp2_fake_stream_exists(nghttp2_session *session, int32_t stream_id);

void nghttp2_fake_reset(nghttp2_session *session);
