#pragma once

#include <stddef.h>
#include <stdint.h>

typedef enum {
  VALK_BODY_CONTINUE,
  VALK_BODY_COMPLETE,
} valk_body_status_e;

typedef struct valk_body_chunk {
  const uint8_t *data;
  size_t len;
  valk_body_status_e status;
} valk_body_chunk_t;

typedef struct valk_header_view {
  const uint8_t *name;
  size_t name_len;
  const uint8_t *value;
  size_t value_len;
} valk_header_view_t;

typedef struct valk_request_meta {
  const char *method;
  size_t method_len;
  const char *scheme;
  size_t scheme_len;
  const char *authority;
  size_t authority_len;
  const char *path;
  size_t path_len;
} valk_request_meta_t;
