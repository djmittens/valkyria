#pragma once
#include "types.h"

#include <stddef.h>

typedef enum {
  VALK_BODY_CONTINUE,
  VALK_BODY_COMPLETE,
} valk_body_status_e;

typedef struct valk_body_chunk {
  const u8 *data;
  u64 len;
  valk_body_status_e status;
} valk_body_chunk_t;

typedef struct valk_header_view {
  const u8 *name;
  u64 name_len;
  const u8 *value;
  u64 value_len;
} valk_header_view_t;

typedef struct valk_request_meta {
  const char *method;
  u64 method_len;
  const char *scheme;
  u64 scheme_len;
  const char *authority;
  u64 authority_len;
  const char *path;
  u64 path_len;
} valk_request_meta_t;
