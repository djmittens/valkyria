#pragma once
#include "types.h"

#include <nghttp2/nghttp2.h>

#define MAKE_NV(NAME, VALUE, VALUELEN)                         \
  {                                                            \
      (u8 *)NAME, (u8 *)VALUE,     sizeof(NAME) - 1, \
      VALUELEN,        NGHTTP2_NV_FLAG_NONE,                   \
  }

#define MAKE_NV2(NAME, VALUE)                                    \
  {                                                              \
      (u8 *)NAME,   (u8 *)VALUE,     sizeof(NAME) - 1, \
      sizeof(VALUE) - 1, NGHTTP2_NV_FLAG_NONE,                   \
  }
