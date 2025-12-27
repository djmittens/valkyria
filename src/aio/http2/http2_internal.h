#pragma once

#include <nghttp2/nghttp2.h>

#define MAKE_NV(NAME, VALUE, VALUELEN)                         \
  {                                                            \
      (uint8_t *)NAME, (uint8_t *)VALUE,     sizeof(NAME) - 1, \
      VALUELEN,        NGHTTP2_NV_FLAG_NONE,                   \
  }

#define MAKE_NV2(NAME, VALUE)                                    \
  {                                                              \
      (uint8_t *)NAME,   (uint8_t *)VALUE,     sizeof(NAME) - 1, \
      sizeof(VALUE) - 1, NGHTTP2_NV_FLAG_NONE,                   \
  }
