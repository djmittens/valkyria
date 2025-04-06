#pragma once
#include <signal.h>

#define UNUSED(x) ({ (void)x; })

#define VALK_RAISE(__msg, ...)                                                 \
  do {                                                                         \
    size_t __len = snprintf(NULL, 0, "%s:%d:%s || %s", __FILE_NAME__,          \
                            __LINE__, __FUNCTION__, (__msg));                  \
    char __fmt[__len + 1];                                                     \
    snprintf(__fmt, __len + 1, "%s:%d:%s || %s", __FILE_NAME__, __LINE__,      \
             __FUNCTION__, (__msg));                                           \
    fprintf(stderr, __fmt, ##__VA_ARGS__);                                     \
    raise(SIGTRAP);                                                            \
  } while (0)

#define VALK_ASSERT(__cond, __msg, ...)                                        \
  if (!(__cond)) {                                                             \
    VALK_RAISE(__msg, ##__VA_ARGS__);                                          \
  }

typedef enum {
  VALK_ERR_SUCCESS,
  VALK_ERR_SSL_INIT,
  VALK_ERR_SSL_HANDSHAKE,
  VALK_ERR_SSL_READ,
  VALK_ERR_SSL_ENCRYPT,
} valk_err_e;
