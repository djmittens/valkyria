#pragma once
#include <signal.h>
#include <sys/types.h>

#define UNUSED(x) ({ (void)x; })

// NOLINTBEGIN(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
#define VALK_RAISE(__msg, ...)                                          \
  do {                                                                  \
    fprintf(stderr, "%s:%d:%s || " __msg "\n", __FILE_NAME__, __LINE__, \
            __FUNCTION__, ##__VA_ARGS__);                               \
    raise(SIGTRAP);                                                     \
  } while (0)
// NOLINTEND(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)

#define VALK_ASSERT(__cond, __msg, ...) \
  if (!(__cond)) {                      \
    VALK_RAISE(__msg, ##__VA_ARGS__);   \
  }

typedef enum {
  VALK_ERR_SUCCESS,
  VALK_ERR_SSL_INIT,
  VALK_ERR_SSL_RE_NEGOTIATE,
  VALK_ERR_SSL_READ,
  VALK_ERR_SSL_ENCRYPT,
} valk_err_e;
