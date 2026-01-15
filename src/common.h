#pragma once
#include <dlfcn.h>
#include <execinfo.h>
#include <signal.h>

#include "debug.h"
#include "types.h"

#define UNUSED(x) ({ (void)x; })

#define VALK_RAISE(__msg, ...)                                          \
  do {                                                                  \
    fprintf(stderr, "%s:%d:%s || " __msg "\n", __FILE_NAME__, __LINE__, \
            __FUNCTION__, ##__VA_ARGS__);                               \
    void *stack[50];                                                    \
    int _size = backtrace(stack, 50);                                   \
    valk_trace_print(stack, _size);                                     \
    raise(SIGTRAP);                                                     \
    __builtin_unreachable();                                            \
  } while (0)

#define VALK_ASSERT(__cond, __msg, ...) \
  if (!(__cond)) {                      \
    VALK_RAISE(__msg, ##__VA_ARGS__);   \
  }

#define VALK_OOM_ASSERT(__ptr) \
  VALK_ASSERT((__ptr) != nullptr, "Out of memory")

// Buffer write macros for JSON/text encoding.
// These wrap snprintf with buffer overflow checks.
//
// Usage:
//   char *p = buf, *end = buf + size;
//   VALK_BUF_PRINTF(p, end, buf_size, "{\"key\":%d}", value);
//   return p - buf;
//
// On buffer overflow, returns the specified overflow_ret value.
// NOTE: Wrap calls with LCOV_EXCL_BR_START/STOP to exclude overflow guards.

#define VALK_BUF_PRINTF(__p, __end, __overflow_ret, ...)                      \
  do {                                                                        \
    int __n = snprintf((__p), (__end) - (__p), __VA_ARGS__);                  \
    if (__n < 0 || (__p) + __n >= (__end)) return (__overflow_ret);           \
    (__p) += __n;                                                             \
  } while (0)

#define VALK_BUF_CHECK(__p, __end, __n, __overflow_ret)                       \
  do {                                                                        \
    if ((__n) < 0 || (__p) + (__n) >= (__end)) return (__overflow_ret);       \
    (__p) += (__n);                                                           \
  } while (0)

typedef enum {
  VALK_ERR_SUCCESS,
  VALK_ERR_SSL_INIT,
  VALK_ERR_SSL_RE_NEGOTIATE,
  VALK_ERR_SSL_READ,
  VALK_ERR_SSL_ENCRYPT,
  VALK_ERR_SSL_INVALID,      // SSL context is nullptr or freed
  VALK_ERR_SSL_BUFFER_FULL,  // Output buffer is full
  VALK_ERR_SSL_SYSCALL,      // System call error during SSL operation
  VALK_ERR_SSL_PROTOCOL,     // SSL protocol error
  VALK_ERR_SSL_PEER_CLOSED,  // Peer closed connection (not an error under load)
} valk_err_e;
