#ifndef VALK_AIO_ALLOC_H
#define VALK_AIO_ALLOC_H

#include <stddef.h>
#include <nghttp2/nghttp2.h>
#include "types.h"

// Memory tracking for AIO subsystem (SSL + nghttp2 + libuv)
// All counters are atomic for thread-safe access from diagnostics

// Initialize tracking allocators - must be called before any SSL/nghttp2/libuv usage
void valk_aio_alloc_init(void);

// Get current memory usage stats
u64 valk_aio_ssl_bytes_used(void);
u64 valk_aio_nghttp2_bytes_used(void);
u64 valk_aio_libuv_bytes_used(void);

// Combined AIO library memory (SSL + nghttp2 + libuv)
static inline u64 valk_aio_lib_bytes_used(void) {
  return valk_aio_ssl_bytes_used() + valk_aio_nghttp2_bytes_used() + valk_aio_libuv_bytes_used();
}

// Get nghttp2 allocator for use with nghttp2_session_*_new functions
nghttp2_mem *valk_aio_nghttp2_mem(void);

#endif // VALK_AIO_ALLOC_H
