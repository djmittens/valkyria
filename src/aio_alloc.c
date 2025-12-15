#include "aio_alloc.h"
#include "common.h"
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <openssl/crypto.h>
#include <uv.h>

// Atomic counters for memory tracking
static _Atomic size_t __ssl_bytes_used = 0;
static _Atomic size_t __nghttp2_bytes_used = 0;
static _Atomic size_t __libuv_bytes_used = 0;

// Allocation header to track size (prepended to each allocation)
typedef struct {
  size_t size;
} alloc_header_t;

#define HEADER_SIZE sizeof(alloc_header_t)

// =============================================================================
// OpenSSL tracking allocator
// =============================================================================

static void *__ssl_malloc(size_t num, const char *file, int line) {
  UNUSED(file);
  UNUSED(line);

  void *ptr = malloc(HEADER_SIZE + num);
  if (!ptr) return NULL;

  alloc_header_t *hdr = (alloc_header_t *)ptr;
  hdr->size = num;

  atomic_fetch_add(&__ssl_bytes_used, num);

  return (char *)ptr + HEADER_SIZE;
}

static void *__ssl_realloc(void *addr, size_t num, const char *file, int line) {
  UNUSED(file);
  UNUSED(line);

  if (!addr) {
    return __ssl_malloc(num, file, line);
  }

  alloc_header_t *old_hdr = (alloc_header_t *)((char *)addr - HEADER_SIZE);
  size_t old_size = old_hdr->size;

  void *new_ptr = realloc(old_hdr, HEADER_SIZE + num);
  if (!new_ptr) return NULL;

  alloc_header_t *new_hdr = (alloc_header_t *)new_ptr;
  new_hdr->size = num;

  // Update counter: subtract old, add new
  atomic_fetch_sub(&__ssl_bytes_used, old_size);
  atomic_fetch_add(&__ssl_bytes_used, num);

  return (char *)new_ptr + HEADER_SIZE;
}

static void __ssl_free(void *addr, const char *file, int line) {
  UNUSED(file);
  UNUSED(line);

  if (!addr) return;

  alloc_header_t *hdr = (alloc_header_t *)((char *)addr - HEADER_SIZE);
  size_t size = hdr->size;

  atomic_fetch_sub(&__ssl_bytes_used, size);

  free(hdr);
}

// =============================================================================
// nghttp2 tracking allocator
// =============================================================================

static void *__nghttp2_malloc(size_t size, void *mem_user_data) {
  UNUSED(mem_user_data);

  void *ptr = malloc(HEADER_SIZE + size);
  if (!ptr) return NULL;

  alloc_header_t *hdr = (alloc_header_t *)ptr;
  hdr->size = size;

  atomic_fetch_add(&__nghttp2_bytes_used, size);

  return (char *)ptr + HEADER_SIZE;
}

static void __nghttp2_free(void *ptr, void *mem_user_data) {
  UNUSED(mem_user_data);

  if (!ptr) return;

  alloc_header_t *hdr = (alloc_header_t *)((char *)ptr - HEADER_SIZE);
  size_t size = hdr->size;

  atomic_fetch_sub(&__nghttp2_bytes_used, size);

  free(hdr);
}

static void *__nghttp2_calloc(size_t nmemb, size_t size, void *mem_user_data) {
  size_t total = nmemb * size;
  void *ptr = __nghttp2_malloc(total, mem_user_data);
  if (ptr) {
    memset(ptr, 0, total);
  }
  return ptr;
}

static void *__nghttp2_realloc(void *ptr, size_t size, void *mem_user_data) {
  if (!ptr) {
    return __nghttp2_malloc(size, mem_user_data);
  }

  if (size == 0) {
    __nghttp2_free(ptr, mem_user_data);
    return NULL;
  }

  alloc_header_t *old_hdr = (alloc_header_t *)((char *)ptr - HEADER_SIZE);
  size_t old_size = old_hdr->size;

  void *new_ptr = realloc(old_hdr, HEADER_SIZE + size);
  if (!new_ptr) return NULL;

  alloc_header_t *new_hdr = (alloc_header_t *)new_ptr;
  new_hdr->size = size;

  atomic_fetch_sub(&__nghttp2_bytes_used, old_size);
  atomic_fetch_add(&__nghttp2_bytes_used, size);

  return (char *)new_ptr + HEADER_SIZE;
}

// Static nghttp2_mem structure
static nghttp2_mem __nghttp2_mem = {
  .mem_user_data = NULL,
  .malloc = __nghttp2_malloc,
  .free = __nghttp2_free,
  .calloc = __nghttp2_calloc,
  .realloc = __nghttp2_realloc,
};

// =============================================================================
// libuv tracking allocator
// =============================================================================

static void *__libuv_malloc(size_t size) {
  void *ptr = malloc(HEADER_SIZE + size);
  if (!ptr) return NULL;

  alloc_header_t *hdr = (alloc_header_t *)ptr;
  hdr->size = size;

  atomic_fetch_add(&__libuv_bytes_used, size);

  return (char *)ptr + HEADER_SIZE;
}

static void *__libuv_realloc(void *ptr, size_t size) {
  if (!ptr) {
    return __libuv_malloc(size);
  }

  if (size == 0) {
    // realloc(ptr, 0) is implementation-defined, treat as free
    alloc_header_t *hdr = (alloc_header_t *)((char *)ptr - HEADER_SIZE);
    atomic_fetch_sub(&__libuv_bytes_used, hdr->size);
    free(hdr);
    return NULL;
  }

  alloc_header_t *old_hdr = (alloc_header_t *)((char *)ptr - HEADER_SIZE);
  size_t old_size = old_hdr->size;

  void *new_ptr = realloc(old_hdr, HEADER_SIZE + size);
  if (!new_ptr) return NULL;

  alloc_header_t *new_hdr = (alloc_header_t *)new_ptr;
  new_hdr->size = size;

  atomic_fetch_sub(&__libuv_bytes_used, old_size);
  atomic_fetch_add(&__libuv_bytes_used, size);

  return (char *)new_ptr + HEADER_SIZE;
}

static void *__libuv_calloc(size_t count, size_t size) {
  size_t total = count * size;
  void *ptr = __libuv_malloc(total);
  if (ptr) {
    memset(ptr, 0, total);
  }
  return ptr;
}

static void __libuv_free(void *ptr) {
  if (!ptr) return;

  alloc_header_t *hdr = (alloc_header_t *)((char *)ptr - HEADER_SIZE);
  size_t size = hdr->size;

  atomic_fetch_sub(&__libuv_bytes_used, size);

  free(hdr);
}

// =============================================================================
// Public API
// =============================================================================

// Use constructor attribute to initialize BEFORE main() runs
// This ensures we install hooks before any library can initialize
// Priority 101 is early (lower = earlier, 0-100 reserved for system)
__attribute__((constructor(101)))
static void __valk_aio_alloc_early_init(void) {
  // Install libuv allocator hooks FIRST - libuv often initializes early
  // NOTE: This must be called BEFORE any libuv functions!
  int uv_result = uv_replace_allocator(__libuv_malloc, __libuv_realloc,
                                       __libuv_calloc, __libuv_free);
  if (uv_result != 0) {
    fprintf(stderr, "WARNING: libuv memory hooks not installed - "
                    "libuv memory won't be tracked (error: %d)\n", uv_result);
  }

  // Install OpenSSL allocator hooks
  // NOTE: This must be called BEFORE any OpenSSL functions!
  int ssl_result = CRYPTO_set_mem_functions(__ssl_malloc, __ssl_realloc, __ssl_free);

  // Verify installation succeeded (returns 1 on success, 0 if already set)
  if (ssl_result == 0) {
    // OpenSSL already initialized - our hooks weren't installed
    // This can happen if another library initialized OpenSSL first
    fprintf(stderr, "WARNING: OpenSSL memory hooks not installed - "
                    "SSL memory won't be tracked\n");
  }

  // Debug output
  fprintf(stderr, "[aio_alloc] Memory tracking: libuv=%s, ssl=%s\n",
          uv_result == 0 ? "ok" : "FAILED",
          ssl_result == 1 ? "ok" : "FAILED");
}

void valk_aio_alloc_init(void) {
  // Now a no-op - initialization happens in constructor
  // Kept for API compatibility
}

size_t valk_aio_ssl_bytes_used(void) {
  return atomic_load(&__ssl_bytes_used);
}

size_t valk_aio_nghttp2_bytes_used(void) {
  return atomic_load(&__nghttp2_bytes_used);
}

size_t valk_aio_libuv_bytes_used(void) {
  return atomic_load(&__libuv_bytes_used);
}

nghttp2_mem *valk_aio_nghttp2_mem(void) {
  return &__nghttp2_mem;
}
