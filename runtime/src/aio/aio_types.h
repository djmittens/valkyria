#ifndef VALK_AIO_TYPES_H
#define VALK_AIO_TYPES_H

#include <stddef.h>
#include <stdbool.h>
#include <stdatomic.h>
#include "types.h"

// ============================================================================
// Forward Declarations (opaque types defined elsewhere)
// ============================================================================

typedef struct valk_aio_system valk_aio_system_t;
typedef struct valk_aio_system_config valk_aio_system_config_t;
typedef struct valk_aio_handle_t valk_aio_handle_t;
typedef struct valk_async_handle_t valk_async_handle_t;
typedef struct valk_aio_http_server valk_aio_http_server;
typedef struct valk_aio_http2_client valk_aio_http2_client;

typedef struct valk_http2_server_request valk_http2_server_request_t;
typedef struct valk_http2_request_t valk_http2_request_t;
typedef struct valk_http2_response_t valk_http2_response_t;



struct valk_lval_t;
struct valk_lenv_t;
struct valk_mem_arena;
struct valk_mem_allocator_t;
struct valk_slab_t;
struct valk_slab_item_t;

// ============================================================================
// Core Enums
// ============================================================================

typedef enum valk_async_status_t {
  VALK_ASYNC_PENDING,
  VALK_ASYNC_RUNNING,
  VALK_ASYNC_COMPLETED,
  VALK_ASYNC_FAILED,
  VALK_ASYNC_CANCELLED,
} valk_async_status_t;

// ============================================================================
// Callback Types
// ============================================================================

typedef void (*valk_async_done_fn)(struct valk_async_handle_t *handle, void *ctx);
typedef void (*valk_async_cleanup_fn)(void *ctx);
typedef void (*valk_async_on_child_fn)(struct valk_async_handle_t *child);

// ============================================================================
// HTTP/2 Header Type (shared between request/response)
// ============================================================================

struct valk_http2_header_t {
  u8 *name;
  u8 *value;
  u64 nameLen;
  u64 valueLen;
};

#endif // VALK_AIO_TYPES_H
