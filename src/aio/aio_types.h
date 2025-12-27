#ifndef VALK_AIO_TYPES_H
#define VALK_AIO_TYPES_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

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

typedef struct valk_sse_stream valk_sse_stream_t;
typedef struct valk_sse_event valk_sse_event_t;
typedef struct valk_sse_manager valk_sse_manager_t;
typedef struct valk_sse_stream_entry valk_sse_stream_entry_t;
typedef struct valk_sse_stream_registry valk_sse_stream_registry_t;
typedef struct valk_sse_diag_state valk_sse_diag_state_t;
typedef struct valk_sse_diag_conn valk_sse_diag_conn_t;

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
typedef bool (*valk_async_is_closed_fn)(void *ctx);

// ============================================================================
// HTTP/2 Header Type (shared between request/response)
// ============================================================================

struct valk_http2_header_t {
  uint8_t *name;
  uint8_t *value;
  size_t nameLen;
  size_t valueLen;
};

#endif // VALK_AIO_TYPES_H
