#pragma once

#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif
#define _POSIX_C_SOURCE 200809L

#include <pthread.h>
#include <nghttp2/nghttp2.h>
#include <openssl/ssl.h>
#include <openssl/ssl3.h>
#include <uv.h>
#include <stdbool.h>

#include "aio.h"
#include "system/aio_chase_lev.h"
#include "http2/aio_conn_io.h"
#include "aio_metrics.h"
#include "http2/stream/aio_stream_body.h"
#include "http2/overload/aio_overload_backpressure.h"
#include "http2/overload/aio_overload_admission.h"
#include "system/aio_maintenance.h"
#include "aio_ops.h"
#include "io/io_tcp_uv_types.h"
#include "metrics_v2.h"
#include "event_loop_metrics.h"
#include "parser.h"
#include "memory.h"
#include "gc.h"
#include "collections.h"
#include "aio_alloc.h"
#include "aio_diagnostics_builtins.h"
#include "gc.h"
#include "system/aio_task.h"

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

enum {
  AIO_QUEUE_SIZE = 10,
  AIO_MAX_HANDLES = 2056,
  HTTP_MAX_SERVERS = 8,
  HTTP_MAX_CLIENTS = 8,
  HTTP_SLAB_ITEM_SIZE = (SSL3_RT_MAX_PACKET_SIZE * 2),
  HTTP_MAX_IO_REQUESTS = (1024),
  HTTP_MAX_CONNECTIONS = (100),
  HTTP_MAX_CONNECTION_HEAP = (1024000),
  HTTP_MAX_REQUEST_SIZE_BYTES = ((int)8e6),
  HTTP_MAX_RESPONSE_SIZE_BYTES = ((int)64e6),
  HTTP_STREAM_ARENA_SIZE = (67108864),
  HTTP_STREAM_ARENA_POOL_SIZE = (64),
};

#define BACKPRESSURE_LIST_MAX_LIMIT 100000
#define PENDING_STREAM_POOL_MAX_LIMIT 10000
#define HTTP2_MAX_SERIALIZED_FRAME (16384 + 9 + 256)
#define BUFFERS_PER_CONNECTION 4
#define BUFFERS_TO_RESUME 2
#define ARENA_SLOT_RELEASED UINT32_MAX
#define VALK_AIO_HANDLE_MAGIC 0xBA1CADA1

typedef struct {
  valk_counter_v2_t* requests_total;
  valk_counter_v2_t* requests_success;
  valk_counter_v2_t* requests_client_error;
  valk_counter_v2_t* requests_server_error;
  valk_gauge_v2_t* connections_active;
  valk_gauge_v2_t* sse_streams_active;
  valk_histogram_v2_t* request_duration;
  valk_histogram_v2_t* sse_stream_duration;
  valk_counter_v2_t* bytes_sent;
  valk_counter_v2_t* bytes_recv;
  valk_counter_v2_t* overload_responses;
} valk_server_metrics_t;

#define VALK_MAX_OWNERS (HTTP_MAX_SERVERS + HTTP_MAX_CLIENTS)

struct valk_owner_entry {
  char name[32];
  u8 type;
  void *ptr;
};

struct valk_owner_registry {
  valk_owner_entry_t entries[VALK_MAX_OWNERS];
  u16 count;
};

typedef enum handle_kind_t {
  VALK_HNDL_EMPTY,
  VALK_HNDL_TCP,
  VALK_HNDL_TASK,
  VALK_HNDL_TIMER,
  VALK_HNDL_HTTP_CONN,
} handle_kind_t;

#include "http2/aio_http2_conn_fsm.h"

typedef enum __aio_http_srv_e {
  VALK_SRV_INIT,
  VALK_SRV_LISTENING,
  VALK_SRV_CLOSING,
  VALK_SRV_CLOSED,
} __aio_http_srv_e;

#define VALK_UV_DATA_TIMER_MAGIC 0x71AE8721
#define VALK_INTERVAL_TIMER_MAGIC 0x71AE8722

typedef struct valk_async_handle_uv_data {
  u32 magic;
  union {
    alignas(16) uv_timer_t timer;
  } uv;
  valk_async_handle_t *handle;
} valk_async_handle_uv_data_t;

typedef struct valk_arena_ref {
  valk_slab_item_t *slab_item;
  u32 slot;
} valk_arena_ref_t;

#define VALK_ARENA_REF_EMPTY ((valk_arena_ref_t){.slab_item = nullptr, .slot = UINT32_MAX})

static inline bool valk_arena_ref_valid(valk_arena_ref_t ref) {
  return ref.slab_item != nullptr;
}

static inline valk_arena_ref_t valk_arena_ref_take(valk_arena_ref_t *src) {
  valk_arena_ref_t ref = *src;
  *src = VALK_ARENA_REF_EMPTY;
  return ref;
}

static inline void valk_arena_ref_give(valk_arena_ref_t *dst, valk_arena_ref_t ref) {
  *dst = ref;
}

static inline void valk_arena_ref_release(valk_arena_ref_t *ref, valk_slab_t *pool) {
  if (ref->slab_item && pool) {
    valk_slab_release(pool, ref->slab_item);
  }
  *ref = VALK_ARENA_REF_EMPTY;
}

typedef struct valk_http_async_ctx {
  void *session;
  i32 stream_id;
  struct valk_aio_handle_t *conn;
  valk_mem_arena_t *arena;
  valk_arena_ref_t arena_ref;
} valk_http_async_ctx_t;

typedef struct valk_standalone_async_ctx {
  valk_mem_arena_t *arena;
  valk_arena_ref_t arena_ref;
  valk_aio_system_t *sys;
} valk_standalone_async_ctx_t;

typedef struct __tcp_buffer_slab_item_t {
  uv_write_t req;
  uv_buf_t buf;
  valk_aio_handle_t *conn;
  char data[HTTP_SLAB_ITEM_SIZE];
} __tcp_buffer_slab_item_t;

typedef struct __http2_connect_req {
  valk_aio_system_t *sys;
  valk_aio_http2_client *client;
} __http2_connect_req;

typedef struct valk_http2_server_request {
  char *method;
  char *scheme;
  char *authority;
  char *path;
  struct {
    struct valk_http2_header_t *items;
    u64 count;
    u64 capacity;
  } headers;
  u8 *body;
  u64 bodyLen;
  u64 bodyCapacity;
  valk_aio_handle_t *conn;
  i32 stream_id;
  valk_mem_arena_t *stream_arena;
  valk_arena_ref_t arena_ref;
  valk_region_t region;
  u32 next_arena_slot;
  u64 start_time_us;
  u64 bytes_sent;
  u64 bytes_recv;
  int status_code;
  u64 response_sent_time_us;
  bool response_complete;
  struct valk_sse_stream_entry *sse_entry;
  struct valk_request_ctx *request_ctx;
} valk_http2_server_request_t;

typedef struct {
  valk_lval_t* request;
  valk_lval_t* handler_fn;
  valk_aio_handle_t* conn;
  i32 stream_id;
} valk_http_request_item_t;

typedef struct {
  valk_lval_t* response;
  valk_aio_handle_t* conn;
  i32 stream_id;
} valk_http_response_item_t;

typedef struct {
  valk_mutex_t request_mutex;
  valk_cond_t request_ready;
  valk_http_request_item_t* request_items;
  u64 request_idx;
  u64 request_count;
  u64 request_capacity;
  valk_mutex_t response_mutex;
  valk_cond_t response_ready;
  valk_http_response_item_t* response_items;
  u64 response_idx;
  u64 response_count;
  u64 response_capacity;
} valk_http_queue_t;

struct valk_aio_handle_t {
  u32 magic;
  handle_kind_t kind;
  valk_aio_handle_t *prev;
  valk_aio_handle_t *next;
  valk_aio_system_t *sys;
  void *arg;

  void (*onOpen)(valk_aio_handle_t *);
  void (*onClose)(valk_aio_handle_t *);

  union {
    valk_io_tcp_t tcp;
    uv_async_t task;
    uv_timer_t timer;
  } uv;

  struct {
    __aio_http_conn_e state;
    valk_conn_io_t io;
    nghttp2_session *session;
    valk_http2_handler_t *httpHandler;
    uv_connect_t connectReq;
    valk_aio_http_server *server;
    int active_streams;

    u64 last_activity_ms;

    bool backpressure;
    valk_aio_handle_t *backpressure_next;
    u64 backpressure_start_time;

    bool arena_backpressure;

    valk_handle_diag_t diag;

    valk_stream_body_t *stream_bodies;
    u32 active_arena_head;
    
    void *pending_client_requests;
  } http;
};

_Static_assert(offsetof(valk_aio_handle_t, magic) == 0,
               "magic must be first field for handle identification");
_Static_assert(offsetof(valk_aio_handle_t, uv) == offsetof(valk_aio_handle_t, uv.tcp),
               "uv.tcp must be at start of union for uv_handle_t casts");

typedef void (*valk_aio_task_fn)(void *ctx);

typedef struct valk_aio_task_item {
  valk_aio_task_fn fn;
  void *ctx;
} valk_aio_task_item_t;

typedef struct valk_aio_task_queue {
  valk_chase_lev_deque_t deque;
  uv_async_t notify;
  uv_check_t drain_check;
  bool initialized;
} valk_aio_task_queue_t;

struct valk_aio_system {
  valk_aio_system_config_t config;
  char name[64];
  const valk_aio_ops_t *ops;

  uv_sem_t startup_sem;

  uv_loop_t *eventloop;
  uv_thread_t loopThread;

  valk_aio_handle_t *stopperHandle;

  valk_slab_t *httpServers;
  valk_aio_http_server *serverList;
  valk_slab_t *httpClients;
  valk_slab_t *httpStreamArenas;
  valk_slab_t *tcpBufferSlab;

  valk_slab_t *handleSlab;
  valk_aio_handle_t liveHandles;

  valk_region_t system_region;

  _Atomic bool shuttingDown;
  bool cleanedUp;

  valk_gc_malloc_heap_t *loop_gc_heap;

  uv_timer_t maintenance_timer;

  valk_http_queue_t http_queue;

  valk_backpressure_list_t backpressure;
  valk_conn_admission_ctx_t admission;

  char (*port_strs)[8];
  u64 port_str_idx;

  valk_aio_task_queue_t task_queue;

  uv_async_t gc_wakeup;

  valk_aio_metrics_state_t *metrics_state;
  valk_owner_registry_t owner_registry;
  valk_event_loop_metrics_v2_t loop_metrics;
};

struct valk_aio_http_server {
  __aio_http_srv_e state;
  valk_aio_system_t *sys;
  SSL_CTX *ssl_ctx;
  valk_aio_handle_t *listener;
  char interface[200];
  int port;
  valk_http2_handler_t handler;
  valk_handle_t lisp_handler_handle;
  valk_lenv_t* sandbox_env;
  valk_http_server_config_t config;
  valk_server_metrics_t metrics;
  u16 owner_idx;
  struct valk_aio_http_server *next;
  struct valk_aio_http_server *prev;
};

struct valk_aio_http2_client {
  valk_aio_system_t *sys;
  SSL_CTX *ssl_ctx;
  valk_aio_handle_t *connection;
  char interface[200];
  int port;
  char hostname[200];
};

typedef struct __valk_request_client_pair_t {
  valk_aio_http2_client *client;
  valk_http2_request_t *req;
} __valk_request_client_pair_t;

typedef struct {
  const char *body;
  u64 body_len;
  u64 offset;
  bool needs_free;
} http_body_source_t;

typedef struct {
  alignas(16) uv_timer_t timer;
  valk_lval_t *callback;
  valk_handle_t callback_handle;
  u64 schedule_id;
  valk_async_handle_t *async_handle;
} valk_schedule_timer_t;

typedef struct valk_interval_timer {
  u32 magic;
  alignas(16) uv_timer_t timer;
  valk_lval_t *callback;
  valk_handle_t callback_handle;
  u64 interval_id;
  bool stopped;
  valk_async_handle_t *async_handle;
} valk_interval_timer_t;

typedef struct {
  int count;
  int active;
  int closing;
} __drain_diag_t;

extern u64 g_async_handle_id;

extern valk_gauge_v2_t* client_connections_active;



static inline bool __conn_is_closing(valk_aio_handle_t *conn) {
  return conn->http.state == VALK_CONN_CLOSING ||
         conn->http.state == VALK_CONN_CLOSED;
}

static inline bool __conn_is_closing_or_uv(valk_aio_handle_t *conn) {
  return __conn_is_closing(conn) ||
         uv_is_closing((uv_handle_t *)&conn->uv.tcp.uv);
}

#define CONN_UV_TCP(conn) (&(conn)->uv.tcp.uv)
#define CONN_UV_STREAM(conn) ((uv_stream_t *)&(conn)->uv.tcp.uv)
#define CONN_UV_HANDLE(conn) ((uv_handle_t *)&(conn)->uv.tcp.uv)
#define CONN_UV_LOOP(conn) ((conn)->uv.tcp.uv.loop)

#define VALK_HANDLE_VALID(h) \
  ((h) && (h)->magic == VALK_AIO_HANDLE_MAGIC)

#define VALK_ASSERT_HANDLE(h) \
  VALK_ASSERT(VALK_HANDLE_VALID(h), "Invalid handle magic: %x", (h) ? (h)->magic : 0)

#define VALK_ASSERT_SESSION(conn) \
  VALK_ASSERT((conn)->http.session != nullptr, "nullptr session on connection")

#define VALK_ASSERT_SERVER(conn) \
  VALK_ASSERT((conn)->http.server != nullptr, "nullptr server on connection")

#define VALK_ASSERT_SYS(conn) \
  VALK_ASSERT((conn)->http.server && (conn)->http.server->sys, "nullptr sys on connection")

#define GUARD_CONN_CLOSING(conn) \
  do { if (__conn_is_closing(conn)) return; } while(0)

#define GUARD_CONN_CLOSING_RET(conn, retval) \
  do { if (__conn_is_closing(conn)) return (retval); } while(0)

#define GUARD_CONN_ACTIVE(conn) \
  do { if (__conn_is_closing(conn) || !(conn)->http.session) return; } while(0)

#define GUARD_CONN_ACTIVE_RET(conn, retval) \
  do { if (__conn_is_closing(conn) || !(conn)->http.session) return (retval); } while(0)

static inline valk_lval_t* __http_error_qexpr(const char *status, const char *body) {
  valk_lval_t* items[] = {
    valk_lval_sym(":status"), valk_lval_str(status),
    valk_lval_sym(":body"), valk_lval_str(body)
  };
  return valk_lval_qlist(items, 4);
}



// Arena slot management (implemented in aio_uv.c)
void valk_http2_remove_from_active_arenas(valk_aio_handle_t *conn, u32 target_slot);

// Write buffer flush continuation (implemented in aio_uv.c)
void valk_http2_continue_pending_send(valk_aio_handle_t *conn);

// Task execution (implemented in aio_uv.c)
void valk_uv_exec_task(valk_aio_system_t *sys, valk_aio_task_new *task);

// Task queue API (implemented in aio_task_queue.c)
void valk_aio_task_queue_init(valk_aio_system_t *sys);
void valk_aio_task_queue_shutdown(valk_aio_system_t *sys);
void valk_aio_enqueue_task(valk_aio_system_t *sys, valk_aio_task_fn fn, void *ctx);
bool valk_aio_task_queue_empty(valk_aio_system_t *sys);
i64 valk_aio_task_queue_size(valk_aio_system_t *sys);
