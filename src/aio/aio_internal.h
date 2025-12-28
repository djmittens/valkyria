#pragma once

#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif
#define _POSIX_C_SOURCE 200809L

#include <nghttp2/nghttp2.h>
#include <openssl/ssl.h>
#include <openssl/ssl3.h>
#include <uv.h>
#include <stdbool.h>

#include "aio.h"
#include "aio_conn_io.h"
#include "aio_metrics.h"
#include "aio_sse.h"
#include "aio_sse_diagnostics.h"
#include "aio_sse_stream_registry.h"
#include "aio_pending_stream.h"
#include "aio_backpressure.h"
#include "aio_conn_admission.h"
#include "aio_maintenance.h"
#include "aio_ops.h"
#include "io/io_tcp_uv_types.h"
#include "metrics_v2.h"
#include "event_loop_metrics.h"
#include "concurrency.h"
#include "parser.h"
#include "memory.h"
#include "collections.h"
#include "aio_alloc.h"

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

#ifdef VALK_METRICS_ENABLED
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
#endif

typedef enum handle_kind_t {
  VALK_HNDL_EMPTY,
  VALK_HNDL_TCP,
  VALK_HNDL_TASK,
  VALK_HNDL_TIMER,
  VALK_HNDL_HTTP_CONN,
} handle_kind_t;

typedef enum __aio_http_conn_e {
  VALK_CONN_INIT,
  VALK_CONN_ESTABLISHED,
  VALK_CONN_CLOSING,
  VALK_CONN_CLOSED
} __aio_http_conn_e;

typedef enum __aio_http_srv_e {
  VALK_SRV_INIT,
  VALK_SRV_LISTENING,
  VALK_SRV_CLOSING,
  VALK_SRV_CLOSED,
} __aio_http_srv_e;

typedef struct valk_async_handle_uv_data {
  union {
    alignas(16) uv_timer_t timer;
  } uv;
  valk_async_handle_t *handle;
} valk_async_handle_uv_data_t;

typedef struct valk_http_async_ctx {
  void *session;
  i32 stream_id;
  struct valk_aio_handle_t *conn;
  valk_mem_arena_t *arena;
  void *arena_slab_item;
  u32 arena_slot;
} valk_http_async_ctx_t;

typedef struct valk_standalone_async_ctx {
  valk_mem_arena_t *arena;
  valk_slab_item_t *arena_slab_item;
  valk_aio_system_t *sys;
} valk_standalone_async_ctx_t;

typedef struct __tcp_buffer_slab_item_t {
  uv_write_t req;
  uv_buf_t buf;
  valk_aio_handle_t *conn;
  char data[HTTP_SLAB_ITEM_SIZE];
} __tcp_buffer_slab_item_t;

typedef struct __http2_req_res_t {
  u64 streamid;
  valk_http2_request_t *req;
  valk_arc_box *res_box;
  valk_http2_response_t *res;
  valk_promise promise;
} __http2_req_res_t;

typedef struct __http2_connect_req {
  valk_aio_system_t *sys;
  valk_aio_http2_client *client;
} __http2_connect_req;

typedef valk_pending_header_t pending_header_t;
typedef valk_pending_stream_t pending_stream_t;

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
  valk_slab_item_t *arena_slab_item;
  u32 arena_slot;
  u32 next_arena_slot;
#ifdef VALK_METRICS_ENABLED
  u64 start_time_us;
  u64 bytes_sent;
  u64 bytes_recv;
  int status_code;
  u64 response_sent_time_us;
  bool response_complete;
  struct valk_sse_stream_entry *sse_entry;
#endif
} valk_http2_server_request_t;

typedef struct valk_http_request_ctx {
  nghttp2_session *session;
  i32 stream_id;
  valk_aio_handle_t *conn;
  valk_http2_server_request_t *req;
  valk_lenv_t *env;
} valk_http_request_ctx_t;

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

#ifdef VALK_METRICS_ENABLED
    valk_handle_diag_t diag;
#endif

    struct valk_sse_diag_state *sse_state;
    valk_sse_stream_t *sse_streams;
    u32 active_arena_head;
  } http;
};

_Static_assert(offsetof(valk_aio_handle_t, magic) == 0,
               "magic must be first field for handle identification");
_Static_assert(offsetof(valk_aio_handle_t, uv) == offsetof(valk_aio_handle_t, uv.tcp),
               "uv.tcp must be at start of union for uv_handle_t casts");

struct valk_aio_system {
  valk_aio_system_config_t config;
  char name[64];
  const valk_aio_ops_t *ops;

  uv_sem_t startup_sem;

  uv_loop_t *eventloop;
  uv_thread_t loopThread;

  valk_aio_handle_t *stopperHandle;

  valk_slab_t *httpServers;
  valk_slab_t *httpClients;
  valk_slab_t *httpStreamArenas;
  valk_slab_t *tcpBufferSlab;

  valk_slab_t *handleSlab;
  valk_aio_handle_t liveHandles;

  bool shuttingDown;
  bool cleanedUp;

  uv_timer_t maintenance_timer;

  valk_http_queue_t http_queue;

  valk_pending_stream_queue_t pending_streams;
  valk_backpressure_list_t backpressure;
  valk_conn_admission_ctx_t admission;

  valk_http_request_ctx_t *current_request_ctx;

  char (*port_strs)[8];
  u64 port_str_idx;

#ifdef VALK_METRICS_ENABLED
  valk_aio_metrics_state_t *metrics_state;
  valk_owner_registry_t owner_registry;
  valk_sse_stream_registry_t sse_registry;
  valk_event_loop_metrics_v2_t loop_metrics;
#endif
};

struct valk_aio_http_server {
  __aio_http_srv_e state;
  valk_aio_system_t *sys;
  SSL_CTX *ssl_ctx;
  valk_aio_handle_t *listener;
  char interface[200];
  int port;
  valk_http2_handler_t handler;
  valk_lval_t* lisp_handler_fn;
  valk_lenv_t* sandbox_env;
  valk_http_server_config_t config;
#ifdef VALK_METRICS_ENABLED
  valk_server_metrics_t metrics;
  u16 owner_idx;
#endif
};

struct valk_aio_http2_client {
  valk_aio_system_t *sys;
  SSL_CTX *ssl_ctx;
  valk_aio_handle_t *connection;
  char interface[200];
  int port;
  char hostname[200];
  valk_promise _promise;
};

typedef struct valk_aio_task_new {
  void *arg;
  valk_promise promise;
  void (*callback)(valk_aio_system_t *, struct valk_aio_task_new *);
  valk_mem_allocator_t *allocator;
} valk_aio_task_new;

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
  valk_lval_t *continuation;
  nghttp2_session *session;
  i32 stream_id;
  valk_aio_handle_t *conn;
  valk_mem_arena_t *stream_arena;
  valk_lenv_t *env;
} valk_delay_timer_t;

typedef struct {
  alignas(16) uv_timer_t timer;
  valk_lval_t *callback;
  valk_lenv_t *env;
} valk_schedule_timer_t;

typedef struct {
  int count;
  int active;
  int closing;
} __drain_diag_t;

extern valk_aio_system_t *g_last_started_aio_system;
extern valk_aio_system_t *valk_aio_active_system;
extern u64 g_async_handle_id;

#ifdef VALK_METRICS_ENABLED
extern valk_gauge_v2_t* client_connections_active;
#endif



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

static inline bool __is_pending_stream(void *user_data) {
  return user_data && ((uptr)user_data & (1ULL << 63));
}

static inline pending_stream_t *__get_pending_stream(void *user_data) {
  if (!__is_pending_stream(user_data)) return NULL;
  return (pending_stream_t *)((uptr)user_data & ~(1ULL << 63));
}

#define VALK_HANDLE_VALID(h) \
  ((h) && (h)->magic == VALK_AIO_HANDLE_MAGIC)

#define VALK_ASSERT_HANDLE(h) \
  VALK_ASSERT(VALK_HANDLE_VALID(h), "Invalid handle magic: %x", (h) ? (h)->magic : 0)

#define VALK_ASSERT_SESSION(conn) \
  VALK_ASSERT((conn)->http.session != NULL, "NULL session on connection")

#define VALK_ASSERT_SERVER(conn) \
  VALK_ASSERT((conn)->http.server != NULL, "NULL server on connection")

#define VALK_ASSERT_SYS(conn) \
  VALK_ASSERT((conn)->http.server && (conn)->http.server->sys, "NULL sys on connection")

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
