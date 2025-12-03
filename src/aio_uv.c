#include "collections.h"
#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif
#define _POSIX_C_SOURCE \
  200809L  // The fuck is this ? turns out sigaction and shit has to be enabled
           // separately in strict mode

#include <netinet/in.h>
#include <netdb.h>
#include <nghttp2/nghttp2.h>
#include <openssl/bio.h>
#include <openssl/conf.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <openssl/ssl3.h>
#include <openssl/tls1.h>
#include <signal.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>
#include <execinfo.h>

#include "aio.h"
#include "aio_ssl.h"
#include "aio_metrics.h"
#include "common.h"
#include "concurrency.h"
#include "parser.h"  // For valk_lval_t in HTTP queue
#include "memory.h"
#include "log.h"

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

// It houses requests to the event loop
enum {
  AIO_QUEUE_SIZE = 10,
  AIO_MAX_HANDLES = 2056,
  HTTP_MAX_SERVERS = 3,
  HTTP_MAX_CLIENTS = 3,
  HTTP_SLAB_ITEM_SIZE = (SSL3_RT_MAX_PACKET_SIZE * 2),
  HTTP_MAX_IO_REQUESTS = (1024),
  HTTP_MAX_CONNECTIONS = (10),
  // TODO(networking): Figure out a good initial value for this.
  HTTP_MAX_CONNECTION_HEAP = (1024000),
  HTTP_MAX_CONCURRENT_REQUESTS = (1024),
  HTTP_MAX_REQUEST_SIZE_BYTES = ((int)8e6),
  HTTP_MAX_RESPONSE_SIZE_BYTES = ((int)8e6),
  // Per-stream arena configuration
  HTTP_STREAM_ARENA_SIZE = (67108864),        // 64MB per stream arena (generous for handler eval)
  HTTP_MAX_STREAMS_PER_CONNECTION = (128),    // Max concurrent streams per conn
  HTTP_STREAM_ARENA_POOL_SIZE = (64),         // Total stream arenas in pool (64 * 64MB = 4GB max)
};

// times 2 just for fun

// Singleton: only one AIO system can exist per process
// This prevents accidentally starting multiple event loops which causes race conditions
static valk_aio_system_t *global_aio_system = NULL;

static __thread valk_slab_t *tcp_buffer_slab;
static void __valk_http2_response_free(valk_arc_box *box);

typedef struct __http2_req_res_t {
  size_t streamid;
  valk_http2_request_t *req;
  valk_http2_response_t *res;
  valk_promise promise;
} __http2_req_res_t;

typedef struct __tcp_buffer_slab_item_t {
  uv_write_t req;
  uv_buf_t buf;
  char data[SSL3_RT_MAX_PACKET_SIZE];
} __tcp_buffer_slab_item_t;

typedef struct __http2_connect_req {
  valk_aio_system_t *sys;
  valk_aio_http2_client *client;
} __http2_connect_req;

typedef enum handle_kind_t {
  VALK_HNDL_EMPTY,
  VALK_HNDL_TCP,
  VALK_HNDL_TASK,
  // VALK_TIMER,
  // VALK_FILE,
  // VALK_SIGNAL,
} handle_kind_t;

typedef struct valk_aio_handle_t {
  handle_kind_t kind;
  valk_aio_handle_t *prev;
  valk_aio_handle_t *next;
  valk_aio_system_t *sys;
  void *arg;

  void (*onOpen)(valk_aio_handle_t *);
  void (*onClose)(valk_aio_handle_t *);

  union {
    uv_tcp_t tcp;
    uv_async_t task;
  } uv;
} valk_aio_handle_t;

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf);
void __alloc_callback(uv_handle_t *handle, size_t suggested_size,
                      uv_buf_t *buf) {
  UNUSED(handle);
  UNUSED(suggested_size);
  // TODO(networking): replace it with memory arena for the request
  void *base = (void *)valk_slab_aquire(tcp_buffer_slab)->data;
  buf->base = (char *)base;  // start of payload region
  // Clamp to the configured slab payload size
  buf->len = HTTP_SLAB_ITEM_SIZE;
}

typedef struct valk_aio_task_new {
  void *arg;
  valk_promise promise;
  void (*callback)(valk_aio_system_t *, struct valk_aio_task_new *);
  valk_mem_allocator_t *allocator; // allocator used for this task
} valk_aio_task_new;

typedef struct __valk_request_client_pair_t {
  valk_aio_http2_client *client;
  valk_http2_request_t *req;
} __valk_request_client_pair_t;

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

typedef struct valk_aio_http_conn {
  __aio_http_conn_e state;
  struct valk_aio_http_conn *prev, *next;

  valk_aio_ssl_t ssl;
  nghttp2_session *session;
  valk_http2_handler_t *httpHandler;
  valk_aio_handle_t *handle;
  uv_connect_t req;
  valk_aio_http_server *server;
  int active_streams;
} valk_aio_http_conn;

// Escape analysis: intern value to GC heap for cross-thread sharing
// Takes arena-allocated value, returns GC heap-allocated deep copy
static inline valk_lval_t* valk_http_intern_to_heap(valk_lval_t* arena_val) {
  valk_lval_t* heap_val;
  VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
    heap_val = valk_lval_copy(arena_val);
  }
  return heap_val;
}

// Server-side incoming request data (arena-allocated, per stream)
typedef struct {
  char *method;              // :method pseudo-header
  char *scheme;              // :scheme pseudo-header
  char *authority;           // :authority pseudo-header
  char *path;                // :path pseudo-header
  struct {
    struct valk_http2_header_t *items;
    size_t count;
    size_t capacity;
  } headers;                 // Regular headers
  uint8_t *body;             // Request body data
  size_t bodyLen;
  size_t bodyCapacity;
  valk_aio_http_conn *conn;  // Connection this request came from
  int32_t stream_id;         // HTTP/2 stream ID
  valk_mem_arena_t *stream_arena;       // Per-stream arena
  valk_slab_item_t *arena_slab_item;    // For releasing back to slab
#ifdef VALK_METRICS_ENABLED
  uint64_t start_time_us;    // Request start time for metrics
  uint64_t bytes_sent;       // Bytes sent in response
  uint64_t bytes_recv;       // Bytes received in request
#endif
} valk_http2_server_request_t;

// HTTP request item - event loop -> main thread
typedef struct {
  valk_lval_t* request;      // Request qexpr (GC heap)
  valk_lval_t* handler_fn;   // Handler lambda (GC heap)
  valk_aio_http_conn* conn;  // Connection handle
  int32_t stream_id;         // HTTP/2 stream ID
} valk_http_request_item_t;

// HTTP response item - main thread -> event loop
typedef struct {
  valk_lval_t* response;     // Response qexpr {status body headers}
  valk_aio_http_conn* conn;  // Connection to send on
  int32_t stream_id;         // Stream to respond to
} valk_http_response_item_t;

// Queue for cross-thread HTTP request/response communication
typedef struct {
  pthread_mutex_t request_mutex;
  pthread_cond_t request_ready;
  valk_http_request_item_t* request_items;
  size_t request_idx;
  size_t request_count;
  size_t request_capacity;

  pthread_mutex_t response_mutex;
  pthread_cond_t response_ready;
  valk_http_response_item_t* response_items;
  size_t response_idx;
  size_t response_count;
  size_t response_capacity;
} valk_http_queue_t;

typedef struct valk_aio_system {
  // everything  past this point only accessed inside of event loop
  uv_loop_t *eventloop;
  uv_thread_t loopThread;

  valk_aio_handle_t *stopperHandle;

  valk_slab_t *httpServers;
  valk_slab_t *httpClients;
  valk_slab_t *httpStreamArenas;    // Pool of per-stream arenas

  valk_slab_t *handleSlab;
  valk_aio_handle_t liveHandles;

  bool shuttingDown;

  // HTTP request/response queues for Lisp handlers
  valk_http_queue_t http_queue;

#ifdef VALK_METRICS_ENABLED
  valk_aio_metrics_t metrics;
#endif
} valk_aio_system_t;

typedef struct valk_aio_http_server {
  __aio_http_srv_e state;
  valk_aio_system_t *sys;
  SSL_CTX *ssl_ctx;
  valk_aio_handle_t *listener;
  char interface[200];
  int port;
  valk_http2_handler_t handler;
  valk_lval_t* lisp_handler_fn;  // Lisp lambda for request handling (GC heap)
  valk_lenv_t* sandbox_env;      // Sandbox env that shadows def (created once at startup)
} valk_aio_http_server;

static void __event_loop(void *arg) {
  valk_aio_system_t *sys = arg;
  valk_mem_init_malloc();
  VALK_DEBUG("Initializing UV event loop thread");
  // Slab for TCP buffers using the compile-time constant size
  // HTTP_SLAB_ITEM_SIZE is chosen to be >= any struct we overlay for writes
  tcp_buffer_slab = valk_slab_new(HTTP_SLAB_ITEM_SIZE, HTTP_MAX_IO_REQUESTS);

  // Initialize per-stream arena pool
  // Each slab item contains: valk_mem_arena_t header + arena heap space
  sys->httpStreamArenas = valk_slab_new(
      sizeof(valk_mem_arena_t) + HTTP_STREAM_ARENA_SIZE,
      HTTP_STREAM_ARENA_POOL_SIZE);
  if (!sys->httpStreamArenas) {
    VALK_ERROR("Failed to allocate stream arena slab");
    return;
  }
  VALK_INFO("Initialized %d stream arenas (%zuKB each)",
            HTTP_STREAM_ARENA_POOL_SIZE, HTTP_STREAM_ARENA_SIZE / 1024);

  // Run the loop until stop is requested
  uv_run(sys->eventloop, UV_RUN_DEFAULT);

  // Drain pending close callbacks and timers cleanly. uv_stop only requests
  // the loop to stop; we still need to spin the loop to let close callbacks
  // run to completion.
  while (uv_loop_alive(sys->eventloop)) {
    uv_run(sys->eventloop, UV_RUN_NOWAIT);
  }

  valk_slab_free(tcp_buffer_slab);
  valk_slab_free(sys->httpStreamArenas);
}

static void __valk_aio_http2_on_disconnect(valk_aio_handle_t *handle) {
  VALK_DEBUG("HTTP/2 disconnect called");
  valk_aio_http_conn *conn = handle->arg;
  if (conn->httpHandler && conn->httpHandler->onDisconnect) {
    VALK_TRACE("HTTP/2 onDisconnect handler");
    conn->httpHandler->onDisconnect(conn->httpHandler->arg, conn);
  }

#ifdef VALK_METRICS_ENABLED
  // Record connection close
  valk_aio_metrics_on_close(&handle->sys->metrics);
#endif

  // TODO Tear down http and ssl context's only through the slab... make sure
  // they dont escape into malloc

  valk_aio_ssl_free(&conn->ssl);
  nghttp2_session_del(conn->session);
  free(conn);
}

static void __uv_handle_closed_cb(uv_handle_t *handle) {
  // TODO(networking): Rename this to something more generic as it can be used
  // with any handle
  valk_aio_handle_t *hndl = handle->data;
  VALK_TRACE("UV handle closed %p", handle->data);
  if (hndl->onClose != nullptr) {
    VALK_TRACE("Calling onClose callback");
    hndl->onClose(hndl);
  }
  valk_dll_pop(hndl);  // remove this handle from live handles
  valk_slab_release_ptr(hndl->sys->handleSlab, hndl);  // finally release it
}

static void __aio_uv_walk_close(uv_handle_t *h, void *arg) {
  UNUSED(arg);
  if (!uv_is_closing(h)) {
    VALK_DEBUG("Closing open UV handle");
    uv_close(h, __uv_handle_closed_cb);
  }
}

static void __aio_uv_stop(uv_async_t *h) {
  // Just mark all handles for closing. The drain loop in __event_loop
  // (lines 208-210) will properly complete the shutdown by running until
  // all handles are closed.
  uv_walk(h->loop, __aio_uv_walk_close, NULL);
  // Call uv_stop to break out of UV_RUN_DEFAULT
  uv_stop(h->loop);
}

static int __http_on_header_callback(nghttp2_session *session,
                                     const nghttp2_frame *frame,
                                     const uint8_t *name, size_t namelen,
                                     const uint8_t *value, size_t valuelen,
                                     uint8_t flags, void *user_data) {
  UNUSED(flags);
  UNUSED(user_data);
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  VALK_TRACE("HDR: %.*s: %.*s", (int)namelen, name, (int)valuelen, value);

  // Get request attached to this stream
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

  if (!req) return 0;

#ifdef VALK_METRICS_ENABLED
  // Track received bytes for headers (name + value + overhead for ': ' and \r\n)
  req->bytes_recv += namelen + valuelen + 4;
#endif

  // Allocate strings on per-stream arena
  VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
    // Handle pseudo-headers
    if (namelen > 0 && name[0] == ':') {
      char *str = valk_mem_alloc(valuelen + 1);
      memcpy(str, value, valuelen);
      str[valuelen] = '\0';

      if (namelen == 7 && memcmp(name, ":method", 7) == 0) {
        req->method = str;
      } else if (namelen == 7 && memcmp(name, ":scheme", 7) == 0) {
        req->scheme = str;
      } else if (namelen == 10 && memcmp(name, ":authority", 10) == 0) {
        req->authority = str;
      } else if (namelen == 5 && memcmp(name, ":path", 5) == 0) {
        req->path = str;
      }
    } else {
      // Regular header - add to headers array
      if (req->headers.count >= req->headers.capacity) {
        size_t new_cap = req->headers.capacity == 0 ? 8 : req->headers.capacity * 2;
        struct valk_http2_header_t *new_items = valk_mem_alloc(
            new_cap * sizeof(struct valk_http2_header_t));
        if (req->headers.items) {
          memcpy(new_items, req->headers.items,
                 req->headers.count * sizeof(struct valk_http2_header_t));
        }
        req->headers.items = new_items;
        req->headers.capacity = new_cap;
      }

      struct valk_http2_header_t *h = &req->headers.items[req->headers.count++];
      h->name = valk_mem_alloc(namelen + 1);
      h->value = valk_mem_alloc(valuelen + 1);
      memcpy(h->name, name, namelen);
      memcpy(h->value, value, valuelen);
      h->name[namelen] = '\0';
      h->value[valuelen] = '\0';
      h->nameLen = namelen;
      h->valueLen = valuelen;
    }
  }

  return 0;  // success
}

static int __http_on_begin_headers_callback(nghttp2_session *session,
                                            const nghttp2_frame *frame,
                                            void *user_data) {
  valk_aio_http_conn *conn = (valk_aio_http_conn *)user_data;

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_DEBUG(">>> Received HTTP/2 request (stream_id=%d)",
               frame->hd.stream_id);

    // Track active streams for arena lifecycle
    conn->active_streams++;

#ifdef VALK_METRICS_ENABLED
    // Record stream start
    valk_aio_metrics_on_stream_start(&conn->server->sys->metrics);
#endif

    // Acquire per-stream arena from slab
    valk_slab_item_t *arena_item = valk_slab_aquire(conn->server->sys->httpStreamArenas);
    if (!arena_item) {
      VALK_ERROR("Stream arena pool exhausted for stream %d", frame->hd.stream_id);
      // Return error to reject the stream
      return NGHTTP2_ERR_TEMPORAL_CALLBACK_FAILURE;
    }

    valk_mem_arena_t *stream_arena = (valk_mem_arena_t *)arena_item->data;
    valk_mem_arena_init(stream_arena, HTTP_STREAM_ARENA_SIZE);

    // Allocate request object on STREAM arena
    valk_http2_server_request_t *req;
    VALK_WITH_ALLOC((valk_mem_allocator_t*)stream_arena) {
      req = valk_mem_alloc(sizeof(valk_http2_server_request_t));
      memset(req, 0, sizeof(valk_http2_server_request_t));
      req->conn = conn;
      req->stream_id = frame->hd.stream_id;
      req->stream_arena = stream_arena;
      req->arena_slab_item = arena_item;
#ifdef VALK_METRICS_ENABLED
      req->start_time_us = uv_hrtime() / 1000;  // Record start time
      req->bytes_sent = 0;
      req->bytes_recv = 0;
#endif
    }

    // Attach request to stream
    nghttp2_session_set_stream_user_data(session, frame->hd.stream_id, req);
  }
  return 0;
}

static int __http2_client_on_header_cb(nghttp2_session *session,
                                       const nghttp2_frame *frame,
                                       const uint8_t *name, size_t namelen,
                                       const uint8_t *value, size_t valuelen,
                                       uint8_t flags, void *user_data) {
  UNUSED(session);
  UNUSED(frame);
  UNUSED(flags);
  UNUSED(user_data);

  __http2_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

  if (reqres) {
    // Cache headers into the response object for later inspection
    if (namelen == 7 && memcmp(name, ":status", 7) == 0) {
      char *st = valk_mem_alloc(valuelen + 1);
      memcpy(st, value, valuelen);
      st[valuelen] = '\0';
      reqres->res->status = st;
    } else {
      struct valk_http2_header_t h = {0};
      h.name = valk_mem_alloc(namelen + 1);
      h.value = valk_mem_alloc(valuelen + 1);
      memcpy(h.name, name, namelen);
      memcpy(h.value, value, valuelen);
      h.name[namelen] = '\0';
      h.value[valuelen] = '\0';
      h.nameLen = namelen;
      h.valueLen = valuelen;
      da_add(&reqres->res->headers, h);
    }
  }
  return 0;  // success
}

static void __http_tcp_on_write_cb(uv_write_t *handle, int status) {
  if (status) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Socket On Write error: %s \n", uv_strerror(status));
  }

  __tcp_buffer_slab_item_t *item =
      valk_container_of(handle, __tcp_buffer_slab_item_t, req);
  valk_slab_release_ptr(tcp_buffer_slab, item);
}

static nghttp2_ssize __http_byte_body_cb(nghttp2_session *session,
                                         int32_t stream_id, uint8_t *buf,
                                         size_t length, uint32_t *data_flags,
                                         nghttp2_data_source *source,
                                         void *user_data) {
  UNUSED(session);
  UNUSED(stream_id);
  UNUSED(user_data);

  size_t body_len = strlen(source->ptr);

  // Don't include null terminator in HTTP response body
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memcpy(buf, source->ptr, body_len);

  // This marks that with this call we reached the end of the file, and dont
  // call us back again
  *data_flags |= NGHTTP2_DATA_FLAG_EOF;
  return body_len;
}

static int __demo_response(nghttp2_session *session, int stream_id) {
  printf("WE ARE sending a response ??\n");
  /* Prepare some pseudo-headers: */
  const nghttp2_nv response_headers[] = {
      MAKE_NV2(":status", "200"),
      MAKE_NV2("content-type", "text/html; charset=utf-8"),
      // MAKE_NV2("fuckyou", "this is something else aint it"),
  };

  /* Send HEADERS frame */
  /* nghttp2_submit_headers( */
  /*     session, NGHTTP2_FLAG_END_HEADERS, stream_id, NULL, response_headers,
   */
  /*     sizeof(response_headers) / sizeof(response_headers[0]), NULL); */

  /* Send DATA frame */
  nghttp2_data_provider2 data_prd;
  data_prd.source.ptr = VALK_HTTP_MOTD;
  data_prd.read_callback = __http_byte_body_cb;

  /* return nghttp2_submit_push_promise(session, 0, stream_id, response_headers,
   * 2, */
  /*                                    (void *)body); */
  return nghttp2_submit_response2(
      session, stream_id, response_headers,
      sizeof(response_headers) / sizeof(response_headers[0]), &data_prd);
}

// Extract value for a keyword from qexpr like {:key "value" ...}
static valk_lval_t* __http_qexpr_get(valk_lval_t* qexpr, const char* key) {
  if (LVAL_TYPE(qexpr) != LVAL_QEXPR && LVAL_TYPE(qexpr) != LVAL_CONS) {
    return NULL;
  }

  // Iterate through the qexpr looking for the keyword
  valk_lval_t* curr = qexpr;
  while (!valk_lval_list_is_empty(curr)) {
    valk_lval_t* k = valk_lval_head(curr);
    curr = valk_lval_tail(curr);

    if (valk_lval_list_is_empty(curr)) break;

    valk_lval_t* v = valk_lval_head(curr);
    curr = valk_lval_tail(curr);

    // Check if key matches
    if (LVAL_TYPE(k) == LVAL_SYM && strcmp(k->str, key) == 0) {
      return v;
    }
  }

  return NULL;
}

// Send HTTP/2 response from Lisp qexpr {:status "200" :body "..." :headers {...}}
static int __http_send_response(nghttp2_session *session, int stream_id,
                                 valk_lval_t* response_qexpr, valk_mem_arena_t* arena) {
  // Extract status (default "200")
  const char* status = "200";
  valk_lval_t* status_val = __http_qexpr_get(response_qexpr, ":status");
  if (status_val && LVAL_TYPE(status_val) == LVAL_STR) {
    status = status_val->str;
  }

  // Extract body (default "") - must copy to arena so it outlives this call
  const char* body = "";
  size_t body_len = 0;
  valk_lval_t* body_val = __http_qexpr_get(response_qexpr, ":body");
  if (body_val && LVAL_TYPE(body_val) == LVAL_STR) {
    // Copy body string to arena so it remains valid when body callback is invoked
    body_len = strlen(body_val->str);
    VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
      char* body_copy = valk_mem_alloc(body_len + 1);
      memcpy(body_copy, body_val->str, body_len + 1);
      body = body_copy;
    }
  }

#ifdef VALK_METRICS_ENABLED
  // Track bytes sent for metrics
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (req) {
    req->bytes_sent = body_len;
  }
#endif

  // Extract content-type (default "text/plain; charset=utf-8")
  const char* content_type = "text/plain; charset=utf-8";
  valk_lval_t* ct_val = __http_qexpr_get(response_qexpr, ":content-type");
  if (ct_val && LVAL_TYPE(ct_val) == LVAL_STR) {
    content_type = ct_val->str;
  }

  // Build response headers on arena
  nghttp2_nv* headers;
  size_t header_count = 2; // :status and content-type

  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    headers = valk_mem_alloc(sizeof(nghttp2_nv) * header_count);
    headers[0] = (nghttp2_nv)MAKE_NV(":status", status, strlen(status));
    headers[1] = (nghttp2_nv)MAKE_NV("content-type", content_type, strlen(content_type));
  }

  // Setup data provider for body
  nghttp2_data_provider2 data_prd;
  data_prd.source.ptr = (void*)body;
  data_prd.read_callback = __http_byte_body_cb;

  return nghttp2_submit_response2(session, stream_id, headers, header_count, &data_prd);
}

// Build Lisp qexpr from HTTP/2 request (on arena)
// Returns qexpr like: {:method "GET" :path "/" :headers {{name value}...} :body ""}
static valk_lval_t* __http_build_request_qexpr(valk_http2_server_request_t *req) {
  valk_lval_t *qexpr;

  VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
    // Build headers list (in reverse order, will be reversed by qcons)
    valk_lval_t *headers_list = valk_lval_nil();
    for (size_t i = req->headers.count; i > 0; i--) {
      valk_lval_t *pair_items[2] = {
        valk_lval_str((char*)req->headers.items[i-1].name),
        valk_lval_str((char*)req->headers.items[i-1].value)
      };
      valk_lval_t *pair = valk_lval_qlist(pair_items, 2);
      headers_list = valk_lval_qcons(pair, headers_list);
    }

    // Build main qexpr {... } in correct order
    valk_lval_t *items[8];
    size_t item_count = 0;

    // Add method and value
    items[item_count++] = valk_lval_sym(":method");
    items[item_count++] = valk_lval_str(req->method ? req->method : "GET");

    // Add path and value
    items[item_count++] = valk_lval_sym(":path");
    items[item_count++] = valk_lval_str(req->path ? req->path : "/");

    // Add authority if present
    if (req->authority) {
      items[item_count++] = valk_lval_sym(":authority");
      items[item_count++] = valk_lval_str(req->authority);
    }

    // Add headers and list
    items[item_count++] = valk_lval_sym(":headers");
    items[item_count++] = headers_list;

    // Add :body and value
    // items[item_count++] = valk_lval_sym(":body");
    // items[item_count++] = valk_lval_str(req->body && req->bodyLen > 0 ? (char*)req->body : "");

    qexpr = valk_lval_qlist(items, item_count);
  }

  return qexpr;
}

/* Called when a stream is closed (server-side).
 * Release per-stream arena immediately for instant memory reclamation.
 */
static int __http_server_on_stream_close_callback(nghttp2_session *session,
                                                  int32_t stream_id,
                                                  uint32_t error_code,
                                                  void *user_data) {
  UNUSED(error_code);
  valk_aio_http_conn *conn = (valk_aio_http_conn *)user_data;

  // Get request data to access stream arena
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data(session, stream_id);

  if (req && req->arena_slab_item) {
#ifdef VALK_METRICS_ENABLED
    // Record stream end metrics
    uint64_t end_time_us = uv_hrtime() / 1000;
    uint64_t duration_us = end_time_us - req->start_time_us;
    bool is_error = (error_code != NGHTTP2_NO_ERROR);
    // Add body length to bytes_recv (headers already tracked in on_header callback)
    uint64_t bytes_recv = req->bytes_recv + req->bodyLen;
    valk_aio_metrics_on_stream_end(&conn->server->sys->metrics, is_error,
                                     duration_us, req->bytes_sent, bytes_recv);
#endif

    // Release stream arena back to slab (instant cleanup)
    valk_slab_release(conn->server->sys->httpStreamArenas, req->arena_slab_item);
    VALK_DEBUG("Stream %d closed, arena released", stream_id);
  }

  conn->active_streams--;
  VALK_DEBUG("%d active streams remaining", conn->active_streams);

  return 0;
}

/* Called when a frame is fully received. For a request, we might respond here.
 */
static int __http_on_frame_recv_callback(nghttp2_session *session,
                                         const nghttp2_frame *frame,
                                         void *user_data) {
  valk_aio_http_conn *conn = (valk_aio_http_conn *)user_data;

  if (frame->hd.type == NGHTTP2_GOAWAY) {
    VALK_DEBUG("Received GO AWAY frame");
    return 0;
  }

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    VALK_DEBUG(">>> Received complete HTTP/2 request (stream_id=%d)", frame->hd.stream_id);

    // Get request data attached to this stream
    valk_http2_server_request_t *req =
        nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

    if (!req) {
      VALK_WARN("No request data for stream %d", frame->hd.stream_id);
      return 0;
    }

    // Check if there's a Lisp handler
    if (conn->server && conn->server->lisp_handler_fn) {
      // Build request qexpr on stream arena
      valk_lval_t *arena_qexpr = __http_build_request_qexpr(req);

      // Call handler: (handler request)
      // Use pre-created sandbox env (shadows 'def') and stream arena for allocations
      valk_lval_t *handler = conn->server->lisp_handler_fn;
      valk_lenv_t *sandbox_env = conn->server->sandbox_env;
      valk_lval_t *response;
      VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
        valk_lval_t *args = valk_lval_cons(arena_qexpr, valk_lval_nil());
        response = valk_lval_eval_call(sandbox_env, handler, args);
      }

      // Send response based on handler result
      if (LVAL_TYPE(response) == LVAL_ERR) {
        VALK_WARN("Handler returned error: %s", response->str);
        // Send 500 error response
        VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
          valk_lval_t* error_items[] = {
            valk_lval_sym(":status"), valk_lval_str("500"),
            valk_lval_sym(":body"), valk_lval_str(response->str)
          };
          valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
          __http_send_response(session, frame->hd.stream_id, error_resp, req->stream_arena);
        }
      } else {
        // Send handler's response
        __http_send_response(session, frame->hd.stream_id, response, req->stream_arena);
      }
    } else {
      // Fall back to demo response
      VALK_DEBUG("No Lisp handler, using demo response");
      __demo_response(session, frame->hd.stream_id);
    }
  }

  return 0;
}

// Simple no-op callbacks for demo handler
static void __demo_on_connect(void *arg, valk_aio_http_conn *conn) {
  UNUSED(arg);
  UNUSED(conn);
}

static void __demo_on_disconnect(void *arg, valk_aio_http_conn *conn) {
  UNUSED(arg);
  UNUSED(conn);
}

static void __demo_on_header(void *arg, valk_aio_http_conn *conn, size_t stream,
                             char *name, char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

static void __demo_on_body(void *arg, valk_aio_http_conn *conn, size_t stream,
                           uint8_t flags, valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}

// Export a demo handler for testing
valk_http2_handler_t *valk_aio_http2_demo_handler(void) {
  static valk_http2_handler_t handler;
  static int initialized = 0;
  if (!initialized) {
    handler.arg = NULL;
    handler.onConnect = __demo_on_connect;
    handler.onDisconnect = __demo_on_disconnect;
    handler.onHeader = __demo_on_header;
    handler.onBody = __demo_on_body;
    initialized = 1;
  }
  return &handler;
}

static void __http2_flush_frames(valk_buffer_t *buf,
                                 struct valk_aio_http_conn *conn) {
  const uint8_t *data;

  int len = 0;
  do {
    len = nghttp2_session_mem_send2(conn->session, &data);
    if (len < 0) {
      VALK_ERROR("nghttp2_session_mem_send2 error: %s", nghttp2_strerror((int)len));
    } else if (len) {
      // TODO(networking): Need to handle data greater than the buffer size here

      valk_buffer_append(buf, (void *)data, len);

      if ((buf->count + len) > buf->capacity) {
        // if we read the same amount of data again, we would overflow, so lets
        // stop for now
      VALK_WARN("Send buffer overflow risk: %ld", buf->count + len);
        break;
      }

      VALK_TRACE("Buffered frame len=%ld count=%ld capacity=%ld", (long)len,
                 (long)buf->count, (long)buf->capacity);
    } else {
      VALK_TRACE("No data to send");
    }
  } while (len > 0);
}

static void __http_tcp_unencrypted_read_cb(void *arg,
                                           const valk_buffer_t *buf) {
  struct valk_aio_http_conn *conn = arg;

  // Feed data to nghttp2
  ssize_t rv = nghttp2_session_mem_recv2(
      conn->session, (const uint8_t *)buf->items, buf->count);
  if (rv < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("nghttp2_session_mem_recv error: %zd", rv);
    if (!uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
      uv_close((uv_handle_t *)&conn->handle->uv.tcp, __uv_handle_closed_cb);
    }
  }
}

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf) {
  valk_aio_handle_t *hndl = stream->data;
  struct valk_aio_http_conn *conn = hndl->arg;

  if (nread < 0) {
    // Error or EOF
    if (nread == UV_EOF) {
      printf("[DEBUG] Received EOF on tcp stream\n");
    } else {
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      fprintf(stderr, "[DEBUG] Read error: %s\n", uv_strerror((int)nread));
    }
    printf("[DEBUG] Attempting to close handle %p, is_closing=%d\n",
           (void*)&conn->handle->uv.tcp,
           uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp));
    if (!uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
      printf("[DEBUG] Calling uv_close\n");
      uv_close((uv_handle_t *)&conn->handle->uv.tcp, __uv_handle_closed_cb);
    } else {
      printf("[DEBUG] Skipping uv_close - already closing\n");
    }
    return;
  }

  VALK_TRACE("Feeding data to OpenSSL %ld", nread);

  valk_buffer_t In = {
      .items = buf->base, .count = nread, .capacity = HTTP_SLAB_ITEM_SIZE};

  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_aquire(tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  int err = valk_aio_ssl_on_read(&conn->ssl, &In, &Out, conn,
                                 __http_tcp_unencrypted_read_cb);

  // Only do this if ssl is established:
  if (!err) {
    // Flushies
    In.count = 0;
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memset(In.items, 0, In.capacity);
    __http2_flush_frames(&In, conn);

    // Encrypt the new data n stuff
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);
  }

  int wantToSend = Out.count > 0;
  if (wantToSend) {
    slabItem->buf.base = Out.items;
    slabItem->buf.len = Out.count;

    VALK_TRACE("Sending %ld bytes", Out.count);
    uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
             &slabItem->buf, 1, __http_tcp_on_write_cb);
  } else {
    VALK_TRACE("Nothing to send: %d", wantToSend);
    valk_slab_release_ptr(tcp_buffer_slab, slabItem);
  }

  valk_slab_release_ptr(tcp_buffer_slab, In.items);
}

static int __http_send_server_connection_header(nghttp2_session *session) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, 100}};
  int rv;

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  if (rv != 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

static int __http_send_client_connection_header(nghttp2_session *session) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, 100}};
  int rv;
  VALK_DEBUG("[http2 Client] Sending connection frame");

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  if (rv != 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

static void __http_server_accept_cb(uv_stream_t *stream, int status) {
  if (status < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "New connection error %s\n", uv_strerror(status));
    // error!
    return;
  }

  valk_aio_handle_t *hndl = stream->data;
  valk_aio_http_server *srv = hndl->arg;

  struct valk_aio_http_conn *conn = malloc(sizeof(struct valk_aio_http_conn));
  if (!conn) {
    VALK_ERROR("Failed to allocate connection");
    return;
  }
  memset(conn, 0, sizeof(struct valk_aio_http_conn));
  conn->server = srv;

  conn->handle =
      (valk_aio_handle_t *)valk_slab_aquire(srv->sys->handleSlab)->data;
  memset(conn->handle, 0, sizeof(valk_aio_handle_t));

  conn->handle->kind = VALK_HNDL_TCP;
  conn->handle->sys = srv->sys;
  conn->handle->arg = conn;
  // conn->handle->onClose = nullptr;
  conn->handle->onClose = __valk_aio_http2_on_disconnect;
  conn->handle->uv.tcp.data = conn->handle;

  conn->httpHandler = &srv->handler;

  valk_dll_insert_after(&srv->sys->liveHandles, conn->handle);

  uv_tcp_init(stream->loop, &conn->handle->uv.tcp);

  // dont need for now because we are using nghttp2 mem buffer for send
  // conn->send_buf.base = valk_mem_alloc(MAX_SEND_BYTES);
  int res = uv_accept(stream, (uv_stream_t *)&conn->handle->uv.tcp);

  if (!res) {
    // Get the client IP address
    struct sockaddr_storage client_addr;
    int addr_len = sizeof(client_addr);

    if (uv_tcp_getpeername(&conn->handle->uv.tcp,
                           (struct sockaddr *)&client_addr, &addr_len) == 0) {
      char ip[INET6_ADDRSTRLEN];
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      memset(ip, 0, sizeof(ip));
      uint16_t port = 0;
      if (client_addr.ss_family == AF_INET) {
        // IPv4
        struct sockaddr_in *addr4 = (struct sockaddr_in *)&client_addr;
        uv_ip4_name(addr4, ip, sizeof(ip));
        port = ntohs(addr4->sin_port);
      } else if (client_addr.ss_family == AF_INET6) {
        // IPv6
        struct sockaddr_in6 *addr6 = (struct sockaddr_in6 *)&client_addr;
        uv_ip6_name(addr6, ip, sizeof(ip));
        port = ntohs(addr6->sin6_port);
      }

      VALK_INFO("Accepted connection from %s:%d", ip, port);
    } else {
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      VALK_WARN("Could not get peer name");
    };

    static nghttp2_session_callbacks *callbacks = nullptr;
    if (!callbacks) {
      nghttp2_session_callbacks_new(&callbacks);
      nghttp2_session_callbacks_set_on_begin_headers_callback(
          callbacks, __http_on_begin_headers_callback);
      nghttp2_session_callbacks_set_on_header_callback(
          callbacks, __http_on_header_callback);
      nghttp2_session_callbacks_set_on_frame_recv_callback(
          callbacks, __http_on_frame_recv_callback);
      nghttp2_session_callbacks_set_on_stream_close_callback(
          callbacks, __http_server_on_stream_close_callback);
    }

    nghttp2_session_server_new3(&conn->session, callbacks, conn, nullptr,
                                nullptr);
    valk_aio_ssl_accept(&conn->ssl, srv->ssl_ctx);

    // Send settings to the client
    __http_send_server_connection_header(conn->session);

    //  TODO(networking): Maybe i should call this on the first read?
    if (conn->httpHandler && conn->httpHandler->onConnect) {
      conn->httpHandler->onConnect(conn->httpHandler->arg, conn);
    }

#ifdef VALK_METRICS_ENABLED
    // Record successful connection
    valk_aio_metrics_on_connection(&srv->sys->metrics, true);
#endif

    // start the connection off by listening, (SSL expects client to send first)
    uv_read_start((uv_stream_t *)&conn->handle->uv.tcp, __alloc_callback,
                  __http_tcp_read_cb);
  } else {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_WARN("Accept error: %s", uv_strerror(res));

#ifdef VALK_METRICS_ENABLED
    // Record failed connection
    valk_aio_metrics_on_connection(&srv->sys->metrics, false);
#endif

    // Only close if not already closing
    if (!uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
      uv_close((uv_handle_t *)&conn->handle->uv.tcp, __uv_handle_closed_cb);
    }
    free(conn);
  }
}
static void __http_shutdown_cb(valk_aio_handle_t *hndl) {
  UNUSED(hndl);
  VALK_INFO("TODO: shutdown the server cleanly");
}

static void __http_listen_cb(valk_aio_system_t *sys,
                             struct valk_aio_task_new *task) {
  int r;
  struct sockaddr_in addr;
  // We accept the transfer of ownership for box here
  // therefore we dont aquire it, but are responsible for releasing it
  valk_arc_box *box = task->arg;

  valk_aio_http_server *srv = box->item;
  // Initialize the listener handle
  srv->listener = (void *)valk_slab_aquire(sys->handleSlab)->data;

  memset(srv->listener, 0, sizeof(valk_aio_handle_t));
  srv->listener->kind = VALK_HNDL_TCP;
  srv->listener->sys = sys;
  srv->listener->arg = srv;
  srv->listener->onClose = __http_shutdown_cb;
  srv->listener->uv.tcp.data = srv->listener;

  r = uv_tcp_init(srv->sys->eventloop, &srv->listener->uv.tcp);
  uv_tcp_nodelay(&srv->listener->uv.tcp, 1);

  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Tcp init error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on TcpInit");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  r = uv_ip4_addr(srv->interface, srv->port, &addr);
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Get addr error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Addr");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }
#ifdef __linux__
  r = uv_tcp_bind(&srv->listener->uv.tcp, (const struct sockaddr *)&addr,
                  UV_TCP_REUSEPORT);
#else
  r = uv_tcp_bind(&srv->listener->uv.tcp, (const struct sockaddr *)&addr, 0);
#endif
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Bind error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Bind");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  r = uv_listen((uv_stream_t *)&srv->listener->uv.tcp, 128,
                __http_server_accept_cb);
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("Listen error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Listening");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  VALK_INFO("Listening on %s:%d", srv->interface, srv->port);
  valk_promise_respond(&task->promise, box);
  valk_dll_insert_after(&sys->liveHandles, srv->listener);
  valk_arc_release(box);
}

static int __alpn_select_proto_cb(SSL *ssl, const unsigned char **out,
                                  unsigned char *outlen,
                                  const unsigned char *in, unsigned int inlen,
                                  void *arg) {
  UNUSED(ssl);
  UNUSED(arg);

  int rv;
  rv = nghttp2_select_alpn(out, outlen, in, inlen);
  if (rv == -1) {
    return SSL_TLSEXT_ERR_NOACK;
  }
  return SSL_TLSEXT_ERR_OK;
}

static void __uv_task_close_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  valk_aio_task_new *task = hndl->arg;

  // Release the future reference held by the task
  valk_arc_release(task->promise.item);

  // Free using the original allocator captured at allocation time
  valk_mem_allocator_free(task->allocator, task);

  // Now release the handle
  valk_dll_pop(hndl);
  valk_slab_release_ptr(hndl->sys->handleSlab, hndl);
}

static void __uv_task_cb_new(uv_async_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  valk_aio_task_new *task = hndl->arg;

  task->callback(hndl->sys, task);

  // Close the UV handle - cleanup will happen in the close callback
  uv_close((uv_handle_t *)&hndl->uv.task, __uv_task_close_cb);
}

static void __uv_exec_task(valk_aio_system_t *sys, valk_aio_task_new *task) {
  valk_aio_handle_t *hndl =
      (valk_aio_handle_t *)valk_slab_aquire(sys->handleSlab)->data;
  memset(hndl, 0, sizeof(valk_aio_handle_t));
  hndl->kind = VALK_HNDL_TASK;
  hndl->sys = sys;
  hndl->arg = task;
  hndl->uv.task.data = hndl;

  uv_async_init(sys->eventloop, &hndl->uv.task, __uv_task_cb_new);
  valk_dll_insert_after(&sys->liveHandles, hndl);

  uv_async_send(&hndl->uv.task);
}

static void __valk_aio_http2_server_free(valk_arc_box *box) {
  printf("FREERDOM\n");
  valk_aio_http_server *srv = box->item;
  SSL_CTX_free(srv->ssl_ctx);
  valk_mem_allocator_free(box->allocator, box);
}

// static void __no_free(void *arg) { UNUSED(arg); }
valk_future *valk_aio_http2_listen(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler) {
  valk_arc_box *box = (valk_arc_box *)valk_slab_aquire(sys->httpServers)->data;
  valk_future *res = valk_future_new();

  valk_aio_http_server *srv;
  {
    valk_arc_box_init(box, VALK_SUC, sizeof(valk_aio_http_server));

    box->allocator = (valk_mem_allocator_t *)sys->httpServers;
    box->free = __valk_aio_http2_server_free;

    srv = box->item;
    memset(srv, 0, sizeof(valk_aio_http_server));
    srv->sys = sys;

    // srv->interface = strdup(interface);
    strncpy(srv->interface, interface, 200);
    srv->port = port;
    // handler struct is already zeroed by memset above, so just copy if provided
    if (handler) {
      srv->handler = *handler;  // Copy C handler struct
    }
    srv->lisp_handler_fn = (valk_lval_t*)lisp_handler;  // Set Lisp handler
    // Create sandbox env once at startup - wraps handler's captured env
    // This shadows 'def' to prevent global state mutation from request handlers
    if (lisp_handler) {
      srv->sandbox_env = valk_lenv_sandboxed(((valk_lval_t*)lisp_handler)->fun.env);
    }
    valk_aio_ssl_server_init(&srv->ssl_ctx, keyfile, certfile);
    SSL_CTX_set_alpn_select_cb(srv->ssl_ctx, __alpn_select_proto_cb, NULL);
  }

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  task->arg = box;
  task->promise.item = res;
  valk_arc_retain(res);
  task->callback = __http_listen_cb;

  __uv_exec_task(sys, task);

  return res;
}

void valk_aio_http2_server_set_handler(valk_aio_http_server *srv, void *handler_fn) {
  srv->lisp_handler_fn = (valk_lval_t*)handler_fn;
  // Create sandbox env once - wraps handler's captured env to shadow 'def'
  if (handler_fn) {
    srv->sandbox_env = valk_lenv_sandboxed(((valk_lval_t*)handler_fn)->fun.env);
  }
}

//// HTTP2 CLIENT

typedef struct valk_aio_http2_client {
  valk_aio_system_t *sys;
  SSL_CTX *ssl_ctx;
  // TODO(networking):  connections could be pooled
  valk_aio_http_conn *connection;
  char interface[200];
  int port;
  // Hostname used for TLS SNI and HTTP/2 authority defaults
  char hostname[200];
  // Totally internal, totally unneccessary, but i wanna avoid a tuple
  valk_promise _promise;
} valk_aio_http2_client;

static int __http_client_on_frame_recv_callback(nghttp2_session *session,
                                                const nghttp2_frame *frame,
                                                void *user_data) {
  UNUSED(session);
  UNUSED(user_data);

  VALK_TRACE("on_recv callback");

  switch (frame->hd.type) {
    case NGHTTP2_HEADERS:
      break;
    case NGHTTP2_RST_STREAM:
      VALK_INFO("C <--- S (RST_STREAM) stream=%d error=%d", frame->hd.stream_id,
               frame->rst_stream.error_code);
      break;
    case NGHTTP2_GOAWAY:
      VALK_INFO("C <--- S (GOAWAY) %d", frame->hd.stream_id);
      VALK_INFO("Client received GOAWAY");
      break;
  }

  return 0;
}

static int __http_client_on_stream_close_callback(nghttp2_session *session,
                                                  int32_t stream_id,
                                                  uint32_t error_code,
                                                  void *user_data) {
  UNUSED(user_data);
  __http2_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (reqres) {
    if (error_code != NGHTTP2_NO_ERROR) {
      // Stream was reset or closed with an error - reject the promise
      char errmsg[256];
      snprintf(errmsg, sizeof(errmsg), "HTTP/2 stream error: %s (code=%u)",
               nghttp2_http2_strerror(error_code), error_code);
      valk_arc_box *err = valk_arc_box_err(errmsg);
      valk_promise_respond(&reqres->promise, err);
      valk_arc_release(err);
    } else {
      // Normal close - resolve with the response (even if no DATA arrived)
      valk_arc_box *box = ((valk_arc_box *)reqres->res) - 1;
      valk_promise_respond(&reqres->promise, box);
    }
    valk_arc_release(reqres->promise.item);
    // Free the reqres struct itself
    valk_mem_free(reqres);
  }
  return 0;
}

static int __http_on_data_chunk_recv_callback(nghttp2_session *session,
                                              uint8_t flags, int32_t stream_id,
                                              const uint8_t *data, size_t len,
                                              void *user_data) {
  (void)flags;
  (void)user_data;

  __http2_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, stream_id);

  if (reqres) {
    VALK_INFO("C <--- S (DATA chunk) len=%lu", (unsigned long)len);
    size_t offset = reqres->res->bodyLen;
    VALK_ASSERT((offset + len) < reqres->res->bodyCapacity,
                "Response was too big %ld > %ld", offset + len,
                reqres->res->bodyCapacity);
    // Append into body buffer
    memcpy((char *)reqres->res->body + offset, data, len);
    reqres->res->bodyLen = offset + len;
    ((char *)reqres->res->body)[reqres->res->bodyLen] = '\0';
  }

  return 0;
}

static void __uv_http2_connect_cb(uv_connect_t *req, int status) {
  valk_arc_box *box = req->data;
  // TODO(networking): assert that its a succefull box
  valk_aio_http2_client *client = box->item;
  valk_arc_retain(box);

  if (status < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Client Connection err: %s\n", uv_strerror(status));
    valk_arc_box *err = valk_arc_box_err("Client Connection err");
    valk_promise_respond(&client->_promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }

  printf("Gurr we connected\n");

  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_aquire(tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  static nghttp2_session_callbacks *callbacks = nullptr;
  if (!callbacks) {
    nghttp2_session_callbacks_new(&callbacks);
    /*

      nghttp2_session_callbacks_set_on_frame_recv_callback(callbacks,
                                                           on_frame_recv_callback);

      nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
        callbacks, on_data_chunk_recv_callback);

      nghttp2_session_callbacks_set_on_stream_close_callback(
        callbacks, on_stream_close_callback);

      nghttp2_session_callbacks_set_on_header_callback(callbacks,
                                                       on_header_callback);

      nghttp2_session_callbacks_set_on_begin_headers_callback(
        callbacks, on_begin_headers_callback);
          */

    // nghttp2_session_callbacks_set_on_begin_headers_callback(
    //     callbacks, __http_on_begin_headers_callback);
    nghttp2_session_callbacks_set_on_header_callback(
        callbacks, __http2_client_on_header_cb);
    nghttp2_session_callbacks_set_on_frame_recv_callback(
        callbacks, __http_client_on_frame_recv_callback);

    nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
        callbacks, __http_on_data_chunk_recv_callback);
    nghttp2_session_callbacks_set_on_stream_close_callback(
        callbacks, __http_client_on_stream_close_callback);
  }

  nghttp2_session_client_new(&client->connection->session, callbacks, client);

  __http_send_client_connection_header(client->connection->session);

  valk_aio_ssl_client_init(&client->ssl_ctx);
  SSL_CTX_set_alpn_protos(client->ssl_ctx, (const unsigned char *)"\x02h2", 3);

  valk_aio_ssl_connect(&client->connection->ssl, client->ssl_ctx);
  const char *sni = (client->hostname[0] != '\0') ? client->hostname : "localhost";
  SSL_set_tlsext_host_name(client->connection->ssl.ssl, sni);

  valk_aio_ssl_handshake(&client->connection->ssl, &Out);

  int wantToSend = Out.count > 0;
  if (wantToSend) {
    slabItem->buf.base = Out.items;
    slabItem->buf.len = Out.count;

    printf("[Client] Sending %ld bytes\n", Out.count);
    uv_write(&slabItem->req, (uv_stream_t *)&client->connection->handle->uv.tcp,
             &slabItem->buf, 1, __http_tcp_on_write_cb);
  } else {
    valk_slab_release_ptr(tcp_buffer_slab, slabItem);
  }

  // After handshake, flush any pending HTTP/2 frames (client preface, SETTINGS,
  // or requests submitted before handshake completion).
  if (SSL_is_init_finished(client->connection->ssl.ssl)) {
    char inbuf[SSL3_RT_MAX_PACKET_SIZE];
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memset(inbuf, 0, sizeof(inbuf));
    valk_buffer_t In = {
        .items = inbuf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

    __tcp_buffer_slab_item_t *slab2 =
        (void *)valk_slab_aquire(tcp_buffer_slab)->data;
    valk_buffer_t Out2 = {.items = slab2->data,
                          .count = 0,
                          .capacity = SSL3_RT_MAX_PACKET_SIZE};

    __http2_flush_frames(&In, client->connection);
    valk_aio_ssl_encrypt(&client->connection->ssl, &In, &Out2);

    if (Out2.count > 0) {
      slab2->buf.base = Out2.items;
      slab2->buf.len = Out2.count;
      uv_write(&slab2->req, (uv_stream_t *)&client->connection->handle->uv.tcp,
               &slab2->buf, 1, __http_tcp_on_write_cb);
    } else {
      valk_slab_release_ptr(tcp_buffer_slab, slab2);
    }
  }

  uv_read_start((uv_stream_t *)&client->connection->handle->uv.tcp,
                __alloc_callback, __http_tcp_read_cb);

  printf("Finished initializing client %p\n", (void *)client);

  // Shits connected but not fully established, it will buffer any requests tho
  // releases the promise
  valk_promise_respond(&client->_promise, box);
  valk_arc_release(box);
}

static void __aio_client_connect_cb(valk_aio_system_t *sys,
                                    valk_aio_task_new *task) {
  int r;
  struct sockaddr_in addr;

  valk_arc_box *box = task->arg;
  valk_aio_http2_client *client = box->item;

  client->connection = malloc(sizeof(valk_aio_http_conn));
  VALK_ASSERT(client->connection != NULL,
              "Client connection must be allocated");
  memset(client->connection, 0, sizeof(valk_aio_http_conn));

  client->connection->handle =
      (valk_aio_handle_t *)valk_slab_aquire(sys->handleSlab)->data;
  memset(client->connection->handle, 0, sizeof(valk_aio_handle_t));

  client->connection->handle->kind = VALK_HNDL_TCP;
  client->connection->handle->sys = sys;
  client->connection->handle->arg = client->connection;
  // client->connection->handle->onClose = nullptr;
  client->connection->handle->onClose = __valk_aio_http2_on_disconnect;
  client->connection->handle->uv.tcp.data = client->connection->handle;

  // activate the handle
  valk_dll_insert_after(&sys->liveHandles, client->connection->handle);

  r = uv_tcp_init(sys->eventloop, &client->connection->handle->uv.tcp);

  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "TcpInit err: %s \n", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("TcpInit err");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }

  uv_tcp_nodelay(&client->connection->handle->uv.tcp, 1);

  // Try numeric IPv4 first; if it fails, resolve hostname.
  r = uv_ip4_addr(client->interface, client->port, &addr);
  if (r) {
    struct addrinfo hints, *res = NULL;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    char portstr[16];
    snprintf(portstr, sizeof portstr, "%d", client->port);
    int gai = getaddrinfo(client->interface, portstr, &hints, &res);
    if (gai == 0 && res) {
      memcpy(&addr, res->ai_addr, sizeof(struct sockaddr_in));
      freeaddrinfo(res);
    } else {
      if (res) freeaddrinfo(res);
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      fprintf(stderr, "Addr resolve err: %s\n", gai_strerror(gai));
      valk_arc_box *err = valk_arc_box_err("Addr err");
      valk_promise_respond(&task->promise, err);
      valk_arc_release(err);
      valk_arc_release(box);
      return;
    }
  }

  client->connection->req.data = box;
  client->_promise = task->promise;
  uv_tcp_connect(&client->connection->req, &client->connection->handle->uv.tcp,
                 (const struct sockaddr *)&addr, __uv_http2_connect_cb);
}

static void __valk_aio_http2_client_free(valk_arc_box *box) {
  printf("FREERDOM2 -> the client edition\n");
  valk_aio_http2_client *client = box->item;
  SSL_CTX_free(client->ssl_ctx);
  valk_mem_allocator_free(box->allocator, box);
}

valk_future *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                         const char *ip, const int port,
                                         const char *hostname) {

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  valk_future *res = valk_future_new();
  valk_arc_box *box = valk_arc_box_new(VALK_SUC, sizeof(valk_aio_http2_client));
  box->free = __valk_aio_http2_client_free;

  task->arg = box;
  memset(box->item, 0, sizeof(valk_aio_http2_client));

  valk_aio_http2_client *client = box->item;
  // Store IP for uv connect
  strncpy(client->interface, ip, sizeof(client->interface) - 1);
  client->interface[sizeof(client->interface) - 1] = '\0';
  // Store hostname for SNI
  if (hostname) {
    strncpy(client->hostname, hostname, sizeof(client->hostname) - 1);
    client->hostname[sizeof(client->hostname) - 1] = '\0';
  } else {
    client->hostname[0] = '\0';
  }
  client->sys = sys;
  client->port = port;

  task->promise.item = res;
  valk_arc_retain(res);
  task->callback = __aio_client_connect_cb;

  VALK_DEBUG("Initializing client %p", (void *)client);
  __uv_exec_task(sys, task);

  return res;
}

valk_future *valk_aio_http2_connect(valk_aio_system_t *sys,
                                    const char *interface, const int port,
                                    const char *certfile) {
  UNUSED(certfile);
  // Backward-compatible connect that uses provided interface and defaults SNI
  return valk_aio_http2_connect_host(sys, interface, port, "localhost");
}

static void __http2_submit_demo_request_cb(valk_aio_system_t *sys,
                                           struct valk_aio_task_new *task) {
  UNUSED(sys);

  valk_arc_box *box = task->arg;
  valk_aio_http2_client *client = box->item;

  VALK_DEBUG("Constructing request on client %p", (void *)client);
  valk_aio_http_conn *conn = client->connection;

  int32_t stream_id;
  // http2_stream_data *stream_data = session_data->stream_data;
  // const char *uri = "local/";
  // const struct http_parser_url *u = stream_data->u;

  nghttp2_nv hdrs[] = {MAKE_NV2(":method", "GET"), MAKE_NV2(":scheme", "https"),
                       MAKE_NV2(":authority", "google.com"),
                       // stream_data->authoritylen),
                       MAKE_NV2(":path", "/")};
  // fprintf(stderr, "Request headers:\n");
  // print_headers(stderr, hdrs, ARRLEN(hdrs));

  // TODO(networking): Allocating this promise here temporarily, ideally need to
  // be passing a request object with a promise on it
  valk_promise *prom = valk_mem_alloc(sizeof(valk_promise));
  // valk_mem_free(sizeof(valk_promise)); in callback to nghttp2 recv
  *prom = task->promise;  // copy this shit

  stream_id =
      nghttp2_submit_request2(conn->session, nullptr, hdrs,
                              sizeof(hdrs) / sizeof(hdrs[0]), nullptr, prom);

  if (stream_id < 0) {
    VALK_ERROR("Could not submit HTTP request: %s", nghttp2_strerror(stream_id));
    valk_arc_box *err = valk_arc_box_err("Could not submit HTTP request");
    valk_promise_respond(prom, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_mem_free(prom);
    return;
  }

  VALK_INFO("Submitted request stream_id=%d", stream_id);

  char buf[SSL3_RT_MAX_PACKET_SIZE];
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memset(buf, 0, sizeof(buf));
  valk_buffer_t In = {
      .items = buf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};
  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_aquire(tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  // Only write stuff if ssl is established
  if (SSL_is_init_finished(client->connection->ssl.ssl)) {
    __http2_flush_frames(&In, conn);

    // Encrypt the new data n stuff
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);

    int wantToSend = Out.count > 0;
    if (wantToSend) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;

      printf("Sending %ld bytes\n", Out.count);
      uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
               &slabItem->buf, 1, __http_tcp_on_write_cb);
    } else {
      printf("Nothing to send %d \n", wantToSend);
      valk_slab_release_ptr(tcp_buffer_slab, slabItem);
    }
  }

  valk_arc_release(box);
  // return stream_id;
}

static valk_future *__http2_submit_demo_request(valk_aio_system_t *sys,
                                                valk_arc_box *client) {
  valk_future *res = valk_future_new();
  valk_arc_retain(client);
  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  task->arg = client;
  valk_arc_retain(res);
  task->promise.item = res;
  task->callback = __http2_submit_demo_request_cb;

  // valk_arc_release(client); in callback
  // valk_arc_release(res); in resolve
  __uv_exec_task(sys, task);
  return res;
}

char *valk_client_demo(valk_aio_system_t *sys, const char *domain,
                       const char *port) {
  UNUSED(port);
  // Demo: connect to Google over HTTP/2 TLS using a known IPv4 and SNI
  (void)domain; // future: parse/use
  valk_future *fut =
      valk_aio_http2_connect_host(sys, "142.250.191.78", 443, "google.com");
  printf("Arc count of fut : %ld\n", fut->refcount);
  valk_arc_box *client = valk_future_await(fut);
  printf("Arc count of fut : %ld\n", fut->refcount);
  // valk_arc_release(fut);
  // printf("Arc count of fut : %d\n", fut->refcount);

  VALK_ASSERT(client->type == VALK_SUC, "Error creating client: %s",
              (char *)client->item);

  // valk_arc_trace_report_print(fut);
  valk_arc_release(fut);

  fut = __http2_submit_demo_request(sys, client);
  valk_arc_box *response = valk_future_await(fut);
  // future release is gonna eat that shit for breakfast
  valk_arc_retain(response);
  valk_arc_release(fut);
  // valk_arc_trace_report_print(fut);
  // valk_arc_trace_report_print(response);

  VALK_ASSERT(response->type == VALK_SUC, "Error from the response: %s",
              (char *)response->item);

  printf("Got response %s\n", (char *)response->item);
  char *res = strdup(response->item);

  valk_arc_release(response);
  valk_arc_release(client);

  return res;
}

static void __valk_aio_http2_request_send_cb(valk_aio_system_t *sys,
                                             struct valk_aio_task_new *task) {
  UNUSED(sys);
  __valk_request_client_pair_t *pair = task->arg;

  // TODO(networking): Allocating this promise here temporarily, ideally need
  // to be passing a request object with a promise on it
  // the reason its not done on the arena, is because it will be freed by a
  // callback
  valk_aio_http2_client *client = pair->client;
  VALK_INFO("Client ready: %s:%d", client->interface, client->port);
  VALK_DEBUG("req: %s%s", pair->req->authority, pair->req->path);

  VALK_DEBUG("Constructing request on client %p", (void *)client);
  valk_aio_http_conn *conn = client->connection;

  // Allocate request/response context using malloc (event loop thread allocator)
  __http2_req_res_t *reqres = valk_mem_alloc(sizeof(__http2_req_res_t));
  reqres->req = pair->req;
  reqres->promise = task->promise;

  // Allocate and initialize response using malloc allocator
  // (must match event loop thread where headers/body will be populated)
  valk_arc_box *box =
      valk_arc_box_new(VALK_SUC, sizeof(valk_http2_response_t));
  box->free = __valk_http2_response_free;

  reqres->res = box->item;
  memset(reqres->res, 0, sizeof(valk_http2_response_t));
  da_init(&reqres->res->headers);

  reqres->res->body = valk_mem_alloc(HTTP_MAX_RESPONSE_SIZE_BYTES);
  reqres->res->bodyLen = 0;
  reqres->res->bodyCapacity = HTTP_MAX_RESPONSE_SIZE_BYTES;

  VALK_TRACE("Box: %p, item: %p", (void*)box, reqres->res);

  // Build HTTP/2 headers from request (use request allocator for reading)
  VALK_WITH_ALLOC(pair->req->allocator) {
    // HTTP/2 requires these 4 pseudo-headers
    const size_t NUM_PSEUDO_HEADERS = 4;
    size_t hdrCount = pair->req->headers.count + NUM_PSEUDO_HEADERS;
    struct valk_http2_header_t *phds = pair->req->headers.items;

    nghttp2_nv hdrs[hdrCount];

    hdrs[0].name = (uint8_t *)":method";
    hdrs[0].value = (uint8_t *)pair->req->method;
    hdrs[0].namelen = sizeof(":method") - 1;
    hdrs[0].valuelen = strlen(pair->req->method);
    hdrs[0].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[1].name = (uint8_t *)":scheme";
    hdrs[1].value = (uint8_t *)pair->req->scheme;
    hdrs[1].namelen = sizeof(":scheme") - 1;
    hdrs[1].valuelen = strlen(pair->req->scheme);
    hdrs[1].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[2].name = (uint8_t *)":authority";
    hdrs[2].value = (uint8_t *)pair->req->authority;
    hdrs[2].namelen = sizeof(":authority") - 1;
    hdrs[2].valuelen = strlen(pair->req->authority);
    hdrs[2].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[3].name = (uint8_t *)":path";
    hdrs[3].value = (uint8_t *)pair->req->path;
    hdrs[3].namelen = sizeof(":path") - 1;
    hdrs[3].valuelen = strlen(pair->req->path);
    hdrs[3].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    // Add custom headers from the request
    for (size_t i = 0; i < pair->req->headers.count; ++i) {
      hdrs[NUM_PSEUDO_HEADERS + i].name = phds[i].name;
      hdrs[NUM_PSEUDO_HEADERS + i].value = phds[i].value;
      hdrs[NUM_PSEUDO_HEADERS + i].namelen = phds[i].nameLen;
      hdrs[NUM_PSEUDO_HEADERS + i].valuelen = phds[i].valueLen;
      hdrs[NUM_PSEUDO_HEADERS + i].flags =
          NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;
    }

    reqres->streamid = nghttp2_submit_request2(conn->session, nullptr, hdrs,
                                               hdrCount, nullptr, reqres);

    if (reqres->streamid < 0) {
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      VALK_ERROR("Could not submit HTTP request: %s",
                 nghttp2_strerror(reqres->streamid));
      valk_arc_box *err = valk_arc_box_err("Could not submit HTTP request");
      valk_promise_respond(&task->promise, err);
      valk_arc_release(err);
      // valk_arc_release(task->promise.item);
      return;
    }

    reqres->res->stream_id = reqres->streamid;
    VALK_INFO("Submitted request stream_id=%ld", reqres->streamid);
  }

  // Not request allocated... its connection allocated. Event though technically
  // the buffer could be part of the request maybe
  char buf[SSL3_RT_MAX_PACKET_SIZE];
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memset(buf, 0, sizeof(buf));
  valk_buffer_t In = {
      .items = buf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};
  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_aquire(tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  // Only write stuff if ssl is established
  if (SSL_is_init_finished(client->connection->ssl.ssl)) {
    __http2_flush_frames(&In, conn);

    // Encrypt the new data n stuff
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);

    int wantToSend = Out.count > 0;
    if (wantToSend) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;

      printf("Sending %ld bytes\n", Out.count);
      uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
               &slabItem->buf, 1, __http_tcp_on_write_cb);
    } else {
      printf("Nothing to send %d \n", wantToSend);
      valk_slab_release_ptr(tcp_buffer_slab, slabItem);
    }
  }
}

valk_future *valk_aio_http2_request_send(valk_http2_request_t *req,
                                         valk_aio_http2_client *client) {
  printf("Client's ready to go : %s: %d :: %p\n", client->interface,
         client->port, (void *)client);
  valk_future *res;
  valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)client->sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  task->allocator = (valk_mem_allocator_t *)client->sys->handleSlab;

  VALK_WITH_ALLOC(req->allocator) {
    res = valk_future_new();
    __valk_request_client_pair_t *pair =
        valk_mem_alloc(sizeof(__valk_request_client_pair_t));

    pair->client = client;
    pair->req = req;

    task->arg = pair;
    task->promise.item = res;
    valk_arc_retain(res);
    task->callback = __valk_aio_http2_request_send_cb;
    printf("Client's NOT ready to go : %s: %d :: %p :: %p\n",
           pair->client->interface, pair->client->port, (void *)pair->client,
           (void *)__valk_aio_http2_request_send_cb);
  }
  __uv_exec_task(client->sys, task);
  return res;
}

//
valk_aio_system_t *valk_aio_start() {
  // Singleton guard: check if AIO system is already running
  if (global_aio_system != NULL) {
    VALK_WARN("AIO system already started - returning existing instance. "
              "Multiple AIO systems are not supported and can cause race conditions.");
    return global_aio_system;
  }

  // On linux definitely turn sigpipe off
  // Otherwise ''hit crashes.
  // When the socket dissapears a write may be queued in the event loop
  // In that case we just want to do proper error handling without the
  // signal
  // Simpler portable ignore of SIGPIPE to avoid crashes on broken pipe
  signal(SIGPIPE, SIG_IGN);

  valk_aio_system_t *sys = valk_mem_alloc(sizeof(valk_aio_system_t));
  global_aio_system = sys;  // Store singleton reference

  valk_aio_ssl_start();

  sys->eventloop = uv_default_loop();

  sys->liveHandles.kind = VALK_HNDL_EMPTY;
  memset(&sys->liveHandles, 0, sizeof(valk_aio_handle_t));

  // Allocate AIO slabs with malloc allocator (not GC heap)
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    sys->httpServers = valk_slab_new(
        sizeof(valk_arc_box) + sizeof(valk_aio_http_server), HTTP_MAX_SERVERS);
    sys->httpClients = valk_slab_new(
        sizeof(valk_arc_box) + sizeof(valk_aio_http2_client), HTTP_MAX_CLIENTS);
    sys->handleSlab = valk_slab_new(sizeof(valk_aio_handle_t), AIO_MAX_HANDLES);
  }

  // Initialize HTTP request/response queues for Lisp handlers
  #define HTTP_QUEUE_CAPACITY 256
  sys->http_queue.request_items = malloc(sizeof(valk_http_request_item_t) * HTTP_QUEUE_CAPACITY);
  sys->http_queue.request_idx = 0;
  sys->http_queue.request_count = 0;
  sys->http_queue.request_capacity = HTTP_QUEUE_CAPACITY;
  pthread_mutex_init(&sys->http_queue.request_mutex, NULL);
  pthread_cond_init(&sys->http_queue.request_ready, NULL);

  sys->http_queue.response_items = malloc(sizeof(valk_http_response_item_t) * HTTP_QUEUE_CAPACITY);
  sys->http_queue.response_idx = 0;
  sys->http_queue.response_count = 0;
  sys->http_queue.response_capacity = HTTP_QUEUE_CAPACITY;
  pthread_mutex_init(&sys->http_queue.response_mutex, NULL);
  pthread_cond_init(&sys->http_queue.response_ready, NULL);

#ifdef VALK_METRICS_ENABLED
  valk_aio_metrics_init(&sys->metrics);
#endif

  // printf("Aquiring stopper\n");
  sys->stopperHandle = (valk_aio_handle_t *)valk_slab_aquire(sys->handleSlab)->data;
  memset(sys->stopperHandle, 0, sizeof(valk_aio_handle_t));
  sys->stopperHandle->kind = VALK_HNDL_TASK;
  sys->stopperHandle->sys = sys;
  sys->stopperHandle->uv.task.data = sys->stopperHandle;
  uv_async_init(sys->eventloop, &sys->stopperHandle->uv.task, __aio_uv_stop);
  valk_dll_insert_after(&sys->liveHandles, sys->stopperHandle);

  int status = uv_thread_create(&sys->loopThread, __event_loop, sys);
  if (status) {
    perror("pthread_create");
  }
  return sys;
}

void valk_aio_stop(valk_aio_system_t *sys) {
  uv_async_send(&sys->stopperHandle->uv.task);
  // printf("Processing the stopper\n");
  // fflush(stdout);
  uv_thread_join(&sys->loopThread);
  // printf("AFTER the Processing the stopper\n");
  // fflush(stdout);
  // while (UV_EBUSY == uv_loop_close(sys->eventloop)) {
  // };
  // TODO(networking): need to properly free the system too
  // Slabs were allocated with malloc allocator, so free with malloc allocator
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    valk_slab_free(sys->httpServers);
    valk_slab_free(sys->httpClients);
    valk_slab_free(sys->handleSlab);
  }

  // Reset singleton so AIO can be restarted if needed
  if (global_aio_system == sys) {
    global_aio_system = NULL;
  }

  // printf("Freeing sys\n");
  // fflush(stdout);
  valk_mem_free(sys);
  // printf("Done freeing\n");
  // fflush(stdout);
}

#ifdef VALK_METRICS_ENABLED
// Get metrics from AIO system
valk_aio_metrics_t* valk_aio_get_metrics(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return &sys->metrics;
}
#endif

// reference code for openssl setup
//
static void __valk_http2_response_free(valk_arc_box *box) {
  valk_http2_response_t *res = box->item;
  if (res) {
    if (res->body) free(res->body);
    if (res->status) free((void *)res->status);
    if (res->headers.items) {
      for (size_t i = 0; i < res->headers.count; ++i) {
        if (res->headers.items[i].name) free(res->headers.items[i].name);
        if (res->headers.items[i].value) free(res->headers.items[i].value);
      }
      free(res->headers.items);
    }
  }
  valk_mem_allocator_free(box->allocator, box);
}
// https://github.com/darrenjs/openssl_examples
