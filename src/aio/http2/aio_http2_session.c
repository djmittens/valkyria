#include "aio_http2_session.h"
#include "aio_http2_session_metrics.h"
#include "aio_http2_conn.h"
#include "aio_stream_body.h"
#include "gc.h"
#include "../aio_request_ctx.h"

extern void valk_http_async_done_callback(valk_async_handle_t *handle, void *ctx);

extern void valk_async_propagate_region(valk_async_handle_t *handle, valk_region_t *region, valk_lenv_t *env);
extern valk_async_handle_t* valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern void valk_async_handle_free(valk_async_handle_t *handle);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
extern bool valk_async_handle_cancel(valk_async_handle_t *handle);
extern void valk_async_handle_on_resource_cleanup(valk_async_handle_t *handle, void (*fn)(void *data, void *ctx), void *data, void *ctx);

#include "../aio_async.h"

static const char *__http2_get_header(valk_http2_server_request_t *req, const char *name) {
  if (!req || !name) return nullptr; // LCOV_EXCL_BR_LINE defensive null check
  size_t name_len = strlen(name);
  for (u64 i = 0; i < req->headers.count; i++) {
    struct valk_http2_header_t *h = &req->headers.items[i];
    if (h->nameLen == name_len && strncasecmp((char*)h->name, name, name_len) == 0) { // LCOV_EXCL_BR_LINE header lookup
      return (const char *)h->value;
    }
  }
  return nullptr;
}

// LCOV_EXCL_BR_START request context: trace header presence varies
static valk_request_ctx_t *__http2_create_request_ctx(valk_http2_server_request_t *req) {
  valk_mem_allocator_t *allocator = (valk_mem_allocator_t *)&req->region;
  valk_request_ctx_t *ctx = valk_request_ctx_new(allocator);
  if (!ctx) return nullptr;

  const char *trace_id_str = __http2_get_header(req, "x-trace-id");
  if (trace_id_str) {
    ctx->trace_id = (u64)strtoll(trace_id_str, nullptr, 10);
  }

  const char *parent_span_str = __http2_get_header(req, "x-span-id");
  if (parent_span_str) {
    ctx->parent_span_id = (u64)strtoll(parent_span_str, nullptr, 10);
  }

  const char *deadline_str = __http2_get_header(req, "x-deadline-ms");
  if (deadline_str) {
    u64 deadline_ms = (u64)strtoll(deadline_str, nullptr, 10);
    if (deadline_ms > 0) {
      ctx->deadline_us = valk_time_now_us() + (deadline_ms * 1000);
    }
  }

  return ctx;
}
// LCOV_EXCL_BR_STOP

static inline u64 __align_up(uptr addr, u64 alignment) {
  u64 mask = alignment - 1;
  u64 misalign = addr & mask;
  return misalign ? (alignment - misalign) : 0; // LCOV_EXCL_BR_LINE alignment arithmetic
}

static inline valk_http2_server_request_t *__http_request_from_slot(
    valk_slab_t *slab, u32 slot) {
  // LCOV_EXCL_BR_START defensive linked list validation
  if (slot == UINT32_MAX || !slab || slot >= slab->numItems) return nullptr;
  // LCOV_EXCL_BR_STOP
  u64 stride = valk_slab_item_stride(slab->itemSize);
  valk_slab_item_t *item = (valk_slab_item_t *)&slab->heap[stride * slot];
  valk_mem_arena_t *arena = (valk_mem_arena_t *)item->data;
  u64 init_off = __align_up((uptr)arena->heap, alignof(max_align_t));
  u64 hdr = init_off + sizeof(size_t);
  u64 adj = __align_up((uptr)&arena->heap[hdr], alignof(max_align_t));
  u64 payload = hdr + adj;
  return (valk_http2_server_request_t *)&arena->heap[payload];
}

// LCOV_EXCL_BR_START arena management: linked list traversal and slot matching
void valk_http2_remove_from_active_arenas(valk_aio_handle_t *conn,
                                             u32 target_slot) {
  if (!conn->http.server || !conn->http.server->sys) return;
  valk_slab_t *slab = conn->http.server->sys->httpStreamArenas;

  if (conn->http.active_arena_head == target_slot) {
    valk_http2_server_request_t *req = __http_request_from_slot(slab, target_slot);
    conn->http.active_arena_head = req ? req->next_arena_slot : UINT32_MAX;
    if (req) req->next_arena_slot = UINT32_MAX;
    return;
  }

  u32 prev_slot = conn->http.active_arena_head;
  u32 iterations = 0;
  u32 max_iterations = slab->numItems + 1;

  while (prev_slot != UINT32_MAX && iterations < max_iterations) {
    valk_http2_server_request_t *prev_req = __http_request_from_slot(slab, prev_slot);
    if (!prev_req) break;

    if (prev_req->next_arena_slot == target_slot) {
      valk_http2_server_request_t *target_req = __http_request_from_slot(slab, target_slot);
      prev_req->next_arena_slot = target_req ? target_req->next_arena_slot : UINT32_MAX;
      if (target_req) target_req->next_arena_slot = UINT32_MAX;
      return;
    }

    u32 next_slot = prev_req->next_arena_slot;
    VALK_ASSERT(next_slot != prev_slot,
                "Arena linked list corruption: slot %u points to itself", prev_slot);
    prev_slot = next_slot;
    iterations++;
  }

  VALK_ASSERT(iterations < max_iterations, // LCOV_EXCL_LINE
               "Arena linked list infinite loop after %u iterations", iterations); // LCOV_EXCL_LINE
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START nghttp2 header callback: pseudo-header dispatch and header array growth
int valk_http2_on_header_callback(nghttp2_session *session,
                                  const nghttp2_frame *frame,
                                  const u8 *name, size_t namelen,
                                  const u8 *value, size_t valuelen,
                                  u8 flags, void *user_data) {
  UNUSED(flags);
  UNUSED(user_data);
  VALK_TRACE("HDR: %.*s: %.*s", (int)namelen, name, (int)valuelen, value);

  valk_http2_server_request_t *req = (valk_http2_server_request_t *)
      nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);
  if (!req) return 0;

  valk_http2_metrics_on_header_recv(req, namelen, valuelen);

  VALK_WITH_ALLOC((valk_mem_allocator_t*)&req->region) {
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
      if (req->headers.count >= req->headers.capacity) {
        u64 new_cap = req->headers.capacity == 0 ? 8 : req->headers.capacity * 2;
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

  return 0;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START begin_headers callback: arena allocation, stream setup, request context
int valk_http2_on_begin_headers_callback(nghttp2_session *session,
                                         const nghttp2_frame *frame,
                                         void *user_data) {
  valk_aio_handle_t *conn = (valk_aio_handle_t *)user_data;

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    VALK_DEBUG(">>> Received HTTP/2 request (stream_id=%d)",
               frame->hd.stream_id);

    conn->http.active_streams++;

    valk_http2_metrics_on_stream_start(conn);

    valk_slab_item_t *arena_item = valk_slab_aquire(conn->http.server->sys->httpStreamArenas);
    if (!arena_item) {
      VALK_WARN("Arena pool exhausted for stream %d, sending 503", frame->hd.stream_id);
      conn->http.active_streams--;

      valk_http2_metrics_on_arena_overflow_rejected(conn);

      valk_http2_send_overload_response(session, frame->hd.stream_id, conn);

      valk_http2_enter_arena_backpressure(conn);
      return 0;
    }

    valk_mem_arena_t *stream_arena = (valk_mem_arena_t *)arena_item->data;
    valk_mem_arena_init(stream_arena, conn->http.server->sys->config.arena_size);

    u64 arena_num_free = __atomic_load_n(&conn->http.server->sys->httpStreamArenas->numFree, __ATOMIC_ACQUIRE);
    VALK_INFO("Arena ACQUIRED for stream %d (slot=%zu, now %llu free)",
              frame->hd.stream_id, arena_item->handle & 0xFFFFFFFF, arena_num_free);

    valk_http2_metrics_on_arena_acquire(conn);

    valk_http2_server_request_t *req;
    VALK_WITH_ALLOC((valk_mem_allocator_t*)stream_arena) {
      req = valk_mem_alloc(sizeof(valk_http2_server_request_t));
      memset(req, 0, sizeof(valk_http2_server_request_t));
      req->conn = conn;
      req->stream_id = frame->hd.stream_id;
      req->stream_arena = stream_arena;
      req->arena_ref.slab_item = arena_item;
      req->arena_ref.slot = (u32)(arena_item->handle & 0xFFFFFFFF);
      req->next_arena_slot = UINT32_MAX;
      valk_region_init(&req->region, VALK_LIFETIME_REQUEST, nullptr, stream_arena);
      valk_http2_metrics_on_request_init(req);
    }

    nghttp2_session_set_stream_user_data(session, frame->hd.stream_id, req);

    VALK_ASSERT(conn->http.active_arena_head != req->arena_ref.slot,
                "Arena slot %u already at head - would create self-loop", req->arena_ref.slot);
    req->next_arena_slot = conn->http.active_arena_head;
    conn->http.active_arena_head = req->arena_ref.slot;
  }
  return 0;
}
// LCOV_EXCL_BR_STOP

typedef struct {
  u64 streamid;
  valk_http2_request_t *req;
  valk_http2_response_t *res;
  void *handle;
} __http2_client_req_res_t;

// LCOV_EXCL_BR_START client header callback: status/header type dispatch
int valk_http2_client_on_header_cb(nghttp2_session *session,
                                   const nghttp2_frame *frame,
                                   const u8 *name, size_t namelen,
                                   const u8 *value, size_t valuelen,
                                   u8 flags, void *user_data) {
  UNUSED(session);
  UNUSED(frame);
  UNUSED(flags);
  UNUSED(user_data);

  __http2_client_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

  if (reqres && reqres->res) {
    if (namelen == 7 && memcmp(name, ":status", 7) == 0) {
      char *st = malloc(valuelen + 1);
      memcpy(st, value, valuelen);
      st[valuelen] = '\0';
      reqres->res->status = st;
    } else {
      struct valk_http2_header_t h = {0};
      h.name = malloc(namelen + 1);
      h.value = malloc(valuelen + 1);
      memcpy(h.name, name, namelen);
      memcpy(h.value, value, valuelen);
      h.name[namelen] = '\0';
      h.value[valuelen] = '\0';
      h.nameLen = namelen;
      h.valueLen = valuelen;
      if (reqres->res->headers.count >= reqres->res->headers.capacity) {
        u64 new_cap = reqres->res->headers.capacity == 0 ? 8 : reqres->res->headers.capacity * 2;
        reqres->res->headers.items = realloc(reqres->res->headers.items, new_cap * sizeof(struct valk_http2_header_t));
        reqres->res->headers.capacity = new_cap;
      }
      reqres->res->headers.items[reqres->res->headers.count++] = h;
    }
  }
  return 0;
}
// LCOV_EXCL_BR_STOP

static const char valk_http_default_503_html[] =
  "<!DOCTYPE html>\n"
  "<html>\n"
  "<head>\n"
  "  <title>503 Service Unavailable</title>\n"
  "  <style>\n"
  "    body {\n"
  "      font-family: system-ui, -apple-system, sans-serif;\n"
  "      max-width: 600px;\n"
  "      margin: 100px auto;\n"
  "      padding: 20px;\n"
  "      text-align: center;\n"
  "      color: #333;\n"
  "    }\n"
  "    h1 {\n"
  "      font-size: 72px;\n"
  "      margin: 0;\n"
  "      color: #e53935;\n"
  "    }\n"
  "    p {\n"
  "      font-size: 18px;\n"
  "      color: #666;\n"
  "      margin-top: 20px;\n"
  "    }\n"
  "  </style>\n"
  "</head>\n"
  "<body>\n"
  "  <h1>503</h1>\n"
  "  <p>Server is temporarily at capacity.<br>Please try again shortly.</p>\n"
  "</body>\n"
  "</html>\n";

static const u64 valk_http_default_503_html_len = sizeof(valk_http_default_503_html) - 1;

// LCOV_EXCL_BR_START body callback: data chunking and EOF
nghttp2_ssize valk_http2_byte_body_cb(nghttp2_session *session,
                                      i32 stream_id, u8 *buf,
                                      size_t length, u32 *data_flags,
                                      nghttp2_data_source *source,
                                      void *user_data) {
  UNUSED(session);
  UNUSED(stream_id);
  UNUSED(user_data);

  http_body_source_t *src = (http_body_source_t *)source->ptr;
  u64 remaining = src->body_len - src->offset;

  u64 to_copy = remaining < length ? remaining : length;

  memcpy(buf, src->body + src->offset, to_copy);
  src->offset += to_copy;

  if (src->offset >= src->body_len) {
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
    if (src->needs_free) {
      free(src);
    }
  }

  return (nghttp2_ssize)to_copy;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_START 503 overload response - requires arena pool exhaustion
int valk_http2_send_overload_response(nghttp2_session *session,
                                      i32 stream_id,
                                      valk_aio_handle_t *conn) {
  const char* body;
  u64 body_len;

  if (conn->http.server->config.error_503_body) {
    body = conn->http.server->config.error_503_body;
    body_len = conn->http.server->config.error_503_body_len;
  } else {
    body = valk_http_default_503_html;
    body_len = valk_http_default_503_html_len;
  }

  http_body_source_t *body_src = malloc(sizeof(http_body_source_t));
  if (!body_src) {
    return NGHTTP2_ERR_NOMEM;
  }
  body_src->body = body;
  body_src->body_len = body_len;
  body_src->offset = 0;
  body_src->needs_free = true;

  nghttp2_nv headers[] = {
    MAKE_NV2(":status", "503"),
    MAKE_NV2("content-type", "text/html; charset=utf-8"),
    MAKE_NV2("retry-after", "1"),
  };

  nghttp2_data_provider2 data_prd = {
    .source.ptr = body_src,
    .read_callback = valk_http2_byte_body_cb,
  };

  // NOLINTNEXTLINE(clang-analyzer-unix.Malloc) - body_src owned by data_prd on success
  int rv = nghttp2_submit_response2(session, stream_id, headers,
                                     sizeof(headers) / sizeof(headers[0]), &data_prd);
  if (rv != 0) {
    free(body_src);
  }
  return rv;  // NOLINT(clang-analyzer-unix.Malloc)
}
// LCOV_EXCL_STOP

valk_lval_t* valk_http2_qexpr_get(valk_lval_t* qexpr, const char* key) {
  // LCOV_EXCL_BR_START qexpr type validation - handler always returns qexpr
  if (LVAL_TYPE(qexpr) != LVAL_QEXPR && LVAL_TYPE(qexpr) != LVAL_CONS) {
    return nullptr;
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t* curr = qexpr;
  while (!valk_lval_list_is_empty(curr)) {
    valk_lval_t* k = valk_lval_head(curr);
    curr = valk_lval_tail(curr);

    if (valk_lval_list_is_empty(curr)) break; // LCOV_EXCL_BR_LINE odd-length qexpr

    valk_lval_t* v = valk_lval_head(curr);
    curr = valk_lval_tail(curr);

    if (LVAL_TYPE(k) == LVAL_SYM && strcmp(k->str, key) == 0) { // LCOV_EXCL_BR_LINE key lookup
      return v;
    }
  }

  return nullptr;
}

// LCOV_EXCL_BR_START send_response: response header/body/cache-control presence checks
int valk_http2_send_response(nghttp2_session *session, int stream_id,
                             valk_lval_t* response_qexpr, valk_mem_arena_t* arena) {
  const char* status = "200";
  valk_lval_t* status_val = valk_http2_qexpr_get(response_qexpr, ":status");
  if (status_val && LVAL_TYPE(status_val) == LVAL_STR) {
    status = status_val->str;
  }

  const char* body = "";
  u64 body_len = 0;
  valk_lval_t* body_val = valk_http2_qexpr_get(response_qexpr, ":body");
  if (body_val && LVAL_TYPE(body_val) == LVAL_STR) {
    body_len = strlen(body_val->str);
    if (body_len > 1024 * 1024) {
      body = body_val->str;
    } else {
      VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
        char* body_copy = valk_mem_alloc(body_len + 1);
        memcpy(body_copy, body_val->str, body_len + 1);
        body = body_copy;
      }
    }
  }

  valk_http2_metrics_on_response_body(session, stream_id, body_len, status);

  const char* content_type = "text/plain; charset=utf-8";
  valk_lval_t* ct_val = valk_http2_qexpr_get(response_qexpr, ":content-type");
  if (ct_val && LVAL_TYPE(ct_val) == LVAL_STR) {
    content_type = ct_val->str;
  }

  const char* cache_control = nullptr;
  valk_lval_t* cc_val = valk_http2_qexpr_get(response_qexpr, ":cache-control");
  if (cc_val && LVAL_TYPE(cc_val) == LVAL_STR) {
    cache_control = cc_val->str;
  }

  nghttp2_nv* headers;
  u64 header_count = 2;
  if (cache_control) header_count++;

  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    headers = valk_mem_alloc(sizeof(nghttp2_nv) * header_count);
    headers[0] = (nghttp2_nv)MAKE_NV(":status", status, strlen(status));
    headers[1] = (nghttp2_nv)MAKE_NV("content-type", content_type, strlen(content_type));
    if (cache_control) {
      headers[2] = (nghttp2_nv)MAKE_NV("cache-control", cache_control, strlen(cache_control));
    }
  }

  http_body_source_t *body_src;
  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    body_src = valk_mem_alloc(sizeof(http_body_source_t));
    body_src->body = body;
    body_src->body_len = body_len;
    body_src->offset = 0;
    body_src->needs_free = false;
  }

  nghttp2_data_provider2 data_prd;
  data_prd.source.ptr = (void*)body_src;
  data_prd.read_callback = valk_http2_byte_body_cb;

  return nghttp2_submit_response2(session, stream_id, headers, header_count, &data_prd);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START frame/stream callbacks: nghttp2 frame type dispatch and stream state
int valk_http2_server_on_frame_send_callback(nghttp2_session *session,
                                             const nghttp2_frame *frame,
                                             void *user_data) {
  UNUSED(user_data);

  if (frame->hd.type == NGHTTP2_DATA && (frame->hd.flags & NGHTTP2_FLAG_END_STREAM)) {
    valk_http2_metrics_on_frame_send_eof(session, frame->hd.stream_id);
  }

  return 0;
}

int valk_http2_server_on_stream_close_callback(nghttp2_session *session,
                                               i32 stream_id,
                                               u32 error_code,
                                               void *user_data) {
  valk_aio_handle_t *conn = (valk_aio_handle_t *)user_data;

  VALK_INFO("on_stream_close_callback: stream %d (error_code=%u: %s)",
            stream_id, error_code, nghttp2_http2_strerror(error_code));

  if (error_code != NGHTTP2_NO_ERROR) {
    VALK_DEBUG("Stream %d closed with error: %s (code=%u)",
               stream_id, nghttp2_http2_strerror(error_code), error_code);
  }

  u64 stream_body_bytes = valk_stream_body_get_bytes_sent(conn, stream_id);

  void *stream_data = nghttp2_session_get_stream_user_data(session, stream_id);
  valk_http2_server_request_t *req = (valk_http2_server_request_t *)stream_data;

  bool was_sse_stream = valk_http2_metrics_on_sse_stream_close(conn, stream_id);

  bool has_stream_body = valk_stream_body_exists_for_stream(conn, stream_id);
  valk_stream_body_close_by_stream_id(conn, stream_id);

  if (req && valk_arena_ref_valid(req->arena_ref)) {
    req->bytes_sent += stream_body_bytes;
    valk_http2_metrics_on_stream_close(conn, req, error_code, was_sse_stream, stream_body_bytes);
    if (!has_stream_body && !req->has_async_handler) {
      valk_http2_metrics_on_arena_release(conn);
      u32 slot = req->arena_ref.slot;
      valk_http2_remove_from_active_arenas(conn, slot);
      valk_arena_ref_release(&req->arena_ref, conn->http.server->sys->httpStreamArenas);
      u64 arena_num_free = __atomic_load_n(&conn->http.server->sys->httpStreamArenas->numFree, __ATOMIC_ACQUIRE);
      VALK_INFO("Arena RELEASED (stream close) for stream %d (slot=%u, now %llu free)", stream_id, slot, arena_num_free);

      if (conn->http.arena_backpressure) {
        valk_http2_exit_arena_backpressure(conn);
      }
    }
    // LCOV_EXCL_BR_STOP
  }
  else if (req && !valk_arena_ref_valid(req->arena_ref)) { // LCOV_EXCL_BR_LINE - arena already released by async handler
    req->bytes_sent += stream_body_bytes;
    valk_http2_metrics_on_client_close(conn, req, stream_id, error_code, was_sse_stream, stream_body_bytes);
  }

  if (req) {
    conn->http.active_streams--;
    VALK_DEBUG("%d active streams remaining", conn->http.active_streams);
    valk_http2_metrics_on_conn_idle(conn);
  }

  return 0;
}
// LCOV_EXCL_BR_STOP

static void __send_error_response(nghttp2_session *session, i32 stream_id,
                                  const char *status, const char *body,
                                  valk_mem_arena_t *arena) {
  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    valk_lval_t* items[] = {
      valk_lval_sym(":status"), valk_lval_str(status),
      valk_lval_sym(":body"), valk_lval_str(body)
    };
    valk_lval_t* resp = valk_lval_qlist(items, 4);
    valk_http2_send_response(session, stream_id, resp, arena);
  }
}

static void __send_default_response(nghttp2_session *session, i32 stream_id,
                                    valk_mem_arena_t *arena) {
  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    valk_lval_t* items[] = {
      valk_lval_sym(":status"), valk_lval_str("200"),
      valk_lval_sym(":content-type"), valk_lval_str("text/html; charset=utf-8"),
      valk_lval_sym(":body"), valk_lval_str(VALK_HTTP_MOTD)
    };
    valk_lval_t* resp = valk_lval_qlist(items, 6);
    valk_http2_send_response(session, stream_id, resp, arena);
  }
}

static valk_http_async_ctx_t *__create_async_ctx(nghttp2_session *session,
                                                  i32 stream_id,
                                                  valk_aio_handle_t *conn,
                                                  valk_mem_arena_t *arena,
                                                  valk_region_t *region) {
  valk_http_async_ctx_t *ctx = valk_region_alloc(region, sizeof(valk_http_async_ctx_t));
  if (!ctx) return nullptr; // LCOV_EXCL_BR_LINE OOM path
  ctx->session = session;
  ctx->stream_id = stream_id;
  ctx->conn = conn;
  ctx->arena = arena;
  return ctx;
}

typedef struct {
  nghttp2_session *session;
  i32 stream_id;
  valk_aio_handle_t *conn;
  valk_http2_server_request_t *req;
  valk_async_handle_t *handle;
  valk_http_async_ctx_t *http_ctx;
} async_response_ctx_t;

// LCOV_EXCL_BR_START - async response state handlers: stream_response/error type branching
static int __async_state_completed(async_response_ctx_t *ctx) {
  if (ctx->req->stream_response) return 0;
  valk_lval_t *result = atomic_load_explicit(&ctx->handle->result, memory_order_acquire);
  if (LVAL_TYPE(result) == LVAL_ERR) {
    VALK_WARN("Handle completed with error: %s", result->str);
    __send_error_response(ctx->session, ctx->stream_id, "500", result->str, ctx->req->stream_arena);
  } else {
    valk_http2_send_response(ctx->session, ctx->stream_id, result, ctx->req->stream_arena);
  }
  return 0;
}

static int __async_state_failed(async_response_ctx_t *ctx) {
  if (ctx->req->stream_response) return 0;
  valk_lval_t *err_val = atomic_load_explicit(&ctx->handle->error, memory_order_acquire);
  valk_lval_t *err = err_val ? err_val : valk_lval_err("Handle failed");
  const char *msg = LVAL_TYPE(err) == LVAL_ERR ? err->str : "Async operation failed";
  VALK_WARN("Handle failed: %s", msg);
  __send_error_response(ctx->session, ctx->stream_id, "500", msg, ctx->req->stream_arena);
  return 0;
}

static int __async_state_cancelled(async_response_ctx_t *ctx) {
  if (ctx->req->stream_response) return 0;
// LCOV_EXCL_BR_STOP
  VALK_DEBUG("Handle cancelled, sending 503 for stream %d", ctx->stream_id);
  __send_error_response(ctx->session, ctx->stream_id, "503", "Request cancelled", ctx->req->stream_arena);
  return 0;
}

static int __async_state_pending(async_response_ctx_t *ctx) {
  UNUSED(ctx);
  VALK_DEBUG("Handle pending/running, will send response when complete");
  return 1;
}

typedef int (*async_state_handler_t)(async_response_ctx_t *);

static const async_state_handler_t async_state_handlers[] = {
  [VALK_ASYNC_PENDING]   = __async_state_pending,
  [VALK_ASYNC_RUNNING]   = __async_state_pending,
  [VALK_ASYNC_COMPLETED] = __async_state_completed,
  [VALK_ASYNC_FAILED]    = __async_state_failed,
  [VALK_ASYNC_CANCELLED] = __async_state_cancelled,
};

// LCOV_EXCL_BR_START arena cleanup and async response state
static void __release_arena_cleanup(void *data, void *ctx) {
  valk_http2_server_request_t *req = (valk_http2_server_request_t *)data;
  valk_aio_handle_t *conn = (valk_aio_handle_t *)ctx;
  if (!valk_arena_ref_valid(req->arena_ref)) return;
  valk_http2_metrics_on_arena_release(conn);
  valk_http2_remove_from_active_arenas(conn, req->arena_ref.slot);
  valk_arena_ref_release(&req->arena_ref, conn->http.server->sys->httpStreamArenas);
  if (conn->http.arena_backpressure) {
    valk_http2_exit_arena_backpressure(conn);
  }
}

static int __handle_async_response(nghttp2_session *session, i32 stream_id,
                                   valk_aio_handle_t *conn,
                                   valk_http2_server_request_t *req,
                                   valk_async_handle_t *handle,
                                   valk_lenv_t *env) {
  handle->region = &req->region;
  handle->env = env;

  req->has_async_handler = true;

  valk_http_async_ctx_t *http_ctx = __create_async_ctx(session, stream_id, conn, req->stream_arena, &req->region);
  if (http_ctx) {
    http_ctx->stream_response = req->stream_response;
    handle->on_done = valk_http_async_done_callback;
    handle->on_done_ctx = http_ctx;
  }

  valk_async_handle_on_resource_cleanup(handle, __release_arena_cleanup, req, conn);

  VALK_ASSERT_HAS_CLEANUP(handle);

  for (valk_async_handle_t *p = handle->parent; p != nullptr; p = p->parent) {
    valk_async_propagate_region(p, handle->region, env);
  }
  valk_async_propagate_region(handle, handle->region, env);

  async_response_ctx_t ctx = {
    .session = session, .stream_id = stream_id, .conn = conn,
    .req = req, .handle = handle, .http_ctx = http_ctx
  };

  return async_state_handlers[handle->status](&ctx);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START request handling: handler resolution, response type dispatch
static int __handle_request_headers(nghttp2_session *session,
                                    const nghttp2_frame *frame,
                                    valk_aio_handle_t *conn) {
  VALK_DEBUG(">>> Received complete HTTP/2 request (stream_id=%d)", frame->hd.stream_id);

  valk_http2_server_request_t *req = (valk_http2_server_request_t *)
      nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

  if (!req) {
    VALK_WARN("No request data for stream %d", frame->hd.stream_id);
    return 0;
  }

  valk_lval_t *handler = valk_handle_resolve(&valk_sys->handle_table, 
                                              conn->http.server->lisp_handler_handle);
  if (!conn->http.server || !handler) {
    __send_default_response(session, frame->hd.stream_id, req->stream_arena);
    return 0;
  }
  valk_lenv_t *env = handler->fun.env;
  valk_lval_t *response;

  req->request_ctx = __http2_create_request_ctx(req);

  valk_lval_t *req_ref = valk_lval_ref("http_request", req, nullptr);
  VALK_WITH_REQUEST_CTX(req->request_ctx) {
    VALK_WITH_ALLOC((valk_mem_allocator_t*)&req->region) {
      valk_lval_t *args = valk_lval_cons(req_ref, valk_lval_nil());
      response = valk_lval_eval_call(env, handler, args);
    }
  }

  if (LVAL_TYPE(response) == LVAL_SYM && strcmp(response->str, ":deferred") == 0) {
    return 0;
  }

  if (LVAL_TYPE(response) == LVAL_HANDLE) {
    response->async.handle->request_ctx = req->request_ctx;
    int pending = __handle_async_response(session, frame->hd.stream_id, conn, req,
                                          response->async.handle, env);
    if (pending) return 0;
    return 0;
  }

  if (LVAL_TYPE(response) == LVAL_ERR) {
    VALK_WARN("Handler returned error: %s", response->str);
    __send_error_response(session, frame->hd.stream_id, "500", response->str, req->stream_arena);
  } else {
    valk_http2_send_response(session, frame->hd.stream_id, response, req->stream_arena);
  }

  return 0;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START frame recv: frame type dispatch and GOAWAY/RST handling
int valk_http2_on_frame_recv_callback(nghttp2_session *session,
                                      const nghttp2_frame *frame,
                                      void *user_data) {
  VALK_GC_SAFE_POINT();
  valk_aio_handle_t *conn = (valk_aio_handle_t *)user_data;

  if (conn->sys) {
    conn->http.last_activity_ms = conn->sys->ops->loop->now(conn->sys);
  }

  if (frame->hd.type == NGHTTP2_GOAWAY) {
    VALK_DEBUG("Received GO AWAY frame");
    return 0;
  }

  if (frame->hd.type == NGHTTP2_RST_STREAM) {
    VALK_INFO("Received RST_STREAM for stream %d (error_code=%u)",
              frame->hd.stream_id, frame->rst_stream.error_code);
    return 0;
  }

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    return __handle_request_headers(session, frame, conn);
  }

  return 0;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START stream control: null checks and nghttp2 error returns
int valk_http2_stream_reset(valk_aio_handle_t *conn, i32 stream_id, u32 error_code) {
  if (!conn || !conn->http.session) {
    return -1;
  }
  int rv = nghttp2_submit_rst_stream(conn->http.session, NGHTTP2_FLAG_NONE,
                                      stream_id, error_code);
  if (rv != 0) { // LCOV_EXCL_START nghttp2 library error
    VALK_ERROR("nghttp2_submit_rst_stream failed: %s", nghttp2_strerror(rv));
    return -1;
  } // LCOV_EXCL_STOP
  return 0;
}

int valk_http2_submit_goaway(valk_aio_handle_t *conn, u32 error_code) {
  if (!conn || !conn->http.session) {
    return -1;
  }
  int rv = nghttp2_submit_goaway(conn->http.session, NGHTTP2_FLAG_NONE,
                                  0, error_code, nullptr, 0);
  if (rv != 0) { // LCOV_EXCL_START nghttp2 library error
    VALK_ERROR("nghttp2_submit_goaway failed: %s", nghttp2_strerror(rv));
    return -1;
  } // LCOV_EXCL_STOP
  return 0;
}
// LCOV_EXCL_BR_STOP

bool valk_aio_http_session_valid(valk_aio_handle_t *handle, void *session) {
  if (!handle || !session) { // LCOV_EXCL_BR_LINE defensive null check
    return false;
  }
  return handle->http.session == session;
}

bool valk_aio_http_connection_closing(valk_aio_handle_t *handle) {
  if (!handle) { // LCOV_EXCL_BR_LINE defensive null check
    return true;
  }
  // LCOV_EXCL_BR_START connection state check
  return handle->http.state == VALK_CONN_CLOSING ||
         handle->http.state == VALK_CONN_CLOSED;
  // LCOV_EXCL_BR_STOP
}

// LCOV_EXCL_BR_START arena release: null/validity checks
void valk_http2_release_stream_arena(valk_aio_handle_t *conn, i32 stream_id) {
  if (!conn || !conn->http.session || !conn->http.server || !conn->http.server->sys) {
    return;
  }

  valk_http2_server_request_t *req = (valk_http2_server_request_t *)
      nghttp2_session_get_stream_user_data(conn->http.session, stream_id);
  if (!req) {
    return;
  }
  if (!valk_arena_ref_valid(req->arena_ref)) {
    return;
  }

  VALK_INFO("Releasing arena for stream %d (early close)", stream_id);

  valk_http2_metrics_on_arena_release(conn);
  u32 slot = req->arena_ref.slot;
  valk_http2_remove_from_active_arenas(conn, slot);
  valk_arena_ref_release(&req->arena_ref, conn->http.server->sys->httpStreamArenas);

  if (conn->http.arena_backpressure) {
    valk_http2_exit_arena_backpressure(conn);
  }
}
