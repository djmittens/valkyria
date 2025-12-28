#include "aio_http2_session.h"
#include "aio_http2_conn.h"

extern void valk_http_async_done_callback(valk_async_handle_t *handle, void *ctx);
extern bool valk_http_async_is_closed_callback(void *ctx);
extern void valk_async_propagate_allocator(valk_async_handle_t *handle, valk_mem_allocator_t *allocator, valk_lenv_t *env);
extern valk_async_handle_t* valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern void valk_async_handle_free(valk_async_handle_t *handle);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
extern bool valk_async_handle_cancel(valk_async_handle_t *handle);

static void __pending_stream_process_batch(valk_aio_system_t *sys);

static inline u64 __align_up(uptr addr, u64 alignment) {
  u64 mask = alignment - 1;
  u64 misalign = addr & mask;
  return misalign ? (alignment - misalign) : 0;
}

static inline valk_http2_server_request_t *__http_request_from_slot(
    valk_slab_t *slab, u32 slot) {
  if (slot == UINT32_MAX || !slab || slot >= slab->numItems) return NULL;
  u64 stride = valk_slab_item_stride(slab->itemSize);
  valk_slab_item_t *item = (valk_slab_item_t *)&slab->heap[stride * slot];
  valk_mem_arena_t *arena = (valk_mem_arena_t *)item->data;
  u64 init_off = __align_up((uptr)arena->heap, alignof(max_align_t));
  u64 hdr = init_off + sizeof(size_t);
  u64 adj = __align_up((uptr)&arena->heap[hdr], alignof(max_align_t));
  u64 payload = hdr + adj;
  return (valk_http2_server_request_t *)&arena->heap[payload];
}

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

  VALK_ASSERT(iterations < max_iterations,
              "Arena linked list infinite loop after %u iterations", iterations);
}

int valk_http2_on_header_callback(nghttp2_session *session,
                                  const nghttp2_frame *frame,
                                  const u8 *name, size_t namelen,
                                  const u8 *value, size_t valuelen,
                                  u8 flags, void *user_data) {
  UNUSED(flags);
  UNUSED(user_data);
  VALK_TRACE("HDR: %.*s: %.*s", (int)namelen, name, (int)valuelen, value);

  void *stream_data = nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

  if (__is_pending_stream(stream_data)) {
    pending_stream_t *ps = __get_pending_stream(stream_data);
    if (!ps) return 0;

    if (namelen > 0 && name[0] == ':') {
      char *str = malloc(valuelen + 1);
      if (!str) return 0;
      memcpy(str, value, valuelen);
      str[valuelen] = '\0';

      if (namelen == 7 && memcmp(name, ":method", 7) == 0) {
        if (ps->method) free(ps->method);
        ps->method = str;
      } else if (namelen == 7 && memcmp(name, ":scheme", 7) == 0) {
        if (ps->scheme) free(ps->scheme);
        ps->scheme = str;
      } else if (namelen == 10 && memcmp(name, ":authority", 10) == 0) {
        if (ps->authority) free(ps->authority);
        ps->authority = str;
      } else if (namelen == 5 && memcmp(name, ":path", 5) == 0) {
        if (ps->path) free(ps->path);
        ps->path = str;
      } else {
        free(str);
      }
    } else {
      VALK_DEBUG("Pending stream %d buffering custom header: %.*s", ps->stream_id, (int)namelen, name);
      if (ps->header_count < PENDING_STREAM_MAX_HEADERS) {
        pending_header_t *h = &ps->headers[ps->header_count];
        h->name = malloc(namelen + 1);
        h->value = malloc(valuelen + 1);
        if (h->name && h->value) {
          memcpy(h->name, name, namelen);
          memcpy(h->value, value, valuelen);
          h->name[namelen] = '\0';
          h->value[valuelen] = '\0';
          h->name_len = namelen;
          h->value_len = valuelen;
          ps->header_count++;
        } else {
          if (h->name) free(h->name);
          if (h->value) free(h->value);
          h->name = h->value = NULL;
        }
      }
    }
    return 0;
  }

  valk_http2_server_request_t *req = (valk_http2_server_request_t *)stream_data;
  if (!req) return 0;

#ifdef VALK_METRICS_ENABLED
  req->bytes_recv += namelen + valuelen + 4;
#endif

  VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
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

int valk_http2_on_begin_headers_callback(nghttp2_session *session,
                                         const nghttp2_frame *frame,
                                         void *user_data) {
  valk_aio_handle_t *conn = (valk_aio_handle_t *)user_data;

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    VALK_DEBUG(">>> Received HTTP/2 request (stream_id=%d)",
               frame->hd.stream_id);

    conn->http.active_streams++;

#ifdef VALK_METRICS_ENABLED
    valk_aio_metrics_on_stream_start(&conn->http.server->sys->metrics_state->metrics);

    if (conn->http.active_streams == 1) {
      conn->http.diag.state = VALK_DIAG_CONN_ACTIVE;
      conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
    }
#endif

    valk_slab_item_t *arena_item = valk_slab_aquire(conn->http.server->sys->httpStreamArenas);
    if (!arena_item) {
      valk_aio_system_t *sys = conn->http.server->sys;
      pending_stream_t *ps = valk_pending_stream_alloc(&sys->pending_streams);
      if (ps) {
        ps->conn = conn;
        ps->session = session;
        ps->stream_id = frame->hd.stream_id;
        ps->queued_time_ms = conn->sys->ops->loop->now(conn->sys);
        ps->headers_complete = false;

        nghttp2_session_set_stream_user_data(session, frame->hd.stream_id,
            (void*)((uptr)ps | (1ULL << 63)));

        valk_pending_stream_enqueue(&sys->pending_streams, ps);
        VALK_INFO("Stream %d queued for backpressure (arena pool exhausted, %zu pending)",
                  frame->hd.stream_id, sys->pending_streams.count);

#ifdef VALK_METRICS_ENABLED
        atomic_fetch_add(&conn->http.server->sys->metrics_state->system_stats.arena_pool_overflow, 1);
        valk_aio_system_stats_on_pending_enqueue(&conn->http.server->sys->metrics_state->system_stats);
#endif
        return 0;
      }

      VALK_WARN("Stream arena AND pending pool exhausted for stream %d, sending 503",
                frame->hd.stream_id);
      conn->http.active_streams--;

#ifdef VALK_METRICS_ENABLED
      valk_aio_metrics_on_stream_end(&conn->http.server->sys->metrics_state->metrics, true, 0, 0, 0);
      atomic_fetch_add(&conn->http.server->sys->metrics_state->system_stats.arena_pool_overflow, 1);
      valk_counter_v2_inc(conn->http.server->metrics.overload_responses);
      valk_counter_v2_inc(conn->http.server->metrics.requests_server_error);
#endif

      valk_http2_send_overload_response(session, frame->hd.stream_id, conn);
      return 0;
    }

    valk_mem_arena_t *stream_arena = (valk_mem_arena_t *)arena_item->data;
    valk_mem_arena_init(stream_arena, conn->http.server->sys->config.arena_size);

    u64 arena_num_free = __atomic_load_n(&conn->http.server->sys->httpStreamArenas->numFree, __ATOMIC_ACQUIRE);
    VALK_INFO("Arena ACQUIRED for stream %d (slot=%zu, now %llu free)",
              frame->hd.stream_id, arena_item->handle & 0xFFFFFFFF, arena_num_free);

#ifdef VALK_METRICS_ENABLED
    valk_aio_system_stats_on_arena_acquire(&conn->http.server->sys->metrics_state->system_stats);
#endif

    valk_http2_server_request_t *req;
    VALK_WITH_ALLOC((valk_mem_allocator_t*)stream_arena) {
      req = valk_mem_alloc(sizeof(valk_http2_server_request_t));
      memset(req, 0, sizeof(valk_http2_server_request_t));
      req->conn = conn;
      req->stream_id = frame->hd.stream_id;
      req->stream_arena = stream_arena;
      req->arena_slab_item = arena_item;
      req->arena_slot = (u32)(arena_item->handle & 0xFFFFFFFF);
      req->next_arena_slot = UINT32_MAX;
#ifdef VALK_METRICS_ENABLED
      req->start_time_us = uv_hrtime() / 1000;
      req->bytes_sent = 0;
      req->bytes_recv = 0;
#endif
    }

    nghttp2_session_set_stream_user_data(session, frame->hd.stream_id, req);

    VALK_ASSERT(conn->http.active_arena_head != req->arena_slot,
                "Arena slot %u already at head - would create self-loop", req->arena_slot);
    req->next_arena_slot = conn->http.active_arena_head;
    conn->http.active_arena_head = req->arena_slot;
  }
  return 0;
}

int valk_http2_client_on_header_cb(nghttp2_session *session,
                                   const nghttp2_frame *frame,
                                   const u8 *name, size_t namelen,
                                   const u8 *value, size_t valuelen,
                                   u8 flags, void *user_data) {
  UNUSED(session);
  UNUSED(frame);
  UNUSED(flags);
  UNUSED(user_data);

  __http2_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

  if (reqres) {
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
  return 0;
}

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

  int rv = nghttp2_submit_response2(session, stream_id, headers,
                                     sizeof(headers) / sizeof(headers[0]), &data_prd);
  if (rv != 0) {
    free(body_src);
  }
  return rv;
}

valk_lval_t* valk_http2_qexpr_get(valk_lval_t* qexpr, const char* key) {
  if (LVAL_TYPE(qexpr) != LVAL_QEXPR && LVAL_TYPE(qexpr) != LVAL_CONS) {
    return NULL;
  }

  valk_lval_t* curr = qexpr;
  while (!valk_lval_list_is_empty(curr)) {
    valk_lval_t* k = valk_lval_head(curr);
    curr = valk_lval_tail(curr);

    if (valk_lval_list_is_empty(curr)) break;

    valk_lval_t* v = valk_lval_head(curr);
    curr = valk_lval_tail(curr);

    if (LVAL_TYPE(k) == LVAL_SYM && strcmp(k->str, key) == 0) {
      return v;
    }
  }

  return NULL;
}

int valk_http2_send_response(nghttp2_session *session, int stream_id,
                             valk_lval_t* response_qexpr, valk_mem_arena_t* arena) {
#ifdef VALK_METRICS_ENABLED
  valk_lval_t* body_type_val = valk_http2_qexpr_get(response_qexpr, ":body-type");
  if (body_type_val && LVAL_TYPE(body_type_val) == LVAL_SYM &&
      strcmp(body_type_val->str, ":sse-stream") == 0) {
    valk_http2_server_request_t *req =
        nghttp2_session_get_stream_user_data(session, stream_id);
    if (req && req->conn && req->conn->http.server && req->conn->http.server->sys) {
      VALK_INFO("Setting up SSE diagnostics stream for stream %d", stream_id);

      if (req->arena_slab_item) {
        u32 slot = req->arena_slot;
        valk_http2_remove_from_active_arenas(req->conn, slot);
        req->arena_slot = UINT32_MAX;
        valk_slab_item_t *item = req->arena_slab_item;
        req->arena_slab_item = NULL;
        req->stream_arena = NULL;
        valk_slab_release(req->conn->http.server->sys->httpStreamArenas, item);
        u64 arena_num_free = __atomic_load_n(&req->conn->http.server->sys->httpStreamArenas->numFree, __ATOMIC_ACQUIRE);
        VALK_INFO("Arena RELEASED (SSE) for stream %d (slot=%u, now %llu free)", stream_id, slot, arena_num_free);
      }

      nghttp2_data_provider2 data_prd;
      valk_sse_stream_registry_t *registry = &req->conn->http.server->sys->sse_registry;
      valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
          registry, req->conn, session, stream_id, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);

      if (!entry) {
        VALK_ERROR("Failed to subscribe to SSE registry");
        return -1;
      }

      valk_gauge_v2_inc(req->conn->http.server->metrics.sse_streams_active);
      req->sse_entry = entry;
      req->status_code = 200;

      const char* content_type = "text/event-stream; charset=utf-8";
      nghttp2_nv headers[] = {
        MAKE_NV2(":status", "200"),
        MAKE_NV("content-type", content_type, strlen(content_type)),
        MAKE_NV2("cache-control", "no-cache"),
      };

      int rv = nghttp2_submit_response2(session, stream_id, headers, 3, &data_prd);
      if (rv != 0) {
        VALK_ERROR("nghttp2_submit_response2 failed for SSE stream %d: %s",
                   stream_id, nghttp2_strerror(rv));
      } else {
        VALK_INFO("SSE response submitted for stream %d", stream_id);
      }
      return rv;
    }
  }
#endif

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

#ifdef VALK_METRICS_ENABLED
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (req) {
    req->bytes_sent = body_len;
    req->status_code = atoi(status);
  }
#endif

  const char* content_type = "text/plain; charset=utf-8";
  valk_lval_t* ct_val = valk_http2_qexpr_get(response_qexpr, ":content-type");
  if (ct_val && LVAL_TYPE(ct_val) == LVAL_STR) {
    content_type = ct_val->str;
  }

  nghttp2_nv* headers;
  u64 header_count = 2;

  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    headers = valk_mem_alloc(sizeof(nghttp2_nv) * header_count);
    headers[0] = (nghttp2_nv)MAKE_NV(":status", status, strlen(status));
    headers[1] = (nghttp2_nv)MAKE_NV("content-type", content_type, strlen(content_type));
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

valk_lval_t* valk_http2_build_request_qexpr(valk_http2_server_request_t *req) {
  valk_lval_t *qexpr;

  VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
    valk_lval_t *headers_list = valk_lval_nil();
    for (u64 i = req->headers.count; i > 0; i--) {
      valk_lval_t *pair_items[2] = {
        valk_lval_str((char*)req->headers.items[i-1].name),
        valk_lval_str((char*)req->headers.items[i-1].value)
      };
      valk_lval_t *pair = valk_lval_qlist(pair_items, 2);
      headers_list = valk_lval_qcons(pair, headers_list);
    }

    valk_lval_t *items[8];
    u64 item_count = 0;

    items[item_count++] = valk_lval_sym(":method");
    items[item_count++] = valk_lval_str(req->method ? req->method : "GET");

    items[item_count++] = valk_lval_sym(":path");
    items[item_count++] = valk_lval_str(req->path ? req->path : "/");

    if (req->authority) {
      items[item_count++] = valk_lval_sym(":authority");
      items[item_count++] = valk_lval_str(req->authority);
    }

    items[item_count++] = valk_lval_sym(":headers");
    items[item_count++] = headers_list;

    qexpr = valk_lval_qlist(items, item_count);
  }

  return qexpr;
}

int valk_http2_server_on_frame_send_callback(nghttp2_session *session,
                                             const nghttp2_frame *frame,
                                             void *user_data) {
  UNUSED(user_data);

#ifdef VALK_METRICS_ENABLED
  if (frame->hd.type == NGHTTP2_DATA && (frame->hd.flags & NGHTTP2_FLAG_END_STREAM)) {
    valk_http2_server_request_t *req =
        nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);
    if (req) {
      req->response_sent_time_us = uv_hrtime() / 1000;
      req->response_complete = true;
    }
  }
#endif

  return 0;
}

int valk_http2_server_on_stream_close_callback(nghttp2_session *session,
                                               i32 stream_id,
                                               u32 error_code,
                                               void *user_data) {
  UNUSED(error_code);
  valk_aio_handle_t *conn = (valk_aio_handle_t *)user_data;

  void *stream_data = nghttp2_session_get_stream_user_data(session, stream_id);

  if (__is_pending_stream(stream_data)) {
    pending_stream_t *ps = __get_pending_stream(stream_data);
    if (ps) {
      VALK_INFO("Pending stream %d closed (client reset or timeout), removing from queue",
                stream_id);
      valk_pending_stream_remove(&conn->http.server->sys->pending_streams, ps);
#ifdef VALK_METRICS_ENABLED
      if (conn->http.server && conn->http.server->sys) {
        valk_aio_metrics_on_stream_end(&conn->http.server->sys->metrics_state->metrics, true, 0, 0, 0);
        valk_aio_system_stats_on_pending_drop(&conn->http.server->sys->metrics_state->system_stats);

        valk_server_metrics_t* m = &conn->http.server->metrics;
        valk_counter_v2_inc(m->requests_total);
        valk_counter_v2_inc(m->requests_server_error);

        VALK_INFO("Pending stream %d timeout: recorded as 5xx", stream_id);
      }
#endif
    }
    conn->http.active_streams--;
    return 0;
  }

  valk_http2_server_request_t *req = (valk_http2_server_request_t *)stream_data;

#ifdef VALK_METRICS_ENABLED
  bool was_sse_stream = false;
  if (conn->http.server && conn->http.server->sys) {
    valk_sse_stream_registry_t *registry = &conn->http.server->sys->sse_registry;
    valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(
        registry, conn, stream_id);
    if (entry) {
      VALK_INFO("Stream %d closing, unsubscribing from SSE registry", stream_id);
      valk_sse_registry_unsubscribe(registry, entry);
      valk_gauge_v2_dec(conn->http.server->metrics.sse_streams_active);
      was_sse_stream = true;
    }
  }
#endif

  if (req && req->arena_slab_item) {
#ifdef VALK_METRICS_ENABLED
    u64 end_time_us;
    if (req->response_complete && req->response_sent_time_us > 0) {
      end_time_us = req->response_sent_time_us;
    } else {
      end_time_us = uv_hrtime() / 1000;
    }
    u64 duration_us = end_time_us - req->start_time_us;
    bool is_error = (error_code != NGHTTP2_NO_ERROR);
    u64 bytes_recv = req->bytes_recv + req->bodyLen;
    valk_aio_metrics_on_stream_end(&conn->http.server->sys->metrics_state->metrics, is_error,
                                     duration_us, req->bytes_sent, bytes_recv);

    valk_server_metrics_t* m = &conn->http.server->metrics;

    valk_counter_v2_inc(m->requests_total);

    int status = req->status_code;
    if (status >= 200 && status < 300) {
      valk_counter_v2_inc(m->requests_success);
    } else if (status >= 400 && status < 500) {
      valk_counter_v2_inc(m->requests_client_error);
    } else if (status >= 500) {
      valk_counter_v2_inc(m->requests_server_error);
    }

    if (!was_sse_stream) {
      valk_histogram_v2_observe_us(m->request_duration, duration_us);
    } else {
      valk_histogram_v2_observe_us(m->sse_stream_duration, duration_us);
    }

    valk_counter_v2_add(m->bytes_sent, req->bytes_sent);
    valk_counter_v2_add(m->bytes_recv, bytes_recv);
#endif

#ifdef VALK_METRICS_ENABLED
    valk_aio_system_stats_on_arena_release(&conn->http.server->sys->metrics_state->system_stats);
#endif
    u32 slot = req->arena_slot;
    valk_http2_remove_from_active_arenas(conn, slot);
    req->arena_slot = UINT32_MAX;
    valk_slab_item_t *item = req->arena_slab_item;
    req->arena_slab_item = NULL;
    valk_slab_release(conn->http.server->sys->httpStreamArenas, item);
    u64 arena_num_free = __atomic_load_n(&conn->http.server->sys->httpStreamArenas->numFree, __ATOMIC_ACQUIRE);
    VALK_INFO("Arena RELEASED (stream close) for stream %d (slot=%u, now %llu free)", stream_id, slot, arena_num_free);

    if (conn->http.server->sys->pending_streams.count > 0) {
      __pending_stream_process_batch(conn->http.server->sys);
    }
  }
  else if (req && !req->arena_slab_item) {
#ifdef VALK_METRICS_ENABLED
    if (conn->http.server && conn->http.server->sys) {
      u64 end_time_us = uv_hrtime() / 1000;
      u64 duration_us = end_time_us - req->start_time_us;
      bool is_error = !was_sse_stream && (error_code != NGHTTP2_NO_ERROR);
      valk_aio_metrics_on_stream_end(&conn->http.server->sys->metrics_state->metrics, is_error,
                                       duration_us, req->bytes_sent, req->bytes_recv);

      if (was_sse_stream) {
        valk_server_metrics_t* m = &conn->http.server->metrics;
        valk_histogram_v2_observe_us(m->sse_stream_duration, duration_us);
        VALK_INFO("SSE stream %d closed by client (already counted as 2xx)", stream_id);
      } else {
        valk_server_metrics_t* m = &conn->http.server->metrics;
        valk_counter_v2_inc(m->requests_total);
        valk_counter_v2_inc(m->requests_server_error);
        valk_histogram_v2_observe_us(m->request_duration, duration_us);
        VALK_INFO("Async request timeout: stream %d closed by client after %llu us",
                  stream_id, (unsigned long long)duration_us);
      }
    }
#endif
  }

  conn->http.active_streams--;
  VALK_DEBUG("%d active streams remaining", conn->http.active_streams);

#ifdef VALK_METRICS_ENABLED
  if (conn->http.active_streams == 0) {
    conn->http.diag.state = VALK_DIAG_CONN_IDLE;
    conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
  }
#endif

  return 0;
}

int valk_http2_on_frame_recv_callback(nghttp2_session *session,
                                      const nghttp2_frame *frame,
                                      void *user_data) {
  valk_aio_handle_t *conn = (valk_aio_handle_t *)user_data;

  // Any frame from the peer proves the connection is alive
  // This is especially important for SSE where WINDOW_UPDATE frames
  // are the only incoming traffic
  if (conn->sys) {
    conn->http.last_activity_ms = conn->sys->ops->loop->now(conn->sys);
  }

  if (frame->hd.type == NGHTTP2_GOAWAY) {
    VALK_DEBUG("Received GO AWAY frame");
    return 0;
  }

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    VALK_DEBUG(">>> Received complete HTTP/2 request (stream_id=%d)", frame->hd.stream_id);

    void *stream_data = nghttp2_session_get_stream_user_data(session, frame->hd.stream_id);

    if (__is_pending_stream(stream_data)) {
      pending_stream_t *ps = __get_pending_stream(stream_data);
      if (ps) {
        ps->headers_complete = true;
        VALK_INFO("Pending stream %d headers complete, waiting for arena", frame->hd.stream_id);
      }
      return 0;
    }

    valk_http2_server_request_t *req = (valk_http2_server_request_t *)stream_data;

    if (!req) {
      VALK_WARN("No request data for stream %d", frame->hd.stream_id);
      return 0;
    }

    if (conn->http.server && conn->http.server->lisp_handler_fn) {
      valk_lval_t *arena_qexpr = valk_http2_build_request_qexpr(req);

      valk_lval_t *handler = conn->http.server->lisp_handler_fn;
      valk_lenv_t *sandbox_env = conn->http.server->sandbox_env;
      valk_lval_t *response;

      valk_http_request_ctx_t *req_ctx = valk_mem_alloc(sizeof(valk_http_request_ctx_t));
      req_ctx->session = session;
      req_ctx->stream_id = frame->hd.stream_id;
      req_ctx->conn = conn;
      req_ctx->req = req;
      req_ctx->env = sandbox_env;

      conn->http.server->sys->current_request_ctx = req_ctx;

      valk_lval_t *ctx_ref = valk_lval_ref("http_req_ctx", req_ctx, NULL);

      u64 handler_arity = 1;
      if (LVAL_TYPE(handler) == LVAL_FUN && handler->fun.formals) {
        handler_arity = valk_lval_list_count(handler->fun.formals);
      }

      VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
        valk_lval_t *args;
        if (handler_arity >= 2) {
          args = valk_lval_cons(arena_qexpr, valk_lval_cons(ctx_ref, valk_lval_nil()));
        } else {
          args = valk_lval_cons(arena_qexpr, valk_lval_nil());
        }
        response = valk_lval_eval_call(sandbox_env, handler, args);
      }

      conn->http.server->sys->current_request_ctx = NULL;

      if (LVAL_TYPE(response) == LVAL_SYM && strcmp(response->str, ":deferred") == 0) {
        return 0;
      }

      if (LVAL_TYPE(response) == LVAL_HANDLE) {
        valk_async_handle_t *handle = response->async.handle;

        handle->allocator = (valk_mem_allocator_t*)req->stream_arena;
        handle->env = sandbox_env;

        valk_http_async_ctx_t *http_ctx = malloc(sizeof(valk_http_async_ctx_t));
        if (http_ctx) {
          http_ctx->session = session;
          http_ctx->stream_id = frame->hd.stream_id;
          http_ctx->conn = conn;
          http_ctx->arena = req->stream_arena;
          http_ctx->arena_slab_item = NULL;
          http_ctx->arena_slot = UINT32_MAX;

          handle->on_done = valk_http_async_done_callback;
          handle->on_done_ctx = http_ctx;
          handle->is_closed = valk_http_async_is_closed_callback;
          handle->is_closed_ctx = http_ctx;
        }

        for (valk_async_handle_t *p = handle->parent; p != NULL; p = p->parent) {
          valk_async_propagate_allocator(p, handle->allocator, sandbox_env);
        }
        valk_async_propagate_allocator(handle, handle->allocator, sandbox_env);

        if (handle->status == VALK_ASYNC_COMPLETED) {
          valk_lval_t *result = handle->result;
          if (LVAL_TYPE(result) == LVAL_ERR) {
            VALK_WARN("Handle completed with error: %s", result->str);
            VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
              valk_lval_t* error_items[] = {
                valk_lval_sym(":status"), valk_lval_str("500"),
                valk_lval_sym(":body"), valk_lval_str(result->str)
              };
              valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
              valk_http2_send_response(session, frame->hd.stream_id, error_resp, req->stream_arena);
            }
          } else {
            valk_http2_send_response(session, frame->hd.stream_id, result, req->stream_arena);
          }
          if (http_ctx) free(http_ctx);
        } else if (handle->status == VALK_ASYNC_FAILED) {
          valk_lval_t *err = handle->error ? handle->error : valk_lval_err("Handle failed");
          VALK_WARN("Handle failed: %s", LVAL_TYPE(err) == LVAL_ERR ? err->str : "unknown error");
          VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
            const char *err_msg = LVAL_TYPE(err) == LVAL_ERR ? err->str : "Async operation failed";
            valk_lval_t* error_items[] = {
              valk_lval_sym(":status"), valk_lval_str("500"),
              valk_lval_sym(":body"), valk_lval_str(err_msg)
            };
            valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
            valk_http2_send_response(session, frame->hd.stream_id, error_resp, req->stream_arena);
          }
          if (http_ctx) free(http_ctx);
        } else if (handle->status == VALK_ASYNC_CANCELLED) {
          VALK_DEBUG("Handle cancelled, sending 503 for stream %d", frame->hd.stream_id);
          VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
            valk_lval_t* error_items[] = {
              valk_lval_sym(":status"), valk_lval_str("503"),
              valk_lval_sym(":body"), valk_lval_str("Request cancelled")
            };
            valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
            valk_http2_send_response(session, frame->hd.stream_id, error_resp, req->stream_arena);
          }
          if (http_ctx) free(http_ctx);
        } else {
          VALK_DEBUG("Handle pending/running, will send response when complete");

          u32 slot = req->arena_slot;
          valk_http2_remove_from_active_arenas(conn, slot);

          if (http_ctx) {
            http_ctx->arena_slab_item = req->arena_slab_item;
            http_ctx->arena_slot = slot;
          }

          req->arena_slab_item = NULL;
          req->arena_slot = UINT32_MAX;

          return 0;
        }
        return 0;
      }

      if (LVAL_TYPE(response) == LVAL_ERR) {
        VALK_WARN("Handler returned error: %s", response->str);
        VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
          valk_lval_t* error_items[] = {
            valk_lval_sym(":status"), valk_lval_str("500"),
            valk_lval_sym(":body"), valk_lval_str(response->str)
          };
          valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
          valk_http2_send_response(session, frame->hd.stream_id, error_resp, req->stream_arena);
        }
      } else {
        valk_http2_send_response(session, frame->hd.stream_id, response, req->stream_arena);
      }
    } else {
      VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
        valk_lval_t* items[] = {
          valk_lval_sym(":status"), valk_lval_str("200"),
          valk_lval_sym(":content-type"), valk_lval_str("text/html; charset=utf-8"),
          valk_lval_sym(":body"), valk_lval_str(VALK_HTTP_MOTD)
        };
        valk_lval_t* default_resp = valk_lval_qlist(items, 6);
        valk_http2_send_response(session, frame->hd.stream_id, default_resp, req->stream_arena);
      }
    }
  }

  return 0;
}

static void __pending_stream_process_batch(valk_aio_system_t *sys) {
  while (sys && sys->pending_streams.count > 0) {
    valk_slab_item_t *arena_item = valk_slab_aquire(sys->httpStreamArenas);
    if (!arena_item) {
      VALK_DEBUG("No arenas available yet, %zu streams still pending", sys->pending_streams.count);
      return;
    }

    pending_stream_t *ps = valk_pending_stream_dequeue(&sys->pending_streams);
    VALK_ASSERT(ps != NULL, "pending_stream_count > 0 but dequeue returned NULL");
    VALK_ASSERT(ps->conn != NULL, "pending stream %d has NULL conn", ps->stream_id);
    VALK_ASSERT(ps->session != NULL, "pending stream %d has NULL session", ps->stream_id);

    void *current_data = nghttp2_session_get_stream_user_data(ps->session, ps->stream_id);
    VALK_ASSERT(current_data != NULL, "pending stream %d has NULL user_data", ps->stream_id);
    VALK_ASSERT(__is_pending_stream(current_data),
                "pending stream %d user_data is not a pending stream marker", ps->stream_id);

    u64 wait_ms = ps->conn->sys->ops->loop->now(ps->conn->sys) - ps->queued_time_ms;
    VALK_INFO("Processing pending stream %d (waited %llums)",
              ps->stream_id, (unsigned long)wait_ms);

    valk_mem_arena_t *stream_arena = (valk_mem_arena_t *)arena_item->data;
    valk_mem_arena_init(stream_arena, sys->config.arena_size);

#ifdef VALK_METRICS_ENABLED
    VALK_METRICS_IF(sys) {
      valk_aio_system_stats_on_arena_acquire(&VALK_SYSTEM_STATS(sys));
      valk_aio_system_stats_on_pending_dequeue(&VALK_SYSTEM_STATS(sys), wait_ms * 1000);
    }
#endif

    valk_http2_server_request_t *req;
    VALK_WITH_ALLOC((valk_mem_allocator_t*)stream_arena) {
      req = valk_mem_alloc(sizeof(valk_http2_server_request_t));
      memset(req, 0, sizeof(valk_http2_server_request_t));
      req->conn = ps->conn;
      req->stream_id = ps->stream_id;
      req->stream_arena = stream_arena;
      req->arena_slab_item = arena_item;
      req->arena_slot = (u32)(arena_item->handle & 0xFFFFFFFF);
      req->next_arena_slot = UINT32_MAX;

#ifdef VALK_METRICS_ENABLED
      req->start_time_us = (uv_hrtime() / 1000) - (wait_ms * 1000);
      req->bytes_sent = 0;
      req->bytes_recv = 0;
#endif

      if (ps->method) {
        u64 len = strlen(ps->method);
        req->method = valk_mem_alloc(len + 1);
        memcpy(req->method, ps->method, len + 1);
      }
      if (ps->scheme) {
        u64 len = strlen(ps->scheme);
        req->scheme = valk_mem_alloc(len + 1);
        memcpy(req->scheme, ps->scheme, len + 1);
      }
      if (ps->authority) {
        u64 len = strlen(ps->authority);
        req->authority = valk_mem_alloc(len + 1);
        memcpy(req->authority, ps->authority, len + 1);
      }
      if (ps->path) {
        u64 len = strlen(ps->path);
        req->path = valk_mem_alloc(len + 1);
        memcpy(req->path, ps->path, len + 1);
      }

      if (ps->header_count > 0) {
        req->headers.capacity = ps->header_count;
        req->headers.items = valk_mem_alloc(ps->header_count * sizeof(struct valk_http2_header_t));
        req->headers.count = ps->header_count;

        for (u64 i = 0; i < ps->header_count; i++) {
          pending_header_t *ph = &ps->headers[i];
          struct valk_http2_header_t *h = &req->headers.items[i];

          h->name = valk_mem_alloc(ph->name_len + 1);
          h->value = valk_mem_alloc(ph->value_len + 1);
          memcpy(h->name, ph->name, ph->name_len + 1);
          memcpy(h->value, ph->value, ph->value_len + 1);
          h->nameLen = ph->name_len;
          h->valueLen = ph->value_len;
        }
      }

      if (ps->body && ps->body_len > 0) {
        req->body = valk_mem_alloc(ps->body_len);
        memcpy(req->body, ps->body, ps->body_len);
        req->bodyLen = ps->body_len;
        req->bodyCapacity = ps->body_len;
      }
    }

    nghttp2_session_set_stream_user_data(ps->session, ps->stream_id, req);

    req->next_arena_slot = ps->conn->http.active_arena_head;
    ps->conn->http.active_arena_head = req->arena_slot;

    VALK_INFO("Pending stream %d converted to full request (arena slot %u)",
              ps->stream_id, req->arena_slot);

    if (ps->headers_complete) {
      if (ps->conn->http.server && ps->conn->http.server->lisp_handler_fn) {
        VALK_DEBUG("Pending stream %d had complete headers, triggering handler", ps->stream_id);

        valk_lval_t *arena_qexpr = valk_http2_build_request_qexpr(req);
        valk_lval_t *handler = ps->conn->http.server->lisp_handler_fn;
        valk_lenv_t *sandbox_env = ps->conn->http.server->sandbox_env;
        valk_lval_t *response;

        valk_http_request_ctx_t *req_ctx = valk_mem_alloc(sizeof(valk_http_request_ctx_t));
        req_ctx->session = ps->session;
        req_ctx->stream_id = ps->stream_id;
        req_ctx->conn = ps->conn;
        req_ctx->req = req;
        req_ctx->env = sandbox_env;

        sys->current_request_ctx = req_ctx;

        valk_lval_t *ctx_ref = valk_lval_ref("http_req_ctx", req_ctx, NULL);

        u64 handler_arity = 1;
        if (LVAL_TYPE(handler) == LVAL_FUN && handler->fun.formals) {
          handler_arity = valk_lval_list_count(handler->fun.formals);
        }

        VALK_WITH_ALLOC((valk_mem_allocator_t*)req->stream_arena) {
          valk_lval_t *args;
          if (handler_arity >= 2) {
            args = valk_lval_cons(arena_qexpr, valk_lval_cons(ctx_ref, valk_lval_nil()));
          } else {
            args = valk_lval_cons(arena_qexpr, valk_lval_nil());
          }
          response = valk_lval_eval_call(sandbox_env, handler, args);
        }

        sys->current_request_ctx = NULL;

        if (LVAL_TYPE(response) == LVAL_SYM && strcmp(response->str, ":deferred") == 0) {
        } else if (LVAL_TYPE(response) != LVAL_HANDLE) {
          valk_http2_send_response(ps->session, ps->stream_id, response, req->stream_arena);
        }
      }
    }

    valk_pending_stream_free(&sys->pending_streams, ps);
  }
}

int valk_http2_stream_reset(valk_aio_handle_t *conn, i32 stream_id, u32 error_code) {
  if (!conn || !conn->http.session) {
    return -1;
  }
  int rv = nghttp2_submit_rst_stream(conn->http.session, NGHTTP2_FLAG_NONE,
                                      stream_id, error_code);
  if (rv != 0) {
    VALK_ERROR("nghttp2_submit_rst_stream failed: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

int valk_http2_submit_goaway(valk_aio_handle_t *conn, u32 error_code) {
  if (!conn || !conn->http.session) {
    return -1;
  }
  int rv = nghttp2_submit_goaway(conn->http.session, NGHTTP2_FLAG_NONE,
                                  0, error_code, NULL, 0);
  if (rv != 0) {
    VALK_ERROR("nghttp2_submit_goaway failed: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

bool valk_aio_http_session_valid(valk_aio_handle_t *handle, void *session) {
  if (!handle || !session) {
    return false;
  }
  return handle->http.session == session;
}

bool valk_aio_http_connection_closing(valk_aio_handle_t *handle) {
  if (!handle) {
    return true;
  }
  return handle->http.state == VALK_CONN_CLOSING ||
         handle->http.state == VALK_CONN_CLOSED;
}
