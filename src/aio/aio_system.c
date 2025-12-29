#include "aio_internal.h"
#include "aio_http2_session.h"
#include "aio_http2_server.h"
#include "aio_http2_client.h"
#include "aio_http2_conn.h"

extern void __event_loop(void *arg);
extern void __aio_uv_stop(uv_async_t *h);

const char *valk_aio_system_config_validate(const valk_aio_system_config_t *cfg) {
  if (cfg->max_connections < 1 || cfg->max_connections > 100000)
    return "max_connections must be between 1 and 100,000";

  if (cfg->max_concurrent_streams < 1 || cfg->max_concurrent_streams > 1000)
    return "max_concurrent_streams must be between 1 and 1,000";

  if (cfg->max_handles < 16 || cfg->max_handles > 100000)
    return "max_handles must be between 16 and 100,000";

  if (cfg->max_servers < 1 || cfg->max_servers > 64)
    return "max_servers must be between 1 and 64";

  if (cfg->max_clients < 1 || cfg->max_clients > 64)
    return "max_clients must be between 1 and 64";

  if (cfg->tcp_buffer_pool_size < 2 || cfg->tcp_buffer_pool_size > 1000000)
    return "tcp_buffer_pool_size must be between 2 and 1,000,000";

  if (cfg->arena_pool_size < 1 || cfg->arena_pool_size > 10000)
    return "arena_pool_size must be between 1 and 10,000";

  if (cfg->arena_size < (1 << 20) || cfg->arena_size > (256ULL << 20))
    return "arena_size must be between 1MB and 256MB";

  if (cfg->max_request_body_size < (1 << 10) || cfg->max_request_body_size > (1ULL << 30))
    return "max_request_body_size must be between 1KB and 1GB";

  if (cfg->queue_capacity < 2 || cfg->queue_capacity > 100000)
    return "queue_capacity must be between 2 and 100,000";

  if (cfg->backpressure_list_max < 1 || cfg->backpressure_list_max > BACKPRESSURE_LIST_MAX_LIMIT)
    return "backpressure_list_max must be between 1 and 100,000";

  if (cfg->backpressure_timeout_ms < 1000 || cfg->backpressure_timeout_ms > 600000)
    return "backpressure_timeout_ms must be between 1,000 and 600,000 (1s-10min)";

  if (cfg->pending_stream_pool_size < 1 || cfg->pending_stream_pool_size > PENDING_STREAM_POOL_MAX_LIMIT)
    return "pending_stream_pool_size must be between 1 and 10,000";

  if (cfg->tcp_buffer_pool_size > 16 && cfg->tcp_buffer_pool_size < cfg->max_connections)
    return "tcp_buffer_pool_size must be >= max_connections (or <= 16 for testing)";

  if (cfg->arena_pool_size < cfg->max_connections / 10)
    return "arena_pool_size must be >= max_connections / 10";

  return NULL;
}

int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg) {
  if (cfg->max_connections == 0) cfg->max_connections = 100;
  if (cfg->max_concurrent_streams == 0) cfg->max_concurrent_streams = 100;

  if (cfg->max_handles == 0) cfg->max_handles = 2056;
  if (cfg->max_servers == 0) cfg->max_servers = 8;
  if (cfg->max_clients == 0) cfg->max_clients = 8;
  if (cfg->max_connections_per_client == 0) cfg->max_connections_per_client = 2;

  if (cfg->tcp_buffer_pool_size == 0) {
    u64 server_conns = cfg->max_servers * cfg->max_connections;
    u64 client_conns = cfg->max_clients * cfg->max_connections_per_client;
    u64 total_conns = server_conns + client_conns;
    cfg->tcp_buffer_pool_size = total_conns * 4;
  }

  if (cfg->arena_pool_size == 0) {
    cfg->arena_pool_size = cfg->max_connections * 4;
    if (cfg->arena_pool_size > 1024) cfg->arena_pool_size = 1024;
    if (cfg->arena_pool_size < 64) cfg->arena_pool_size = 64;
  }

  if (cfg->arena_size == 0)
    cfg->arena_size = 64 * 1024 * 1024;

  if (cfg->max_request_body_size == 0)
    cfg->max_request_body_size = 8 * 1024 * 1024;

  if (cfg->queue_capacity == 0)
    cfg->queue_capacity = cfg->max_connections * 2;

  if (cfg->buffer_high_watermark == 0.0f)
    cfg->buffer_high_watermark = 0.85f;

  if (cfg->buffer_critical_watermark == 0.0f)
    cfg->buffer_critical_watermark = 0.95f;

  if (cfg->min_buffers_per_conn == 0)
    cfg->min_buffers_per_conn = BUFFERS_PER_CONNECTION;

  if (cfg->backpressure_list_max == 0) cfg->backpressure_list_max = 1000;
  if (cfg->backpressure_timeout_ms == 0) cfg->backpressure_timeout_ms = 30000;
  if (cfg->pending_stream_pool_size == 0) cfg->pending_stream_pool_size = 64;
  if (cfg->pending_stream_timeout_ms == 0) cfg->pending_stream_timeout_ms = 10000;

  if (cfg->connection_idle_timeout_ms == 0) cfg->connection_idle_timeout_ms = 60000;
  if (cfg->maintenance_interval_ms == 0) cfg->maintenance_interval_ms = 1000;

  if (cfg->buffer_high_watermark >= cfg->buffer_critical_watermark) {
    fprintf(stderr, "AIO config error: buffer_high_watermark must be < buffer_critical_watermark\n");
    return -1;
  }

  const char *err = valk_aio_system_config_validate(cfg);
  if (err) {
    fprintf(stderr, "AIO config error: %s\n", err);
    return -1;
  }

  return 0;
}

valk_aio_system_t *valk_aio_start(void) {
  return valk_aio_start_with_config(NULL);
}

valk_aio_system_t *valk_aio_start_with_config(valk_aio_system_config_t *config) {
  valk_aio_system_config_t resolved;
  if (config) {
    resolved = *config;
  } else {
    resolved = valk_aio_system_config_default();
  }

  if (valk_aio_system_config_resolve(&resolved) != 0) {
    return NULL;
  }

  signal(SIGPIPE, SIG_IGN);

  valk_aio_system_t *sys = valk_mem_alloc(sizeof(valk_aio_system_t));
  memset(sys, 0, sizeof(valk_aio_system_t));
  sys->config = resolved;
  snprintf(sys->name, sizeof(sys->name), "main");

  valk_aio_ssl_start();

  sys->ops = &valk_aio_ops_production;

  int init_rc = sys->ops->loop->init(sys);
  if (init_rc != 0) {
    VALK_ERROR("Failed to initialize event loop");
    free(sys);
    return NULL;
  }

#ifdef VALK_METRICS_ENABLED
  int rc = uv_loop_configure(sys->eventloop, UV_METRICS_IDLE_TIME);
  if (rc != 0) {
    VALK_WARN("Failed to enable loop metrics: %s", uv_strerror(rc));
  }
#endif

  memset(&sys->liveHandles, 0, sizeof(valk_aio_handle_t));
  sys->liveHandles.magic = VALK_AIO_HANDLE_MAGIC;
  sys->liveHandles.kind = VALK_HNDL_EMPTY;

  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    sys->httpServers = valk_slab_new(
        sizeof(valk_arc_box) + sizeof(valk_aio_http_server), sys->config.max_servers);
    sys->httpClients = valk_slab_new(
        sizeof(valk_arc_box) + sizeof(valk_aio_http2_client), sys->config.max_clients);
    sys->handleSlab = valk_slab_new(sizeof(valk_aio_handle_t), sys->config.max_handles);
  }

  if (valk_pending_stream_queue_init(&sys->pending_streams, sys->config.pending_stream_pool_size) != 0) {
    VALK_ERROR("Failed to allocate pending stream pool");
    return NULL;
  }
  valk_backpressure_list_init(&sys->backpressure, sys->config.backpressure_list_max,
                               sys->config.backpressure_timeout_ms);

  valk_conn_admission_init_from_config(&sys->admission,
                                        sys->config.buffer_high_watermark,
                                        sys->config.buffer_critical_watermark,
                                        sys->config.backpressure_timeout_ms);

  sys->port_strs = calloc(sys->config.max_servers, 8);
  if (!sys->port_strs) {
    VALK_ERROR("Failed to allocate port strings buffer");
    valk_pending_stream_queue_destroy(&sys->pending_streams);
    return NULL;
  }

  sys->http_queue.request_items = malloc(sizeof(valk_http_request_item_t) * sys->config.queue_capacity);
  sys->http_queue.request_idx = 0;
  sys->http_queue.request_count = 0;
  sys->http_queue.request_capacity = sys->config.queue_capacity;
  valk_mutex_init(&sys->http_queue.request_mutex);
  valk_cond_init(&sys->http_queue.request_ready);

  sys->http_queue.response_items = malloc(sizeof(valk_http_response_item_t) * sys->config.queue_capacity);
  sys->http_queue.response_idx = 0;
  sys->http_queue.response_count = 0;
  sys->http_queue.response_capacity = sys->config.queue_capacity;
  valk_mutex_init(&sys->http_queue.response_mutex);
  valk_cond_init(&sys->http_queue.response_ready);

#ifdef VALK_METRICS_ENABLED
  static bool metrics_initialized = false;
  if (!metrics_initialized) {
    valk_metrics_registry_init();
    metrics_initialized = true;
  }
  sys->metrics_state = valk_aio_metrics_state_new(
      sys->config.arena_pool_size,
      sys->config.tcp_buffer_pool_size,
      sys->config.queue_capacity,
      sys->name);
  if (sys->metrics_state) {
    sys->metrics_state->gc_heap = (valk_gc_malloc_heap_t*)valk_thread_ctx.heap;
    sys->metrics_state->scratch_arena = valk_thread_ctx.scratch;
  }
  memset(&sys->owner_registry, 0, sizeof(sys->owner_registry));
  valk_sse_registry_init(&sys->sse_registry, sys);
  valk_event_loop_metrics_v2_init(&sys->loop_metrics, sys->name);
#endif

  sys->stopperHandle = (valk_aio_handle_t *)valk_slab_aquire(sys->handleSlab)->data;
  memset(sys->stopperHandle, 0, sizeof(valk_aio_handle_t));
  sys->stopperHandle->magic = VALK_AIO_HANDLE_MAGIC;
  sys->stopperHandle->kind = VALK_HNDL_TASK;
  sys->stopperHandle->sys = sys;
  sys->stopperHandle->uv.task.data = sys->stopperHandle;
  uv_async_init(sys->eventloop, &sys->stopperHandle->uv.task, __aio_uv_stop);
  valk_dll_insert_after(&sys->liveHandles, sys->stopperHandle);

  if (uv_sem_init(&sys->startup_sem, 0) != 0) {
    VALK_ERROR("Failed to initialize startup semaphore");
    return NULL;
  }

  // Use uv_thread_create_ex with a larger stack size (8MB) to support
  // deep Lisp recursion. Default thread stack is ~512KB which overflows
  // with recursive evaluators running Lisp handlers.
  uv_thread_options_t thread_opts = {
    .flags = UV_THREAD_HAS_STACK_SIZE,
    .stack_size = 8 * 1024 * 1024  // 8MB stack
  };
  int status = uv_thread_create_ex(&sys->loopThread, &thread_opts, __event_loop, sys);
  if (status) {
    perror("uv_thread_create_ex");
    uv_sem_destroy(&sys->startup_sem);
    return NULL;
  }

  uv_sem_wait(&sys->startup_sem);

  return sys;
}

bool valk_aio_is_shutting_down(valk_aio_system_t *sys) {
  if (!sys) return true;
  return sys->shuttingDown;
}

void valk_aio_wait_for_shutdown(valk_aio_system_t *sys) {
  if (!sys) return;

  if (!valk_thread_equal(valk_thread_self(), (valk_thread_t)sys->loopThread)) {
    uv_thread_join(&sys->loopThread);
  }

#ifdef VALK_METRICS_ENABLED
  valk_sse_registry_shutdown(&sys->sse_registry);
#endif

  free(sys->http_queue.request_items);
  free(sys->http_queue.response_items);
  valk_mutex_destroy(&sys->http_queue.request_mutex);
  valk_cond_destroy(&sys->http_queue.request_ready);
  valk_mutex_destroy(&sys->http_queue.response_mutex);
  valk_cond_destroy(&sys->http_queue.response_ready);

  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    valk_slab_free(sys->httpServers);
    valk_slab_free(sys->httpClients);
    valk_slab_free(sys->handleSlab);
  }

  valk_pending_stream_queue_destroy(&sys->pending_streams);
  free(sys->port_strs);

  if (sys->ops && sys->ops->loop) {
    sys->ops->loop->destroy(sys);
  }

  uv_sem_destroy(&sys->startup_sem);

  sys->cleanedUp = true;
  free(sys);
}

void valk_aio_stop(valk_aio_system_t *sys) {
  if (!sys) return;

  if (sys->shuttingDown) {
    return;
  }

  sys->shuttingDown = true;
  
  if (!sys->stopperHandle) {
    VALK_ERROR("valk_aio_stop: stopperHandle is NULL!");
    return;
  }
  if (sys->stopperHandle->magic != VALK_AIO_HANDLE_MAGIC) {
    VALK_ERROR("valk_aio_stop: stopperHandle magic is invalid: 0x%x",
               sys->stopperHandle->magic);
    return;
  }
  if (uv_is_closing((uv_handle_t*)&sys->stopperHandle->uv.task)) {
    VALK_ERROR("valk_aio_stop: stopperHandle is already closing!");
    return;
  }
  
  int rv = uv_async_send(&sys->stopperHandle->uv.task);
  if (rv != 0) {
    VALK_ERROR("valk_aio_stop: uv_async_send failed: %s", uv_strerror(rv));
  }
}

#ifdef VALK_METRICS_ENABLED
valk_aio_metrics_t* valk_aio_get_metrics(valk_aio_system_t* sys) {
  if (!sys || !sys->metrics_state) return nullptr;
  return &sys->metrics_state->metrics;
}

valk_aio_system_stats_t* valk_aio_get_system_stats(valk_aio_system_t* sys) {
  if (!sys || !sys->metrics_state) return nullptr;
  return &sys->metrics_state->system_stats;
}

valk_http_clients_registry_t* valk_aio_get_http_clients_registry(valk_aio_system_t* sys) {
  if (!sys || !sys->metrics_state) return nullptr;
  return &sys->metrics_state->http_clients;
}

void valk_aio_update_queue_stats(valk_aio_system_t* sys) {
  if (!sys || !sys->metrics_state) return;

  pthread_mutex_lock(&sys->http_queue.request_mutex);
  u64 pending_requests = sys->http_queue.request_count - sys->http_queue.request_idx;
  pthread_mutex_unlock(&sys->http_queue.request_mutex);

  pthread_mutex_lock(&sys->http_queue.response_mutex);
  u64 pending_responses = sys->http_queue.response_count - sys->http_queue.response_idx;
  pthread_mutex_unlock(&sys->http_queue.response_mutex);

  valk_aio_system_stats_update_queue(&sys->metrics_state->system_stats, pending_requests, pending_responses);

  if (sys->tcpBufferSlab) {
    u64 available = valk_slab_available(sys->tcpBufferSlab);
    u64 total = sys->config.tcp_buffer_pool_size;
    u64 used = (available <= total) ? (total - available) : 0;
    atomic_store(&sys->metrics_state->system_stats.tcp_buffers_used, used);
  }

  if (sys->httpStreamArenas) {
    u64 available = valk_slab_available(sys->httpStreamArenas);
    u64 total = sys->config.arena_pool_size;
    u64 used = (available <= total) ? (total - available) : 0;
    atomic_store(&sys->metrics_state->system_stats.arenas_used, used);
  }
}
#endif

uv_loop_t* valk_aio_get_event_loop(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return sys->eventloop;
}

void valk_aio_update_loop_metrics(valk_aio_system_t* sys) {
#ifdef VALK_METRICS_ENABLED
  if (!sys || !sys->eventloop) return;
  valk_event_loop_metrics_v2_update(&sys->loop_metrics, sys->eventloop);
  i64 handle_count = 0;
  valk_aio_handle_t *h = sys->liveHandles.next;
  while (h && h != &sys->liveHandles) {
    handle_count++;
    h = h->next;
  }
  valk_event_loop_metrics_v2_set_handles(&sys->loop_metrics, handle_count);
#else
  (void)sys;
#endif
}

const char* valk_aio_get_name(valk_aio_system_t* sys) {
  if (!sys) return "unknown";
  return sys->name;
}

void valk_aio_set_name(valk_aio_system_t* sys, const char* name) {
  if (!sys || !name) return;
  snprintf(sys->name, sizeof(sys->name), "%s", name);
}

#ifdef VALK_METRICS_ENABLED
valk_gc_malloc_heap_t* valk_aio_get_gc_heap(valk_aio_system_t* sys) {
  if (!sys || !sys->metrics_state) return nullptr;
  return (valk_gc_malloc_heap_t*)sys->metrics_state->gc_heap;
}

valk_mem_arena_t* valk_aio_get_scratch_arena(valk_aio_system_t* sys) {
  if (!sys || !sys->metrics_state) return nullptr;
  return (valk_mem_arena_t*)sys->metrics_state->scratch_arena;
}

valk_sse_stream_registry_t* valk_aio_get_sse_registry(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return &sys->sse_registry;
}
#endif
