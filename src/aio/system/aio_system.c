#include "aio_internal.h"
#include "aio_http2_session.h"
#include "aio_http2_server.h"
#include "aio_http2_client.h"
#include "aio_http2_conn.h"
#include "aio_metrics_v2.h"

void valk_aio_destroy(valk_aio_system_t *sys);
extern void __loop_stop_cb(uv_async_t *h);
extern void __gc_wakeup_cb(uv_async_t *handle);

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

  if (cfg->tcp_buffer_pool_size > 16 && cfg->tcp_buffer_pool_size < cfg->max_connections)
    return "tcp_buffer_pool_size must be >= max_connections (or <= 16 for testing)";

  if (cfg->arena_pool_size < cfg->max_connections / 10)
    return "arena_pool_size must be >= max_connections / 10";

  return nullptr;
}

int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg) {
  if (cfg->max_connections == 0) cfg->max_connections = 16;
  if (cfg->max_concurrent_streams == 0) cfg->max_concurrent_streams = 32;

  if (cfg->max_handles == 0) cfg->max_handles = 2056;
  if (cfg->max_servers == 0) cfg->max_servers = 8;
  if (cfg->max_clients == 0) cfg->max_clients = 8;
  if (cfg->max_connections_per_client == 0) cfg->max_connections_per_client = 2;
  if (cfg->max_timers == 0) cfg->max_timers = cfg->max_handles / 4;

  if (cfg->tcp_buffer_pool_size == 0) {
    u64 server_conns = cfg->max_servers * cfg->max_connections;
    u64 client_conns = cfg->max_clients * cfg->max_connections_per_client;
    u64 total_conns = server_conns + client_conns;
    cfg->tcp_buffer_pool_size = total_conns * 4;
  }

  if (cfg->arena_pool_size == 0) {
    u64 derived = (u64)cfg->max_connections * cfg->max_concurrent_streams;
    cfg->arena_pool_size = derived > 10000 ? 10000 : (u32)derived;
  }

  if (cfg->arena_size == 0)
    cfg->arena_size = 4 * 1024 * 1024;

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

  if (cfg->connection_idle_timeout_ms == 0) cfg->connection_idle_timeout_ms = 60000;
  if (cfg->maintenance_interval_ms == 0) cfg->maintenance_interval_ms = 1000;

  if (cfg->num_threads == 0) {
    unsigned int n = uv_available_parallelism();
    cfg->num_threads = n > 0 ? (u32)n : 4;
  }
  if (cfg->num_threads > 64) cfg->num_threads = 64;

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
  return valk_aio_start_with_config(nullptr);
}

valk_aio_system_t *valk_aio_start_with_config(valk_aio_system_config_t *config) {
  valk_aio_system_config_t resolved;
  if (config) {
    resolved = *config;
  } else {
    resolved = valk_aio_system_config_default();
  }

  if (valk_aio_system_config_resolve(&resolved) != 0) {
    return nullptr;
  }

  signal(SIGPIPE, SIG_IGN);

  valk_aio_system_t *sys = valk_mem_alloc(sizeof(valk_aio_system_t));
  memset(sys, 0, sizeof(valk_aio_system_t));
  sys->config = resolved;
  snprintf(sys->name, sizeof(sys->name), "main");

  valk_aio_ssl_start();

  sys->ops = &valk_aio_ops_production;

  u32 num_loops = resolved.num_threads;
  sys->num_loops = num_loops;
  sys->loops = calloc(num_loops, sizeof(valk_aio_loop_t));

  for (u32 i = 0; i < num_loops; i++) {
    valk_aio_loop_t *loop = &sys->loops[i];
    loop->sys = sys;
    loop->id = i;
    loop->thread_joined = false;

    loop->uv_loop = malloc(sizeof(uv_loop_t));
    uv_loop_init(loop->uv_loop);

    uv_async_init(loop->uv_loop, &loop->stopper, __loop_stop_cb);
    loop->stopper.data = loop;

    uv_async_init(loop->uv_loop, &loop->gc_wakeup, __gc_wakeup_cb);
    loop->gc_wakeup.data = loop;
    uv_unref((uv_handle_t *)&loop->gc_wakeup);
  }

  sys->eventloop = sys->loops[0].uv_loop;

  int rc = uv_loop_configure(sys->eventloop, UV_METRICS_IDLE_TIME);
  if (rc != 0) { // LCOV_EXCL_BR_LINE
    VALK_WARN("Failed to enable loop metrics: %s", uv_strerror(rc)); // LCOV_EXCL_LINE
  }

  memset(&sys->liveHandles, 0, sizeof(valk_aio_handle_t));
  sys->liveHandles.magic = VALK_AIO_HANDLE_MAGIC;
  sys->liveHandles.kind = VALK_HNDL_EMPTY;

  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    sys->httpServers = valk_slab_new(
        sizeof(valk_aio_http_server), sys->config.max_servers);
    sys->httpClients = valk_slab_new(
        sizeof(valk_aio_http2_client), sys->config.max_clients);
    sys->handleSlab = valk_slab_new(sizeof(valk_aio_handle_t), sys->config.max_handles);
  }

  sz system_arena_size = 16 * 1024 * 1024;
  valk_mem_arena_t *system_arena = malloc(sizeof(valk_mem_arena_t) + system_arena_size);
  valk_mem_arena_init(system_arena, system_arena_size);
  valk_region_init(&sys->system_region, VALK_LIFETIME_REQUEST, nullptr, system_arena);
  sys->system_region.owns_arena = true;

  valk_backpressure_list_init(&sys->backpressure, sys->config.backpressure_list_max,
                               sys->config.backpressure_timeout_ms);

  valk_conn_admission_init_from_config(&sys->admission,
                                        sys->config.buffer_high_watermark,
                                        sys->config.buffer_critical_watermark,
                                        sys->config.backpressure_timeout_ms);

  sys->port_strs = calloc(sys->config.max_servers, 8);
  if (!sys->port_strs) { // LCOV_EXCL_START
    VALK_ERROR("Failed to allocate port strings buffer");
    return nullptr;
  } // LCOV_EXCL_STOP

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
    sys->metrics_state->gc_heap = (valk_gc_heap_t*)valk_thread_ctx.heap;
    sys->metrics_state->scratch_arena = valk_thread_ctx.scratch;
  }
  memset(&sys->owner_registry, 0, sizeof(sys->owner_registry));
  valk_event_loop_metrics_v2_init(&sys->loop_metrics, sys->name);

  if (valk_sys->initialized) {
    valk_system_add_subsystem(valk_sys,
                             (void(*)(void*))valk_aio_stop,
                             (void(*)(void*))valk_aio_wait_for_shutdown,
                             (void(*)(void*))valk_aio_destroy,
                             sys);
  }

  uv_thread_options_t thread_opts = {
    .flags = UV_THREAD_HAS_STACK_SIZE,
    .stack_size = 8 * 1024 * 1024
  };

  for (u32 i = 0; i < num_loops; i++) {
    valk_aio_loop_t *loop = &sys->loops[i];
    uv_sem_init(&loop->ready_sem, 0);
    int status = uv_thread_create_ex(&loop->thread, &thread_opts, __loop_thread_fn, loop);
    if (status) { // LCOV_EXCL_START
      VALK_ERROR("Failed to create loop thread %u: %s", i, uv_strerror(status));
      return nullptr;
    } // LCOV_EXCL_STOP
  }

  for (u32 i = 0; i < num_loops; i++) {
    uv_sem_wait(&sys->loops[i].ready_sem);
  }

  return sys;
}

bool valk_aio_is_shutting_down(valk_aio_system_t *sys) {
  if (!sys) return true;
  return sys->shuttingDown;
}

void valk_aio_wait_for_shutdown(valk_aio_system_t *sys) {
  if (!sys) return;

  if (!sys->shuttingDown) {
    VALK_WARN("valk_aio_wait_for_shutdown: system not stopping, calling valk_aio_stop() automatically");
    valk_aio_stop(sys);
  }

  for (u32 i = 0; i < sys->num_loops; i++) {
    valk_aio_loop_t *loop = &sys->loops[i];
    if (!loop->thread_joined &&
        !valk_thread_equal(valk_thread_self(), (valk_thread_t)loop->thread)) {
      uv_thread_join(&loop->thread);
      loop->thread_joined = true;
    }
  }

  for (u32 i = 0; i < sys->num_loops; i++) {
    valk_aio_loop_task_queue_destroy(&sys->loops[i]);
  }

  free(sys->http_queue.request_items);
  free(sys->http_queue.response_items);
  valk_mutex_destroy(&sys->http_queue.request_mutex);
  valk_cond_destroy(&sys->http_queue.request_ready);
  valk_mutex_destroy(&sys->http_queue.response_mutex);
  valk_cond_destroy(&sys->http_queue.response_ready);

  valk_aio_http2_cleanup_all_servers(sys);

  free(sys->port_strs);

  if (sys->ops && sys->ops->loop) {
    sys->ops->loop->destroy(sys);
  }

  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    valk_slab_free(sys->httpServers);
    valk_slab_free(sys->httpClients);
    valk_slab_free(sys->handleSlab);
  }

  if (sys->system_region.owns_arena && sys->system_region.arena) {
    free(sys->system_region.arena);
  }

  for (u32 i = 0; i < sys->num_loops; i++) {
    uv_sem_destroy(&sys->loops[i].ready_sem);
  }

  free(sys->loops);

  sys->cleanedUp = true;
}

void valk_aio_destroy(valk_aio_system_t *sys) {
  if (!sys) return;
  free(sys);
}

void valk_aio_stop(valk_aio_system_t *sys) {
  if (!sys) return;

  bool expected = false;
  if (!atomic_compare_exchange_strong(&sys->shuttingDown, &expected, true)) {
    return;
  }

  for (u32 i = 0; i < sys->num_loops; i++) {
    uv_async_send(&sys->loops[i].stopper);
  }
}



void valk_aio_update_queue_stats(valk_aio_system_t* sys) {
  if (!sys || !sys->metrics_state) return;

  pthread_mutex_lock(&sys->http_queue.request_mutex);
  u64 pending_requests = sys->http_queue.request_count - sys->http_queue.request_idx;
  pthread_mutex_unlock(&sys->http_queue.request_mutex);

  pthread_mutex_lock(&sys->http_queue.response_mutex);
  u64 pending_responses = sys->http_queue.response_count - sys->http_queue.response_idx;
  pthread_mutex_unlock(&sys->http_queue.response_mutex);

  valk_aio_system_stats_v2_update_queue(
      (valk_aio_system_stats_v2_t*)sys->metrics_state->system_stats_v2,
      pending_requests, pending_responses);

  if (sys->tcpBufferSlab) {
    u64 available = valk_slab_available(sys->tcpBufferSlab);
    u64 total = sys->config.tcp_buffer_pool_size;
    u64 used = (available <= total) ? (total - available) : 0;
    valk_aio_system_stats_v2_t* s_v2 = (valk_aio_system_stats_v2_t*)sys->metrics_state->system_stats_v2;
    if (s_v2) valk_gauge_v2_set(s_v2->tcp_buffers_used, (i64)used);
  }

  if (sys->httpStreamArenas) {
    u64 available = valk_slab_available(sys->httpStreamArenas);
    u64 total = sys->config.arena_pool_size;
    u64 used = (available <= total) ? (total - available) : 0;
    valk_aio_system_stats_v2_t* s_v2 = (valk_aio_system_stats_v2_t*)sys->metrics_state->system_stats_v2;
    if (s_v2) valk_gauge_v2_set(s_v2->arenas_used, (i64)used);
  }
}

uv_loop_t* valk_aio_get_event_loop(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return sys->eventloop;
}

void valk_aio_update_loop_metrics(valk_aio_system_t* sys) {
  if (!sys || !sys->eventloop) return;
  valk_event_loop_metrics_v2_update(&sys->loop_metrics, sys->eventloop);
  i64 handle_count = 0;
  valk_aio_handle_t *h = sys->liveHandles.next;
  while (h && h != &sys->liveHandles) {
    handle_count++;
    h = h->next;
  }
  valk_event_loop_metrics_v2_set_handles(&sys->loop_metrics, handle_count);
}

const char* valk_aio_get_name(valk_aio_system_t* sys) {
  if (!sys) return "unknown";
  return sys->name;
}

void valk_aio_set_name(valk_aio_system_t* sys, const char* name) {
  if (!sys || !name) return;
  snprintf(sys->name, sizeof(sys->name), "%s", name);
}

valk_gc_heap_t* valk_aio_get_gc_heap(valk_aio_system_t* sys) {
  if (!sys || !sys->metrics_state) return nullptr;
  return (valk_gc_heap_t*)sys->metrics_state->gc_heap;
}

valk_mem_arena_t* valk_aio_get_scratch_arena(valk_aio_system_t* sys) {
  if (!sys || !sys->metrics_state) return nullptr;
  return (valk_mem_arena_t*)sys->metrics_state->scratch_arena;
}
