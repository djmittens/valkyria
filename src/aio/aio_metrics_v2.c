// src/aio/aio_metrics_v2.c - AIO metrics V2 registry implementation
#include "aio_metrics_v2.h"
#include "common.h"
#include <string.h>

// LCOV_EXCL_BR_START - metrics init null checks are defensive
bool valk_aio_metrics_v2_init(valk_aio_metrics_v2_t *m, const char *system_name) {
  if (!m) return false;
  memset(m, 0, sizeof(*m));
  m->system_name = system_name;

  valk_label_set_v2_t labels = {0};
  if (system_name) {
    labels.labels[0] = (valk_label_v2_t){"system", system_name};
    labels.count = 1;
  }

  m->requests_total = valk_counter_get_or_create(
      "aio_requests_total", "Total HTTP requests completed", &labels);
  if (!m->requests_total) return false;
  valk_counter_set_persistent(m->requests_total);

  m->requests_active = valk_gauge_get_or_create(
      "aio_requests_active", "Currently active HTTP requests", &labels);
  if (!m->requests_active) return false;
  valk_gauge_set_persistent(m->requests_active);

  m->requests_errors = valk_counter_get_or_create(
      "aio_requests_errors", "Total HTTP request errors", &labels);
  if (!m->requests_errors) return false;
  valk_counter_set_persistent(m->requests_errors);

  m->request_bytes_sent = valk_counter_get_or_create(
      "aio_request_bytes_sent", "Total bytes sent in HTTP requests", &labels);
  if (!m->request_bytes_sent) return false;
  valk_counter_set_persistent(m->request_bytes_sent);

  m->request_bytes_recv = valk_counter_get_or_create(
      "aio_request_bytes_recv", "Total bytes received in HTTP requests", &labels);
  if (!m->request_bytes_recv) return false;
  valk_counter_set_persistent(m->request_bytes_recv);

  m->request_duration_us_sum = valk_counter_get_or_create(
      "aio_request_duration_us_sum", "Sum of request durations in microseconds", &labels);
  if (!m->request_duration_us_sum) return false;
  valk_counter_set_persistent(m->request_duration_us_sum);

  m->request_duration = valk_histogram_get_or_create(
      "aio_request_duration_seconds", "HTTP request duration histogram",
      VALK_REQUEST_DURATION_BUCKETS, VALK_REQUEST_DURATION_BUCKET_COUNT, &labels);
  if (!m->request_duration) return false;
  valk_histogram_set_persistent(m->request_duration);

  m->connections_total = valk_counter_get_or_create(
      "aio_connections_total", "Total connection attempts", &labels);
  if (!m->connections_total) return false;
  valk_counter_set_persistent(m->connections_total);

  m->connections_active = valk_gauge_get_or_create(
      "aio_connections_active", "Currently active connections", &labels);
  if (!m->connections_active) return false;
  valk_gauge_set_persistent(m->connections_active);

  m->connections_failed = valk_counter_get_or_create(
      "aio_connections_failed", "Total failed connection attempts", &labels);
  if (!m->connections_failed) return false;
  valk_counter_set_persistent(m->connections_failed);

  m->connections_rejected = valk_counter_get_or_create(
      "aio_connections_rejected", "Connections rejected at limit", &labels);
  if (!m->connections_rejected) return false;
  valk_counter_set_persistent(m->connections_rejected);

  m->connections_rejected_load = valk_counter_get_or_create(
      "aio_connections_rejected_load", "Connections rejected due to load", &labels);
  if (!m->connections_rejected_load) return false;
  valk_counter_set_persistent(m->connections_rejected_load);

  m->connections_connecting = valk_gauge_get_or_create(
      "aio_connections_connecting", "Connections being established", &labels);
  if (!m->connections_connecting) return false;
  valk_gauge_set_persistent(m->connections_connecting);

  m->connections_idle = valk_gauge_get_or_create(
      "aio_connections_idle", "Idle connections awaiting reuse", &labels);
  if (!m->connections_idle) return false;
  valk_gauge_set_persistent(m->connections_idle);

  m->connections_closing = valk_gauge_get_or_create(
      "aio_connections_closing", "Connections in graceful shutdown", &labels);
  if (!m->connections_closing) return false;
  valk_gauge_set_persistent(m->connections_closing);

  m->streams_total = valk_counter_get_or_create(
      "aio_streams_total", "Total HTTP/2 streams created", &labels);
  if (!m->streams_total) return false;
  valk_counter_set_persistent(m->streams_total);

  m->streams_active = valk_gauge_get_or_create(
      "aio_streams_active", "Currently active HTTP/2 streams", &labels);
  if (!m->streams_active) return false;
  valk_gauge_set_persistent(m->streams_active);

  m->bytes_sent_total = valk_counter_get_or_create(
      "aio_bytes_sent_total", "Total bytes sent", &labels);
  if (!m->bytes_sent_total) return false;
  valk_counter_set_persistent(m->bytes_sent_total);

  m->bytes_recv_total = valk_counter_get_or_create(
      "aio_bytes_recv_total", "Total bytes received", &labels);
  if (!m->bytes_recv_total) return false;
  valk_counter_set_persistent(m->bytes_recv_total);

  m->uptime_seconds = valk_gauge_get_or_create(
      "aio_uptime_seconds", "Time since metrics initialization", &labels);
  if (!m->uptime_seconds) return false;
  valk_gauge_set_persistent(m->uptime_seconds);

  return true;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - system stats init null checks are defensive
bool valk_aio_system_stats_v2_init(valk_aio_system_stats_v2_t *s,
                                    const char *system_name,
                                    u64 arenas_total,
                                    u64 tcp_buffers_total,
                                    u64 queue_capacity) {
  if (!s) return false;
  memset(s, 0, sizeof(*s));
  s->system_name = system_name;

  valk_label_set_v2_t labels = {0};
  if (system_name) {
    labels.labels[0] = (valk_label_v2_t){"system", system_name};
    labels.count = 1;
  }

  s->servers_count = valk_gauge_get_or_create(
      "aio_servers_count", "Number of HTTP servers", &labels);
  if (!s->servers_count) return false;
  valk_gauge_set_persistent(s->servers_count);

  s->clients_count = valk_gauge_get_or_create(
      "aio_clients_count", "Number of HTTP clients", &labels);
  if (!s->clients_count) return false;
  valk_gauge_set_persistent(s->clients_count);

  s->handles_count = valk_gauge_get_or_create(
      "aio_handles_count", "Total active handles", &labels);
  if (!s->handles_count) return false;
  valk_gauge_set_persistent(s->handles_count);

  s->arenas_used = valk_gauge_get_or_create(
      "aio_arenas_used", "Stream arenas in use", &labels);
  if (!s->arenas_used) return false;
  valk_gauge_set_persistent(s->arenas_used);

  s->arenas_total = valk_gauge_get_or_create(
      "aio_arenas_total", "Total stream arenas available", &labels);
  if (!s->arenas_total) return false;
  valk_gauge_set_persistent(s->arenas_total);
  valk_gauge_v2_set(s->arenas_total, (i64)arenas_total);

  s->tcp_buffers_used = valk_gauge_get_or_create(
      "aio_tcp_buffers_used", "TCP buffers in use", &labels);
  if (!s->tcp_buffers_used) return false;
  valk_gauge_set_persistent(s->tcp_buffers_used);

  s->tcp_buffers_total = valk_gauge_get_or_create(
      "aio_tcp_buffers_total", "Total TCP buffers available", &labels);
  if (!s->tcp_buffers_total) return false;
  valk_gauge_set_persistent(s->tcp_buffers_total);
  valk_gauge_v2_set(s->tcp_buffers_total, (i64)tcp_buffers_total);

  s->queue_depth = valk_gauge_get_or_create(
      "aio_queue_depth", "HTTP queue depth", &labels);
  if (!s->queue_depth) return false;
  valk_gauge_set_persistent(s->queue_depth);

  s->pending_requests = valk_gauge_get_or_create(
      "aio_pending_requests", "Pending HTTP requests", &labels);
  if (!s->pending_requests) return false;
  valk_gauge_set_persistent(s->pending_requests);

  s->pending_responses = valk_gauge_get_or_create(
      "aio_pending_responses", "Pending HTTP responses", &labels);
  if (!s->pending_responses) return false;
  valk_gauge_set_persistent(s->pending_responses);

  s->queue_capacity = valk_gauge_get_or_create(
      "aio_queue_capacity", "Queue capacity", &labels);
  if (!s->queue_capacity) return false;
  valk_gauge_set_persistent(s->queue_capacity);
  valk_gauge_v2_set(s->queue_capacity, (i64)queue_capacity);

  s->arena_pool_overflow = valk_counter_get_or_create(
      "aio_arena_pool_overflow_total", "Arena acquire failures", &labels);
  if (!s->arena_pool_overflow) return false;
  valk_counter_set_persistent(s->arena_pool_overflow);

  s->tcp_buffer_overflow = valk_counter_get_or_create(
      "aio_tcp_buffer_overflow_total", "TCP buffer acquire failures", &labels);
  if (!s->tcp_buffer_overflow) return false;
  valk_counter_set_persistent(s->tcp_buffer_overflow);

  s->connections_rejected_load = valk_counter_get_or_create(
      "aio_connections_rejected_load_total", "Connections rejected due to load", &labels);
  if (!s->connections_rejected_load) return false;
  valk_counter_set_persistent(s->connections_rejected_load);

  return true;
}
// LCOV_EXCL_BR_STOP
