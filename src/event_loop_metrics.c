// src/event_loop_metrics.c
// Event Loop Metrics implementation
#include "event_loop_metrics.h"
#include "log.h"
#include <uv.h>
#include <string.h>

// ============================================================================
// FACTORY IMPLEMENTATION
// ============================================================================

bool valk_event_loop_metrics_v2_init(valk_event_loop_metrics_v2_t *m,
                                      const char *loop_name) {
  if (!m || !loop_name) return false;

  memset(m, 0, sizeof(*m));
  m->loop_name = loop_name;

  // Build label set with loop name
  valk_label_set_v2_t labels = {
    .labels = {{.key = "loop", .value = loop_name}},
    .count = 1,
    .hash = 0  // Will be computed by get_or_create
  };

  // LCOV_EXCL_BR_START - metric creation failure: requires registry exhaustion
  m->iterations = valk_counter_get_or_create("event_loop_iterations",
    "Total event loop iterations", &labels);
  if (!m->iterations) return false;
  valk_counter_set_persistent(m->iterations);

  m->events = valk_counter_get_or_create("event_loop_events",
    "Total I/O events processed", &labels);
  if (!m->events) return false;
  valk_counter_set_persistent(m->events);

  m->events_waiting = valk_gauge_get_or_create("event_loop_events_waiting",
    "Events currently waiting to be processed", &labels);
  if (!m->events_waiting) return false;
  valk_gauge_set_persistent(m->events_waiting);

  m->idle_time_us = valk_gauge_get_or_create("event_loop_idle_us",
    "Cumulative time spent idle in kernel poll (microseconds)", &labels);
  if (!m->idle_time_us) return false;
  valk_gauge_set_persistent(m->idle_time_us);

  m->handles = valk_gauge_get_or_create("event_loop_handles",
    "Number of active handles (sockets, timers, etc.)", &labels);
  if (!m->handles) return false;
  valk_gauge_set_persistent(m->handles);

  m->busy_pct = valk_gauge_get_or_create("event_loop_busy_pct",
    "Event loop busy percentage (0-100)", &labels);
  if (!m->busy_pct) return false;
  valk_gauge_set_persistent(m->busy_pct);

  m->iter_rate = valk_gauge_get_or_create("event_loop_iter_rate",
    "Event loop iterations per second", &labels);
  if (!m->iter_rate) return false;
  valk_gauge_set_persistent(m->iter_rate);
  // LCOV_EXCL_BR_STOP

  m->prev_idle_ns = 0;
  m->prev_update_ns = uv_hrtime();

  return true;
}

// ============================================================================
// UPDATE HELPERS
// ============================================================================

void valk_event_loop_metrics_v2_update(valk_event_loop_metrics_v2_t *m,
                                        struct uv_loop_s *loop) {
  if (!m || !loop) return;

  // LCOV_EXCL_START - libuv metric collection: error path and delta checks
  uv_metrics_t metrics;
  int rc = uv_metrics_info(loop, &metrics);
  if (rc != 0) {
    static bool warned = false;
    if (!warned) {
      VALK_WARN("uv_metrics_info failed: %s", uv_strerror(rc));
      warned = true;
    }
    return;
  }
  // LCOV_EXCL_STOP

  u64 iter_delta = metrics.loop_count - m->prev_iterations;
  u64 events_delta = metrics.events - m->prev_events;

  if (iter_delta > 0 && m->iterations) {
    valk_counter_v2_add(m->iterations, iter_delta);
  }
  if (events_delta > 0 && m->events) {
    valk_counter_v2_add(m->events, events_delta);
  }

  if (m->events_waiting) {
    valk_gauge_v2_set(m->events_waiting, (i64)metrics.events_waiting);
  }

  // Get idle time (requires UV_METRICS_IDLE_TIME option)
  // Returns nanoseconds, convert to microseconds
  u64 idle_ns = uv_metrics_idle_time(loop);
  if (m->idle_time_us) {
    valk_gauge_v2_set(m->idle_time_us, (i64)(idle_ns / 1000));
  }

  // Compute busy percentage and iteration rate from deltas
  u64 now_ns = uv_hrtime();
  u64 wall_delta = now_ns - m->prev_update_ns;
  u64 idle_delta = idle_ns - m->prev_idle_ns;

  if (wall_delta > 0) {
    // busy% = 100 * (1 - idle_delta / wall_delta)
    if (m->busy_pct) {
      i64 busy = 100 - (i64)(100 * idle_delta / wall_delta);
      if (busy < 0) busy = 0;
      if (busy > 100) busy = 100;
      valk_gauge_v2_set(m->busy_pct, busy);
    }

    // iter_rate = iter_delta / wall_delta_seconds (use iter_delta computed above)
    if (m->iter_rate) {
      i64 rate = (i64)(iter_delta * 1000000000ULL / wall_delta);
      valk_gauge_v2_set(m->iter_rate, rate);
    }
  }

  // Update prev values AFTER computing deltas
  m->prev_iterations = metrics.loop_count;
  m->prev_events = metrics.events;
  m->prev_idle_ns = idle_ns;
  m->prev_update_ns = now_ns;
}

void valk_event_loop_metrics_v2_set_handles(valk_event_loop_metrics_v2_t *m,
                                             i64 handles) {
  if (!m || !m->handles) return;
  valk_gauge_v2_set(m->handles, handles);
}
