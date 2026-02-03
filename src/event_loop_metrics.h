// src/event_loop_metrics.h
// Event Loop Metrics - Standard metrics for libuv event loops
#ifndef VALK_EVENT_LOOP_METRICS_H
#define VALK_EVENT_LOOP_METRICS_H

#include "metrics_v2.h"

// Forward declaration
struct uv_loop_s;

// ============================================================================
// EVENT LOOP METRICS BUNDLE
// ============================================================================

// Standard metrics for a libuv event loop
// These are marked as persistent (non-evictable) at creation
typedef struct {
  valk_counter_v2_t *iterations;      // Loop iterations (monotonic)
  valk_counter_v2_t *events;          // Total events processed (monotonic)
  valk_gauge_v2_t *events_waiting;    // Events currently waiting
  valk_gauge_v2_t *idle_time_us;      // Cumulative idle time in microseconds
  valk_gauge_v2_t *handles;           // Active handle count
  valk_gauge_v2_t *busy_pct;          // Busy percentage (0-100) computed from idle delta
  valk_gauge_v2_t *iter_rate;         // Iterations per second (computed from delta)
  const char *loop_name;              // For debugging

  // Previous values for delta tracking (counters are monotonic from libuv)
  u64 prev_iterations;
  u64 prev_events;
  u64 prev_idle_ns;                   // Previous idle time for busy% calculation
  u64 prev_update_ns;                 // Previous update timestamp (hrtime)
} valk_event_loop_metrics_v2_t;

// ============================================================================
// FACTORY API
// ============================================================================

// Create standard metrics for an event loop with loop={name} label
// All metrics are created and marked as persistent (non-evictable)
// Returns true on success, false if registry is full
// Metric names:
//   event_loop_iterations{loop="name"}
//   event_loop_events{loop="name"}
//   event_loop_events_waiting{loop="name"}
//   event_loop_idle_us{loop="name"}
//   event_loop_handles{loop="name"}
bool valk_event_loop_metrics_v2_init(valk_event_loop_metrics_v2_t *m,
                                      const char *loop_name);

// ============================================================================
// UPDATE HELPERS
// ============================================================================

// Update metrics by reading current state from libuv loop
// Should be called periodically (e.g., each loop iteration or on timer)
void valk_event_loop_metrics_v2_update(valk_event_loop_metrics_v2_t *m,
                                        struct uv_loop_s *loop);

// Update handles count separately (if not reading from libuv directly)
void valk_event_loop_metrics_v2_set_handles(valk_event_loop_metrics_v2_t *m,
                                             i64 handles);

#endif // VALK_EVENT_LOOP_METRICS_H
