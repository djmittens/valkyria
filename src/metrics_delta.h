// Line 1-120 (new file)
#ifndef VALK_METRICS_DELTA_H
#define VALK_METRICS_DELTA_H

#include "metrics_v2.h"

// ============================================================================
// DELTA SNAPSHOT STRUCTURE
// ============================================================================

// Change type for a metric
typedef enum {
  VALK_DELTA_NONE,       // No change since last snapshot
  VALK_DELTA_INCREMENT,  // Counter increased
  VALK_DELTA_SET,        // Gauge changed
  VALK_DELTA_OBSERVE,    // Histogram received observations
} valk_delta_type_e;

// Single metric delta
typedef struct {
  const char *name;
  valk_label_set_v2_t *labels;
  valk_delta_type_e type;
  union {
    u64 increment;     // For counters: delta value
    i64 value;          // For gauges: new value
    struct {                // For histograms
      u64 bucket_deltas[VALK_MAX_BUCKETS + 1];
      u64 count_delta;
      u64 sum_delta_micros;
      const double *bucket_bounds;
      u8 bucket_count;
    } histogram;
  } data;
} valk_metric_delta_t;

// Delta snapshot (collection of changes)
typedef struct {
  u64 timestamp_us;
  u64 prev_timestamp_us;
  u64 interval_us;

  // Changed metrics
  valk_metric_delta_t *deltas;
  u64 delta_count;
  u64 delta_capacity;

  // Summary statistics
  u64 counters_changed;
  u64 gauges_changed;
  u64 histograms_changed;
  u64 summaries_changed;
} valk_delta_snapshot_t;

// ============================================================================
// PER-CONNECTION BASELINE (for multi-client delta tracking)
// ============================================================================

// Stores baseline values for a single SSE connection
// This allows multiple connections to independently track deltas
typedef struct {
  // Counter baselines (indexed same as registry)
  u64 counter_baselines[VALK_REGISTRY_MAX_COUNTERS];

  // Gauge baselines
  i64 gauge_baselines[VALK_REGISTRY_MAX_GAUGES];

  // Histogram baselines
  struct {
    u64 buckets[VALK_MAX_BUCKETS + 1];
    u64 count;
    u64 sum_micros;
  } histogram_baselines[VALK_REGISTRY_MAX_HISTOGRAMS];

  // Timestamp of last collection
  u64 last_collect_time;

  // Whether this baseline has been initialized from registry
  bool initialized;
} valk_metrics_baseline_t;

// Initialize baseline (call once per connection)
void valk_metrics_baseline_init(valk_metrics_baseline_t *baseline);

// Initialize baseline from current registry values (call on first connect)
void valk_metrics_baseline_sync(valk_metrics_baseline_t *baseline,
                                 valk_metrics_registry_t *registry);

// ============================================================================
// DELTA COLLECTION API
// ============================================================================

// Initialize delta snapshot
void valk_delta_snapshot_init(valk_delta_snapshot_t *snap);

// Collect deltas from registry (compares with internal last_* fields)
// Returns number of changed metrics
// DEPRECATED: Use valk_delta_snapshot_collect_stateless for multi-client
u64 valk_delta_snapshot_collect(valk_delta_snapshot_t *snap,
                                    valk_metrics_registry_t *registry);

// Collect deltas using per-connection baseline (doesn't modify global state)
// This is safe to call from multiple timers concurrently
// Returns number of changed metrics
u64 valk_delta_snapshot_collect_stateless(valk_delta_snapshot_t *snap,
                                              valk_metrics_registry_t *registry,
                                              valk_metrics_baseline_t *baseline);

// Free delta snapshot resources
void valk_delta_snapshot_free(valk_delta_snapshot_t *snap);

// ============================================================================
// DELTA ENCODING FORMATS
// ============================================================================

// Encode delta to JSON (for SSE streaming)
// Format: {"ts":123,"interval":1000,"deltas":[...]}
u64 valk_delta_to_json(const valk_delta_snapshot_t *snap,
                          char *buf, u64 buf_size);

// Encode delta to SSE event
// Format: event: metrics-delta\nid: <ts>\ndata: <json>\n\n
u64 valk_delta_to_sse(const valk_delta_snapshot_t *snap,
                         char *buf, u64 buf_size);

// Encode delta to Prometheus exposition format (for /metrics endpoint)
// Only includes metrics that changed (with full current value)
u64 valk_delta_to_prometheus(const valk_delta_snapshot_t *snap,
                                valk_metrics_registry_t *registry,
                                char *buf, u64 buf_size);

// Export full metrics state as JSON (for diagnostics/dashboard)
// Returns the number of bytes written
u64 valk_metrics_v2_to_json(valk_metrics_registry_t *registry,
                               char *buf, u64 buf_size);

#endif // VALK_METRICS_DELTA_H
