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
    uint64_t increment;     // For counters: delta value
    int64_t value;          // For gauges: new value
    struct {                // For histograms
      uint64_t bucket_deltas[VALK_MAX_BUCKETS + 1];
      uint64_t count_delta;
      uint64_t sum_delta_micros;
      const double *bucket_bounds;
      uint8_t bucket_count;
    } histogram;
  } data;
} valk_metric_delta_t;

// Delta snapshot (collection of changes)
typedef struct {
  uint64_t timestamp_us;
  uint64_t prev_timestamp_us;
  uint64_t interval_us;

  // Changed metrics
  valk_metric_delta_t *deltas;
  size_t delta_count;
  size_t delta_capacity;

  // Summary statistics
  size_t counters_changed;
  size_t gauges_changed;
  size_t histograms_changed;
  size_t summaries_changed;
} valk_delta_snapshot_t;

// ============================================================================
// PER-CONNECTION BASELINE (for multi-client delta tracking)
// ============================================================================

// Stores baseline values for a single SSE connection
// This allows multiple connections to independently track deltas
typedef struct {
  // Counter baselines (indexed same as registry)
  uint64_t counter_baselines[VALK_REGISTRY_MAX_COUNTERS];

  // Gauge baselines
  int64_t gauge_baselines[VALK_REGISTRY_MAX_GAUGES];

  // Histogram baselines
  struct {
    uint64_t buckets[VALK_MAX_BUCKETS + 1];
    uint64_t count;
    uint64_t sum_micros;
  } histogram_baselines[VALK_REGISTRY_MAX_HISTOGRAMS];

  // Timestamp of last collection
  uint64_t last_collect_time;

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
size_t valk_delta_snapshot_collect(valk_delta_snapshot_t *snap,
                                    valk_metrics_registry_t *registry);

// Collect deltas using per-connection baseline (doesn't modify global state)
// This is safe to call from multiple timers concurrently
// Returns number of changed metrics
size_t valk_delta_snapshot_collect_stateless(valk_delta_snapshot_t *snap,
                                              valk_metrics_registry_t *registry,
                                              valk_metrics_baseline_t *baseline);

// Free delta snapshot resources
void valk_delta_snapshot_free(valk_delta_snapshot_t *snap);

// ============================================================================
// DELTA ENCODING FORMATS
// ============================================================================

// Encode delta to JSON (for SSE streaming)
// Format: {"ts":123,"interval":1000,"deltas":[...]}
size_t valk_delta_to_json(const valk_delta_snapshot_t *snap,
                          char *buf, size_t buf_size);

// Encode delta to SSE event
// Format: event: metrics-delta\nid: <ts>\ndata: <json>\n\n
size_t valk_delta_to_sse(const valk_delta_snapshot_t *snap,
                         char *buf, size_t buf_size);

// Encode delta to Prometheus exposition format (for /metrics endpoint)
// Only includes metrics that changed (with full current value)
size_t valk_delta_to_prometheus(const valk_delta_snapshot_t *snap,
                                valk_metrics_registry_t *registry,
                                char *buf, size_t buf_size);

// Export full metrics state as JSON (for diagnostics/dashboard)
// Returns the number of bytes written
size_t valk_metrics_v2_to_json(valk_metrics_registry_t *registry,
                               char *buf, size_t buf_size);

// ============================================================================
// COMPRESSION STRATEGIES
// ============================================================================

// RLE encoding for histogram bucket deltas
// Format: "bucket_idx:delta,bucket_idx:delta,..." (skip zeros)
size_t valk_histogram_delta_rle(const uint64_t *deltas, size_t count,
                                 char *buf, size_t buf_size);

// Sparse gauge encoding (only non-zero changes)
// Format: "name:value,name:value,..."
size_t valk_gauge_delta_sparse(const valk_metric_delta_t *deltas,
                                size_t count, char *buf, size_t buf_size);

#endif // VALK_METRICS_DELTA_H
