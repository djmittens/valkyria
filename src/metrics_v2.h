// src/metrics_v2.h
#ifndef VALK_METRICS_V2_H
#define VALK_METRICS_V2_H

#include <stdatomic.h>
#include <stdbool.h>
#include "types.h"
#include "valk_thread.h"

// ============================================================================
// METRIC TYPES
// ============================================================================

typedef enum {
  VALK_METRIC_COUNTER,
  VALK_METRIC_GAUGE,
  VALK_METRIC_HISTOGRAM,
  VALK_METRIC_SUMMARY,      // NEW: For percentile calculations
} valk_metric_type_e;

// Label key-value pair (interned strings for fast comparison)
typedef struct {
  const char *key;
  const char *value;
} valk_label_v2_t;

// Label set (up to 8 labels)
#define VALK_MAX_LABELS_V2 8
typedef struct {
  valk_label_v2_t labels[VALK_MAX_LABELS_V2];
  u8 count;
  u32 hash;  // Pre-computed hash for fast lookup
} valk_label_set_v2_t;

// ============================================================================
// COUNTER - Monotonically increasing value
// ============================================================================

typedef struct {
  const char *name;
  const char *help;
  valk_label_set_v2_t labels;
  _Atomic u64 value;
  _Atomic u64 last_value;      // For delta calculation
  _Atomic u64 last_timestamp;  // When last_value was captured

  // LRU eviction support
  _Atomic u64 last_updated_us; // Timestamp of last update (for LRU)
  _Atomic u32 generation;      // Incremented on eviction (for safe reuse)
  _Atomic bool active;              // false = slot available for reuse
  bool evictable;                   // false for persistent metrics (pool, gc)
} valk_counter_v2_t;

// ============================================================================
// GAUGE - Value that can go up or down
// ============================================================================

typedef struct {
  const char *name;
  const char *help;
  valk_label_set_v2_t labels;
  _Atomic i64 value;
  _Atomic i64 last_value;
  _Atomic u64 last_timestamp;

  // LRU eviction support
  _Atomic u64 last_updated_us; // Timestamp of last update (for LRU)
  _Atomic u32 generation;      // Incremented on eviction (for safe reuse)
  _Atomic bool active;              // false = slot available for reuse
  bool evictable;                   // false for persistent metrics (pool, gc)
} valk_gauge_v2_t;

// ============================================================================
// HISTOGRAM - Distribution with configurable buckets
// ============================================================================

#define VALK_MAX_BUCKETS 32

typedef struct {
  const char *name;
  const char *help;
  valk_label_set_v2_t labels;

  // Bucket configuration
  double bucket_bounds[VALK_MAX_BUCKETS];
  u8 bucket_count;

  // Atomic counters
  _Atomic u64 buckets[VALK_MAX_BUCKETS + 1];  // +1 for +Inf
  _Atomic u64 count;
  _Atomic u64 sum_micros;  // Sum in microseconds for precision

  // Delta tracking (per bucket)
  u64 last_buckets[VALK_MAX_BUCKETS + 1];
  u64 last_count;
  u64 last_sum_micros;
  u64 last_timestamp;

  // LRU eviction support
  _Atomic u64 last_updated_us; // Timestamp of last update (for LRU)
  _Atomic u32 generation;      // Incremented on eviction (for safe reuse)
  _Atomic bool active;              // false = slot available for reuse
  bool evictable;                   // false for persistent metrics (pool, gc)
} valk_histogram_v2_t;

// ============================================================================
// SUMMARY - Streaming percentile calculation (NEW)
// ============================================================================

// T-Digest style streaming quantile estimation
#define VALK_SUMMARY_CENTROIDS 100

typedef struct {
  double mean;
  u64 weight;
} valk_centroid_t;

typedef struct {
  const char *name;
  const char *help;
  valk_label_set_v2_t labels;

  // T-Digest centroids
  valk_centroid_t centroids[VALK_SUMMARY_CENTROIDS];
  u32 centroid_count;
  _Atomic u64 total_weight;
  _Atomic double sum;

  // Requested quantiles (e.g., 0.5, 0.9, 0.99)
  double quantiles[8];
  u8 quantile_count;

  // Lock for centroid updates (rare path)
  valk_mutex_t lock;

  // Delta tracking
  u64 last_total_weight;
  double last_sum;
  u64 last_timestamp;

  // LRU eviction support
  _Atomic u64 last_updated_us; // Timestamp of last update (for LRU)
  _Atomic u32 generation;      // Incremented on eviction (for safe reuse)
  _Atomic bool active;              // false = slot available for reuse
  bool evictable;                   // false for persistent metrics (pool, gc)
} valk_summary_v2_t;

// ============================================================================
// METRIC HANDLES - For safe references to evictable metrics
// ============================================================================

// Handle = slot index + generation (for safe access after potential eviction)
typedef struct {
  u32 slot;
  u32 generation;
} valk_metric_handle_t;

#define VALK_INVALID_SLOT 0xFFFFFFFF
#define VALK_HANDLE_INVALID ((valk_metric_handle_t){VALK_INVALID_SLOT, 0})

// ============================================================================
// FREE LIST - Lock-free slot reuse
// ============================================================================

typedef struct {
  _Atomic u32 head;  // Index of first free slot (VALK_INVALID_SLOT = empty)
} valk_free_list_t;

// ============================================================================
// REGISTRY STATS - Meta-metrics about the metrics system itself
// ============================================================================

// These are NOT stored as metric objects to avoid recursion.
// Instead, they're computed on-demand and exported alongside metrics.
typedef struct {
  // Registry utilization (active counts)
  u64 counters_active;
  u64 gauges_active;
  u64 histograms_active;
  u64 summaries_active;

  // High water marks (slots ever used)
  u64 counters_hwm;
  u64 gauges_hwm;
  u64 histograms_hwm;
  u64 summaries_hwm;

  // Capacity limits
  u64 counters_capacity;
  u64 gauges_capacity;
  u64 histograms_capacity;
  u64 summaries_capacity;

  // String pool
  u64 string_pool_used;
  u64 string_pool_capacity;

  // Eviction stats (lifetime totals)
  u64 evictions_total;
  u64 evictions_counters;
  u64 evictions_gauges;
  u64 evictions_histograms;
  u64 evictions_summaries;

  // Free list depths (available slots for reuse)
  u64 counters_free;
  u64 gauges_free;
  u64 histograms_free;
  u64 summaries_free;

  // Collection timing
  u64 last_collect_time_us;
  u64 collect_duration_us;
} valk_registry_stats_t;

// ============================================================================
// REGISTRY - Central metric storage
// ============================================================================

#define VALK_REGISTRY_MAX_COUNTERS    1024
#define VALK_REGISTRY_MAX_GAUGES      512
#define VALK_REGISTRY_MAX_HISTOGRAMS  128
#define VALK_REGISTRY_MAX_SUMMARIES   64

// Default: 5 minutes before a metric is considered stale
#define VALK_EVICTION_THRESHOLD_US (5 * 60 * 1000000ULL)
// Trigger eviction when array > 80% full
#define VALK_EVICTION_TRIGGER_PCT 80

typedef struct {
  // Metric arrays
  valk_counter_v2_t counters[VALK_REGISTRY_MAX_COUNTERS];
  _Atomic u64 counter_count;  // High water mark (not current active count)

  valk_gauge_v2_t gauges[VALK_REGISTRY_MAX_GAUGES];
  _Atomic u64 gauge_count;

  valk_histogram_v2_t histograms[VALK_REGISTRY_MAX_HISTOGRAMS];
  _Atomic u64 histogram_count;

  valk_summary_v2_t summaries[VALK_REGISTRY_MAX_SUMMARIES];
  _Atomic u64 summary_count;

  // Free lists for slot reuse (per metric type)
  // next_free array stores next pointer for each slot (VALK_INVALID_SLOT = end)
  valk_free_list_t counter_free;
  u32 counter_next_free[VALK_REGISTRY_MAX_COUNTERS];

  valk_free_list_t gauge_free;
  u32 gauge_next_free[VALK_REGISTRY_MAX_GAUGES];

  valk_free_list_t histogram_free;
  u32 histogram_next_free[VALK_REGISTRY_MAX_HISTOGRAMS];

  valk_free_list_t summary_free;
  u32 summary_next_free[VALK_REGISTRY_MAX_SUMMARIES];

  // String interning pool
  const char *string_pool[4096];
  u64 string_pool_count;
  valk_mutex_t pool_lock;

  // Snapshot interval tracking
  u64 last_snapshot_time;
  u64 snapshot_interval_us;  // Default: 1000000 (1s)

  // Eviction configuration
  u64 eviction_threshold_us;  // Default: 5 minutes

  // Eviction tracking (for meta-metrics)
  _Atomic u64 evictions_total;
  _Atomic u64 evictions_counters;
  _Atomic u64 evictions_gauges;
  _Atomic u64 evictions_histograms;
  _Atomic u64 evictions_summaries;

  // Timing
  u64 start_time_us;
} valk_metrics_registry_t;

// Global registry instance
extern valk_metrics_registry_t g_metrics;

// ============================================================================
// REGISTRY LIFECYCLE
// ============================================================================

void valk_metrics_registry_init(void);
void valk_metrics_registry_destroy(void);

// ============================================================================
// EVICTION API
// ============================================================================

// Evict stale metrics when registry is under pressure
// Returns number of metrics evicted
u64 valk_metrics_evict_stale(void);

// ============================================================================
// REGISTRY STATS API (Meta-metrics)
// ============================================================================

// Collect current registry statistics into stats struct
// This is computed on-demand, not stored as metrics objects
void valk_registry_stats_collect(valk_registry_stats_t *stats);

// Export registry stats as JSON
// Returns bytes written (excluding null terminator)
u64 valk_registry_stats_to_json(const valk_registry_stats_t *stats,
                                    char *buf, u64 buf_size);

// Mark a metric as persistent (non-evictable)
// Use for core system metrics that should never be evicted
void valk_counter_set_persistent(valk_counter_v2_t *c);
void valk_gauge_set_persistent(valk_gauge_v2_t *g);
void valk_histogram_set_persistent(valk_histogram_v2_t *h);
void valk_summary_set_persistent(valk_summary_v2_t *s);

// Safe handle-based access (returns nullptr if evicted)
valk_counter_v2_t *valk_counter_deref(valk_metric_handle_t h);
valk_gauge_v2_t *valk_gauge_deref(valk_metric_handle_t h);
valk_histogram_v2_t *valk_histogram_deref(valk_metric_handle_t h);
valk_summary_v2_t *valk_summary_deref(valk_metric_handle_t h);

// Get handle from metric pointer (for caching references to evictable metrics)
valk_metric_handle_t valk_counter_handle(valk_counter_v2_t *c);
valk_metric_handle_t valk_gauge_handle(valk_gauge_v2_t *g);
valk_metric_handle_t valk_histogram_handle(valk_histogram_v2_t *h);
valk_metric_handle_t valk_summary_handle(valk_summary_v2_t *s);

// Get current time in microseconds (implemented in metrics_v2.c)
u64 valk_metrics_now_us(void);

// ============================================================================
// COUNTER API
// ============================================================================

valk_counter_v2_t *valk_counter_get_or_create(const char *name,
                                               const char *help,
                                               const valk_label_set_v2_t *labels);

// Lock-free increment (updates LRU timestamp)
static inline void valk_counter_v2_inc(valk_counter_v2_t *c) {
  atomic_fetch_add_explicit(&c->value, 1, memory_order_relaxed);
  atomic_store_explicit(&c->last_updated_us, valk_metrics_now_us(), memory_order_relaxed);
}

static inline void valk_counter_v2_add(valk_counter_v2_t *c, u64 n) {
  atomic_fetch_add_explicit(&c->value, n, memory_order_relaxed);
  atomic_store_explicit(&c->last_updated_us, valk_metrics_now_us(), memory_order_relaxed);
}

// ============================================================================
// GAUGE API
// ============================================================================

valk_gauge_v2_t *valk_gauge_get_or_create(const char *name,
                                          const char *help,
                                          const valk_label_set_v2_t *labels);

// Gauge updates (all update LRU timestamp)
static inline void valk_gauge_v2_set(valk_gauge_v2_t *g, i64 v) {
  atomic_store_explicit(&g->value, v, memory_order_relaxed);
  atomic_store_explicit(&g->last_updated_us, valk_metrics_now_us(), memory_order_relaxed);
}

static inline void valk_gauge_v2_inc(valk_gauge_v2_t *g) {
  atomic_fetch_add_explicit(&g->value, 1, memory_order_relaxed);
  atomic_store_explicit(&g->last_updated_us, valk_metrics_now_us(), memory_order_relaxed);
}

static inline void valk_gauge_v2_dec(valk_gauge_v2_t *g) {
  atomic_fetch_sub_explicit(&g->value, 1, memory_order_relaxed);
  atomic_store_explicit(&g->last_updated_us, valk_metrics_now_us(), memory_order_relaxed);
}

static inline void valk_gauge_v2_add(valk_gauge_v2_t *g, i64 n) {
  atomic_fetch_add_explicit(&g->value, n, memory_order_relaxed);
  atomic_store_explicit(&g->last_updated_us, valk_metrics_now_us(), memory_order_relaxed);
}

// ============================================================================
// HISTOGRAM API
// ============================================================================

valk_histogram_v2_t *valk_histogram_get_or_create(
    const char *name,
    const char *help,
    const double *bounds,
    u64 bound_count,
    const valk_label_set_v2_t *labels);

// Lock-free observation (updates LRU timestamp)
static inline void valk_histogram_v2_observe_us(valk_histogram_v2_t *h, u64 us) {
  atomic_fetch_add_explicit(&h->count, 1, memory_order_relaxed);
  atomic_fetch_add_explicit(&h->sum_micros, us, memory_order_relaxed);

  // Find bucket
  double seconds = (double)us / 1000000.0;
  for (u8 i = 0; i < h->bucket_count; i++) {
    if (seconds <= h->bucket_bounds[i]) {
      atomic_fetch_add_explicit(&h->buckets[i], 1, memory_order_relaxed);
      atomic_store_explicit(&h->last_updated_us, valk_metrics_now_us(), memory_order_relaxed);
      return;
    }
  }
  // +Inf bucket
  atomic_fetch_add_explicit(&h->buckets[h->bucket_count], 1, memory_order_relaxed);
  atomic_store_explicit(&h->last_updated_us, valk_metrics_now_us(), memory_order_relaxed);
}

#endif // VALK_METRICS_V2_H
