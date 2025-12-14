// src/metrics_v2.h
#ifndef VALK_METRICS_V2_H
#define VALK_METRICS_V2_H

#include <stdint.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <pthread.h>

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
  uint8_t count;
  uint32_t hash;  // Pre-computed hash for fast lookup
} valk_label_set_v2_t;

// ============================================================================
// COUNTER - Monotonically increasing value
// ============================================================================

typedef struct {
  const char *name;
  const char *help;
  valk_label_set_v2_t labels;
  _Atomic uint64_t value;
  _Atomic uint64_t last_value;      // For delta calculation
  _Atomic uint64_t last_timestamp;  // When last_value was captured

  // LRU eviction support
  _Atomic uint64_t last_updated_us; // Timestamp of last update (for LRU)
  _Atomic uint32_t generation;      // Incremented on eviction (for safe reuse)
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
  _Atomic int64_t value;
  _Atomic int64_t last_value;
  _Atomic uint64_t last_timestamp;

  // LRU eviction support
  _Atomic uint64_t last_updated_us; // Timestamp of last update (for LRU)
  _Atomic uint32_t generation;      // Incremented on eviction (for safe reuse)
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
  uint8_t bucket_count;

  // Atomic counters
  _Atomic uint64_t buckets[VALK_MAX_BUCKETS + 1];  // +1 for +Inf
  _Atomic uint64_t count;
  _Atomic uint64_t sum_micros;  // Sum in microseconds for precision

  // Delta tracking (per bucket)
  uint64_t last_buckets[VALK_MAX_BUCKETS + 1];
  uint64_t last_count;
  uint64_t last_sum_micros;
  uint64_t last_timestamp;

  // LRU eviction support
  _Atomic uint64_t last_updated_us; // Timestamp of last update (for LRU)
  _Atomic uint32_t generation;      // Incremented on eviction (for safe reuse)
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
  uint64_t weight;
} valk_centroid_t;

typedef struct {
  const char *name;
  const char *help;
  valk_label_set_v2_t labels;

  // T-Digest centroids
  valk_centroid_t centroids[VALK_SUMMARY_CENTROIDS];
  uint32_t centroid_count;
  _Atomic uint64_t total_weight;
  _Atomic double sum;

  // Requested quantiles (e.g., 0.5, 0.9, 0.99)
  double quantiles[8];
  uint8_t quantile_count;

  // Lock for centroid updates (rare path)
  pthread_mutex_t lock;

  // Delta tracking
  uint64_t last_total_weight;
  double last_sum;
  uint64_t last_timestamp;

  // LRU eviction support
  _Atomic uint64_t last_updated_us; // Timestamp of last update (for LRU)
  _Atomic uint32_t generation;      // Incremented on eviction (for safe reuse)
  _Atomic bool active;              // false = slot available for reuse
  bool evictable;                   // false for persistent metrics (pool, gc)
} valk_summary_v2_t;

// ============================================================================
// METRIC HANDLES - For safe references to evictable metrics
// ============================================================================

// Handle = slot index + generation (for safe access after potential eviction)
typedef struct {
  uint32_t slot;
  uint32_t generation;
} valk_metric_handle_t;

#define VALK_INVALID_SLOT 0xFFFFFFFF
#define VALK_HANDLE_INVALID ((valk_metric_handle_t){VALK_INVALID_SLOT, 0})

// ============================================================================
// FREE LIST - Lock-free slot reuse
// ============================================================================

typedef struct {
  _Atomic uint32_t head;  // Index of first free slot (VALK_INVALID_SLOT = empty)
} valk_free_list_t;

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
  _Atomic size_t counter_count;  // High water mark (not current active count)

  valk_gauge_v2_t gauges[VALK_REGISTRY_MAX_GAUGES];
  _Atomic size_t gauge_count;

  valk_histogram_v2_t histograms[VALK_REGISTRY_MAX_HISTOGRAMS];
  _Atomic size_t histogram_count;

  valk_summary_v2_t summaries[VALK_REGISTRY_MAX_SUMMARIES];
  _Atomic size_t summary_count;

  // Free lists for slot reuse (per metric type)
  // next_free array stores next pointer for each slot (VALK_INVALID_SLOT = end)
  valk_free_list_t counter_free;
  uint32_t counter_next_free[VALK_REGISTRY_MAX_COUNTERS];

  valk_free_list_t gauge_free;
  uint32_t gauge_next_free[VALK_REGISTRY_MAX_GAUGES];

  valk_free_list_t histogram_free;
  uint32_t histogram_next_free[VALK_REGISTRY_MAX_HISTOGRAMS];

  valk_free_list_t summary_free;
  uint32_t summary_next_free[VALK_REGISTRY_MAX_SUMMARIES];

  // String interning pool
  const char *string_pool[4096];
  size_t string_pool_count;
  pthread_mutex_t pool_lock;

  // Snapshot interval tracking
  uint64_t last_snapshot_time;
  uint64_t snapshot_interval_us;  // Default: 1000000 (1s)

  // Eviction configuration
  uint64_t eviction_threshold_us;  // Default: 5 minutes

  // Timing
  uint64_t start_time_us;
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
size_t valk_metrics_evict_stale(void);

// Mark a metric as persistent (non-evictable)
// Use for core system metrics that should never be evicted
void valk_counter_set_persistent(valk_counter_v2_t *c);
void valk_gauge_set_persistent(valk_gauge_v2_t *g);
void valk_histogram_set_persistent(valk_histogram_v2_t *h);
void valk_summary_set_persistent(valk_summary_v2_t *s);

// Safe handle-based access (returns NULL if evicted)
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
uint64_t valk_metrics_now_us(void);

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

static inline void valk_counter_v2_add(valk_counter_v2_t *c, uint64_t n) {
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
static inline void valk_gauge_v2_set(valk_gauge_v2_t *g, int64_t v) {
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

static inline void valk_gauge_v2_add(valk_gauge_v2_t *g, int64_t n) {
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
    size_t bound_count,
    const valk_label_set_v2_t *labels);

// Lock-free observation (updates LRU timestamp)
static inline void valk_histogram_v2_observe_us(valk_histogram_v2_t *h, uint64_t us) {
  atomic_fetch_add_explicit(&h->count, 1, memory_order_relaxed);
  atomic_fetch_add_explicit(&h->sum_micros, us, memory_order_relaxed);

  // Find bucket
  double seconds = (double)us / 1000000.0;
  for (uint8_t i = 0; i < h->bucket_count; i++) {
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
