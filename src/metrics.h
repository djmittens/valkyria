// src/metrics.h
#pragma once

#ifdef VALK_METRICS_ENABLED

//=============================================================================
// METRICS ENABLED - Full Implementation
//=============================================================================

#include <stdint.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <pthread.h>

// Limits
#define VALK_METRICS_MAX_LABELS      8
#define VALK_METRICS_MAX_COUNTERS    512
#define VALK_METRICS_MAX_GAUGES      256
#define VALK_METRICS_MAX_HISTOGRAMS  64
#define VALK_METRICS_LABEL_POOL_SIZE 1024
#define VALK_METRICS_MAX_BUCKETS     16

// Label (key-value pair with interned strings)
typedef struct {
  const char* key;    // Interned pointer
  const char* value;  // Interned pointer
} valk_label_t;

// Label set
typedef struct {
  valk_label_t labels[VALK_METRICS_MAX_LABELS];
  uint8_t count;
} valk_labels_t;

// Counter - monotonically increasing
typedef struct valk_counter {
  const char* name;
  valk_labels_t labels;
  _Atomic uint64_t value;
} valk_counter_t;

// Gauge - can go up or down
typedef struct valk_gauge {
  const char* name;
  valk_labels_t labels;
  _Atomic int64_t value;
} valk_gauge_t;

// Histogram - distribution of values
typedef struct valk_histogram {
  const char* name;
  valk_labels_t labels;
  _Atomic uint64_t count;
  _Atomic uint64_t sum_us;  // Microseconds for precision
  _Atomic uint64_t buckets[VALK_METRICS_MAX_BUCKETS + 1];  // +1 for +Inf
  double bucket_bounds[VALK_METRICS_MAX_BUCKETS];
  uint8_t bucket_count;
} valk_histogram_t;

// Central metrics store
typedef struct valk_metrics_store {
  // Registration lock (not used for updates)
  pthread_mutex_t registry_lock;

  // Metric storage (append-only)
  valk_counter_t counters[VALK_METRICS_MAX_COUNTERS];
  _Atomic size_t counter_count;

  valk_gauge_t gauges[VALK_METRICS_MAX_GAUGES];
  _Atomic size_t gauge_count;

  valk_histogram_t histograms[VALK_METRICS_MAX_HISTOGRAMS];
  _Atomic size_t histogram_count;

  // Interned label strings (pointer comparison instead of strcmp)
  const char* label_pool[VALK_METRICS_LABEL_POOL_SIZE];
  size_t label_pool_count;

  // Timing
  uint64_t start_time_us;
} valk_metrics_store_t;

// Global store instance
extern valk_metrics_store_t g_valk_metrics;

//-----------------------------------------------------------------------------
// Lifecycle
//-----------------------------------------------------------------------------

void valk_metrics_init(void);
void valk_metrics_destroy(void);

//-----------------------------------------------------------------------------
// Registration (takes lock, returns cached pointer)
// Label pairs are NULL-terminated: "key1", "val1", "key2", "val2", NULL
//-----------------------------------------------------------------------------

valk_counter_t* valk_metric_counter(const char* name, ...);
valk_gauge_t* valk_metric_gauge(const char* name, ...);
valk_histogram_t* valk_metric_histogram(const char* name,
                                         const double* bounds, size_t bucket_count,
                                         ...);

// Variant with explicit label array
valk_counter_t* valk_metric_counter_labels(const char* name,
                                            const char** keys, const char** vals,
                                            size_t count);

//-----------------------------------------------------------------------------
// Updates (lock-free, inline for zero overhead)
//-----------------------------------------------------------------------------

static inline void valk_counter_inc(valk_counter_t* c) {
  atomic_fetch_add_explicit(&c->value, 1, memory_order_relaxed);
}

static inline void valk_counter_add(valk_counter_t* c, uint64_t n) {
  atomic_fetch_add_explicit(&c->value, n, memory_order_relaxed);
}

static inline void valk_gauge_set(valk_gauge_t* g, int64_t v) {
  atomic_store_explicit(&g->value, v, memory_order_relaxed);
}

static inline void valk_gauge_inc(valk_gauge_t* g) {
  atomic_fetch_add_explicit(&g->value, 1, memory_order_relaxed);
}

static inline void valk_gauge_dec(valk_gauge_t* g) {
  atomic_fetch_sub_explicit(&g->value, 1, memory_order_relaxed);
}

static inline void valk_gauge_add(valk_gauge_t* g, int64_t n) {
  atomic_fetch_add_explicit(&g->value, n, memory_order_relaxed);
}

static inline void valk_histogram_observe(valk_histogram_t* h, double v) {
  atomic_fetch_add_explicit(&h->count, 1, memory_order_relaxed);
  atomic_fetch_add_explicit(&h->sum_us, (uint64_t)(v * 1e6), memory_order_relaxed);

  // Find bucket
  for (uint8_t i = 0; i < h->bucket_count; i++) {
    if (v <= h->bucket_bounds[i]) {
      atomic_fetch_add_explicit(&h->buckets[i], 1, memory_order_relaxed);
      return;
    }
  }
  // +Inf bucket
  atomic_fetch_add_explicit(&h->buckets[h->bucket_count], 1, memory_order_relaxed);
}

// Observe with microseconds (avoids float conversion on hot path)
static inline void valk_histogram_observe_us(valk_histogram_t* h, uint64_t us) {
  valk_histogram_observe(h, (double)us / 1e6);
}

//-----------------------------------------------------------------------------
// Iteration (for export)
//-----------------------------------------------------------------------------

typedef void (*valk_counter_iter_fn)(const valk_counter_t* c, void* ctx);
typedef void (*valk_gauge_iter_fn)(const valk_gauge_t* g, void* ctx);
typedef void (*valk_histogram_iter_fn)(const valk_histogram_t* h, void* ctx);

void valk_metrics_foreach_counter(valk_counter_iter_fn fn, void* ctx);
void valk_metrics_foreach_gauge(valk_gauge_iter_fn fn, void* ctx);
void valk_metrics_foreach_histogram(valk_histogram_iter_fn fn, void* ctx);

//-----------------------------------------------------------------------------
// Export
//-----------------------------------------------------------------------------

// Write Prometheus text format to buffer, returns bytes written
size_t valk_metrics_prometheus(char* buf, size_t cap);

// Write JSON format to buffer, returns bytes written
size_t valk_metrics_json(char* buf, size_t cap);

//-----------------------------------------------------------------------------
// Querying (for dashboard)
//-----------------------------------------------------------------------------

// Find metrics by label match
typedef bool (*valk_label_match_fn)(const valk_labels_t* labels, void* ctx);

void valk_metrics_query_counters(valk_label_match_fn match, void* match_ctx,
                                  valk_counter_iter_fn iter, void* iter_ctx);

#else

//=============================================================================
// METRICS DISABLED - Zero Overhead Stubs
//=============================================================================

// Dummy types for compilation (never instantiated)
typedef struct valk_counter { char _unused; } valk_counter_t;
typedef struct valk_gauge { char _unused; } valk_gauge_t;
typedef struct valk_histogram { char _unused; } valk_histogram_t;

// All operations compile to nothing
#define valk_metrics_init()                   ((void)0)
#define valk_metrics_destroy()                ((void)0)

#define valk_metric_counter(...)              ((valk_counter_t*)0)
#define valk_metric_gauge(...)                ((valk_gauge_t*)0)
#define valk_metric_histogram(...)            ((valk_histogram_t*)0)
#define valk_metric_counter_labels(...)       ((valk_counter_t*)0)

#define valk_counter_inc(c)                   ((void)0)
#define valk_counter_add(c, n)                ((void)0)
#define valk_gauge_set(g, v)                  ((void)0)
#define valk_gauge_inc(g)                     ((void)0)
#define valk_gauge_dec(g)                     ((void)0)
#define valk_gauge_add(g, n)                  ((void)0)
#define valk_histogram_observe(h, v)          ((void)0)
#define valk_histogram_observe_us(h, us)      ((void)0)

#define valk_metrics_foreach_counter(fn, ctx)   ((void)0)
#define valk_metrics_foreach_gauge(fn, ctx)     ((void)0)
#define valk_metrics_foreach_histogram(fn, ctx) ((void)0)

#define valk_metrics_prometheus(buf, cap)     ((size_t)0)
#define valk_metrics_json(buf, cap)           ((size_t)0)

#define valk_metrics_query_counters(...)      ((void)0)

#endif // VALK_METRICS_ENABLED
