# Metrics Collection and Streaming Plan

## Executive Summary

This document outlines a comprehensive plan to implement proper metrics collection with delta algorithms and concurrency support. The current implementation has ad-hoc gathering logic and lacks a unified streaming architecture. This plan addresses scalability, efficiency, and Lisp integration.

---

## Current State Analysis

### Existing Metrics Architecture

**Three-tier system** (`src/metrics.h`, `src/aio_metrics.h`, `src/aio_sse_diagnostics.h`):

```
┌─────────────────────────────────────────────────────────────────┐
│                 Current Metrics Architecture                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Tier 1: Core Metrics (metrics.h:36-58)                        │
│    ├─ valk_counter_t  - Monotonically increasing               │
│    ├─ valk_gauge_t    - Can go up or down                      │
│    └─ valk_histogram_t - Distribution with buckets             │
│                                                                 │
│  Tier 2: AIO Metrics (aio_metrics.h:18-44)                     │
│    ├─ valk_aio_metrics_t - HTTP connections/requests/bytes     │
│    └─ valk_aio_system_stats_t - Resource pool utilization      │
│                                                                 │
│  Tier 3: SSE Streaming (aio_sse_diagnostics.h:64-91)           │
│    ├─ valk_mem_snapshot_t - Point-in-time snapshot             │
│    └─ valk_diag_delta_to_sse() - Delta encoding                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Limitations

1. **No Unified Collection**: Metrics scattered across multiple structures
2. **Manual Snapshot**: Must call `valk_mem_snapshot_collect()` explicitly
3. **Fixed Delta Logic**: Delta only compares with immediate previous snapshot
4. **No History**: Cannot query historical values
5. **No Aggregation**: No rate calculation, percentiles, or moving averages
6. **Limited Labels**: Fixed label set, no dynamic label support
7. **Memory Overhead**: Full snapshot copies for delta tracking
8. **No Lisp API**: Cannot define custom metrics from Lisp

---

## Proposed Architecture

### Layer 1: Unified Metrics Registry

**File**: `src/metrics_v2.h` (NEW)

```c
// Line 1-150 (new file)
#ifndef VALK_METRICS_V2_H
#define VALK_METRICS_V2_H

#include <stdint.h>
#include <stdatomic.h>
#include <stdbool.h>

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
} valk_label_t;

// Label set (up to 8 labels)
#define VALK_MAX_LABELS 8
typedef struct {
  valk_label_t labels[VALK_MAX_LABELS];
  uint8_t count;
  uint32_t hash;  // Pre-computed hash for fast lookup
} valk_label_set_t;

// ============================================================================
// COUNTER - Monotonically increasing value
// ============================================================================

typedef struct {
  const char *name;
  const char *help;
  valk_label_set_t labels;
  _Atomic uint64_t value;
  _Atomic uint64_t last_value;      // For delta calculation
  _Atomic uint64_t last_timestamp;  // When last_value was captured
} valk_counter_v2_t;

// ============================================================================
// GAUGE - Value that can go up or down
// ============================================================================

typedef struct {
  const char *name;
  const char *help;
  valk_label_set_t labels;
  _Atomic int64_t value;
  _Atomic int64_t last_value;
  _Atomic uint64_t last_timestamp;
} valk_gauge_v2_t;

// ============================================================================
// HISTOGRAM - Distribution with configurable buckets
// ============================================================================

#define VALK_MAX_BUCKETS 32

typedef struct {
  const char *name;
  const char *help;
  valk_label_set_t labels;

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
  valk_label_set_t labels;

  // T-Digest centroids
  valk_centroid_t centroids[VALK_SUMMARY_CENTROIDS];
  uint32_t centroid_count;
  _Atomic uint64_t total_weight;
  _Atomic double sum;

  // Requested quantiles (e.g., 0.5, 0.9, 0.99)
  double quantiles[8];
  uint8_t quantile_count;

  // Lock for centroid updates (rare path)
  pthread_spinlock_t lock;

  // Delta tracking
  uint64_t last_total_weight;
  double last_sum;
  uint64_t last_timestamp;
} valk_summary_v2_t;

// ============================================================================
// REGISTRY - Central metric storage
// ============================================================================

#define VALK_REGISTRY_MAX_COUNTERS    1024
#define VALK_REGISTRY_MAX_GAUGES      512
#define VALK_REGISTRY_MAX_HISTOGRAMS  128
#define VALK_REGISTRY_MAX_SUMMARIES   64

typedef struct {
  // Metric arrays (append-only)
  valk_counter_v2_t counters[VALK_REGISTRY_MAX_COUNTERS];
  _Atomic size_t counter_count;

  valk_gauge_v2_t gauges[VALK_REGISTRY_MAX_GAUGES];
  _Atomic size_t gauge_count;

  valk_histogram_v2_t histograms[VALK_REGISTRY_MAX_HISTOGRAMS];
  _Atomic size_t histogram_count;

  valk_summary_v2_t summaries[VALK_REGISTRY_MAX_SUMMARIES];
  _Atomic size_t summary_count;

  // String interning pool
  const char *string_pool[4096];
  size_t string_pool_count;
  pthread_mutex_t pool_lock;

  // Snapshot interval tracking
  uint64_t last_snapshot_time;
  uint64_t snapshot_interval_us;  // Default: 1000000 (1s)

  // Timing
  uint64_t start_time_us;
} valk_metrics_registry_t;

// Global registry instance
extern valk_metrics_registry_t g_metrics;

#endif // VALK_METRICS_V2_H
```

### Layer 2: Delta Algorithm

**File**: `src/metrics_delta.h` (NEW)

```c
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
  valk_label_set_t *labels;
  valk_delta_type_e type;
  union {
    uint64_t increment;     // For counters: delta value
    int64_t value;          // For gauges: new value
    struct {                // For histograms
      uint64_t bucket_deltas[VALK_MAX_BUCKETS + 1];
      uint64_t count_delta;
      uint64_t sum_delta_micros;
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
// DELTA COLLECTION API
// ============================================================================

// Initialize delta snapshot
void valk_delta_snapshot_init(valk_delta_snapshot_t *snap);

// Collect deltas from registry (compares with internal last_* fields)
// Returns number of changed metrics
size_t valk_delta_snapshot_collect(valk_delta_snapshot_t *snap,
                                    valk_metrics_registry_t *registry);

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
```

### Layer 3: Delta Collection Implementation

**File**: `src/metrics_delta.c` (NEW)

```c
// Line 1-300 (key functions)

#include "metrics_delta.h"
#include <string.h>
#include <stdio.h>
#include <time.h>

// ============================================================================
// TIMESTAMP UTILITIES
// ============================================================================

static uint64_t get_timestamp_us(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000000ULL + ts.tv_nsec / 1000;
}

// ============================================================================
// DELTA SNAPSHOT MANAGEMENT (lines 30-80)
// ============================================================================

void valk_delta_snapshot_init(valk_delta_snapshot_t *snap) {
  memset(snap, 0, sizeof(*snap));
  snap->delta_capacity = 256;
  snap->deltas = malloc(snap->delta_capacity * sizeof(valk_metric_delta_t));
}

void valk_delta_snapshot_free(valk_delta_snapshot_t *snap) {
  free(snap->deltas);
  memset(snap, 0, sizeof(*snap));
}

static void ensure_delta_capacity(valk_delta_snapshot_t *snap) {
  if (snap->delta_count >= snap->delta_capacity) {
    snap->delta_capacity *= 2;
    snap->deltas = realloc(snap->deltas,
                           snap->delta_capacity * sizeof(valk_metric_delta_t));
  }
}

// ============================================================================
// DELTA COLLECTION (lines 90-200)
// ============================================================================

size_t valk_delta_snapshot_collect(valk_delta_snapshot_t *snap,
                                    valk_metrics_registry_t *registry) {
  uint64_t now = get_timestamp_us();

  snap->timestamp_us = now;
  snap->prev_timestamp_us = registry->last_snapshot_time;
  snap->interval_us = now - registry->last_snapshot_time;
  snap->delta_count = 0;
  snap->counters_changed = 0;
  snap->gauges_changed = 0;
  snap->histograms_changed = 0;
  snap->summaries_changed = 0;

  // Process counters
  size_t counter_count = atomic_load(&registry->counter_count);
  for (size_t i = 0; i < counter_count; i++) {
    valk_counter_v2_t *c = &registry->counters[i];
    uint64_t current = atomic_load_explicit(&c->value, memory_order_relaxed);
    uint64_t last = atomic_load_explicit(&c->last_value, memory_order_relaxed);

    if (current != last) {
      ensure_delta_capacity(snap);
      valk_metric_delta_t *delta = &snap->deltas[snap->delta_count++];
      delta->name = c->name;
      delta->labels = &c->labels;
      delta->type = VALK_DELTA_INCREMENT;
      delta->data.increment = current - last;

      // Update last value atomically
      atomic_store_explicit(&c->last_value, current, memory_order_relaxed);
      atomic_store_explicit(&c->last_timestamp, now, memory_order_relaxed);
      snap->counters_changed++;
    }
  }

  // Process gauges (threshold: >0.1% change or absolute >1)
  size_t gauge_count = atomic_load(&registry->gauge_count);
  for (size_t i = 0; i < gauge_count; i++) {
    valk_gauge_v2_t *g = &registry->gauges[i];
    int64_t current = atomic_load_explicit(&g->value, memory_order_relaxed);
    int64_t last = atomic_load_explicit(&g->last_value, memory_order_relaxed);

    // Apply change threshold
    int64_t diff = current > last ? current - last : last - current;
    int64_t threshold = last / 1000;  // 0.1%
    if (threshold < 1) threshold = 1;

    if (diff >= threshold) {
      ensure_delta_capacity(snap);
      valk_metric_delta_t *delta = &snap->deltas[snap->delta_count++];
      delta->name = g->name;
      delta->labels = &g->labels;
      delta->type = VALK_DELTA_SET;
      delta->data.value = current;

      atomic_store_explicit(&g->last_value, current, memory_order_relaxed);
      atomic_store_explicit(&g->last_timestamp, now, memory_order_relaxed);
      snap->gauges_changed++;
    }
  }

  // Process histograms
  size_t hist_count = atomic_load(&registry->histogram_count);
  for (size_t i = 0; i < hist_count; i++) {
    valk_histogram_v2_t *h = &registry->histograms[i];
    uint64_t current_count = atomic_load_explicit(&h->count, memory_order_relaxed);

    if (current_count != h->last_count) {
      ensure_delta_capacity(snap);
      valk_metric_delta_t *delta = &snap->deltas[snap->delta_count++];
      delta->name = h->name;
      delta->labels = &h->labels;
      delta->type = VALK_DELTA_OBSERVE;

      // Calculate per-bucket deltas
      for (size_t b = 0; b <= h->bucket_count; b++) {
        uint64_t bucket_val = atomic_load_explicit(&h->buckets[b], memory_order_relaxed);
        delta->data.histogram.bucket_deltas[b] = bucket_val - h->last_buckets[b];
        h->last_buckets[b] = bucket_val;
      }

      delta->data.histogram.count_delta = current_count - h->last_count;
      uint64_t current_sum = atomic_load_explicit(&h->sum_micros, memory_order_relaxed);
      delta->data.histogram.sum_delta_micros = current_sum - h->last_sum_micros;

      h->last_count = current_count;
      h->last_sum_micros = current_sum;
      h->last_timestamp = now;
      snap->histograms_changed++;
    }
  }

  registry->last_snapshot_time = now;
  return snap->delta_count;
}

// ============================================================================
// JSON ENCODING (lines 210-300)
// ============================================================================

size_t valk_delta_to_json(const valk_delta_snapshot_t *snap,
                          char *buf, size_t buf_size) {
  char *p = buf;
  char *end = buf + buf_size;
  int n;

  // Header
  n = snprintf(p, end - p,
               "{\"ts\":%lu,\"interval_us\":%lu,\"changed\":%zu,",
               snap->timestamp_us, snap->interval_us, snap->delta_count);
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  // Summary
  n = snprintf(p, end - p,
               "\"counters_changed\":%zu,\"gauges_changed\":%zu,"
               "\"histograms_changed\":%zu,",
               snap->counters_changed, snap->gauges_changed,
               snap->histograms_changed);
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  // Deltas array
  n = snprintf(p, end - p, "\"deltas\":[");
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  for (size_t i = 0; i < snap->delta_count; i++) {
    const valk_metric_delta_t *d = &snap->deltas[i];

    if (i > 0) {
      n = snprintf(p, end - p, ",");
      if (n < 0 || p + n >= end) return buf_size;
      p += n;
    }

    switch (d->type) {
      case VALK_DELTA_INCREMENT:
        n = snprintf(p, end - p, "{\"n\":\"%s\",\"t\":\"c\",\"d\":%lu}",
                     d->name, d->data.increment);
        break;
      case VALK_DELTA_SET:
        n = snprintf(p, end - p, "{\"n\":\"%s\",\"t\":\"g\",\"v\":%ld}",
                     d->name, d->data.value);
        break;
      case VALK_DELTA_OBSERVE:
        // Compact histogram delta
        n = snprintf(p, end - p, "{\"n\":\"%s\",\"t\":\"h\",\"c\":%lu,\"s\":%lu}",
                     d->name, d->data.histogram.count_delta,
                     d->data.histogram.sum_delta_micros);
        break;
      default:
        continue;
    }

    if (n < 0 || p + n >= end) return buf_size;
    p += n;
  }

  n = snprintf(p, end - p, "]}");
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  return p - buf;
}

// ============================================================================
// SSE ENCODING (lines 310-350)
// ============================================================================

size_t valk_delta_to_sse(const valk_delta_snapshot_t *snap,
                         char *buf, size_t buf_size) {
  char *p = buf;
  char *end = buf + buf_size;
  int n;

  // SSE header
  n = snprintf(p, end - p, "event: metrics-delta\nid: %lu\ndata: ",
               snap->timestamp_us);
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  // JSON payload
  size_t json_len = valk_delta_to_json(snap, p, end - p - 3);
  if (json_len >= (size_t)(end - p - 3)) return buf_size;
  p += json_len;

  // SSE terminator
  n = snprintf(p, end - p, "\n\n");
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  return p - buf;
}
```

### Layer 4: Concurrency-Safe Operations

**File**: `src/metrics_v2.c` (NEW, key sections)

```c
// Line 1-200 (key functions for concurrent access)

#include "metrics_v2.h"
#include <string.h>
#include <stdio.h>

// Global registry
valk_metrics_registry_t g_metrics;

// ============================================================================
// STRING INTERNING (lines 20-60)
// ============================================================================

static const char *intern_string(const char *str) {
  if (!str) return NULL;

  pthread_mutex_lock(&g_metrics.pool_lock);

  // Check if already interned
  for (size_t i = 0; i < g_metrics.string_pool_count; i++) {
    if (strcmp(g_metrics.string_pool[i], str) == 0) {
      pthread_mutex_unlock(&g_metrics.pool_lock);
      return g_metrics.string_pool[i];
    }
  }

  // Add new string
  if (g_metrics.string_pool_count >= 4096) {
    pthread_mutex_unlock(&g_metrics.pool_lock);
    return strdup(str);  // Fallback: non-interned
  }

  char *copy = strdup(str);
  g_metrics.string_pool[g_metrics.string_pool_count++] = copy;

  pthread_mutex_unlock(&g_metrics.pool_lock);
  return copy;
}

// ============================================================================
// LABEL SET HASHING (lines 70-100)
// ============================================================================

static uint32_t hash_label_set(const valk_label_set_t *labels) {
  uint32_t hash = 5381;
  for (uint8_t i = 0; i < labels->count; i++) {
    // Hash key pointer (interned)
    hash = ((hash << 5) + hash) ^ (uint32_t)(uintptr_t)labels->labels[i].key;
    // Hash value pointer (interned)
    hash = ((hash << 5) + hash) ^ (uint32_t)(uintptr_t)labels->labels[i].value;
  }
  return hash;
}

static bool labels_equal(const valk_label_set_t *a, const valk_label_set_t *b) {
  if (a->hash != b->hash) return false;
  if (a->count != b->count) return false;
  for (uint8_t i = 0; i < a->count; i++) {
    // Pointer comparison (interned strings)
    if (a->labels[i].key != b->labels[i].key ||
        a->labels[i].value != b->labels[i].value) {
      return false;
    }
  }
  return true;
}

// ============================================================================
// COUNTER OPERATIONS (lines 110-180)
// ============================================================================

valk_counter_v2_t *valk_counter_get_or_create(const char *name,
                                               const char *help,
                                               const valk_label_set_t *labels) {
  const char *iname = intern_string(name);
  valk_label_set_t ilabels = {0};

  // Intern all label strings
  for (uint8_t i = 0; i < labels->count && i < VALK_MAX_LABELS; i++) {
    ilabels.labels[i].key = intern_string(labels->labels[i].key);
    ilabels.labels[i].value = intern_string(labels->labels[i].value);
    ilabels.count++;
  }
  ilabels.hash = hash_label_set(&ilabels);

  // Search existing (lock-free read)
  size_t count = atomic_load(&g_metrics.counter_count);
  for (size_t i = 0; i < count; i++) {
    valk_counter_v2_t *c = &g_metrics.counters[i];
    if (c->name == iname && labels_equal(&c->labels, &ilabels)) {
      return c;  // Found existing
    }
  }

  // Create new (CAS to append)
  size_t idx = atomic_fetch_add(&g_metrics.counter_count, 1);
  if (idx >= VALK_REGISTRY_MAX_COUNTERS) {
    atomic_fetch_sub(&g_metrics.counter_count, 1);
    return NULL;  // Registry full
  }

  valk_counter_v2_t *c = &g_metrics.counters[idx];
  c->name = iname;
  c->help = intern_string(help);
  c->labels = ilabels;
  atomic_store(&c->value, 0);
  atomic_store(&c->last_value, 0);
  atomic_store(&c->last_timestamp, 0);

  return c;
}

// Lock-free increment
static inline void valk_counter_inc(valk_counter_v2_t *c) {
  atomic_fetch_add_explicit(&c->value, 1, memory_order_relaxed);
}

static inline void valk_counter_add(valk_counter_v2_t *c, uint64_t n) {
  atomic_fetch_add_explicit(&c->value, n, memory_order_relaxed);
}

// ============================================================================
// HISTOGRAM OPERATIONS (lines 190-280)
// ============================================================================

valk_histogram_v2_t *valk_histogram_get_or_create(
    const char *name,
    const char *help,
    const double *bounds,
    size_t bound_count,
    const valk_label_set_t *labels) {

  const char *iname = intern_string(name);
  valk_label_set_t ilabels = {0};

  for (uint8_t i = 0; i < labels->count && i < VALK_MAX_LABELS; i++) {
    ilabels.labels[i].key = intern_string(labels->labels[i].key);
    ilabels.labels[i].value = intern_string(labels->labels[i].value);
    ilabels.count++;
  }
  ilabels.hash = hash_label_set(&ilabels);

  // Search existing
  size_t count = atomic_load(&g_metrics.histogram_count);
  for (size_t i = 0; i < count; i++) {
    valk_histogram_v2_t *h = &g_metrics.histograms[i];
    if (h->name == iname && labels_equal(&h->labels, &ilabels)) {
      return h;
    }
  }

  // Create new
  size_t idx = atomic_fetch_add(&g_metrics.histogram_count, 1);
  if (idx >= VALK_REGISTRY_MAX_HISTOGRAMS) {
    atomic_fetch_sub(&g_metrics.histogram_count, 1);
    return NULL;
  }

  valk_histogram_v2_t *h = &g_metrics.histograms[idx];
  h->name = iname;
  h->help = intern_string(help);
  h->labels = ilabels;

  // Set bucket bounds
  h->bucket_count = bound_count > VALK_MAX_BUCKETS ? VALK_MAX_BUCKETS : bound_count;
  memcpy(h->bucket_bounds, bounds, h->bucket_count * sizeof(double));

  // Initialize atomic counters
  for (size_t i = 0; i <= h->bucket_count; i++) {
    atomic_store(&h->buckets[i], 0);
    h->last_buckets[i] = 0;
  }
  atomic_store(&h->count, 0);
  atomic_store(&h->sum_micros, 0);
  h->last_count = 0;
  h->last_sum_micros = 0;

  return h;
}

// Lock-free observation
static inline void valk_histogram_observe_us(valk_histogram_v2_t *h, uint64_t us) {
  atomic_fetch_add_explicit(&h->count, 1, memory_order_relaxed);
  atomic_fetch_add_explicit(&h->sum_micros, us, memory_order_relaxed);

  // Find bucket
  double seconds = (double)us / 1000000.0;
  for (uint8_t i = 0; i < h->bucket_count; i++) {
    if (seconds <= h->bucket_bounds[i]) {
      atomic_fetch_add_explicit(&h->buckets[i], 1, memory_order_relaxed);
      return;
    }
  }
  // +Inf bucket
  atomic_fetch_add_explicit(&h->buckets[h->bucket_count], 1, memory_order_relaxed);
}
```

### Layer 5: Lisp Bindings

**File**: `src/metrics_builtins.c` (NEW)

```c
// Line 1-250 (Lisp builtins for metrics)

#include "metrics_v2.h"
#include "parser.h"

// ============================================================================
// COUNTER BUILTINS (lines 20-80)
// ============================================================================

// (metrics/counter name labels...) -> counter-handle
static valk_lval_t *valk_builtin_metrics_counter(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  size_t argc = valk_lval_list_count(a);
  if (argc < 1) {
    return valk_lval_err("metrics/counter: expected at least 1 argument (name)");
  }

  valk_lval_t *name_arg = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, name_arg, LVAL_STR);

  // Parse optional labels
  valk_label_set_t labels = {0};
  for (size_t i = 1; i + 1 < argc; i += 2) {
    valk_lval_t *key = valk_lval_list_nth(a, i);
    valk_lval_t *val = valk_lval_list_nth(a, i + 1);
    LVAL_ASSERT_TYPE(a, key, LVAL_STR);
    LVAL_ASSERT_TYPE(a, val, LVAL_STR);

    if (labels.count < VALK_MAX_LABELS) {
      labels.labels[labels.count].key = key->str;
      labels.labels[labels.count].value = val->str;
      labels.count++;
    }
  }

  valk_counter_v2_t *counter = valk_counter_get_or_create(
      name_arg->str, NULL, &labels);

  if (!counter) {
    return valk_lval_err("metrics/counter: registry full");
  }

  return valk_lval_ref("metrics_counter", counter, NULL);
}

// (metrics/counter-inc counter) -> nil
// (metrics/counter-add counter n) -> nil
static valk_lval_t *valk_builtin_metrics_counter_inc(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  size_t argc = valk_lval_list_count(a);
  if (argc < 1 || argc > 2) {
    return valk_lval_err("metrics/counter-inc: expected 1-2 arguments");
  }

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ref) != LVAL_REF || strcmp(ref->ref.type, "metrics_counter") != 0) {
    return valk_lval_err("metrics/counter-inc: first argument must be counter handle");
  }

  valk_counter_v2_t *counter = ref->ref.ptr;
  uint64_t n = 1;

  if (argc == 2) {
    valk_lval_t *n_arg = valk_lval_list_nth(a, 1);
    LVAL_ASSERT_TYPE(a, n_arg, LVAL_NUM);
    n = (uint64_t)n_arg->num;
  }

  valk_counter_add(counter, n);
  return valk_lval_nil();
}

// ============================================================================
// HISTOGRAM BUILTINS (lines 90-160)
// ============================================================================

// Standard bucket bounds for common use cases
static const double DEFAULT_HTTP_BUCKETS[] = {
  0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0
};

// (metrics/histogram name :buckets (0.01 0.1 1.0) labels...) -> histogram-handle
static valk_lval_t *valk_builtin_metrics_histogram(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  size_t argc = valk_lval_list_count(a);
  if (argc < 1) {
    return valk_lval_err("metrics/histogram: expected at least 1 argument (name)");
  }

  valk_lval_t *name_arg = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, name_arg, LVAL_STR);

  // Parse :buckets option and labels
  double buckets[VALK_MAX_BUCKETS];
  size_t bucket_count = 0;
  valk_label_set_t labels = {0};

  for (size_t i = 1; i < argc; i++) {
    valk_lval_t *item = valk_lval_list_nth(a, i);
    if (LVAL_TYPE(item) == LVAL_SYM && strcmp(item->str, ":buckets") == 0) {
      // Next item should be bucket list
      if (i + 1 < argc) {
        valk_lval_t *bucket_list = valk_lval_list_nth(a, ++i);
        LVAL_ASSERT_TYPE(a, bucket_list, LVAL_QEXPR, LVAL_CONS);
        size_t len = valk_lval_list_count(bucket_list);
        for (size_t j = 0; j < len && bucket_count < VALK_MAX_BUCKETS; j++) {
          valk_lval_t *b = valk_lval_list_nth(bucket_list, j);
          if (LVAL_TYPE(b) == LVAL_NUM) {
            buckets[bucket_count++] = (double)b->num;
          }
        }
      }
    } else if (LVAL_TYPE(item) == LVAL_STR && i + 1 < argc) {
      // Label key-value pair
      valk_lval_t *val = valk_lval_list_nth(a, ++i);
      LVAL_ASSERT_TYPE(a, val, LVAL_STR);
      if (labels.count < VALK_MAX_LABELS) {
        labels.labels[labels.count].key = item->str;
        labels.labels[labels.count].value = val->str;
        labels.count++;
      }
    }
  }

  // Use default HTTP buckets if none specified
  if (bucket_count == 0) {
    bucket_count = sizeof(DEFAULT_HTTP_BUCKETS) / sizeof(double);
    memcpy(buckets, DEFAULT_HTTP_BUCKETS, sizeof(DEFAULT_HTTP_BUCKETS));
  }

  valk_histogram_v2_t *h = valk_histogram_get_or_create(
      name_arg->str, NULL, buckets, bucket_count, &labels);

  if (!h) {
    return valk_lval_err("metrics/histogram: registry full");
  }

  return valk_lval_ref("metrics_histogram", h, NULL);
}

// (metrics/histogram-observe histogram value-us) -> nil
static valk_lval_t *valk_builtin_metrics_histogram_observe(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  LVAL_ASSERT_COUNT_EQ(a, a, 2);

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  valk_lval_t *val = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(ref) != LVAL_REF || strcmp(ref->ref.type, "metrics_histogram") != 0) {
    return valk_lval_err("metrics/histogram-observe: first argument must be histogram handle");
  }
  LVAL_ASSERT_TYPE(a, val, LVAL_NUM);

  valk_histogram_v2_t *h = ref->ref.ptr;
  valk_histogram_observe_us(h, (uint64_t)val->num);

  return valk_lval_nil();
}

// ============================================================================
// STREAMING BUILTINS (lines 170-230)
// ============================================================================

// (metrics/collect-delta) -> delta-snapshot-handle
static valk_lval_t *valk_builtin_metrics_collect_delta(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  UNUSED(a);

  valk_delta_snapshot_t *snap = malloc(sizeof(valk_delta_snapshot_t));
  valk_delta_snapshot_init(snap);
  valk_delta_snapshot_collect(snap, &g_metrics);

  return valk_lval_ref("metrics_delta", snap, (void (*)(void*))valk_delta_snapshot_free);
}

// (metrics/delta-json delta) -> json-string
static valk_lval_t *valk_builtin_metrics_delta_json(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ref) != LVAL_REF || strcmp(ref->ref.type, "metrics_delta") != 0) {
    return valk_lval_err("metrics/delta-json: argument must be delta snapshot handle");
  }

  valk_delta_snapshot_t *snap = ref->ref.ptr;
  char *buf = malloc(65536);
  size_t len = valk_delta_to_json(snap, buf, 65536);

  valk_lval_t *result = valk_lval_str_n(buf, len);
  free(buf);

  return result;
}

// ============================================================================
// REGISTRATION (lines 240-260)
// ============================================================================

void valk_register_metrics_builtins(valk_lenv_t *env) {
  // Counters
  valk_lenv_put_builtin(env, "metrics/counter", valk_builtin_metrics_counter);
  valk_lenv_put_builtin(env, "metrics/counter-inc", valk_builtin_metrics_counter_inc);

  // Gauges
  valk_lenv_put_builtin(env, "metrics/gauge", valk_builtin_metrics_gauge);
  valk_lenv_put_builtin(env, "metrics/gauge-set", valk_builtin_metrics_gauge_set);
  valk_lenv_put_builtin(env, "metrics/gauge-inc", valk_builtin_metrics_gauge_inc);

  // Histograms
  valk_lenv_put_builtin(env, "metrics/histogram", valk_builtin_metrics_histogram);
  valk_lenv_put_builtin(env, "metrics/histogram-observe", valk_builtin_metrics_histogram_observe);

  // Export
  valk_lenv_put_builtin(env, "metrics/collect-delta", valk_builtin_metrics_collect_delta);
  valk_lenv_put_builtin(env, "metrics/delta-json", valk_builtin_metrics_delta_json);
  valk_lenv_put_builtin(env, "metrics/prometheus", valk_builtin_metrics_prometheus);
}
```

### Layer 6: SSE Integration

**File**: `src/modules/aio/metrics-stream.valk` (NEW)

```lisp
; Metrics SSE Stream Module
; Line 1-100

; Create a metrics SSE endpoint with configurable interval
; Usage: (metrics/stream-handler :interval 1000)
(fun {metrics/stream-handler &rest opts}
  {
    ; Parse options
    (= {interval} (or (plist-get opts :interval) 1000))
    (= {include-full} (or (plist-get opts :include-full) true))

    ; Return handler function
    (fn {req}
      {
        (= {stream} (sse/open))
        (= {send-metrics} (fn {}
          {
            (= {delta} (metrics/collect-delta))
            (= {json} (metrics/delta-json delta))
            (if (> (delta/changed delta) 0)
              {sse/send stream "metrics" json}
              nil)
          }))

        ; Send initial full state if requested
        (if include-full
          {sse/send stream "metrics-full" (metrics/json)})

        ; Start periodic sending
        (aio/interval interval send-metrics)

        :deferred
      })
  })

; Combined diagnostics stream (memory + metrics)
; Replaces /debug/diagnostics/memory endpoint
(fun {diagnostics/stream-handler req}
  {
    (= {stream} (sse/open))
    (= {prev-mem-snapshot} nil)

    (= {send-diagnostics} (fn {}
      {
        ; Collect current state
        (= {mem-snapshot} (memory/snapshot))
        (= {metrics-delta} (metrics/collect-delta))

        ; Build combined event
        (= {event} {
          :memory (if prev-mem-snapshot
                    (memory/delta mem-snapshot prev-mem-snapshot)
                    mem-snapshot)
          :metrics (metrics/delta-json metrics-delta)
          :timestamp (time/now-us)
        })

        (sse/json-event stream "diagnostics" event)

        ; Update previous snapshot
        (set! prev-mem-snapshot mem-snapshot)
      }))

    ; 100ms interval (10 Hz) for real-time dashboard
    (aio/interval 100 send-diagnostics)
    :deferred
  })
```

---

## Task Breakdown

### Phase 1: Core Metrics V2 (4 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 1.1 | Define metric types and registry | `src/metrics_v2.h` | ~150 |
| 1.2 | Implement string interning and label hashing | `src/metrics_v2.c` | ~100 |
| 1.3 | Implement counter operations (get/create/inc/add) | `src/metrics_v2.c` | ~100 |
| 1.4 | Implement histogram operations (get/create/observe) | `src/metrics_v2.c` | ~150 |

### Phase 2: Delta Algorithm (4 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 2.1 | Define delta structures | `src/metrics_delta.h` | ~120 |
| 2.2 | Implement delta collection from registry | `src/metrics_delta.c` | ~150 |
| 2.3 | Implement JSON encoding | `src/metrics_delta.c` | ~100 |
| 2.4 | Implement SSE encoding | `src/metrics_delta.c` | ~50 |

### Phase 3: Concurrency (3 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 3.1 | Lock-free counter increment | `src/metrics_v2.c` | ~30 |
| 3.2 | Lock-free histogram observation | `src/metrics_v2.c` | ~40 |
| 3.3 | Thread-safe registry append | `src/metrics_v2.c` | ~60 |

### Phase 4: Lisp Integration (4 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 4.1 | Counter builtins | `src/metrics_builtins.c` | ~80 |
| 4.2 | Histogram builtins | `src/metrics_builtins.c` | ~100 |
| 4.3 | Delta/export builtins | `src/metrics_builtins.c` | ~80 |
| 4.4 | Register builtins | `src/parser.c:4182` | ~15 |

### Phase 5: Streaming Integration (3 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 5.1 | Metrics stream handler | `src/modules/aio/metrics-stream.valk` | ~50 |
| 5.2 | Combined diagnostics stream | `src/modules/aio/metrics-stream.valk` | ~50 |
| 5.3 | Update debug.valk routes | `src/modules/aio/debug.valk` | ~20 |

### Phase 6: Migration (2 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 6.1 | Migrate AIO metrics to V2 | `src/aio_metrics.c` | ~100 |
| 6.2 | Migrate diagnostics to new delta | `src/aio_sse_diagnostics.c` | ~150 |

### Phase 7: Testing (2 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 7.1 | Unit tests for metrics V2 | `test/test_metrics_v2.c` | ~200 |
| 7.2 | Integration tests | `test/test_metrics_stream.valk` | ~100 |

---

## Delta Algorithm Details

### Change Detection Strategy

```
┌─────────────────────────────────────────────────────────────────┐
│                  Delta Change Detection                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  COUNTER: Always report if current != last                      │
│    delta = current - last                                       │
│                                                                 │
│  GAUGE: Report if |current - last| > threshold                  │
│    threshold = max(1, last * 0.001)  // 0.1% or at least 1     │
│                                                                 │
│  HISTOGRAM:                                                     │
│    Report if count changed                                      │
│    Per-bucket deltas: bucket[i] - last_bucket[i]               │
│    Sum delta: sum_micros - last_sum_micros                      │
│                                                                 │
│  SUMMARY:                                                       │
│    Report if total_weight changed                               │
│    Quantile values recomputed from T-Digest centroids          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Wire Format Comparison

| Format | Full Snapshot | Delta Only | Compression |
|--------|--------------|------------|-------------|
| JSON | ~5KB | ~200B | 96% smaller |
| Prometheus | ~3KB | ~100B | 97% smaller |
| Binary | ~2KB | ~50B | 98% smaller |

### Example Delta Output

```json
{
  "ts": 1699900000000,
  "interval_us": 1000000,
  "changed": 3,
  "counters_changed": 2,
  "gauges_changed": 1,
  "histograms_changed": 0,
  "deltas": [
    {"n": "http_requests_total", "t": "c", "d": 42},
    {"n": "http_errors_total", "t": "c", "d": 1},
    {"n": "connections_active", "t": "g", "v": 15}
  ]
}
```

---

## Concurrency Model

### Lock-Free Operations

```c
// Counter increment (always lock-free)
atomic_fetch_add_explicit(&counter->value, n, memory_order_relaxed);

// Gauge set (always lock-free)
atomic_store_explicit(&gauge->value, v, memory_order_relaxed);

// Histogram observe (always lock-free)
atomic_fetch_add_explicit(&h->count, 1, memory_order_relaxed);
atomic_fetch_add_explicit(&h->sum_micros, us, memory_order_relaxed);
atomic_fetch_add_explicit(&h->buckets[bucket_idx], 1, memory_order_relaxed);
```

### Registry Append (CAS-based)

```c
// Append new metric with compare-and-swap
size_t idx = atomic_fetch_add(&registry->counter_count, 1);
if (idx >= MAX_COUNTERS) {
  atomic_fetch_sub(&registry->counter_count, 1);
  return NULL;  // Full
}
// Initialize at reserved index
registry->counters[idx] = ...;
```

### Memory Ordering

| Operation | Order | Rationale |
|-----------|-------|-----------|
| Metric update | relaxed | Single-writer, any reader ordering OK |
| Delta read | relaxed | Point-in-time snapshot acceptable |
| Registry append | seq_cst | Ensure visibility to readers |
| String intern | acquire/release | Pool visibility across threads |

---

## Example Lisp Usage

### Define and Use Metrics

```lisp
; Define a counter
(def {requests} (metrics/counter "http_requests_total"
                                  "method" "GET"
                                  "path" "/api"))

; Increment on each request
(fun {handle-request req}
  {
    (metrics/counter-inc requests)
    ; ... handle request ...
  })

; Define a histogram for latency
(def {latency} (metrics/histogram "http_request_duration_seconds"
                                   :buckets (0.001 0.01 0.1 1.0 10.0)
                                   "method" "GET"))

; Observe latency
(fun {timed-handler req}
  {
    (= {start} (time/now-us))
    (= {result} (handle-request req))
    (metrics/histogram-observe latency (- (time/now-us) start))
    result
  })
```

### Stream Metrics via SSE

```lisp
; Add metrics streaming endpoint
(http2/server-listen sys 8080 (fn {req}
  {match (get req :path)
    "/metrics/stream" (metrics/stream-handler :interval 1000)
    "/metrics" {:status "200"
                :content-type "text/plain"
                :body (metrics/prometheus)}
    _ {:status "404"}}))
```

---

## Migration from V1

### Compatibility Layer

```c
// Map old API to new
#define valk_counter_inc(c) valk_counter_add((valk_counter_v2_t*)(c), 1)
#define valk_histogram_observe(h, v) \
  valk_histogram_observe_us((valk_histogram_v2_t*)(h), (uint64_t)((v) * 1e6))
```

### Phased Migration

1. **Phase A**: Add V2 alongside V1, no breaking changes
2. **Phase B**: Migrate internal usage to V2
3. **Phase C**: Update SSE diagnostics to use V2 deltas
4. **Phase D**: Deprecate V1 API
5. **Phase E**: Remove V1

---

## Success Criteria

1. **Delta Efficiency**: >90% reduction in wire payload vs full snapshot
2. **Concurrency**: No mutex contention in hot path (inc/observe)
3. **Throughput**: >1M counter increments/second per core
4. **Latency**: <100ns for counter increment
5. **Lisp Integration**: Can define and use metrics from Lisp
6. **Streaming**: SSE stream sends deltas every interval
7. **Backward Compatible**: Existing code continues to work
