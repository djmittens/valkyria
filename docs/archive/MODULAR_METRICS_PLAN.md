# Modular Metrics System Implementation Plan

## Executive Summary

A **label-based, centralized metrics store** with:
- **Prometheus-style labels**: Multi-dimensional identification `{server="api", port="8443", status="2xx"}`
- **Dedicated memory area**: Decoupled from core structs, contiguous and cache-friendly
- **Lock-free updates**: Atomic operations on hot path, lock only for registration
- **Compile-time optional**: Zero overhead when disabled - no code, no memory

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    valk_metrics_store_t                         │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │
│  │  Counters   │  │   Gauges    │  │      Histograms         │  │
│  │  [512]      │  │   [256]     │  │        [64]             │  │
│  │             │  │             │  │                         │  │
│  │ name        │  │ name        │  │ name                    │  │
│  │ labels[]    │  │ labels[]    │  │ labels[]                │  │
│  │ _Atomic val │  │ _Atomic val │  │ _Atomic count/sum/buck  │  │
│  └─────────────┘  └─────────────┘  └─────────────────────────┘  │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                   Label Pool (interned strings)         │    │
│  │  "server" "api" "port" "8443" "status" "2xx" ...        │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                 │
│  registry_lock (mutex) - only for registration                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Phase 1: Core Types and Store

### 1.1 Header (`src/metrics.h`)

```c
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
```

### 1.2 Implementation (`src/metrics.c`)

```c
// src/metrics.c
#ifdef VALK_METRICS_ENABLED

#include "metrics.h"
#include <string.h>
#include <stdio.h>
#include <stdarg.h>
#include <time.h>

// Global store
valk_metrics_store_t g_valk_metrics;

//-----------------------------------------------------------------------------
// Internal: Label interning
//-----------------------------------------------------------------------------

static const char* intern_string(const char* str) {
  if (!str) return NULL;

  // Check if already interned
  for (size_t i = 0; i < g_valk_metrics.label_pool_count; i++) {
    if (strcmp(g_valk_metrics.label_pool[i], str) == 0) {
      return g_valk_metrics.label_pool[i];
    }
  }

  // Add to pool
  if (g_valk_metrics.label_pool_count >= VALK_METRICS_LABEL_POOL_SIZE) {
    return str;  // Pool full, fall back to non-interned
  }

  char* copy = strdup(str);
  g_valk_metrics.label_pool[g_valk_metrics.label_pool_count++] = copy;
  return copy;
}

static bool labels_equal(const valk_labels_t* a, const valk_labels_t* b) {
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

static void parse_labels_va(valk_labels_t* out, va_list ap) {
  out->count = 0;
  while (out->count < VALK_METRICS_MAX_LABELS) {
    const char* key = va_arg(ap, const char*);
    if (!key) break;
    const char* value = va_arg(ap, const char*);
    if (!value) break;

    out->labels[out->count].key = intern_string(key);
    out->labels[out->count].value = intern_string(value);
    out->count++;
  }
}

//-----------------------------------------------------------------------------
// Lifecycle
//-----------------------------------------------------------------------------

void valk_metrics_init(void) {
  memset(&g_valk_metrics, 0, sizeof(g_valk_metrics));
  pthread_mutex_init(&g_valk_metrics.registry_lock, NULL);

  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  g_valk_metrics.start_time_us = ts.tv_sec * 1000000ULL + ts.tv_nsec / 1000;
}

void valk_metrics_destroy(void) {
  pthread_mutex_destroy(&g_valk_metrics.registry_lock);

  // Free interned strings
  for (size_t i = 0; i < g_valk_metrics.label_pool_count; i++) {
    free((void*)g_valk_metrics.label_pool[i]);
  }
}

//-----------------------------------------------------------------------------
// Registration
//-----------------------------------------------------------------------------

valk_counter_t* valk_metric_counter(const char* name, ...) {
  pthread_mutex_lock(&g_valk_metrics.registry_lock);

  valk_labels_t labels;
  va_list ap;
  va_start(ap, name);
  parse_labels_va(&labels, ap);
  va_end(ap);

  const char* iname = intern_string(name);

  // Check if exists
  size_t count = atomic_load(&g_valk_metrics.counter_count);
  for (size_t i = 0; i < count; i++) {
    valk_counter_t* c = &g_valk_metrics.counters[i];
    if (c->name == iname && labels_equal(&c->labels, &labels)) {
      pthread_mutex_unlock(&g_valk_metrics.registry_lock);
      return c;
    }
  }

  // Create new
  if (count >= VALK_METRICS_MAX_COUNTERS) {
    pthread_mutex_unlock(&g_valk_metrics.registry_lock);
    return NULL;  // Store full
  }

  valk_counter_t* c = &g_valk_metrics.counters[count];
  c->name = iname;
  c->labels = labels;
  atomic_store(&c->value, 0);
  atomic_fetch_add(&g_valk_metrics.counter_count, 1);

  pthread_mutex_unlock(&g_valk_metrics.registry_lock);
  return c;
}

valk_gauge_t* valk_metric_gauge(const char* name, ...) {
  pthread_mutex_lock(&g_valk_metrics.registry_lock);

  valk_labels_t labels;
  va_list ap;
  va_start(ap, name);
  parse_labels_va(&labels, ap);
  va_end(ap);

  const char* iname = intern_string(name);

  // Check if exists
  size_t count = atomic_load(&g_valk_metrics.gauge_count);
  for (size_t i = 0; i < count; i++) {
    valk_gauge_t* g = &g_valk_metrics.gauges[i];
    if (g->name == iname && labels_equal(&g->labels, &labels)) {
      pthread_mutex_unlock(&g_valk_metrics.registry_lock);
      return g;
    }
  }

  // Create new
  if (count >= VALK_METRICS_MAX_GAUGES) {
    pthread_mutex_unlock(&g_valk_metrics.registry_lock);
    return NULL;
  }

  valk_gauge_t* g = &g_valk_metrics.gauges[count];
  g->name = iname;
  g->labels = labels;
  atomic_store(&g->value, 0);
  atomic_fetch_add(&g_valk_metrics.gauge_count, 1);

  pthread_mutex_unlock(&g_valk_metrics.registry_lock);
  return g;
}

valk_histogram_t* valk_metric_histogram(const char* name,
                                         const double* bounds, size_t bucket_count,
                                         ...) {
  pthread_mutex_lock(&g_valk_metrics.registry_lock);

  valk_labels_t labels;
  va_list ap;
  va_start(ap, bucket_count);
  parse_labels_va(&labels, ap);
  va_end(ap);

  const char* iname = intern_string(name);

  // Check if exists
  size_t count = atomic_load(&g_valk_metrics.histogram_count);
  for (size_t i = 0; i < count; i++) {
    valk_histogram_t* h = &g_valk_metrics.histograms[i];
    if (h->name == iname && labels_equal(&h->labels, &labels)) {
      pthread_mutex_unlock(&g_valk_metrics.registry_lock);
      return h;
    }
  }

  // Create new
  if (count >= VALK_METRICS_MAX_HISTOGRAMS) {
    pthread_mutex_unlock(&g_valk_metrics.registry_lock);
    return NULL;
  }

  valk_histogram_t* h = &g_valk_metrics.histograms[count];
  h->name = iname;
  h->labels = labels;
  atomic_store(&h->count, 0);
  atomic_store(&h->sum_us, 0);

  h->bucket_count = (bucket_count > VALK_METRICS_MAX_BUCKETS)
                    ? VALK_METRICS_MAX_BUCKETS : bucket_count;
  for (uint8_t i = 0; i < h->bucket_count; i++) {
    h->bucket_bounds[i] = bounds[i];
    atomic_store(&h->buckets[i], 0);
  }
  atomic_store(&h->buckets[h->bucket_count], 0);  // +Inf

  atomic_fetch_add(&g_valk_metrics.histogram_count, 1);

  pthread_mutex_unlock(&g_valk_metrics.registry_lock);
  return h;
}

//-----------------------------------------------------------------------------
// Iteration
//-----------------------------------------------------------------------------

void valk_metrics_foreach_counter(valk_counter_iter_fn fn, void* ctx) {
  size_t count = atomic_load(&g_valk_metrics.counter_count);
  for (size_t i = 0; i < count; i++) {
    fn(&g_valk_metrics.counters[i], ctx);
  }
}

void valk_metrics_foreach_gauge(valk_gauge_iter_fn fn, void* ctx) {
  size_t count = atomic_load(&g_valk_metrics.gauge_count);
  for (size_t i = 0; i < count; i++) {
    fn(&g_valk_metrics.gauges[i], ctx);
  }
}

void valk_metrics_foreach_histogram(valk_histogram_iter_fn fn, void* ctx) {
  size_t count = atomic_load(&g_valk_metrics.histogram_count);
  for (size_t i = 0; i < count; i++) {
    fn(&g_valk_metrics.histograms[i], ctx);
  }
}

//-----------------------------------------------------------------------------
// Export: Prometheus
//-----------------------------------------------------------------------------

static size_t write_labels(char* buf, size_t cap, const valk_labels_t* labels) {
  if (labels->count == 0) return 0;

  size_t pos = 0;
  pos += snprintf(buf + pos, cap - pos, "{");

  for (uint8_t i = 0; i < labels->count; i++) {
    if (i > 0) pos += snprintf(buf + pos, cap - pos, ",");
    pos += snprintf(buf + pos, cap - pos, "%s=\"%s\"",
                    labels->labels[i].key, labels->labels[i].value);
  }

  pos += snprintf(buf + pos, cap - pos, "}");
  return pos;
}

typedef struct {
  char* buf;
  size_t cap;
  size_t pos;
} prom_ctx_t;

static void prom_counter(const valk_counter_t* c, void* ctx) {
  prom_ctx_t* p = ctx;
  uint64_t val = atomic_load_explicit(&c->value, memory_order_relaxed);

  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, "%s", c->name);
  p->pos += write_labels(p->buf + p->pos, p->cap - p->pos, &c->labels);
  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, " %lu\n", val);
}

static void prom_gauge(const valk_gauge_t* g, void* ctx) {
  prom_ctx_t* p = ctx;
  int64_t val = atomic_load_explicit(&g->value, memory_order_relaxed);

  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, "%s", g->name);
  p->pos += write_labels(p->buf + p->pos, p->cap - p->pos, &g->labels);
  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, " %ld\n", val);
}

static void prom_histogram(const valk_histogram_t* h, void* ctx) {
  prom_ctx_t* p = ctx;

  uint64_t count = atomic_load_explicit(&h->count, memory_order_relaxed);
  uint64_t sum_us = atomic_load_explicit(&h->sum_us, memory_order_relaxed);

  // Buckets (cumulative)
  uint64_t cumulative = 0;
  for (uint8_t i = 0; i < h->bucket_count; i++) {
    cumulative += atomic_load_explicit(&h->buckets[i], memory_order_relaxed);

    p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, "%s_bucket{", h->name);
    for (uint8_t j = 0; j < h->labels.count; j++) {
      p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, "%s=\"%s\",",
                         h->labels.labels[j].key, h->labels.labels[j].value);
    }
    p->pos += snprintf(p->buf + p->pos, p->cap - p->pos,
                       "le=\"%.3f\"} %lu\n", h->bucket_bounds[i], cumulative);
  }

  // +Inf bucket
  cumulative += atomic_load_explicit(&h->buckets[h->bucket_count], memory_order_relaxed);
  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, "%s_bucket{", h->name);
  for (uint8_t j = 0; j < h->labels.count; j++) {
    p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, "%s=\"%s\",",
                       h->labels.labels[j].key, h->labels.labels[j].value);
  }
  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, "le=\"+Inf\"} %lu\n", cumulative);

  // Sum and count
  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, "%s_sum", h->name);
  p->pos += write_labels(p->buf + p->pos, p->cap - p->pos, &h->labels);
  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, " %.6f\n", (double)sum_us / 1e6);

  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, "%s_count", h->name);
  p->pos += write_labels(p->buf + p->pos, p->cap - p->pos, &h->labels);
  p->pos += snprintf(p->buf + p->pos, p->cap - p->pos, " %lu\n", count);
}

size_t valk_metrics_prometheus(char* buf, size_t cap) {
  prom_ctx_t ctx = { .buf = buf, .cap = cap, .pos = 0 };

  valk_metrics_foreach_counter(prom_counter, &ctx);
  valk_metrics_foreach_gauge(prom_gauge, &ctx);
  valk_metrics_foreach_histogram(prom_histogram, &ctx);

  return ctx.pos;
}

//-----------------------------------------------------------------------------
// Export: JSON
//-----------------------------------------------------------------------------

size_t valk_metrics_json(char* buf, size_t cap) {
  size_t pos = 0;

  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  uint64_t now_us = ts.tv_sec * 1000000ULL + ts.tv_nsec / 1000;
  double uptime = (double)(now_us - g_valk_metrics.start_time_us) / 1e6;

  pos += snprintf(buf + pos, cap - pos, "{\n");
  pos += snprintf(buf + pos, cap - pos, "  \"uptime_seconds\": %.3f,\n", uptime);

  // Counters
  pos += snprintf(buf + pos, cap - pos, "  \"counters\": [\n");
  size_t counter_count = atomic_load(&g_valk_metrics.counter_count);
  for (size_t i = 0; i < counter_count; i++) {
    valk_counter_t* c = &g_valk_metrics.counters[i];
    uint64_t val = atomic_load_explicit(&c->value, memory_order_relaxed);

    pos += snprintf(buf + pos, cap - pos, "    {\"name\": \"%s\", \"value\": %lu, \"labels\": {",
                    c->name, val);
    for (uint8_t j = 0; j < c->labels.count; j++) {
      if (j > 0) pos += snprintf(buf + pos, cap - pos, ", ");
      pos += snprintf(buf + pos, cap - pos, "\"%s\": \"%s\"",
                      c->labels.labels[j].key, c->labels.labels[j].value);
    }
    pos += snprintf(buf + pos, cap - pos, "}}%s\n",
                    (i < counter_count - 1) ? "," : "");
  }
  pos += snprintf(buf + pos, cap - pos, "  ],\n");

  // Gauges
  pos += snprintf(buf + pos, cap - pos, "  \"gauges\": [\n");
  size_t gauge_count = atomic_load(&g_valk_metrics.gauge_count);
  for (size_t i = 0; i < gauge_count; i++) {
    valk_gauge_t* g = &g_valk_metrics.gauges[i];
    int64_t val = atomic_load_explicit(&g->value, memory_order_relaxed);

    pos += snprintf(buf + pos, cap - pos, "    {\"name\": \"%s\", \"value\": %ld, \"labels\": {",
                    g->name, val);
    for (uint8_t j = 0; j < g->labels.count; j++) {
      if (j > 0) pos += snprintf(buf + pos, cap - pos, ", ");
      pos += snprintf(buf + pos, cap - pos, "\"%s\": \"%s\"",
                      g->labels.labels[j].key, g->labels.labels[j].value);
    }
    pos += snprintf(buf + pos, cap - pos, "}}%s\n",
                    (i < gauge_count - 1) ? "," : "");
  }
  pos += snprintf(buf + pos, cap - pos, "  ],\n");

  // Histograms
  pos += snprintf(buf + pos, cap - pos, "  \"histograms\": [\n");
  size_t hist_count = atomic_load(&g_valk_metrics.histogram_count);
  for (size_t i = 0; i < hist_count; i++) {
    valk_histogram_t* h = &g_valk_metrics.histograms[i];
    uint64_t count = atomic_load_explicit(&h->count, memory_order_relaxed);
    uint64_t sum_us = atomic_load_explicit(&h->sum_us, memory_order_relaxed);

    pos += snprintf(buf + pos, cap - pos,
                    "    {\"name\": \"%s\", \"count\": %lu, \"sum\": %.6f, \"labels\": {",
                    h->name, count, (double)sum_us / 1e6);
    for (uint8_t j = 0; j < h->labels.count; j++) {
      if (j > 0) pos += snprintf(buf + pos, cap - pos, ", ");
      pos += snprintf(buf + pos, cap - pos, "\"%s\": \"%s\"",
                      h->labels.labels[j].key, h->labels.labels[j].value);
    }
    pos += snprintf(buf + pos, cap - pos, "}, \"buckets\": [");
    for (uint8_t j = 0; j <= h->bucket_count; j++) {
      if (j > 0) pos += snprintf(buf + pos, cap - pos, ", ");
      pos += snprintf(buf + pos, cap - pos, "%lu",
                      atomic_load_explicit(&h->buckets[j], memory_order_relaxed));
    }
    pos += snprintf(buf + pos, cap - pos, "]}%s\n",
                    (i < hist_count - 1) ? "," : "");
  }
  pos += snprintf(buf + pos, cap - pos, "  ]\n");

  pos += snprintf(buf + pos, cap - pos, "}\n");

  return pos;
}

#endif // VALK_METRICS_ENABLED
```

---

## Phase 2: Integration with AIO

### 2.1 Server Metrics

```c
// src/aio_uv.c

#include "metrics.h"

// Per-server metric handles (cached at server creation)
typedef struct {
  valk_counter_t* requests_total;
  valk_counter_t* requests_success;
  valk_counter_t* requests_client_error;
  valk_counter_t* requests_server_error;
  valk_gauge_t* connections_active;
  valk_histogram_t* request_duration;
  valk_counter_t* bytes_sent;
  valk_counter_t* bytes_recv;
} valk_server_metrics_t;

// In valk_aio_http_server struct, add:
//   valk_server_metrics_t metrics;

static void server_metrics_init(valk_server_metrics_t* m,
                                 const char* name, int port) {
  char port_str[8];
  snprintf(port_str, sizeof(port_str), "%d", port);

  m->requests_total = valk_metric_counter("http_requests_total",
    "server", name, "port", port_str, NULL);

  m->requests_success = valk_metric_counter("http_requests_total",
    "server", name, "port", port_str, "status", "2xx", NULL);

  m->requests_client_error = valk_metric_counter("http_requests_total",
    "server", name, "port", port_str, "status", "4xx", NULL);

  m->requests_server_error = valk_metric_counter("http_requests_total",
    "server", name, "port", port_str, "status", "5xx", NULL);

  m->connections_active = valk_metric_gauge("http_connections_active",
    "server", name, "port", port_str, NULL);

  static const double latency_buckets[] = {
    0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0
  };
  m->request_duration = valk_metric_histogram("http_request_duration_seconds",
    latency_buckets, 12, "server", name, "port", port_str, NULL);

  m->bytes_sent = valk_metric_counter("http_bytes_sent_total",
    "server", name, "port", port_str, NULL);

  m->bytes_recv = valk_metric_counter("http_bytes_recv_total",
    "server", name, "port", port_str, NULL);
}

// In connection accept callback:
static void on_connection_accept(valk_aio_http_server* server) {
  valk_gauge_inc(server->metrics.connections_active);
}

// In connection close callback:
static void on_connection_close(valk_aio_http_server* server) {
  valk_gauge_dec(server->metrics.connections_active);
}

// In request completion:
static void on_request_complete(valk_aio_http_server* server,
                                 int status, uint64_t start_us,
                                 size_t bytes_sent, size_t bytes_recv) {
  uint64_t now_us = uv_hrtime() / 1000;
  double duration_sec = (double)(now_us - start_us) / 1e6;

  valk_counter_inc(server->metrics.requests_total);
  valk_histogram_observe(server->metrics.request_duration, duration_sec);
  valk_counter_add(server->metrics.bytes_sent, bytes_sent);
  valk_counter_add(server->metrics.bytes_recv, bytes_recv);

  if (status >= 200 && status < 400) {
    valk_counter_inc(server->metrics.requests_success);
  } else if (status >= 400 && status < 500) {
    valk_counter_inc(server->metrics.requests_client_error);
  } else if (status >= 500) {
    valk_counter_inc(server->metrics.requests_server_error);
  }
}
```

### 2.2 Runtime Metrics

```c
// In src/gc.c, after collection:

#include "metrics.h"

static valk_counter_t* gc_collections_total;
static valk_counter_t* gc_collections_major;
static valk_histogram_t* gc_pause_duration;
static valk_gauge_t* gc_heap_bytes;

void gc_metrics_init(void) {
  gc_collections_total = valk_metric_counter("gc_collections_total", NULL);
  gc_collections_major = valk_metric_counter("gc_collections_total",
    "type", "major", NULL);

  static const double pause_buckets[] = {
    0.0001, 0.0005, 0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1.0
  };
  gc_pause_duration = valk_metric_histogram("gc_pause_seconds",
    pause_buckets, 9, NULL);

  gc_heap_bytes = valk_metric_gauge("gc_heap_bytes", NULL);
}

void gc_record_collection(bool major, uint64_t pause_us, size_t heap_bytes) {
  valk_counter_inc(gc_collections_total);
  if (major) valk_counter_inc(gc_collections_major);
  valk_histogram_observe_us(gc_pause_duration, pause_us);
  valk_gauge_set(gc_heap_bytes, heap_bytes);
}
```

---

## Phase 3: Lisp Builtins

### 3.1 Conditional Registration

```c
// src/parser.c

#ifdef VALK_METRICS_ENABLED

static valk_lval_t* builtin_metrics_json(valk_lenv_t* e, valk_lval_t* a) {
  LASSERT_NUM("metrics/json", a, 0);

  char buf[65536];
  size_t len = valk_metrics_json(buf, sizeof(buf));
  return valk_lval_str_n(buf, len);
}

static valk_lval_t* builtin_metrics_prometheus(valk_lenv_t* e, valk_lval_t* a) {
  LASSERT_NUM("metrics/prometheus", a, 0);

  char buf[65536];
  size_t len = valk_metrics_prometheus(buf, sizeof(buf));
  return valk_lval_str_n(buf, len);
}

static valk_lval_t* builtin_metrics_counter_inc(valk_lenv_t* e, valk_lval_t* a) {
  // (metrics/counter-inc "name" "key1" "val1" "key2" "val2" ...)
  LASSERT_MIN("metrics/counter-inc", a, 1);
  LASSERT_TYPE("metrics/counter-inc", a->cell.items[0], LVAL_STR);

  const char* name = a->cell.items[0]->str;

  // Build label arrays from remaining args
  size_t label_count = (a->cell.count - 1) / 2;
  const char* keys[VALK_METRICS_MAX_LABELS];
  const char* vals[VALK_METRICS_MAX_LABELS];

  for (size_t i = 0; i < label_count && i < VALK_METRICS_MAX_LABELS; i++) {
    keys[i] = a->cell.items[1 + i*2]->str;
    vals[i] = a->cell.items[2 + i*2]->str;
  }

  valk_counter_t* c = valk_metric_counter_labels(name, keys, vals, label_count);
  if (c) valk_counter_inc(c);

  return valk_lval_nil();
}

#endif

void valk_lenv_add_builtins(valk_lenv_t* e) {
  // ... other builtins ...

#ifdef VALK_METRICS_ENABLED
  valk_lenv_add_builtin(e, "metrics/json", builtin_metrics_json);
  valk_lenv_add_builtin(e, "metrics/prometheus", builtin_metrics_prometheus);
  valk_lenv_add_builtin(e, "metrics/counter-inc", builtin_metrics_counter_inc);
#endif
}
```

---

## Phase 4: Build System

### 4.1 Makefile

```makefile
# Feature flags
VALK_METRICS ?= 0

# Base flags
CFLAGS := -std=c23 -Wall -Wextra -O2
LDFLAGS := -luv -lssl -lcrypto -lnghttp2

# Core sources (always included)
SRCS := src/parser.c src/memory.c src/gc.c src/aio_uv.c src/repl.c

# Conditional: Metrics
ifeq ($(VALK_METRICS),1)
  CFLAGS += -DVALK_METRICS_ENABLED=1
  SRCS += src/metrics.c
endif

# Targets
build: $(SRCS)
	$(CC) $(CFLAGS) -o build/valk $(SRCS) $(LDFLAGS)

build-metrics:
	$(MAKE) build VALK_METRICS=1

test: build
	./build/test_std
	./build/valk test/test_prelude.valk

test-metrics:
	$(MAKE) test VALK_METRICS=1

.PHONY: build build-metrics test test-metrics
```

---

## Phase 5: Example Output

### 5.1 Prometheus Format

```prometheus
# HELP http_requests_total Total HTTP requests
# TYPE http_requests_total counter
http_requests_total{server="api",port="8443"} 12543
http_requests_total{server="api",port="8443",status="2xx"} 11890
http_requests_total{server="api",port="8443",status="4xx"} 623
http_requests_total{server="api",port="8443",status="5xx"} 30

# HELP http_connections_active Active HTTP connections
# TYPE http_connections_active gauge
http_connections_active{server="api",port="8443"} 45

# HELP http_request_duration_seconds Request latency
# TYPE http_request_duration_seconds histogram
http_request_duration_seconds_bucket{server="api",port="8443",le="0.001"} 3420
http_request_duration_seconds_bucket{server="api",port="8443",le="0.005"} 8932
http_request_duration_seconds_bucket{server="api",port="8443",le="0.010"} 10234
http_request_duration_seconds_bucket{server="api",port="8443",le="0.025"} 11456
http_request_duration_seconds_bucket{server="api",port="8443",le="0.050"} 12001
http_request_duration_seconds_bucket{server="api",port="8443",le="0.100"} 12345
http_request_duration_seconds_bucket{server="api",port="8443",le="+Inf"} 12543
http_request_duration_seconds_sum{server="api",port="8443"} 287.432
http_request_duration_seconds_count{server="api",port="8443"} 12543

# HELP gc_collections_total GC collections
# TYPE gc_collections_total counter
gc_collections_total 1456
gc_collections_total{type="major"} 234

# HELP gc_heap_bytes Current heap size
# TYPE gc_heap_bytes gauge
gc_heap_bytes 67108864
```

### 5.2 JSON Format

```json
{
  "uptime_seconds": 3600.123,
  "counters": [
    {"name": "http_requests_total", "value": 12543, "labels": {"server": "api", "port": "8443"}},
    {"name": "http_requests_total", "value": 11890, "labels": {"server": "api", "port": "8443", "status": "2xx"}},
    {"name": "gc_collections_total", "value": 1456, "labels": {}}
  ],
  "gauges": [
    {"name": "http_connections_active", "value": 45, "labels": {"server": "api", "port": "8443"}},
    {"name": "gc_heap_bytes", "value": 67108864, "labels": {}}
  ],
  "histograms": [
    {
      "name": "http_request_duration_seconds",
      "count": 12543,
      "sum": 287.432,
      "labels": {"server": "api", "port": "8443"},
      "buckets": [3420, 5512, 1302, 1222, 545, 344, 198]
    }
  ]
}
```

---

## Concurrency Summary

| Operation | Lock | Overhead |
|-----------|------|----------|
| `valk_metrics_init()` | N/A | Once at startup |
| `valk_metric_counter(...)` | `registry_lock` | ~100ns (cache result) |
| `valk_counter_inc(c)` | None | ~5ns (atomic fetch_add) |
| `valk_histogram_observe(h, v)` | None | ~20ns (atomic ops) |
| `valk_metrics_prometheus(...)` | None | Reads relaxed atomics |
| `valk_metrics_json(...)` | None | Reads relaxed atomics |

**Key design decisions:**
1. Registration takes lock (rare operation, called at init)
2. Updates use `memory_order_relaxed` atomics (no barriers needed for counters)
3. Reads during export may see slightly stale values (acceptable for metrics)
4. No per-update memory allocation

---

## File Summary

| File | Action | Conditional |
|------|--------|-------------|
| `src/metrics.h` | CREATE | Contains both enabled/disabled code |
| `src/metrics.c` | CREATE | Only compiled with `VALK_METRICS=1` |
| `src/aio_uv.c` | MODIFY | Add metric hooks |
| `src/gc.c` | MODIFY | Add GC metric hooks |
| `src/parser.c` | MODIFY | Add Lisp builtins (conditional) |
| `Makefile` | MODIFY | Add `VALK_METRICS` flag |
| `test/test_metrics.c` | CREATE | Only compiled with `VALK_METRICS=1` |
