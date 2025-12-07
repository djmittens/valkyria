// src/metrics.c
#ifdef VALK_METRICS_ENABLED

#include "metrics.h"
#include <string.h>
#include <stdio.h>
#include <stdarg.h>
#include <time.h>
#include <stdlib.h>

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

valk_counter_t* valk_metric_counter_labels(const char* name,
                                            const char** keys, const char** vals,
                                            size_t count) {
  pthread_mutex_lock(&g_valk_metrics.registry_lock);

  valk_labels_t labels;
  labels.count = 0;
  for (size_t i = 0; i < count && i < VALK_METRICS_MAX_LABELS; i++) {
    labels.labels[i].key = intern_string(keys[i]);
    labels.labels[i].value = intern_string(vals[i]);
    labels.count++;
  }

  const char* iname = intern_string(name);

  // Check if exists
  size_t counter_count = atomic_load(&g_valk_metrics.counter_count);
  for (size_t i = 0; i < counter_count; i++) {
    valk_counter_t* c = &g_valk_metrics.counters[i];
    if (c->name == iname && labels_equal(&c->labels, &labels)) {
      pthread_mutex_unlock(&g_valk_metrics.registry_lock);
      return c;
    }
  }

  // Create new
  if (counter_count >= VALK_METRICS_MAX_COUNTERS) {
    pthread_mutex_unlock(&g_valk_metrics.registry_lock);
    return NULL;  // Store full
  }

  valk_counter_t* c = &g_valk_metrics.counters[counter_count];
  c->name = iname;
  c->labels = labels;
  atomic_store(&c->value, 0);
  atomic_fetch_add(&g_valk_metrics.counter_count, 1);

  pthread_mutex_unlock(&g_valk_metrics.registry_lock);
  return c;
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
    // Output buckets with bounds and counts
    pos += snprintf(buf + pos, cap - pos, "}, \"buckets\": [");
    for (uint8_t j = 0; j < h->bucket_count; j++) {
      if (j > 0) pos += snprintf(buf + pos, cap - pos, ", ");
      pos += snprintf(buf + pos, cap - pos, "{\"le\": %.6f, \"count\": %lu}",
                      h->bucket_bounds[j],
                      atomic_load_explicit(&h->buckets[j], memory_order_relaxed));
    }
    // Add +Inf bucket
    if (h->bucket_count > 0) pos += snprintf(buf + pos, cap - pos, ", ");
    pos += snprintf(buf + pos, cap - pos, "{\"le\": \"+Inf\", \"count\": %lu}",
                    atomic_load_explicit(&h->buckets[h->bucket_count], memory_order_relaxed));
    pos += snprintf(buf + pos, cap - pos, "]}%s\n",
                    (i < hist_count - 1) ? "," : "");
  }
  pos += snprintf(buf + pos, cap - pos, "  ]\n");

  pos += snprintf(buf + pos, cap - pos, "}\n");

  return pos;
}

#endif // VALK_METRICS_ENABLED
