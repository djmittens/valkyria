// src/metrics_v2.c
#include "metrics_v2.h"
#include <string.h>
#include <stdio.h>
#include <time.h>
#include <stdlib.h>

// ============================================================================
// GLOBAL REGISTRY
// ============================================================================

valk_metrics_registry_t g_metrics;

// ============================================================================
// TIMESTAMP UTILITIES
// ============================================================================

static uint64_t get_timestamp_us(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000000ULL + ts.tv_nsec / 1000;
}

// ============================================================================
// STRING INTERNING
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
// LABEL SET HASHING
// ============================================================================

static uint32_t hash_label_set(const valk_label_set_v2_t *labels) {
  uint32_t hash = 5381;
  for (uint8_t i = 0; i < labels->count; i++) {
    // Hash key pointer (interned)
    hash = ((hash << 5) + hash) ^ (uint32_t)(uintptr_t)labels->labels[i].key;
    // Hash value pointer (interned)
    hash = ((hash << 5) + hash) ^ (uint32_t)(uintptr_t)labels->labels[i].value;
  }
  return hash;
}

static bool labels_equal(const valk_label_set_v2_t *a, const valk_label_set_v2_t *b) {
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
// REGISTRY INITIALIZATION
// ============================================================================

void valk_metrics_registry_init(void) {
  memset(&g_metrics, 0, sizeof(g_metrics));
  pthread_mutex_init(&g_metrics.pool_lock, NULL);

  g_metrics.snapshot_interval_us = 1000000;  // 1 second default
  g_metrics.start_time_us = get_timestamp_us();
  g_metrics.last_snapshot_time = g_metrics.start_time_us;
}

void valk_metrics_registry_destroy(void) {
  pthread_mutex_destroy(&g_metrics.pool_lock);

  // Free interned strings
  for (size_t i = 0; i < g_metrics.string_pool_count; i++) {
    free((void*)g_metrics.string_pool[i]);
  }

  memset(&g_metrics, 0, sizeof(g_metrics));
}

// ============================================================================
// COUNTER OPERATIONS
// ============================================================================

valk_counter_v2_t *valk_counter_get_or_create(const char *name,
                                               const char *help,
                                               const valk_label_set_v2_t *labels) {
  const char *iname = intern_string(name);
  valk_label_set_v2_t ilabels = {0};

  // Intern all label strings
  for (uint8_t i = 0; i < labels->count && i < VALK_MAX_LABELS_V2; i++) {
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

// ============================================================================
// GAUGE OPERATIONS
// ============================================================================

valk_gauge_v2_t *valk_gauge_get_or_create(const char *name,
                                          const char *help,
                                          const valk_label_set_v2_t *labels) {
  const char *iname = intern_string(name);
  valk_label_set_v2_t ilabels = {0};

  // Intern all label strings
  for (uint8_t i = 0; i < labels->count && i < VALK_MAX_LABELS_V2; i++) {
    ilabels.labels[i].key = intern_string(labels->labels[i].key);
    ilabels.labels[i].value = intern_string(labels->labels[i].value);
    ilabels.count++;
  }
  ilabels.hash = hash_label_set(&ilabels);

  // Search existing (lock-free read)
  size_t count = atomic_load(&g_metrics.gauge_count);
  for (size_t i = 0; i < count; i++) {
    valk_gauge_v2_t *g = &g_metrics.gauges[i];
    if (g->name == iname && labels_equal(&g->labels, &ilabels)) {
      return g;  // Found existing
    }
  }

  // Create new (CAS to append)
  size_t idx = atomic_fetch_add(&g_metrics.gauge_count, 1);
  if (idx >= VALK_REGISTRY_MAX_GAUGES) {
    atomic_fetch_sub(&g_metrics.gauge_count, 1);
    return NULL;  // Registry full
  }

  valk_gauge_v2_t *g = &g_metrics.gauges[idx];
  g->name = iname;
  g->help = intern_string(help);
  g->labels = ilabels;
  atomic_store(&g->value, 0);
  atomic_store(&g->last_value, 0);
  atomic_store(&g->last_timestamp, 0);

  return g;
}

// ============================================================================
// HISTOGRAM OPERATIONS
// ============================================================================

valk_histogram_v2_t *valk_histogram_get_or_create(
    const char *name,
    const char *help,
    const double *bounds,
    size_t bound_count,
    const valk_label_set_v2_t *labels) {

  const char *iname = intern_string(name);
  valk_label_set_v2_t ilabels = {0};

  for (uint8_t i = 0; i < labels->count && i < VALK_MAX_LABELS_V2; i++) {
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
  h->last_timestamp = 0;

  return h;
}
