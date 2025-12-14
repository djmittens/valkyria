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

// Public API for timestamp (used by inline functions in header)
uint64_t valk_metrics_now_us(void) {
  return get_timestamp_us();
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
  g_metrics.eviction_threshold_us = VALK_EVICTION_THRESHOLD_US;

  // Initialize free list heads to empty
  atomic_store(&g_metrics.counter_free.head, VALK_INVALID_SLOT);
  atomic_store(&g_metrics.gauge_free.head, VALK_INVALID_SLOT);
  atomic_store(&g_metrics.histogram_free.head, VALK_INVALID_SLOT);
  atomic_store(&g_metrics.summary_free.head, VALK_INVALID_SLOT);
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
// FREE LIST HELPERS
// ============================================================================

// Pop a slot from free list (returns VALK_INVALID_SLOT if empty)
static uint32_t free_list_pop(valk_free_list_t *fl, uint32_t *next_free) {
  uint32_t head = atomic_load(&fl->head);
  while (head != VALK_INVALID_SLOT) {
    uint32_t next = next_free[head];
    if (atomic_compare_exchange_weak(&fl->head, &head, next)) {
      return head;
    }
    // CAS failed, head was updated - loop will retry with new head
  }
  return VALK_INVALID_SLOT;
}

// Push a slot onto free list
static void free_list_push(valk_free_list_t *fl, uint32_t *next_free, uint32_t slot) {
  uint32_t head = atomic_load(&fl->head);
  do {
    next_free[slot] = head;
  } while (!atomic_compare_exchange_weak(&fl->head, &head, slot));
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

  // Search existing active slots (lock-free read)
  size_t count = atomic_load(&g_metrics.counter_count);
  for (size_t i = 0; i < count; i++) {
    valk_counter_v2_t *c = &g_metrics.counters[i];
    if (atomic_load(&c->active) && c->name == iname && labels_equal(&c->labels, &ilabels)) {
      return c;  // Found existing
    }
  }

  // Try to get a slot from free list first
  uint32_t idx = free_list_pop(&g_metrics.counter_free, g_metrics.counter_next_free);
  if (idx == VALK_INVALID_SLOT) {
    // No free slots, allocate new
    idx = atomic_fetch_add(&g_metrics.counter_count, 1);
    if (idx >= VALK_REGISTRY_MAX_COUNTERS) {
      atomic_fetch_sub(&g_metrics.counter_count, 1);
      // Try eviction and retry once
      if (valk_metrics_evict_stale() > 0) {
        idx = free_list_pop(&g_metrics.counter_free, g_metrics.counter_next_free);
        if (idx == VALK_INVALID_SLOT) {
          return NULL;  // Still no space
        }
      } else {
        return NULL;  // Registry full
      }
    }
  }

  valk_counter_v2_t *c = &g_metrics.counters[idx];
  uint64_t now = get_timestamp_us();

  c->name = iname;
  c->help = intern_string(help);
  c->labels = ilabels;
  atomic_store(&c->value, 0);
  atomic_store(&c->last_value, 0);
  atomic_store(&c->last_timestamp, 0);
  atomic_store(&c->last_updated_us, now);
  atomic_fetch_add(&c->generation, 1);  // Increment generation on reuse
  c->evictable = true;  // Default to evictable
  atomic_store(&c->active, true);

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

  // Search existing active slots (lock-free read)
  size_t count = atomic_load(&g_metrics.gauge_count);
  for (size_t i = 0; i < count; i++) {
    valk_gauge_v2_t *g = &g_metrics.gauges[i];
    if (atomic_load(&g->active) && g->name == iname && labels_equal(&g->labels, &ilabels)) {
      return g;  // Found existing
    }
  }

  // Try to get a slot from free list first
  uint32_t idx = free_list_pop(&g_metrics.gauge_free, g_metrics.gauge_next_free);
  if (idx == VALK_INVALID_SLOT) {
    // No free slots, allocate new
    idx = atomic_fetch_add(&g_metrics.gauge_count, 1);
    if (idx >= VALK_REGISTRY_MAX_GAUGES) {
      atomic_fetch_sub(&g_metrics.gauge_count, 1);
      // Try eviction and retry once
      if (valk_metrics_evict_stale() > 0) {
        idx = free_list_pop(&g_metrics.gauge_free, g_metrics.gauge_next_free);
        if (idx == VALK_INVALID_SLOT) {
          return NULL;  // Still no space
        }
      } else {
        return NULL;  // Registry full
      }
    }
  }

  valk_gauge_v2_t *g = &g_metrics.gauges[idx];
  uint64_t now = get_timestamp_us();

  g->name = iname;
  g->help = intern_string(help);
  g->labels = ilabels;
  atomic_store(&g->value, 0);
  atomic_store(&g->last_value, 0);
  atomic_store(&g->last_timestamp, 0);
  atomic_store(&g->last_updated_us, now);
  atomic_fetch_add(&g->generation, 1);  // Increment generation on reuse
  g->evictable = true;  // Default to evictable
  atomic_store(&g->active, true);

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

  // Search existing active slots
  size_t count = atomic_load(&g_metrics.histogram_count);
  for (size_t i = 0; i < count; i++) {
    valk_histogram_v2_t *h = &g_metrics.histograms[i];
    if (atomic_load(&h->active) && h->name == iname && labels_equal(&h->labels, &ilabels)) {
      return h;
    }
  }

  // Try to get a slot from free list first
  uint32_t idx = free_list_pop(&g_metrics.histogram_free, g_metrics.histogram_next_free);
  if (idx == VALK_INVALID_SLOT) {
    // No free slots, allocate new
    idx = atomic_fetch_add(&g_metrics.histogram_count, 1);
    if (idx >= VALK_REGISTRY_MAX_HISTOGRAMS) {
      atomic_fetch_sub(&g_metrics.histogram_count, 1);
      // Try eviction and retry once
      if (valk_metrics_evict_stale() > 0) {
        idx = free_list_pop(&g_metrics.histogram_free, g_metrics.histogram_next_free);
        if (idx == VALK_INVALID_SLOT) {
          return NULL;  // Still no space
        }
      } else {
        return NULL;  // Registry full
      }
    }
  }

  valk_histogram_v2_t *h = &g_metrics.histograms[idx];
  uint64_t now = get_timestamp_us();

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

  // LRU fields
  atomic_store(&h->last_updated_us, now);
  atomic_fetch_add(&h->generation, 1);  // Increment generation on reuse
  h->evictable = true;  // Default to evictable
  atomic_store(&h->active, true);

  return h;
}

// ============================================================================
// EVICTION
// ============================================================================

// Evict stale metrics (called when registry is under pressure)
// Returns number of metrics evicted
size_t valk_metrics_evict_stale(void) {
  uint64_t now = get_timestamp_us();
  uint64_t threshold = g_metrics.eviction_threshold_us;
  size_t evicted = 0;

  // Evict stale counters
  size_t counter_count = atomic_load(&g_metrics.counter_count);
  for (size_t i = 0; i < counter_count; i++) {
    valk_counter_v2_t *c = &g_metrics.counters[i];
    if (!atomic_load(&c->active)) continue;
    if (!c->evictable) continue;

    uint64_t last_updated = atomic_load(&c->last_updated_us);
    if (now - last_updated > threshold) {
      // Mark as inactive and push to free list
      atomic_store(&c->active, false);
      free_list_push(&g_metrics.counter_free, g_metrics.counter_next_free, i);
      evicted++;
    }
  }

  // Evict stale gauges
  size_t gauge_count = atomic_load(&g_metrics.gauge_count);
  for (size_t i = 0; i < gauge_count; i++) {
    valk_gauge_v2_t *g = &g_metrics.gauges[i];
    if (!atomic_load(&g->active)) continue;
    if (!g->evictable) continue;

    uint64_t last_updated = atomic_load(&g->last_updated_us);
    if (now - last_updated > threshold) {
      atomic_store(&g->active, false);
      free_list_push(&g_metrics.gauge_free, g_metrics.gauge_next_free, i);
      evicted++;
    }
  }

  // Evict stale histograms
  size_t histogram_count = atomic_load(&g_metrics.histogram_count);
  for (size_t i = 0; i < histogram_count; i++) {
    valk_histogram_v2_t *h = &g_metrics.histograms[i];
    if (!atomic_load(&h->active)) continue;
    if (!h->evictable) continue;

    uint64_t last_updated = atomic_load(&h->last_updated_us);
    if (now - last_updated > threshold) {
      atomic_store(&h->active, false);
      free_list_push(&g_metrics.histogram_free, g_metrics.histogram_next_free, i);
      evicted++;
    }
  }

  // Evict stale summaries
  size_t summary_count = atomic_load(&g_metrics.summary_count);
  for (size_t i = 0; i < summary_count; i++) {
    valk_summary_v2_t *s = &g_metrics.summaries[i];
    if (!atomic_load(&s->active)) continue;
    if (!s->evictable) continue;

    uint64_t last_updated = atomic_load(&s->last_updated_us);
    if (now - last_updated > threshold) {
      atomic_store(&s->active, false);
      free_list_push(&g_metrics.summary_free, g_metrics.summary_next_free, i);
      evicted++;
    }
  }

  return evicted;
}

// ============================================================================
// PERSISTENCE API
// ============================================================================

void valk_counter_set_persistent(valk_counter_v2_t *c) {
  if (c) c->evictable = false;
}

void valk_gauge_set_persistent(valk_gauge_v2_t *g) {
  if (g) g->evictable = false;
}

void valk_histogram_set_persistent(valk_histogram_v2_t *h) {
  if (h) h->evictable = false;
}

void valk_summary_set_persistent(valk_summary_v2_t *s) {
  if (s) s->evictable = false;
}

// ============================================================================
// HANDLE API - Safe dereference for evictable metrics
// ============================================================================

valk_metric_handle_t valk_counter_handle(valk_counter_v2_t *c) {
  if (!c) return VALK_HANDLE_INVALID;
  uint32_t slot = (uint32_t)(c - g_metrics.counters);
  if (slot >= VALK_REGISTRY_MAX_COUNTERS) return VALK_HANDLE_INVALID;
  return (valk_metric_handle_t){slot, atomic_load(&c->generation)};
}

valk_metric_handle_t valk_gauge_handle(valk_gauge_v2_t *g) {
  if (!g) return VALK_HANDLE_INVALID;
  uint32_t slot = (uint32_t)(g - g_metrics.gauges);
  if (slot >= VALK_REGISTRY_MAX_GAUGES) return VALK_HANDLE_INVALID;
  return (valk_metric_handle_t){slot, atomic_load(&g->generation)};
}

valk_metric_handle_t valk_histogram_handle(valk_histogram_v2_t *h) {
  if (!h) return VALK_HANDLE_INVALID;
  uint32_t slot = (uint32_t)(h - g_metrics.histograms);
  if (slot >= VALK_REGISTRY_MAX_HISTOGRAMS) return VALK_HANDLE_INVALID;
  return (valk_metric_handle_t){slot, atomic_load(&h->generation)};
}

valk_metric_handle_t valk_summary_handle(valk_summary_v2_t *s) {
  if (!s) return VALK_HANDLE_INVALID;
  uint32_t slot = (uint32_t)(s - g_metrics.summaries);
  if (slot >= VALK_REGISTRY_MAX_SUMMARIES) return VALK_HANDLE_INVALID;
  return (valk_metric_handle_t){slot, atomic_load(&s->generation)};
}

valk_counter_v2_t *valk_counter_deref(valk_metric_handle_t h) {
  if (h.slot == VALK_INVALID_SLOT || h.slot >= VALK_REGISTRY_MAX_COUNTERS) return NULL;
  valk_counter_v2_t *c = &g_metrics.counters[h.slot];
  if (!atomic_load(&c->active)) return NULL;
  if (atomic_load(&c->generation) != h.generation) return NULL;
  return c;
}

valk_gauge_v2_t *valk_gauge_deref(valk_metric_handle_t h) {
  if (h.slot == VALK_INVALID_SLOT || h.slot >= VALK_REGISTRY_MAX_GAUGES) return NULL;
  valk_gauge_v2_t *g = &g_metrics.gauges[h.slot];
  if (!atomic_load(&g->active)) return NULL;
  if (atomic_load(&g->generation) != h.generation) return NULL;
  return g;
}

valk_histogram_v2_t *valk_histogram_deref(valk_metric_handle_t h) {
  if (h.slot == VALK_INVALID_SLOT || h.slot >= VALK_REGISTRY_MAX_HISTOGRAMS) return NULL;
  valk_histogram_v2_t *histo = &g_metrics.histograms[h.slot];
  if (!atomic_load(&histo->active)) return NULL;
  if (atomic_load(&histo->generation) != h.generation) return NULL;
  return histo;
}

valk_summary_v2_t *valk_summary_deref(valk_metric_handle_t h) {
  if (h.slot == VALK_INVALID_SLOT || h.slot >= VALK_REGISTRY_MAX_SUMMARIES) return NULL;
  valk_summary_v2_t *s = &g_metrics.summaries[h.slot];
  if (!atomic_load(&s->active)) return NULL;
  if (atomic_load(&s->generation) != h.generation) return NULL;
  return s;
}
