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

static u64 get_timestamp_us(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000000ULL + ts.tv_nsec / 1000;
}

// Public API for timestamp (used by inline functions in header)
u64 valk_metrics_now_us(void) {
  return get_timestamp_us();
}

// ============================================================================
// STRING INTERNING
// ============================================================================

static const char *intern_string(const char *str) {
  if (!str) return nullptr;

  valk_mutex_lock(&g_metrics.pool_lock);

  for (u64 i = 0; i < g_metrics.string_pool_count; i++) {
    if (strcmp(g_metrics.string_pool[i], str) == 0) {
      valk_mutex_unlock(&g_metrics.pool_lock);
      return g_metrics.string_pool[i];
    }
  }

  if (g_metrics.string_pool_count >= 4096) {
    valk_mutex_unlock(&g_metrics.pool_lock);
    return strdup(str);
  }

  char *copy = strdup(str);
  g_metrics.string_pool[g_metrics.string_pool_count++] = copy;

  valk_mutex_unlock(&g_metrics.pool_lock);
  return copy;
}

// ============================================================================
// LABEL SET HASHING
// ============================================================================

static u32 hash_label_set(const valk_label_set_v2_t *labels) {
  u32 hash = 5381;
  for (u8 i = 0; i < labels->count; i++) {
    // Hash key pointer (interned)
    hash = ((hash << 5) + hash) ^ (u32)(uptr)labels->labels[i].key;
    // Hash value pointer (interned)
    hash = ((hash << 5) + hash) ^ (u32)(uptr)labels->labels[i].value;
  }
  return hash;
}

static bool labels_equal(const valk_label_set_v2_t *a, const valk_label_set_v2_t *b) {
  if (a->hash != b->hash) return false;
  if (a->count != b->count) return false;
  for (u8 i = 0; i < a->count; i++) {
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
  valk_mutex_init(&g_metrics.pool_lock);

  g_metrics.snapshot_interval_us = 1000000;
  g_metrics.start_time_us = get_timestamp_us();
  g_metrics.last_snapshot_time = g_metrics.start_time_us;
  g_metrics.eviction_threshold_us = VALK_EVICTION_THRESHOLD_US;

  atomic_store(&g_metrics.counter_free.head, VALK_INVALID_SLOT);
  atomic_store(&g_metrics.gauge_free.head, VALK_INVALID_SLOT);
  atomic_store(&g_metrics.histogram_free.head, VALK_INVALID_SLOT);
  atomic_store(&g_metrics.summary_free.head, VALK_INVALID_SLOT);
}

void valk_metrics_registry_destroy(void) {
  valk_mutex_destroy(&g_metrics.pool_lock);

  // Free interned strings
  for (u64 i = 0; i < g_metrics.string_pool_count; i++) {
    free((void*)g_metrics.string_pool[i]);
  }

  memset(&g_metrics, 0, sizeof(g_metrics));
}

// ============================================================================
// FREE LIST HELPERS
// ============================================================================

// Pop a slot from free list (returns VALK_INVALID_SLOT if empty)
static u32 free_list_pop(valk_free_list_t *fl, u32 *next_free) {
  u32 head = atomic_load(&fl->head);
  while (head != VALK_INVALID_SLOT) {
    u32 next = next_free[head];
    if (atomic_compare_exchange_weak(&fl->head, &head, next)) {
      return head;
    }
    // CAS failed, head was updated - loop will retry with new head
  }
  return VALK_INVALID_SLOT;
}

// Push a slot onto free list
static void free_list_push(valk_free_list_t *fl, u32 *next_free, u32 slot) {
  u32 head = atomic_load(&fl->head);
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
  for (u8 i = 0; i < labels->count && i < VALK_MAX_LABELS_V2; i++) {
    ilabels.labels[i].key = intern_string(labels->labels[i].key);
    ilabels.labels[i].value = intern_string(labels->labels[i].value);
    ilabels.count++;
  }
  ilabels.hash = hash_label_set(&ilabels);

  // Search existing active slots (lock-free read)
  u64 count = atomic_load(&g_metrics.counter_count);
  for (u64 i = 0; i < count; i++) {
    valk_counter_v2_t *c = &g_metrics.counters[i];
    if (atomic_load(&c->active) && c->name == iname && labels_equal(&c->labels, &ilabels)) {
      return c;  // Found existing
    }
  }

  // Try to get a slot from free list first
  u32 idx = free_list_pop(&g_metrics.counter_free, g_metrics.counter_next_free);
  if (idx == VALK_INVALID_SLOT) {
    // No free slots, allocate new
    idx = atomic_fetch_add(&g_metrics.counter_count, 1);
    if (idx >= VALK_REGISTRY_MAX_COUNTERS) {
      atomic_fetch_sub(&g_metrics.counter_count, 1);
      // Try eviction and retry once
      if (valk_metrics_evict_stale() > 0) {
        idx = free_list_pop(&g_metrics.counter_free, g_metrics.counter_next_free);
        if (idx == VALK_INVALID_SLOT) {
          return nullptr;  // Still no space
        }
      } else {
        return nullptr;  // Registry full
      }
    }
  }

  valk_counter_v2_t *c = &g_metrics.counters[idx];
  u64 now = get_timestamp_us();

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
  for (u8 i = 0; i < labels->count && i < VALK_MAX_LABELS_V2; i++) {
    ilabels.labels[i].key = intern_string(labels->labels[i].key);
    ilabels.labels[i].value = intern_string(labels->labels[i].value);
    ilabels.count++;
  }
  ilabels.hash = hash_label_set(&ilabels);

  // Search existing active slots (lock-free read)
  u64 count = atomic_load(&g_metrics.gauge_count);
  for (u64 i = 0; i < count; i++) {
    valk_gauge_v2_t *g = &g_metrics.gauges[i];
    if (atomic_load(&g->active) && g->name == iname && labels_equal(&g->labels, &ilabels)) {
      return g;  // Found existing
    }
  }

  // Try to get a slot from free list first
  u32 idx = free_list_pop(&g_metrics.gauge_free, g_metrics.gauge_next_free);
  if (idx == VALK_INVALID_SLOT) {
    // No free slots, allocate new
    idx = atomic_fetch_add(&g_metrics.gauge_count, 1);
    if (idx >= VALK_REGISTRY_MAX_GAUGES) {
      atomic_fetch_sub(&g_metrics.gauge_count, 1);
      // Try eviction and retry once
      if (valk_metrics_evict_stale() > 0) {
        idx = free_list_pop(&g_metrics.gauge_free, g_metrics.gauge_next_free);
        if (idx == VALK_INVALID_SLOT) {
          return nullptr;  // Still no space
        }
      } else {
        return nullptr;  // Registry full
      }
    }
  }

  valk_gauge_v2_t *g = &g_metrics.gauges[idx];
  u64 now = get_timestamp_us();

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
    u64 bound_count,
    const valk_label_set_v2_t *labels) {

  const char *iname = intern_string(name);
  valk_label_set_v2_t ilabels = {0};

  for (u8 i = 0; i < labels->count && i < VALK_MAX_LABELS_V2; i++) {
    ilabels.labels[i].key = intern_string(labels->labels[i].key);
    ilabels.labels[i].value = intern_string(labels->labels[i].value);
    ilabels.count++;
  }
  ilabels.hash = hash_label_set(&ilabels);

  // Search existing active slots
  u64 count = atomic_load(&g_metrics.histogram_count);
  for (u64 i = 0; i < count; i++) {
    valk_histogram_v2_t *h = &g_metrics.histograms[i];
    if (atomic_load(&h->active) && h->name == iname && labels_equal(&h->labels, &ilabels)) {
      return h;
    }
  }

  // Try to get a slot from free list first
  u32 idx = free_list_pop(&g_metrics.histogram_free, g_metrics.histogram_next_free);
  if (idx == VALK_INVALID_SLOT) {
    // No free slots, allocate new
    idx = atomic_fetch_add(&g_metrics.histogram_count, 1);
    if (idx >= VALK_REGISTRY_MAX_HISTOGRAMS) {
      atomic_fetch_sub(&g_metrics.histogram_count, 1);
      // Try eviction and retry once
      if (valk_metrics_evict_stale() > 0) {
        idx = free_list_pop(&g_metrics.histogram_free, g_metrics.histogram_next_free);
        if (idx == VALK_INVALID_SLOT) {
          return nullptr;  // Still no space
        }
      } else {
        return nullptr;  // Registry full
      }
    }
  }

  valk_histogram_v2_t *h = &g_metrics.histograms[idx];
  u64 now = get_timestamp_us();

  h->name = iname;
  h->help = intern_string(help);
  h->labels = ilabels;

  // Set bucket bounds
  h->bucket_count = bound_count > VALK_MAX_BUCKETS ? VALK_MAX_BUCKETS : bound_count;
  memcpy(h->bucket_bounds, bounds, h->bucket_count * sizeof(double));

  // Initialize atomic counters
  for (u64 i = 0; i <= h->bucket_count; i++) {
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
u64 valk_metrics_evict_stale(void) {
  u64 now = get_timestamp_us();
  u64 threshold = g_metrics.eviction_threshold_us;
  u64 evicted = 0;
  u64 counters_evicted = 0;
  u64 gauges_evicted = 0;
  u64 histograms_evicted = 0;
  u64 summaries_evicted = 0;

  // Evict stale counters
  u64 counter_count = atomic_load(&g_metrics.counter_count);
  for (u64 i = 0; i < counter_count; i++) {
    valk_counter_v2_t *c = &g_metrics.counters[i];
    if (!atomic_load(&c->active)) continue;
    if (!c->evictable) continue;

    u64 last_updated = atomic_load(&c->last_updated_us);
    if (now - last_updated > threshold) {
      // Mark as inactive and push to free list
      atomic_store(&c->active, false);
      free_list_push(&g_metrics.counter_free, g_metrics.counter_next_free, i);
      counters_evicted++;
    }
  }

  // Evict stale gauges
  u64 gauge_count = atomic_load(&g_metrics.gauge_count);
  for (u64 i = 0; i < gauge_count; i++) {
    valk_gauge_v2_t *g = &g_metrics.gauges[i];
    if (!atomic_load(&g->active)) continue;
    if (!g->evictable) continue;

    u64 last_updated = atomic_load(&g->last_updated_us);
    if (now - last_updated > threshold) {
      atomic_store(&g->active, false);
      free_list_push(&g_metrics.gauge_free, g_metrics.gauge_next_free, i);
      gauges_evicted++;
    }
  }

  // Evict stale histograms
  u64 histogram_count = atomic_load(&g_metrics.histogram_count);
  for (u64 i = 0; i < histogram_count; i++) {
    valk_histogram_v2_t *h = &g_metrics.histograms[i];
    if (!atomic_load(&h->active)) continue;
    if (!h->evictable) continue;

    u64 last_updated = atomic_load(&h->last_updated_us);
    if (now - last_updated > threshold) {
      atomic_store(&h->active, false);
      free_list_push(&g_metrics.histogram_free, g_metrics.histogram_next_free, i);
      histograms_evicted++;
    }
  }

  // Evict stale summaries
  u64 summary_count = atomic_load(&g_metrics.summary_count);
  for (u64 i = 0; i < summary_count; i++) {
    valk_summary_v2_t *s = &g_metrics.summaries[i];
    if (!atomic_load(&s->active)) continue;
    if (!s->evictable) continue;

    u64 last_updated = atomic_load(&s->last_updated_us);
    if (now - last_updated > threshold) {
      atomic_store(&s->active, false);
      free_list_push(&g_metrics.summary_free, g_metrics.summary_next_free, i);
      summaries_evicted++;
    }
  }

  // Update eviction tracking counters
  evicted = counters_evicted + gauges_evicted + histograms_evicted + summaries_evicted;
  if (evicted > 0) {
    atomic_fetch_add(&g_metrics.evictions_total, evicted);
    if (counters_evicted > 0)
      atomic_fetch_add(&g_metrics.evictions_counters, counters_evicted);
    if (gauges_evicted > 0)
      atomic_fetch_add(&g_metrics.evictions_gauges, gauges_evicted);
    if (histograms_evicted > 0)
      atomic_fetch_add(&g_metrics.evictions_histograms, histograms_evicted);
    if (summaries_evicted > 0)
      atomic_fetch_add(&g_metrics.evictions_summaries, summaries_evicted);
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
  u32 slot = (u32)(c - g_metrics.counters);
  if (slot >= VALK_REGISTRY_MAX_COUNTERS) return VALK_HANDLE_INVALID;
  return (valk_metric_handle_t){slot, atomic_load(&c->generation)};
}

valk_metric_handle_t valk_gauge_handle(valk_gauge_v2_t *g) {
  if (!g) return VALK_HANDLE_INVALID;
  u32 slot = (u32)(g - g_metrics.gauges);
  if (slot >= VALK_REGISTRY_MAX_GAUGES) return VALK_HANDLE_INVALID;
  return (valk_metric_handle_t){slot, atomic_load(&g->generation)};
}

valk_metric_handle_t valk_histogram_handle(valk_histogram_v2_t *h) {
  if (!h) return VALK_HANDLE_INVALID;
  u32 slot = (u32)(h - g_metrics.histograms);
  if (slot >= VALK_REGISTRY_MAX_HISTOGRAMS) return VALK_HANDLE_INVALID;
  return (valk_metric_handle_t){slot, atomic_load(&h->generation)};
}

valk_metric_handle_t valk_summary_handle(valk_summary_v2_t *s) {
  if (!s) return VALK_HANDLE_INVALID;
  u32 slot = (u32)(s - g_metrics.summaries);
  if (slot >= VALK_REGISTRY_MAX_SUMMARIES) return VALK_HANDLE_INVALID;
  return (valk_metric_handle_t){slot, atomic_load(&s->generation)};
}

valk_counter_v2_t *valk_counter_deref(valk_metric_handle_t h) {
  if (h.slot == VALK_INVALID_SLOT || h.slot >= VALK_REGISTRY_MAX_COUNTERS) return nullptr;
  valk_counter_v2_t *c = &g_metrics.counters[h.slot];
  if (!atomic_load(&c->active)) return nullptr;
  if (atomic_load(&c->generation) != h.generation) return nullptr;
  return c;
}

valk_gauge_v2_t *valk_gauge_deref(valk_metric_handle_t h) {
  if (h.slot == VALK_INVALID_SLOT || h.slot >= VALK_REGISTRY_MAX_GAUGES) return nullptr;
  valk_gauge_v2_t *g = &g_metrics.gauges[h.slot];
  if (!atomic_load(&g->active)) return nullptr;
  if (atomic_load(&g->generation) != h.generation) return nullptr;
  return g;
}

valk_histogram_v2_t *valk_histogram_deref(valk_metric_handle_t h) {
  if (h.slot == VALK_INVALID_SLOT || h.slot >= VALK_REGISTRY_MAX_HISTOGRAMS) return nullptr;
  valk_histogram_v2_t *histo = &g_metrics.histograms[h.slot];
  if (!atomic_load(&histo->active)) return nullptr;
  if (atomic_load(&histo->generation) != h.generation) return nullptr;
  return histo;
}

valk_summary_v2_t *valk_summary_deref(valk_metric_handle_t h) {
  if (h.slot == VALK_INVALID_SLOT || h.slot >= VALK_REGISTRY_MAX_SUMMARIES) return nullptr;
  valk_summary_v2_t *s = &g_metrics.summaries[h.slot];
  if (!atomic_load(&s->active)) return nullptr;
  if (atomic_load(&s->generation) != h.generation) return nullptr;
  return s;
}

// ============================================================================
// REGISTRY STATS (Meta-metrics)
// ============================================================================

// Helper: count free list depth
static u64 count_free_list(valk_free_list_t *fl, u32 *next_free, u64 max_slots) {
  u64 count = 0;
  u32 idx = atomic_load(&fl->head);
  while (idx != VALK_INVALID_SLOT && count < max_slots) {
    count++;
    idx = next_free[idx];
  }
  return count;
}

void valk_registry_stats_collect(valk_registry_stats_t *stats) {
  if (!stats) return;

  u64 start = get_timestamp_us();
  memset(stats, 0, sizeof(*stats));

  // High water marks (slots ever allocated)
  stats->counters_hwm = atomic_load(&g_metrics.counter_count);
  stats->gauges_hwm = atomic_load(&g_metrics.gauge_count);
  stats->histograms_hwm = atomic_load(&g_metrics.histogram_count);
  stats->summaries_hwm = atomic_load(&g_metrics.summary_count);

  // Count active metrics (iterate through HWM, check active flag)
  for (u64 i = 0; i < stats->counters_hwm; i++) {
    if (atomic_load(&g_metrics.counters[i].active)) {
      stats->counters_active++;
    }
  }
  for (u64 i = 0; i < stats->gauges_hwm; i++) {
    if (atomic_load(&g_metrics.gauges[i].active)) {
      stats->gauges_active++;
    }
  }
  for (u64 i = 0; i < stats->histograms_hwm; i++) {
    if (atomic_load(&g_metrics.histograms[i].active)) {
      stats->histograms_active++;
    }
  }
  for (u64 i = 0; i < stats->summaries_hwm; i++) {
    if (atomic_load(&g_metrics.summaries[i].active)) {
      stats->summaries_active++;
    }
  }

  // Capacities
  stats->counters_capacity = VALK_REGISTRY_MAX_COUNTERS;
  stats->gauges_capacity = VALK_REGISTRY_MAX_GAUGES;
  stats->histograms_capacity = VALK_REGISTRY_MAX_HISTOGRAMS;
  stats->summaries_capacity = VALK_REGISTRY_MAX_SUMMARIES;

  // String pool usage
  stats->string_pool_used = g_metrics.string_pool_count;
  stats->string_pool_capacity = 4096;

  // Eviction stats
  stats->evictions_total = atomic_load(&g_metrics.evictions_total);
  stats->evictions_counters = atomic_load(&g_metrics.evictions_counters);
  stats->evictions_gauges = atomic_load(&g_metrics.evictions_gauges);
  stats->evictions_histograms = atomic_load(&g_metrics.evictions_histograms);
  stats->evictions_summaries = atomic_load(&g_metrics.evictions_summaries);

  // Free list depths
  stats->counters_free = count_free_list(&g_metrics.counter_free,
                                          g_metrics.counter_next_free,
                                          VALK_REGISTRY_MAX_COUNTERS);
  stats->gauges_free = count_free_list(&g_metrics.gauge_free,
                                        g_metrics.gauge_next_free,
                                        VALK_REGISTRY_MAX_GAUGES);
  stats->histograms_free = count_free_list(&g_metrics.histogram_free,
                                            g_metrics.histogram_next_free,
                                            VALK_REGISTRY_MAX_HISTOGRAMS);
  stats->summaries_free = count_free_list(&g_metrics.summary_free,
                                           g_metrics.summary_next_free,
                                           VALK_REGISTRY_MAX_SUMMARIES);

  // Timing
  u64 end = get_timestamp_us();
  stats->last_collect_time_us = end;
  stats->collect_duration_us = end - start;
}

u64 valk_registry_stats_to_json(const valk_registry_stats_t *stats,
                                    char *buf, u64 buf_size) {
  if (!stats || !buf || buf_size == 0) return 0;

  int n = snprintf(buf, buf_size,
    "{"
    "\"counters\":{\"active\":%llu,\"hwm\":%llu,\"capacity\":%llu,\"free\":%llu},"
    "\"gauges\":{\"active\":%llu,\"hwm\":%llu,\"capacity\":%llu,\"free\":%llu},"
    "\"histograms\":{\"active\":%llu,\"hwm\":%llu,\"capacity\":%llu,\"free\":%llu},"
    "\"summaries\":{\"active\":%llu,\"hwm\":%llu,\"capacity\":%llu,\"free\":%llu},"
    "\"string_pool\":{\"used\":%llu,\"capacity\":%llu},"
    "\"evictions\":{\"total\":%llu,\"counters\":%llu,\"gauges\":%llu,\"histograms\":%llu,\"summaries\":%llu},"
    "\"collect_time_us\":%llu"
    "}",
    (unsigned long long)stats->counters_active, (unsigned long long)stats->counters_hwm, (unsigned long long)stats->counters_capacity, (unsigned long long)stats->counters_free,
    (unsigned long long)stats->gauges_active, (unsigned long long)stats->gauges_hwm, (unsigned long long)stats->gauges_capacity, (unsigned long long)stats->gauges_free,
    (unsigned long long)stats->histograms_active, (unsigned long long)stats->histograms_hwm, (unsigned long long)stats->histograms_capacity, (unsigned long long)stats->histograms_free,
    (unsigned long long)stats->summaries_active, (unsigned long long)stats->summaries_hwm, (unsigned long long)stats->summaries_capacity, (unsigned long long)stats->summaries_free,
    (unsigned long long)stats->string_pool_used, (unsigned long long)stats->string_pool_capacity,
    (unsigned long long)stats->evictions_total, (unsigned long long)stats->evictions_counters, (unsigned long long)stats->evictions_gauges,
    (unsigned long long)stats->evictions_histograms, (unsigned long long)stats->evictions_summaries,
    (unsigned long long)stats->collect_duration_us
  );

  if (n < 0 || (u64)n >= buf_size) {
    return 0;
  }
  return (u64)n;
}
