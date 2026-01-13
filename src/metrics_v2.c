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

static u32 free_list_pop(valk_free_list_t *fl, u32 *next_free) {
  u32 head = atomic_load(&fl->head);
  while (head != VALK_INVALID_SLOT) {
    u32 next = next_free[head];
    if (atomic_compare_exchange_weak(&fl->head, &head, next)) {
      return head;
    }
  }
  return VALK_INVALID_SLOT;
}

static void free_list_push(valk_free_list_t *fl, u32 *next_free, u32 slot) {
  u32 head = atomic_load(&fl->head);
  do {
    next_free[slot] = head;
  } while (!atomic_compare_exchange_weak(&fl->head, &head, slot));
}

// ============================================================================
// SHARED METRIC HELPERS
// ============================================================================

static valk_label_set_v2_t intern_labels(const valk_label_set_v2_t *labels) {
  valk_label_set_v2_t ilabels = {0};
  for (u8 i = 0; i < labels->count && i < VALK_MAX_LABELS_V2; i++) {
    ilabels.labels[i].key = intern_string(labels->labels[i].key);
    ilabels.labels[i].value = intern_string(labels->labels[i].value);
    ilabels.count++;
  }
  ilabels.hash = hash_label_set(&ilabels);
  return ilabels;
}

static u32 allocate_metric_slot(valk_free_list_t *fl, u32 *next_free,
                                 _Atomic u64 *count, u64 max_slots) {
  u32 idx = free_list_pop(fl, next_free);
  if (idx != VALK_INVALID_SLOT) return idx;

  idx = atomic_fetch_add(count, 1);
  if (idx < max_slots) return idx;

  atomic_fetch_sub(count, 1);
  if (valk_metrics_evict_stale() == 0) return VALK_INVALID_SLOT;

  return free_list_pop(fl, next_free);
}

// ============================================================================
// COUNTER OPERATIONS
// ============================================================================

valk_counter_v2_t *valk_counter_get_or_create(const char *name,
                                               const char *help,
                                               const valk_label_set_v2_t *labels) {
  const char *iname = intern_string(name);
  valk_label_set_v2_t ilabels = intern_labels(labels);

  u64 count = atomic_load(&g_metrics.counter_count);
  for (u64 i = 0; i < count; i++) {
    valk_counter_v2_t *c = &g_metrics.counters[i];
    if (atomic_load(&c->active) && c->name == iname && labels_equal(&c->labels, &ilabels)) {
      return c;
    }
  }

  u32 idx = allocate_metric_slot(&g_metrics.counter_free, g_metrics.counter_next_free,
                                  &g_metrics.counter_count, VALK_REGISTRY_MAX_COUNTERS);
  if (idx == VALK_INVALID_SLOT) return nullptr;

  valk_counter_v2_t *c = &g_metrics.counters[idx];
  u64 now = get_timestamp_us();

  c->name = iname;
  c->help = intern_string(help);
  c->labels = ilabels;
  atomic_store(&c->value, 0);
  atomic_store(&c->last_value, 0);
  atomic_store(&c->last_timestamp, 0);
  atomic_store(&c->last_updated_us, now);
  atomic_fetch_add(&c->generation, 1);
  c->evictable = true;
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
  valk_label_set_v2_t ilabels = intern_labels(labels);

  u64 count = atomic_load(&g_metrics.gauge_count);
  for (u64 i = 0; i < count; i++) {
    valk_gauge_v2_t *g = &g_metrics.gauges[i];
    if (atomic_load(&g->active) && g->name == iname && labels_equal(&g->labels, &ilabels)) {
      return g;
    }
  }

  u32 idx = allocate_metric_slot(&g_metrics.gauge_free, g_metrics.gauge_next_free,
                                  &g_metrics.gauge_count, VALK_REGISTRY_MAX_GAUGES);
  if (idx == VALK_INVALID_SLOT) return nullptr;

  valk_gauge_v2_t *g = &g_metrics.gauges[idx];
  u64 now = get_timestamp_us();

  g->name = iname;
  g->help = intern_string(help);
  g->labels = ilabels;
  atomic_store(&g->value, 0);
  atomic_store(&g->last_value, 0);
  atomic_store(&g->last_timestamp, 0);
  atomic_store(&g->last_updated_us, now);
  atomic_fetch_add(&g->generation, 1);
  g->evictable = true;
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
  valk_label_set_v2_t ilabels = intern_labels(labels);

  u64 count = atomic_load(&g_metrics.histogram_count);
  for (u64 i = 0; i < count; i++) {
    valk_histogram_v2_t *h = &g_metrics.histograms[i];
    if (atomic_load(&h->active) && h->name == iname && labels_equal(&h->labels, &ilabels)) {
      return h;
    }
  }

  u32 idx = allocate_metric_slot(&g_metrics.histogram_free, g_metrics.histogram_next_free,
                                  &g_metrics.histogram_count, VALK_REGISTRY_MAX_HISTOGRAMS);
  if (idx == VALK_INVALID_SLOT) return nullptr;

  valk_histogram_v2_t *h = &g_metrics.histograms[idx];
  u64 now = get_timestamp_us();

  h->name = iname;
  h->help = intern_string(help);
  h->labels = ilabels;

  h->bucket_count = bound_count > VALK_MAX_BUCKETS ? VALK_MAX_BUCKETS : bound_count;
  memcpy(h->bucket_bounds, bounds, h->bucket_count * sizeof(double));

  for (u64 i = 0; i <= h->bucket_count; i++) {
    atomic_store(&h->buckets[i], 0);
    h->last_buckets[i] = 0;
  }
  atomic_store(&h->count, 0);
  atomic_store(&h->sum_micros, 0);
  h->last_count = 0;
  h->last_sum_micros = 0;
  h->last_timestamp = 0;

  atomic_store(&h->last_updated_us, now);
  atomic_fetch_add(&h->generation, 1);
  h->evictable = true;
  atomic_store(&h->active, true);

  return h;
}

// ============================================================================
// EVICTION
// ============================================================================

static u64 evict_stale_metrics_of_type(void *array, u64 elem_size, u64 count,
                                        u64 active_offset, u64 evictable_offset,
                                        u64 last_updated_offset,
                                        valk_free_list_t *fl, u32 *next_free,
                                        u64 now, u64 threshold) {
  u64 evicted = 0;
  for (u64 i = 0; i < count; i++) {
    char *m = (char *)array + i * elem_size;
    _Atomic bool *active = (_Atomic bool *)(m + active_offset);
    bool *evictable = (bool *)(m + evictable_offset);
    _Atomic u64 *last_updated = (_Atomic u64 *)(m + last_updated_offset);

    if (!atomic_load(active) || !*evictable) continue;
    if (now - atomic_load(last_updated) > threshold) {
      atomic_store(active, false);
      free_list_push(fl, next_free, i);
      evicted++;
    }
  }
  return evicted;
}

u64 valk_metrics_evict_stale(void) {
  u64 now = get_timestamp_us();
  u64 threshold = g_metrics.eviction_threshold_us;

  u64 counters_evicted = evict_stale_metrics_of_type(
      g_metrics.counters, sizeof(valk_counter_v2_t),
      atomic_load(&g_metrics.counter_count),
      offsetof(valk_counter_v2_t, active),
      offsetof(valk_counter_v2_t, evictable),
      offsetof(valk_counter_v2_t, last_updated_us),
      &g_metrics.counter_free, g_metrics.counter_next_free,
      now, threshold);

  u64 gauges_evicted = evict_stale_metrics_of_type(
      g_metrics.gauges, sizeof(valk_gauge_v2_t),
      atomic_load(&g_metrics.gauge_count),
      offsetof(valk_gauge_v2_t, active),
      offsetof(valk_gauge_v2_t, evictable),
      offsetof(valk_gauge_v2_t, last_updated_us),
      &g_metrics.gauge_free, g_metrics.gauge_next_free,
      now, threshold);

  u64 histograms_evicted = evict_stale_metrics_of_type(
      g_metrics.histograms, sizeof(valk_histogram_v2_t),
      atomic_load(&g_metrics.histogram_count),
      offsetof(valk_histogram_v2_t, active),
      offsetof(valk_histogram_v2_t, evictable),
      offsetof(valk_histogram_v2_t, last_updated_us),
      &g_metrics.histogram_free, g_metrics.histogram_next_free,
      now, threshold);

  u64 summaries_evicted = evict_stale_metrics_of_type(
      g_metrics.summaries, sizeof(valk_summary_v2_t),
      atomic_load(&g_metrics.summary_count),
      offsetof(valk_summary_v2_t, active),
      offsetof(valk_summary_v2_t, evictable),
      offsetof(valk_summary_v2_t, last_updated_us),
      &g_metrics.summary_free, g_metrics.summary_next_free,
      now, threshold);

  u64 evicted = counters_evicted + gauges_evicted + histograms_evicted + summaries_evicted;
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
