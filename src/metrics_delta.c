// metrics_delta.c - Delta collection and encoding for metrics
//
// This file implements the delta algorithm for efficient metrics streaming:
// - Timestamp utilities
// - Delta snapshot management
// - Delta collection from registry
// - JSON encoding for SSE
// - SSE event formatting

#include "metrics_delta.h"
#include "common.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
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
// DELTA SNAPSHOT MANAGEMENT
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
// PER-CONNECTION BASELINE API
// ============================================================================

void valk_metrics_baseline_init(valk_metrics_baseline_t *baseline) {
  memset(baseline, 0, sizeof(*baseline));
  baseline->initialized = false;
}

void valk_metrics_baseline_sync(valk_metrics_baseline_t *baseline,
                                 valk_metrics_registry_t *registry) {
  // Snapshot current counter values as baseline
  size_t counter_count = atomic_load(&registry->counter_count);
  for (size_t i = 0; i < counter_count; i++) {
    baseline->counter_baselines[i] =
        atomic_load_explicit(&registry->counters[i].value, memory_order_relaxed);
  }

  // Snapshot current gauge values
  size_t gauge_count = atomic_load(&registry->gauge_count);
  for (size_t i = 0; i < gauge_count; i++) {
    baseline->gauge_baselines[i] =
        atomic_load_explicit(&registry->gauges[i].value, memory_order_relaxed);
  }

  // Snapshot current histogram values
  size_t hist_count = atomic_load(&registry->histogram_count);
  for (size_t i = 0; i < hist_count; i++) {
    valk_histogram_v2_t *h = &registry->histograms[i];
    baseline->histogram_baselines[i].count =
        atomic_load_explicit(&h->count, memory_order_relaxed);
    baseline->histogram_baselines[i].sum_micros =
        atomic_load_explicit(&h->sum_micros, memory_order_relaxed);
    for (size_t b = 0; b <= h->bucket_count; b++) {
      baseline->histogram_baselines[i].buckets[b] =
          atomic_load_explicit(&h->buckets[b], memory_order_relaxed);
    }
  }

  baseline->last_collect_time = get_timestamp_us();
  baseline->initialized = true;
}

// Stateless delta collection (doesn't modify global registry)
size_t valk_delta_snapshot_collect_stateless(valk_delta_snapshot_t *snap,
                                              valk_metrics_registry_t *registry,
                                              valk_metrics_baseline_t *baseline) {
  uint64_t now = get_timestamp_us();

  // If baseline not initialized, sync it first
  if (!baseline->initialized) {
    valk_metrics_baseline_sync(baseline, registry);
    // On first call, report no changes (baseline just set)
    snap->timestamp_us = now;
    snap->prev_timestamp_us = baseline->last_collect_time;
    snap->interval_us = 0;
    snap->delta_count = 0;
    snap->counters_changed = 0;
    snap->gauges_changed = 0;
    snap->histograms_changed = 0;
    snap->summaries_changed = 0;
    return 0;
  }

  snap->timestamp_us = now;
  snap->prev_timestamp_us = baseline->last_collect_time;
  snap->interval_us = now - baseline->last_collect_time;
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
    uint64_t last = baseline->counter_baselines[i];

    if (current != last) {
      ensure_delta_capacity(snap);
      valk_metric_delta_t *delta = &snap->deltas[snap->delta_count++];
      delta->name = c->name;
      delta->labels = &c->labels;
      delta->type = VALK_DELTA_INCREMENT;
      delta->data.increment = current - last;

      // Update per-connection baseline (NOT global registry)
      baseline->counter_baselines[i] = current;
      snap->counters_changed++;
    }
  }

  // Process gauges - send if value changed (Prometheus-style simplicity)
  // No percentage threshold - predictable behavior, negligible bandwidth impact
  size_t gauge_count = atomic_load(&registry->gauge_count);
  for (size_t i = 0; i < gauge_count; i++) {
    valk_gauge_v2_t *g = &registry->gauges[i];
    int64_t current = atomic_load_explicit(&g->value, memory_order_relaxed);
    int64_t last = baseline->gauge_baselines[i];

    if (current != last) {
      ensure_delta_capacity(snap);
      valk_metric_delta_t *delta = &snap->deltas[snap->delta_count++];
      delta->name = g->name;
      delta->labels = &g->labels;
      delta->type = VALK_DELTA_SET;
      delta->data.value = current;

      baseline->gauge_baselines[i] = current;
      snap->gauges_changed++;
    }
  }

  // Process histograms
  size_t hist_count = atomic_load(&registry->histogram_count);
  for (size_t i = 0; i < hist_count; i++) {
    valk_histogram_v2_t *h = &registry->histograms[i];
    uint64_t current_count = atomic_load_explicit(&h->count, memory_order_relaxed);

    if (current_count != baseline->histogram_baselines[i].count) {
      ensure_delta_capacity(snap);
      valk_metric_delta_t *delta = &snap->deltas[snap->delta_count++];
      delta->name = h->name;
      delta->labels = &h->labels;
      delta->type = VALK_DELTA_OBSERVE;

      // Calculate per-bucket deltas
      for (size_t b = 0; b <= h->bucket_count; b++) {
        uint64_t bucket_val = atomic_load_explicit(&h->buckets[b], memory_order_relaxed);
        delta->data.histogram.bucket_deltas[b] =
            bucket_val - baseline->histogram_baselines[i].buckets[b];
        baseline->histogram_baselines[i].buckets[b] = bucket_val;
      }

      delta->data.histogram.count_delta =
          current_count - baseline->histogram_baselines[i].count;
      uint64_t current_sum = atomic_load_explicit(&h->sum_micros, memory_order_relaxed);
      delta->data.histogram.sum_delta_micros =
          current_sum - baseline->histogram_baselines[i].sum_micros;
      delta->data.histogram.bucket_bounds = h->bucket_bounds;
      delta->data.histogram.bucket_count = h->bucket_count;

      baseline->histogram_baselines[i].count = current_count;
      baseline->histogram_baselines[i].sum_micros = current_sum;
      snap->histograms_changed++;
    }
  }

  baseline->last_collect_time = now;
  return snap->delta_count;
}

// ============================================================================
// LEGACY DELTA COLLECTION (modifies global registry state)
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

  // Process gauges - send if value changed (Prometheus-style simplicity)
  size_t gauge_count = atomic_load(&registry->gauge_count);
  for (size_t i = 0; i < gauge_count; i++) {
    valk_gauge_v2_t *g = &registry->gauges[i];
    int64_t current = atomic_load_explicit(&g->value, memory_order_relaxed);
    int64_t last = atomic_load_explicit(&g->last_value, memory_order_relaxed);

    if (current != last) {
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
      delta->data.histogram.bucket_bounds = h->bucket_bounds;
      delta->data.histogram.bucket_count = h->bucket_count;

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
// JSON ENCODING
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

    // Helper: write labels object inline
    char labels_buf[256] = {0};
    if (d->labels && d->labels->count > 0) {
      char *lp = labels_buf;
      char *lend = labels_buf + sizeof(labels_buf);
      int ln = snprintf(lp, lend - lp, ",\"l\":{");
      if (ln > 0) lp += ln;
      for (uint8_t j = 0; j < d->labels->count && lp < lend - 32; j++) {
        ln = snprintf(lp, lend - lp, "%s\"%s\":\"%s\"",
                      j > 0 ? "," : "",
                      d->labels->labels[j].key,
                      d->labels->labels[j].value);
        if (ln > 0) lp += ln;
      }
      snprintf(lp, lend - lp, "}");
    }

    switch (d->type) {
      case VALK_DELTA_INCREMENT:
        n = snprintf(p, end - p, "{\"n\":\"%s\",\"t\":\"c\",\"d\":%lu%s}",
                     d->name, d->data.increment, labels_buf);
        break;
      case VALK_DELTA_SET:
        n = snprintf(p, end - p, "{\"n\":\"%s\",\"t\":\"g\",\"v\":%ld%s}",
                     d->name, d->data.value, labels_buf);
        break;
      case VALK_DELTA_OBSERVE: {
        n = snprintf(p, end - p, "{\"n\":\"%s\",\"t\":\"h\",\"c\":%lu,\"s\":%lu,\"b\":[",
                     d->name, d->data.histogram.count_delta,
                     d->data.histogram.sum_delta_micros);
        if (n < 0 || p + n >= end) return buf_size;
        p += n;
        uint64_t cumulative = 0;
        for (uint8_t b = 0; b <= d->data.histogram.bucket_count; b++) {
          cumulative += d->data.histogram.bucket_deltas[b];
          if (b < d->data.histogram.bucket_count) {
            n = snprintf(p, end - p, "%s{\"le\":%.6f,\"d\":%lu}",
                         b > 0 ? "," : "", d->data.histogram.bucket_bounds[b], cumulative);
          } else {
            n = snprintf(p, end - p, "%s{\"le\":\"+Inf\",\"d\":%lu}",
                         b > 0 ? "," : "", cumulative);
          }
          if (n < 0 || p + n >= end) return buf_size;
          p += n;
        }
        n = snprintf(p, end - p, "]%s}", labels_buf);
        break;
      }
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
// SSE ENCODING
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

// ============================================================================
// PROMETHEUS ENCODING
// ============================================================================

static size_t write_labels_prometheus(char *buf, size_t cap, const valk_label_set_v2_t *labels) {
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

size_t valk_delta_to_prometheus(const valk_delta_snapshot_t *snap,
                                valk_metrics_registry_t *registry,
                                char *buf, size_t buf_size) {
  UNUSED(snap);  // We export full state, not just deltas

  char *p = buf;
  char *end = buf + buf_size;
  int n;

  // Export counters
  size_t counter_count = atomic_load(&registry->counter_count);
  for (size_t i = 0; i < counter_count; i++) {
    valk_counter_v2_t *c = &registry->counters[i];
    uint64_t val = atomic_load_explicit(&c->value, memory_order_relaxed);

    n = snprintf(p, end - p, "%s", c->name);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    p += write_labels_prometheus(p, end - p, &c->labels);

    n = snprintf(p, end - p, " %lu\n", val);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;
  }

  // Export gauges
  size_t gauge_count = atomic_load(&registry->gauge_count);
  for (size_t i = 0; i < gauge_count; i++) {
    valk_gauge_v2_t *g = &registry->gauges[i];
    int64_t val = atomic_load_explicit(&g->value, memory_order_relaxed);

    n = snprintf(p, end - p, "%s", g->name);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    p += write_labels_prometheus(p, end - p, &g->labels);

    n = snprintf(p, end - p, " %ld\n", val);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;
  }

  // Export histograms
  size_t hist_count = atomic_load(&registry->histogram_count);
  for (size_t i = 0; i < hist_count; i++) {
    valk_histogram_v2_t *h = &registry->histograms[i];
    uint64_t count = atomic_load_explicit(&h->count, memory_order_relaxed);
    uint64_t sum = atomic_load_explicit(&h->sum_micros, memory_order_relaxed);

    // Buckets (cumulative)
    uint64_t cumulative = 0;
    for (uint8_t b = 0; b < h->bucket_count; b++) {
      cumulative += atomic_load_explicit(&h->buckets[b], memory_order_relaxed);

      n = snprintf(p, end - p, "%s_bucket{", h->name);
      if (n < 0 || p + n >= end) return buf_size;
      p += n;

      for (uint8_t j = 0; j < h->labels.count; j++) {
        n = snprintf(p, end - p, "%s=\"%s\",",
                     h->labels.labels[j].key, h->labels.labels[j].value);
        if (n < 0 || p + n >= end) return buf_size;
        p += n;
      }

      n = snprintf(p, end - p, "le=\"%.3f\"} %lu\n", h->bucket_bounds[b], cumulative);
      if (n < 0 || p + n >= end) return buf_size;
      p += n;
    }

    // +Inf bucket
    cumulative += atomic_load_explicit(&h->buckets[h->bucket_count], memory_order_relaxed);
    n = snprintf(p, end - p, "%s_bucket{", h->name);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    for (uint8_t j = 0; j < h->labels.count; j++) {
      n = snprintf(p, end - p, "%s=\"%s\",",
                   h->labels.labels[j].key, h->labels.labels[j].value);
      if (n < 0 || p + n >= end) return buf_size;
      p += n;
    }

    n = snprintf(p, end - p, "le=\"+Inf\"} %lu\n", cumulative);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    // Sum and count
    n = snprintf(p, end - p, "%s_sum", h->name);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    p += write_labels_prometheus(p, end - p, &h->labels);

    n = snprintf(p, end - p, " %.6f\n", (double)sum / 1e6);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    n = snprintf(p, end - p, "%s_count", h->name);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    p += write_labels_prometheus(p, end - p, &h->labels);

    n = snprintf(p, end - p, " %lu\n", count);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;
  }

  return p - buf;
}

// ============================================================================
// JSON FULL EXPORT
// ============================================================================

// Helper to write labels as JSON object
static size_t write_labels_json(char *buf, size_t buf_size,
                                const valk_label_set_v2_t *labels) {
  if (labels->count == 0) return 0;

  char *p = buf;
  char *end = buf + buf_size;
  int n;

  n = snprintf(p, end - p, ",\"labels\":{");
  if (n < 0 || p + n >= end) return 0;
  p += n;

  for (uint8_t i = 0; i < labels->count; i++) {
    n = snprintf(p, end - p, "%s\"%s\":\"%s\"",
                 i > 0 ? "," : "",
                 labels->labels[i].key, labels->labels[i].value);
    if (n < 0 || p + n >= end) return 0;
    p += n;
  }

  n = snprintf(p, end - p, "}");
  if (n < 0 || p + n >= end) return 0;
  p += n;

  return p - buf;
}

size_t valk_metrics_v2_to_json(valk_metrics_registry_t *registry,
                               char *buf, size_t buf_size) {
  char *p = buf;
  char *end = buf + buf_size;
  int n;

  // Start JSON object
  n = snprintf(p, end - p, "{\"uptime_seconds\":%.2f,",
               (double)(get_timestamp_us() - registry->start_time_us) / 1e6);
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  // Counters array
  n = snprintf(p, end - p, "\"counters\":[");
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  size_t counter_count = atomic_load(&registry->counter_count);
  for (size_t i = 0; i < counter_count; i++) {
    valk_counter_v2_t *c = &registry->counters[i];
    uint64_t val = atomic_load_explicit(&c->value, memory_order_relaxed);

    n = snprintf(p, end - p, "%s{\"name\":\"%s\",\"value\":%lu",
                 i > 0 ? "," : "", c->name, val);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    p += write_labels_json(p, end - p, &c->labels);

    n = snprintf(p, end - p, "}");
    if (n < 0 || p + n >= end) return buf_size;
    p += n;
  }

  n = snprintf(p, end - p, "],");
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  // Gauges array
  n = snprintf(p, end - p, "\"gauges\":[");
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  size_t gauge_count = atomic_load(&registry->gauge_count);
  for (size_t i = 0; i < gauge_count; i++) {
    valk_gauge_v2_t *g = &registry->gauges[i];
    int64_t val = atomic_load_explicit(&g->value, memory_order_relaxed);

    n = snprintf(p, end - p, "%s{\"name\":\"%s\",\"value\":%ld",
                 i > 0 ? "," : "", g->name, val);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    p += write_labels_json(p, end - p, &g->labels);

    n = snprintf(p, end - p, "}");
    if (n < 0 || p + n >= end) return buf_size;
    p += n;
  }

  n = snprintf(p, end - p, "],");
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  // Histograms array
  n = snprintf(p, end - p, "\"histograms\":[");
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  size_t hist_count = atomic_load(&registry->histogram_count);
  for (size_t i = 0; i < hist_count; i++) {
    valk_histogram_v2_t *h = &registry->histograms[i];
    uint64_t count = atomic_load_explicit(&h->count, memory_order_relaxed);
    uint64_t sum = atomic_load_explicit(&h->sum_micros, memory_order_relaxed);

    n = snprintf(p, end - p, "%s{\"name\":\"%s\",\"count\":%lu,\"sum_us\":%lu",
                 i > 0 ? "," : "", h->name, count, sum);
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    p += write_labels_json(p, end - p, &h->labels);

    // Add bucket bounds and counts
    n = snprintf(p, end - p, ",\"buckets\":[");
    if (n < 0 || p + n >= end) return buf_size;
    p += n;

    uint64_t cumulative = 0;
    for (uint8_t b = 0; b <= h->bucket_count; b++) {
      cumulative += atomic_load_explicit(&h->buckets[b], memory_order_relaxed);
      if (b < h->bucket_count) {
        n = snprintf(p, end - p, "%s{\"le\":%.6f,\"count\":%lu}",
                     b > 0 ? "," : "", h->bucket_bounds[b], cumulative);
      } else {
        n = snprintf(p, end - p, "%s{\"le\":\"+Inf\",\"count\":%lu}",
                     b > 0 ? "," : "", cumulative);
      }
      if (n < 0 || p + n >= end) return buf_size;
      p += n;
    }

    n = snprintf(p, end - p, "]}");
    if (n < 0 || p + n >= end) return buf_size;
    p += n;
  }

  n = snprintf(p, end - p, "]}");
  if (n < 0 || p + n >= end) return buf_size;
  p += n;

  return p - buf;
}
