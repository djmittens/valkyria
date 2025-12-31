// src/metrics_builtins.c - Lisp builtins for metrics V2 system
//
// This file implements Lisp builtins for the metrics V2 system, providing
// a Lisp API for creating and manipulating counters, gauges, and histograms.
//
// Reference implementation patterns from aio_sse_builtins.c

#include "metrics_v2.h"
#include "metrics_delta.h"
#include "aio/aio.h"
#include "memory.h"
#include "parser.h"
#include "common.h"

#include <string.h>
#include <stdlib.h>

// ============================================================================
// FORWARD DECLARATIONS
// ============================================================================

// Map short names to v2 inline functions from metrics_v2.h
#define valk_counter_add(c, n)        valk_counter_v2_add(c, n)
#define valk_gauge_set(g, v)          valk_gauge_v2_set(g, v)
#define valk_gauge_inc(g)             valk_gauge_v2_inc(g)
#define valk_gauge_dec(g)             valk_gauge_v2_dec(g)
#define valk_histogram_observe_us(h, us) valk_histogram_v2_observe_us(h, us)

// Standard bucket bounds for HTTP latency
static const double DEFAULT_HTTP_BUCKETS[] = {
  0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0
};

// ============================================================================
// COUNTER BUILTINS
// ============================================================================

// (metrics/counter name labels...) -> counter-handle
// Labels are key-value pairs: (metrics/counter "http_requests" "method" "GET" "path" "/api")
static valk_lval_t *valk_builtin_metrics_counter(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  u64 argc = valk_lval_list_count(a);
  if (argc < 1) {
    return valk_lval_err("metrics/counter: expected at least 1 argument (name)");
  }

  valk_lval_t *name_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(name_arg) != LVAL_STR) {
    return valk_lval_err("metrics/counter: name must be a string");
  }

  // Parse optional labels (key-value pairs)
  valk_label_set_v2_t labels = {0};
  for (u64 i = 1; i + 1 < argc; i += 2) {
    valk_lval_t *key = valk_lval_list_nth(a, i);
    valk_lval_t *val = valk_lval_list_nth(a, i + 1);
    if (LVAL_TYPE(key) != LVAL_STR || LVAL_TYPE(val) != LVAL_STR) {
      return valk_lval_err("metrics/counter: labels must be string key-value pairs");
    }

    if (labels.count < VALK_MAX_LABELS_V2) {
      labels.labels[labels.count].key = key->str;
      labels.labels[labels.count].value = val->str;
      labels.count++;
    }
  }

  valk_counter_v2_t *counter = valk_counter_get_or_create(
      name_arg->str, nullptr, &labels);

  if (!counter) {
    return valk_lval_err("metrics/counter: registry full");
  }

  return valk_lval_ref("metrics_counter", counter, nullptr);
}

// (metrics/counter-inc counter [n]) -> nil
// Increments counter by 1 or n
static valk_lval_t *valk_builtin_metrics_counter_inc(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  u64 argc = valk_lval_list_count(a);
  if (argc < 1 || argc > 2) {
    return valk_lval_err("metrics/counter-inc: expected 1-2 arguments");
  }

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ref) != LVAL_REF || strcmp(ref->ref.type, "metrics_counter") != 0) {
    return valk_lval_err("metrics/counter-inc: first argument must be counter handle");
  }

  valk_counter_v2_t *counter = (valk_counter_v2_t *)ref->ref.ptr;
  u64 n = 1;

  if (argc == 2) {
    valk_lval_t *n_arg = valk_lval_list_nth(a, 1);
    if (LVAL_TYPE(n_arg) != LVAL_NUM) {
      return valk_lval_err("metrics/counter-inc: second argument must be a number");
    }
    n = (u64)n_arg->num;
  }

  valk_counter_add(counter, n);
  return valk_lval_nil();
}

// ============================================================================
// GAUGE BUILTINS
// ============================================================================

// (metrics/gauge name labels...) -> gauge-handle
static valk_lval_t *valk_builtin_metrics_gauge(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  u64 argc = valk_lval_list_count(a);
  if (argc < 1) {
    return valk_lval_err("metrics/gauge: expected at least 1 argument (name)");
  }

  valk_lval_t *name_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(name_arg) != LVAL_STR) {
    return valk_lval_err("metrics/gauge: name must be a string");
  }

  // Parse optional labels
  valk_label_set_v2_t labels = {0};
  for (u64 i = 1; i + 1 < argc; i += 2) {
    valk_lval_t *key = valk_lval_list_nth(a, i);
    valk_lval_t *val = valk_lval_list_nth(a, i + 1);
    if (LVAL_TYPE(key) != LVAL_STR || LVAL_TYPE(val) != LVAL_STR) {
      return valk_lval_err("metrics/gauge: labels must be string key-value pairs");
    }

    if (labels.count < VALK_MAX_LABELS_V2) {
      labels.labels[labels.count].key = key->str;
      labels.labels[labels.count].value = val->str;
      labels.count++;
    }
  }

  valk_gauge_v2_t *gauge = valk_gauge_get_or_create(
      name_arg->str, nullptr, &labels);

  if (!gauge) {
    return valk_lval_err("metrics/gauge: registry full");
  }

  return valk_lval_ref("metrics_gauge", gauge, nullptr);
}

// (metrics/gauge-set gauge value) -> nil
static valk_lval_t *valk_builtin_metrics_gauge_set(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("metrics/gauge-set: expected 2 arguments");
  }

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  valk_lval_t *val = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(ref) != LVAL_REF || strcmp(ref->ref.type, "metrics_gauge") != 0) {
    return valk_lval_err("metrics/gauge-set: first argument must be gauge handle");
  }
  if (LVAL_TYPE(val) != LVAL_NUM) {
    return valk_lval_err("metrics/gauge-set: second argument must be a number");
  }

  valk_gauge_v2_t *gauge = (valk_gauge_v2_t *)ref->ref.ptr;
  valk_gauge_set(gauge, (i64)val->num);

  return valk_lval_nil();
}

// (metrics/gauge-inc gauge) -> nil
static valk_lval_t *valk_builtin_metrics_gauge_inc(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("metrics/gauge-inc: expected 1 argument");
  }

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ref) != LVAL_REF || strcmp(ref->ref.type, "metrics_gauge") != 0) {
    return valk_lval_err("metrics/gauge-inc: argument must be gauge handle");
  }

  valk_gauge_v2_t *gauge = (valk_gauge_v2_t *)ref->ref.ptr;
  valk_gauge_inc(gauge);

  return valk_lval_nil();
}

// (metrics/gauge-dec gauge) -> nil
static valk_lval_t *valk_builtin_metrics_gauge_dec(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("metrics/gauge-dec: expected 1 argument");
  }

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ref) != LVAL_REF || strcmp(ref->ref.type, "metrics_gauge") != 0) {
    return valk_lval_err("metrics/gauge-dec: argument must be gauge handle");
  }

  valk_gauge_v2_t *gauge = (valk_gauge_v2_t *)ref->ref.ptr;
  valk_gauge_dec(gauge);

  return valk_lval_nil();
}

// ============================================================================
// HISTOGRAM BUILTINS
// ============================================================================

// (metrics/histogram name :buckets (list...) labels...) -> histogram-handle
// Example: (metrics/histogram "http_latency" :buckets (list 0.01 0.1 1.0) "method" "GET")
// If no buckets specified, uses DEFAULT_HTTP_BUCKETS
static valk_lval_t *valk_builtin_metrics_histogram(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  u64 argc = valk_lval_list_count(a);
  if (argc < 1) {
    return valk_lval_err("metrics/histogram: expected at least 1 argument (name)");
  }

  valk_lval_t *name_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(name_arg) != LVAL_STR) {
    return valk_lval_err("metrics/histogram: name must be a string");
  }

  // Parse :buckets option and labels
  double buckets[VALK_MAX_BUCKETS];
  u64 bucket_count = 0;
  valk_label_set_v2_t labels = {0};

  for (u64 i = 1; i < argc; i++) {
    valk_lval_t *item = valk_lval_list_nth(a, i);

    if (LVAL_TYPE(item) == LVAL_SYM && strcmp(item->str, ":buckets") == 0) {
      // Next item should be bucket list
      if (i + 1 < argc) {
        valk_lval_t *bucket_list = valk_lval_list_nth(a, ++i);

        // Accept both LVAL_QEXPR and LVAL_CONS for bucket list
        if (LVAL_TYPE(bucket_list) != LVAL_QEXPR && LVAL_TYPE(bucket_list) != LVAL_CONS) {
          return valk_lval_err("metrics/histogram: :buckets must be followed by a list");
        }

        u64 len = valk_lval_list_count(bucket_list);
        for (u64 j = 0; j < len && bucket_count < VALK_MAX_BUCKETS; j++) {
          valk_lval_t *b = valk_lval_list_nth(bucket_list, j);
          if (LVAL_TYPE(b) == LVAL_NUM) {
            buckets[bucket_count++] = (double)b->num;
          }
        }
      }
    } else if (LVAL_TYPE(item) == LVAL_STR && i + 1 < argc) {
      // Label key-value pair
      valk_lval_t *val = valk_lval_list_nth(a, ++i);
      if (LVAL_TYPE(val) != LVAL_STR) {
        return valk_lval_err("metrics/histogram: label value must be a string");
      }

      if (labels.count < VALK_MAX_LABELS_V2) {
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
      name_arg->str, nullptr, buckets, bucket_count, &labels);

  if (!h) {
    return valk_lval_err("metrics/histogram: registry full");
  }

  return valk_lval_ref("metrics_histogram", h, nullptr);
}

// (metrics/histogram-observe histogram value-us) -> nil
// value-us is the observed value in microseconds
static valk_lval_t *valk_builtin_metrics_histogram_observe(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("metrics/histogram-observe: expected 2 arguments");
  }

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  valk_lval_t *val = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(ref) != LVAL_REF || strcmp(ref->ref.type, "metrics_histogram") != 0) {
    return valk_lval_err("metrics/histogram-observe: first argument must be histogram handle");
  }
  if (LVAL_TYPE(val) != LVAL_NUM) {
    return valk_lval_err("metrics/histogram-observe: second argument must be a number");
  }

  valk_histogram_v2_t *h = (valk_histogram_v2_t *)ref->ref.ptr;
  valk_histogram_observe_us(h, (u64)val->num);

  return valk_lval_nil();
}

// ============================================================================
// EXPORT BUILTINS
// ============================================================================

// Cleanup function for delta snapshot
static void delta_snapshot_cleanup(void *ptr) {
  valk_delta_snapshot_t *snap = (valk_delta_snapshot_t *)ptr;
  if (snap) {
    valk_delta_snapshot_free(snap);
    free(snap);
  }
}

// (metrics/collect-delta) -> delta-snapshot-handle
// Collects a delta snapshot from the global registry
static valk_lval_t *valk_builtin_metrics_collect_delta(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("metrics/collect-delta: expected 0 arguments, got %zu",
                         valk_lval_list_count(a));
  }

  valk_delta_snapshot_t *snap = malloc(sizeof(valk_delta_snapshot_t));
  if (!snap) {
    return valk_lval_err("metrics/collect-delta: allocation failed");
  }

  valk_delta_snapshot_init(snap);
  valk_delta_snapshot_collect(snap, &g_metrics);

  return valk_lval_ref("metrics_delta", snap, delta_snapshot_cleanup);
}

// (metrics/delta-json delta) -> json-string
// Encodes delta snapshot to JSON string
static valk_lval_t *valk_builtin_metrics_delta_json(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("metrics/delta-json: expected 1 argument");
  }

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ref) != LVAL_REF || strcmp(ref->ref.type, "metrics_delta") != 0) {
    return valk_lval_err("metrics/delta-json: argument must be delta snapshot handle");
  }

  valk_delta_snapshot_t *snap = (valk_delta_snapshot_t *)ref->ref.ptr;

  // Allocate buffer for JSON (64KB should be enough for most cases)
  char *buf = malloc(65536);
  if (!buf) {
    return valk_lval_err("metrics/delta-json: allocation failed");
  }

  u64 len = valk_delta_to_json(snap, buf, 65536);

  // Check if buffer was too small
  if (len >= 65536) {
    free(buf);
    return valk_lval_err("metrics/delta-json: output too large");
  }

  valk_lval_t *result = valk_lval_str_n(buf, len);
  free(buf);

  return result;
}

// (metrics/prometheus) -> prometheus-string
// Exports all metrics in Prometheus text exposition format
static valk_lval_t *valk_builtin_metrics_prometheus(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("metrics/prometheus: expected 0 arguments, got %zu",
                         valk_lval_list_count(a));
  }

  // Create a temporary delta snapshot to get current state
  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  // Allocate buffer for Prometheus format (128KB for full snapshot)
  char *buf = malloc(131072);
  if (!buf) {
    valk_delta_snapshot_free(&snap);
    return valk_lval_err("metrics/prometheus: allocation failed");
  }

  u64 len = valk_delta_to_prometheus(&snap, &g_metrics, buf, 131072);

  valk_delta_snapshot_free(&snap);

  // Check if buffer was too small
  if (len >= 131072) {
    free(buf);
    return valk_lval_err("metrics/prometheus: output too large");
  }

  valk_lval_t *result = valk_lval_str_n(buf, len);
  free(buf);

  return result;
}

// (metrics/json) -> json-string
// Exports all metrics in JSON format (full state, not deltas)
static valk_lval_t *valk_builtin_metrics_json(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("metrics/json: expected 0 arguments, got %zu",
                         valk_lval_list_count(a));
  }

  // Allocate buffer for JSON format (128KB)
  char *buf = malloc(131072);
  if (!buf) {
    return valk_lval_err("metrics/json: allocation failed");
  }

  u64 len = valk_metrics_v2_to_json(&g_metrics, buf, 131072);

  // Check if buffer was too small
  if (len >= 131072) {
    free(buf);
    return valk_lval_err("metrics/json: output too large");
  }

  valk_lval_t *result = valk_lval_str_n(buf, len);
  free(buf);

  return result;
}

// (metrics/registry-json) -> json-string
// Returns registry meta-metrics (capacity, usage, evictions)
static valk_lval_t *valk_builtin_metrics_registry_json(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("metrics/registry-json: expected 0 arguments");
  }

  valk_registry_stats_t stats;
  valk_registry_stats_collect(&stats);

  char *buf = malloc(2048);
  if (!buf) {
    return valk_lval_err("metrics/registry-json: allocation failed");
  }

  u64 len = valk_registry_stats_to_json(&stats, buf, 2048);
  if (len == 0 || len >= 2048) {
    free(buf);
    return valk_lval_err("metrics/registry-json: output too large");
  }

  valk_lval_t *result = valk_lval_str_n(buf, len);
  free(buf);
  return result;
}

#ifdef VALK_METRICS_ENABLED
// (aio/slab-buckets sys slab-name start end num-buckets) -> json-string
static valk_lval_t *valk_builtin_aio_slab_buckets(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  u64 argc = valk_lval_list_count(a);
  if (argc < 5) {
    return valk_lval_err("aio/slab-buckets: expected (sys slab-name start end num-buckets)");
  }

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(sys_arg) != LVAL_REF || strcmp(sys_arg->ref.type, "aio_system") != 0) {
    return valk_lval_err("aio/slab-buckets: first argument must be an aio_system");
  }
  valk_aio_system_t *sys = (valk_aio_system_t *)sys_arg->ref.ptr;

  valk_lval_t *name_arg = valk_lval_list_nth(a, 1);
  valk_lval_t *start_arg = valk_lval_list_nth(a, 2);
  valk_lval_t *end_arg = valk_lval_list_nth(a, 3);
  valk_lval_t *buckets_arg = valk_lval_list_nth(a, 4);

  if (LVAL_TYPE(name_arg) != LVAL_STR ||
      LVAL_TYPE(start_arg) != LVAL_NUM ||
      LVAL_TYPE(end_arg) != LVAL_NUM ||
      LVAL_TYPE(buckets_arg) != LVAL_NUM) {
    return valk_lval_err("aio/slab-buckets: invalid argument types");
  }

  const char *slab_name = name_arg->str;
  u64 start = (u64)start_arg->num;
  u64 end = (u64)end_arg->num;
  u64 num_buckets = (u64)buckets_arg->num;

  if (num_buckets == 0 || num_buckets > 4096) {
    return valk_lval_err("aio/slab-buckets: num-buckets must be 1-4096");
  }

  valk_slab_t *slab = nullptr;
  if (strcmp(slab_name, "tcp_buffers") == 0) {
    slab = valk_aio_get_tcp_buffer_slab(sys);
  } else if (strcmp(slab_name, "handles") == 0) {
    slab = valk_aio_get_handle_slab(sys);
  } else if (strcmp(slab_name, "stream_arenas") == 0) {
    slab = valk_aio_get_stream_arenas_slab(sys);
  } else if (strcmp(slab_name, "http_servers") == 0) {
    slab = valk_aio_get_http_servers_slab(sys);
  } else if (strcmp(slab_name, "http_clients") == 0) {
    slab = valk_aio_get_http_clients_slab(sys);
  } else if (strcmp(slab_name, "lval") == 0 || strcmp(slab_name, "lenv") == 0) {
    return valk_lval_err("aio/slab-buckets: lval/lenv slabs no longer exist in heap2");
  }

  if (!slab) {
    return valk_lval_err("aio/slab-buckets: unknown slab name");
  }

  if (!slab->usage_bitmap) {
    return valk_lval_err("aio/slab-buckets: slab has no maintained bitmap");
  }

  valk_bitmap_bucket_t *buckets = malloc(num_buckets * sizeof(valk_bitmap_bucket_t));
  if (!buckets) {
    return valk_lval_err("aio/slab-buckets: allocation failed");
  }

  u64 actual_buckets = valk_slab_bitmap_buckets(slab, start, end, num_buckets, buckets);

  u64 buf_size = 32 + actual_buckets * 32;
  char *buf = malloc(buf_size);
  if (!buf) {
    free(buckets);
    return valk_lval_err("aio/slab-buckets: allocation failed");
  }

  char *p = buf;
  char *buf_end = buf + buf_size;
  int n = snprintf(p, buf_end - p, "{\"buckets\":[");
  p += n;

  for (u64 i = 0; i < actual_buckets && p < buf_end - 30; i++) {
    if (i > 0) *p++ = ',';
    n = snprintf(p, buf_end - p, "{\"u\":%llu,\"f\":%llu}",
                 (unsigned long long)buckets[i].used, (unsigned long long)buckets[i].free);
    if (n > 0) p += n;
  }

  snprintf(p, buf_end - p, "],\"total\":%llu}", (unsigned long long)slab->numItems);

  valk_lval_t *result = valk_lval_str(buf);
  free(buf);
  free(buckets);

  return result;
}
#endif

static void write_slab_json(char **p, char *end, const char *name, valk_slab_t *slab) {
  if (!slab || *p >= end - 100) return;

  u64 used = slab->numItems - slab->numFree;
  u64 total = slab->numItems;
  u64 hwm = slab->peakUsed;
  u64 overflow = slab->overflowCount;

  int n = snprintf(*p, end - *p,
    "{\"name\":\"%s\",\"used\":%llu,\"total\":%llu,\"hwm\":%llu,\"overflow\":%llu}",
    name,
    (unsigned long long)used,
    (unsigned long long)total,
    (unsigned long long)hwm,
    (unsigned long long)overflow);
  if (n > 0 && *p + n < end) *p += n;
}

// (aio/diagnostics-state-json sys) -> json-string
// Returns memory diagnostics for the debug dashboard
static valk_lval_t *valk_builtin_aio_diagnostics_state_json(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/diagnostics-state-json: expected 1 argument (sys)");
  }

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(sys_arg) != LVAL_REF || strcmp(sys_arg->ref.type, "aio_system") != 0) {
    return valk_lval_err("aio/diagnostics-state-json: argument must be an aio_system");
  }

#ifdef VALK_METRICS_ENABLED
  valk_aio_system_t *sys = (valk_aio_system_t *)sys_arg->ref.ptr;

  valk_slab_t *tcp_slab = valk_aio_get_tcp_buffer_slab(sys);
  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  valk_slab_t *arena_slab = valk_aio_get_stream_arenas_slab(sys);
  valk_slab_t *server_slab = valk_aio_get_http_servers_slab(sys);
  valk_slab_t *client_slab = valk_aio_get_http_clients_slab(sys);

  valk_process_memory_t pm = {0};
  valk_process_memory_collect(&pm);

  valk_gc_malloc_heap_t *heap = valk_aio_get_gc_heap(sys);
  u64 gc_used = 0, gc_total = 0;
  if (heap) {
    gc_used = valk_gc_heap2_used_bytes(heap);
    gc_total = heap->hard_limit;
  }

  u64 buf_size = 8192;
  char *buf = malloc(buf_size);
  if (!buf) {
    return valk_lval_err("aio/diagnostics-state-json: allocation failed");
  }

  char *p = buf;
  char *end = buf + buf_size;

  int n = snprintf(p, end - p, "{\"slabs\":[");
  if (n > 0) p += n;

  int first = 1;
  if (tcp_slab) {
    if (!first) { *p++ = ','; } first = 0;
    write_slab_json(&p, end, "tcp_buffers", tcp_slab);
  }
  if (handle_slab) {
    if (!first) { *p++ = ','; } first = 0;
    write_slab_json(&p, end, "handles", handle_slab);
  }
  if (arena_slab) {
    if (!first) { *p++ = ','; } first = 0;
    write_slab_json(&p, end, "stream_arenas", arena_slab);
  }
  if (server_slab) {
    if (!first) { *p++ = ','; } first = 0;
    write_slab_json(&p, end, "http_servers", server_slab);
  }
  if (client_slab) {
    if (!first) { *p++ = ','; }
    write_slab_json(&p, end, "http_clients", client_slab);
  }

  n = snprintf(p, end - p, "],\"arenas\":[");
  if (n > 0) p += n;

  n = snprintf(p, end - p,
    "{\"name\":\"stream_arenas\",\"used\":%llu,\"capacity\":%llu}",
    arena_slab ? (unsigned long long)(arena_slab->numItems - arena_slab->numFree) : 0ULL,
    arena_slab ? (unsigned long long)arena_slab->numItems : 0ULL);
  if (n > 0) p += n;

  n = snprintf(p, end - p,
    "],\"gc\":{\"heap_used_bytes\":%llu,\"heap_total_bytes\":%llu}",
    (unsigned long long)gc_used,
    (unsigned long long)gc_total);
  if (n > 0) p += n;

  n = snprintf(p, end - p,
    ",\"process\":{\"rss\":%llu,\"vms\":%llu,\"system_total\":%llu}",
    (unsigned long long)pm.rss_bytes,
    (unsigned long long)pm.vms_bytes,
    (unsigned long long)pm.system_total_bytes);
  if (n > 0) p += n;

  u64 aio_used = 0, aio_cap = 0;
  if (tcp_slab) {
    aio_used += (tcp_slab->numItems - tcp_slab->numFree) * tcp_slab->itemSize;
    aio_cap += tcp_slab->numItems * tcp_slab->itemSize;
  }
  if (handle_slab) {
    aio_used += (handle_slab->numItems - handle_slab->numFree) * handle_slab->itemSize;
    aio_cap += handle_slab->numItems * handle_slab->itemSize;
  }
  if (arena_slab) {
    aio_used += (arena_slab->numItems - arena_slab->numFree) * arena_slab->itemSize;
    aio_cap += arena_slab->numItems * arena_slab->itemSize;
  }

  n = snprintf(p, end - p,
    ",\"breakdown\":{\"gc_used\":%llu,\"gc_cap\":%llu,"
    "\"aio_used\":%llu,\"aio_cap\":%llu,"
    "\"scratch_used\":0,\"scratch_cap\":0,"
    "\"metrics_used\":0,\"metrics_cap\":0}}",
    (unsigned long long)gc_used,
    (unsigned long long)gc_total,
    (unsigned long long)aio_used,
    (unsigned long long)aio_cap);
  if (n > 0) p += n;

  valk_lval_t *result = valk_lval_str(buf);
  free(buf);
  return result;
#else
  UNUSED(sys_arg);
  return valk_lval_str("{}");
#endif
}

// ============================================================================
// REGISTRATION FUNCTION
// ============================================================================

void valk_register_metrics_builtins(valk_lenv_t *env) {
  // Counter builtins
  valk_lenv_put_builtin(env, "metrics/counter", valk_builtin_metrics_counter);
  valk_lenv_put_builtin(env, "metrics/counter-inc", valk_builtin_metrics_counter_inc);

  // Gauge builtins
  valk_lenv_put_builtin(env, "metrics/gauge", valk_builtin_metrics_gauge);
  valk_lenv_put_builtin(env, "metrics/gauge-set", valk_builtin_metrics_gauge_set);
  valk_lenv_put_builtin(env, "metrics/gauge-inc", valk_builtin_metrics_gauge_inc);
  valk_lenv_put_builtin(env, "metrics/gauge-dec", valk_builtin_metrics_gauge_dec);

  // Histogram builtins
  valk_lenv_put_builtin(env, "metrics/histogram", valk_builtin_metrics_histogram);
  valk_lenv_put_builtin(env, "metrics/histogram-observe", valk_builtin_metrics_histogram_observe);

  // Export builtins
  valk_lenv_put_builtin(env, "metrics/collect-delta", valk_builtin_metrics_collect_delta);
  valk_lenv_put_builtin(env, "metrics/delta-json", valk_builtin_metrics_delta_json);
  valk_lenv_put_builtin(env, "metrics/prometheus", valk_builtin_metrics_prometheus);
  valk_lenv_put_builtin(env, "metrics/json", valk_builtin_metrics_json);
  valk_lenv_put_builtin(env, "metrics/registry-json", valk_builtin_metrics_registry_json);

  // Diagnostics builtin
  valk_lenv_put_builtin(env, "aio/diagnostics-state-json",
                        valk_builtin_aio_diagnostics_state_json);

#ifdef VALK_METRICS_ENABLED
  valk_lenv_put_builtin(env, "aio/slab-buckets",
                        valk_builtin_aio_slab_buckets);
#endif
}
