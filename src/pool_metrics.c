// src/pool_metrics.c
// Pool Metrics Factory implementation
#include "pool_metrics.h"
#include <string.h>
#include <stdio.h>
#include <stdatomic.h>

// ============================================================================
// FACTORY IMPLEMENTATION
// ============================================================================

bool valk_pool_metrics_init(valk_pool_metrics_t *m, const char *pool_name) {
  return valk_pool_metrics_init_custom(m, pool_name, "pool");
}

bool valk_pool_metrics_init_custom(valk_pool_metrics_t *m,
                                    const char *pool_name,
                                    const char *prefix) {
  if (!m || !pool_name || !prefix) return false;

  memset(m, 0, sizeof(*m));
  m->pool_name = pool_name;

  // Build label set with pool name
  valk_label_set_v2_t labels = {
    .labels = {{.key = "pool", .value = pool_name}},
    .count = 1,
    .hash = 0  // Will be computed by get_or_create
  };

  // Build metric names
  char name_used[64], name_total[64], name_peak[64], name_overflow[64];
  snprintf(name_used, sizeof(name_used), "%s_used", prefix);
  snprintf(name_total, sizeof(name_total), "%s_total", prefix);
  snprintf(name_peak, sizeof(name_peak), "%s_peak", prefix);
  snprintf(name_overflow, sizeof(name_overflow), "%s_overflow", prefix);

  // Create gauges for used, total, peak
  m->used = valk_gauge_get_or_create(name_used,
    "Current items/bytes in use in this pool", &labels);
  if (!m->used) return false; // LCOV_EXCL_BR_LINE: OOM in metric registry
  valk_gauge_set_persistent(m->used);

  m->total = valk_gauge_get_or_create(name_total,
    "Total capacity of this pool (slots or bytes)", &labels);
  if (!m->total) return false; // LCOV_EXCL_BR_LINE: OOM in metric registry
  valk_gauge_set_persistent(m->total);

  m->peak = valk_gauge_get_or_create(name_peak,
    "High water mark - maximum concurrent usage observed", &labels);
  if (!m->peak) return false; // LCOV_EXCL_BR_LINE: OOM in metric registry
  valk_gauge_set_persistent(m->peak);

  // Create counter for overflow
  m->overflow = valk_counter_get_or_create(name_overflow,
    "Number of allocation overflows/fallbacks to backup allocator", &labels);
  if (!m->overflow) return false; // LCOV_EXCL_BR_LINE: OOM in metric registry
  valk_counter_set_persistent(m->overflow);

  return true;
}

// ============================================================================
// UPDATE HELPERS
// ============================================================================

void valk_pool_metrics_update_slab(valk_pool_metrics_t *m,
                                    u64 total_slots,
                                    u64 free_slots,
                                    u64 peak_used,
                                    u64 overflow_count) {
  if (!m) return;

  u64 used = total_slots - free_slots;
  valk_pool_metrics_update(m,
    (i64)used,
    (i64)total_slots,
    (i64)peak_used,
    (u64)overflow_count);
}

void valk_pool_metrics_update_arena(valk_pool_metrics_t *m,
                                     u64 capacity,
                                     u64 used,
                                     u64 high_water_mark,
                                     u64 overflow_count) {
  if (!m) return;

  valk_pool_metrics_update(m,
    (i64)used,
    (i64)capacity,
    (i64)high_water_mark,
    (u64)overflow_count);
}

void valk_pool_metrics_update(valk_pool_metrics_t *m,
                               i64 used,
                               i64 total,
                               i64 peak,
                               u64 overflow) {
  if (!m) return;

  // LCOV_EXCL_START: Defensive null checks - metrics always valid after init
  if (m->used) valk_gauge_v2_set(m->used, used);
  if (m->total) valk_gauge_v2_set(m->total, total);
  if (m->peak) valk_gauge_v2_set(m->peak, peak);
  // LCOV_EXCL_STOP

  // Counter: set to absolute value (counters only increment, so we track delta)
  if (m->overflow) {
    u64 current = atomic_load(&m->overflow->value);
    if (overflow > current) {
      valk_counter_v2_add(m->overflow, overflow - current);
    }
  }
}
