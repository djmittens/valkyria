// src/pool_metrics.h
// Pool Metrics Factory - Standard metrics for memory pools (slabs, arenas)
#ifndef VALK_POOL_METRICS_H
#define VALK_POOL_METRICS_H

#include "metrics_v2.h"
#include <stddef.h>

// Forward declarations (avoid including full headers)
struct valk_slab;
struct valk_mem_arena;

// ============================================================================
// POOL METRICS BUNDLE
// ============================================================================

// Standard metrics for any memory pool
// These are marked as persistent (non-evictable) at creation
typedef struct {
  valk_gauge_v2_t *used;      // Current slots/bytes in use
  valk_gauge_v2_t *total;     // Total capacity (slots or bytes)
  valk_gauge_v2_t *peak;      // High water mark
  valk_counter_v2_t *overflow; // Overflow/fallback count
  const char *pool_name;      // For debugging
} valk_pool_metrics_t;

// ============================================================================
// FACTORY API
// ============================================================================

// Create standard metrics for a pool with pool={name} label
// All 4 metrics are created and marked as persistent (non-evictable)
// Returns true on success, false if registry is full
// Metric names:
//   pool_used{pool="name"}
//   pool_total{pool="name"}
//   pool_peak{pool="name"}
//   pool_overflow{pool="name"}
bool valk_pool_metrics_init(valk_pool_metrics_t *m, const char *pool_name);

// Initialize with custom metric names (for existing metric naming conventions)
// prefix: e.g., "slab" -> slab_used, slab_total, slab_peak, slab_overflow
bool valk_pool_metrics_init_custom(valk_pool_metrics_t *m,
                                    const char *pool_name,
                                    const char *prefix);

// ============================================================================
// UPDATE HELPERS
// ============================================================================

// Update metrics from slab allocator state
// slab fields: numItems (total), numFree, peakUsed, overflowCount
void valk_pool_metrics_update_slab(valk_pool_metrics_t *m,
                                    u64 total_slots,
                                    u64 free_slots,
                                    u64 peak_used,
                                    u64 overflow_count);

// Update metrics from arena allocator state
// arena fields: capacity, offset, stats.high_water_mark, stats.overflow_fallbacks
void valk_pool_metrics_update_arena(valk_pool_metrics_t *m,
                                     u64 capacity,
                                     u64 used,
                                     u64 high_water_mark,
                                     u64 overflow_count);

// Update metrics with raw values (generic)
void valk_pool_metrics_update(valk_pool_metrics_t *m,
                               i64 used,
                               i64 total,
                               i64 peak,
                               u64 overflow);

// ============================================================================
// CONVENIENCE MACROS
// ============================================================================

// Initialize pool metrics with automatic naming from variable
#define VALK_POOL_METRICS_INIT(m, name) \
  valk_pool_metrics_init((m), (name))

// Update from slab struct directly (requires including memory.h)
#define VALK_POOL_METRICS_UPDATE_SLAB(m, slab) \
  valk_pool_metrics_update_slab((m), \
    (slab)->numItems, \
    (slab)->numFree, \
    (slab)->peakUsed, \
    (slab)->overflowCount)

#endif // VALK_POOL_METRICS_H
