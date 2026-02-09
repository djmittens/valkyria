#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "metrics_v2.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <sched.h>
#include <uv.h>

// ============================================================================
// System Lifecycle
// ============================================================================

static valk_system_t __system_storage = {0};
valk_system_t *valk_sys = &__system_storage;

static void __system_init_coordinator(valk_system_t *sys) {
  atomic_store(&sys->phase, VALK_GC_PHASE_IDLE);
  atomic_store(&sys->threads_registered, 0);
  sys->barrier_initialized = false;

  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    sys->threads[i].ctx = nullptr;
    sys->threads[i].active = false;
    sys->threads[i].wake_fn = nullptr;
    sys->threads[i].wake_ctx = nullptr;
    memset(&sys->threads[i].mark_queue, 0, sizeof(sys->threads[i].mark_queue));
  }

  atomic_store(&sys->parallel_cycles, 0);
  atomic_store(&sys->parallel_pause_us_total, 0);
}

// LCOV_EXCL_BR_START - system create/destroy defensive checks
valk_system_t *valk_system_create(valk_system_config_t *config) {
  valk_system_t *sys = calloc(1, sizeof(valk_system_t));
  if (!sys) return nullptr;

  __system_init_coordinator(sys);
  valk_handle_table_init(&sys->handle_table);
  pthread_mutex_init(&sys->subsystems_lock, nullptr);
  sys->subsystem_count = 0;
  atomic_store(&sys->shutting_down, false);
  sys->exit_code = 0;

  valk_system_config_t cfg = config ? *config : valk_system_config_default();
  sys->heap = valk_gc_heap_create(cfg.gc_heap_size);
  if (!sys->heap) {
    VALK_ERROR("Failed to create system GC heap");
    free(sys);
    return nullptr;
  }

  valk_metrics_registry_init();

  valk_sys = sys;
  sys->initialized = true;

  valk_system_register_thread(sys, nullptr, nullptr);

  VALK_INFO("System created: gc_heap_size=%llu", (unsigned long long)cfg.gc_heap_size);
  return sys;
}

void valk_system_destroy(valk_system_t *sys) {
  if (!sys) return;

  if (sys->heap) {
    valk_gc_heap_destroy(sys->heap);
    sys->heap = nullptr;
  }

  valk_handle_table_free(&sys->handle_table);

  if (sys->barrier_initialized) {
    valk_barrier_destroy(&sys->barrier);
  }

  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    valk_gc_mark_queue_destroy(&sys->threads[i].mark_queue);
  }

  pthread_mutex_destroy(&sys->subsystems_lock);

  sys->initialized = false;

  if (valk_sys == sys) {
    valk_sys = &__system_storage;
    memset(&__system_storage, 0, sizeof(__system_storage));
  }

  if (sys != &__system_storage) {
    free(sys);
  }
  VALK_INFO("System destroyed");
}

void valk_system_shutdown(valk_system_t *sys, u64 deadline_ms) {
  if (!sys) return;
  atomic_store(&sys->shutting_down, true);

  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++) {
    if (sys->subsystems[i].stop) {
      sys->subsystems[i].stop(sys->subsystems[i].ctx);
    }
  }
  pthread_mutex_unlock(&sys->subsystems_lock);

  u64 deadline_us = deadline_ms * 1000;
  u64 start = uv_hrtime() / 1000;
  while (atomic_load(&sys->threads_registered) > 1) {
    u64 now = uv_hrtime() / 1000;
    if (now - start >= deadline_us) {
      VALK_WARN("Shutdown deadline exceeded, %llu threads still registered",
                (unsigned long long)atomic_load(&sys->threads_registered));
      break;
    }
    usleep(1000);
  }

  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++) {
    if (sys->subsystems[i].wait) {
      sys->subsystems[i].wait(sys->subsystems[i].ctx);
    }
    if (sys->subsystems[i].destroy) {
      sys->subsystems[i].destroy(sys->subsystems[i].ctx);
    }
  }
  sys->subsystem_count = 0;
  pthread_mutex_unlock(&sys->subsystems_lock);

  VALK_INFO("System shutdown complete");
}

void valk_system_register_thread(valk_system_t *sys,
                                 void (*wake_fn)(void *), void *wake_ctx) {
  valk_mem_init_malloc();
  valk_thread_ctx.system = sys;
  valk_thread_ctx.heap = sys->heap;

  u64 idx = atomic_fetch_add(&sys->threads_registered, 1);
  if (idx >= VALK_SYSTEM_MAX_THREADS) {
    VALK_ERROR("Too many threads registered (max %d)", VALK_SYSTEM_MAX_THREADS);
    atomic_fetch_sub(&sys->threads_registered, 1);
    return;
  }

  valk_thread_ctx.gc_thread_id = idx;
  valk_thread_ctx.gc_registered = true;

  valk_thread_ctx.root_stack = malloc(sizeof(valk_lval_t*) * 256);
  valk_thread_ctx.root_stack_capacity = 256;
  valk_thread_ctx.root_stack_count = 0;

  sys->threads[idx].ctx = &valk_thread_ctx;
  sys->threads[idx].thread_id = pthread_self();
  sys->threads[idx].active = true;
  sys->threads[idx].wake_fn = wake_fn;
  sys->threads[idx].wake_ctx = wake_ctx;
  valk_gc_mark_queue_init(&sys->threads[idx].mark_queue);

  VALK_DEBUG("Thread registered: idx=%llu", (unsigned long long)idx);
}

void valk_system_unregister_thread(valk_system_t *sys) {
  if (!valk_thread_ctx.gc_registered) return;

  VALK_GC_SAFE_POINT();

  u64 idx = valk_thread_ctx.gc_thread_id;
  sys->threads[idx].active = false;
  sys->threads[idx].ctx = nullptr;
  sys->threads[idx].wake_fn = nullptr;
  sys->threads[idx].wake_ctx = nullptr;

  atomic_fetch_sub(&sys->threads_registered, 1);

  if (valk_thread_ctx.root_stack) {
    free(valk_thread_ctx.root_stack);
    valk_thread_ctx.root_stack = nullptr;
  }
  valk_thread_ctx.gc_registered = false;

  VALK_DEBUG("Thread unregistered: idx=%llu", (unsigned long long)idx);
}

void valk_system_add_subsystem(valk_system_t *sys,
                               void (*stop)(void *), void (*wait)(void *),
                               void (*destroy)(void *), void *ctx) {
  pthread_mutex_lock(&sys->subsystems_lock);
  if (sys->subsystem_count < VALK_SYSTEM_MAX_SUBSYSTEMS) {
    sys->subsystems[sys->subsystem_count++] = (valk_subsystem_t){
      .stop = stop, .wait = wait, .destroy = destroy, .ctx = ctx
    };
  } else {
    VALK_WARN("Max subsystems reached (%d)", VALK_SYSTEM_MAX_SUBSYSTEMS);
  }
  pthread_mutex_unlock(&sys->subsystems_lock);
}

void valk_system_remove_subsystem(valk_system_t *sys, void *ctx) {
  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++) {
    if (sys->subsystems[i].ctx == ctx) {
      sys->subsystems[i] = sys->subsystems[--sys->subsystem_count];
      break;
    }
  }
  pthread_mutex_unlock(&sys->subsystems_lock);
}

void valk_system_wake_threads(valk_system_t *sys) {
  u64 n = atomic_load(&sys->threads_registered);
  for (u64 i = 0; i < n && i < VALK_SYSTEM_MAX_THREADS; i++) {
    if (sys->threads[i].active && sys->threads[i].wake_fn) {
      sys->threads[i].wake_fn(sys->threads[i].wake_ctx);
    }
  }
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Parallel GC Infrastructure
// ============================================================================

void valk_barrier_init(valk_barrier_t* b, sz count) {
  pthread_mutex_init(&b->mutex, nullptr);
  pthread_cond_init(&b->cond, nullptr);
  atomic_store(&b->count, count);
  atomic_store(&b->waiting, 0);
  atomic_store(&b->phase, 0);
}

void valk_barrier_destroy(valk_barrier_t* b) {
  pthread_mutex_destroy(&b->mutex);
  pthread_cond_destroy(&b->cond);
}

void valk_barrier_reset(valk_barrier_t* b, sz count) {
  pthread_mutex_lock(&b->mutex);
  atomic_store(&b->count, count);
  atomic_store(&b->waiting, 0);
  pthread_mutex_unlock(&b->mutex);
}

void valk_barrier_wait(valk_barrier_t* b) {
  pthread_mutex_lock(&b->mutex);
  sz my_phase = atomic_load(&b->phase);
  sz waiting = atomic_fetch_add(&b->waiting, 1) + 1;
  sz count = atomic_load(&b->count);
  if (waiting == count) {
    atomic_store(&b->waiting, 0);
    atomic_fetch_add(&b->phase, 1);
    pthread_cond_broadcast(&b->cond);
  } else {
    while (atomic_load(&b->phase) == my_phase) {
      pthread_cond_wait(&b->cond, &b->mutex);
    }
  }
  pthread_mutex_unlock(&b->mutex);
}

// ============================================================================
// Mark Queue (thin wrappers around Chase-Lev deque)
// ============================================================================

void valk_gc_mark_queue_init(valk_gc_mark_queue_t* q) {
  valk_chase_lev_init(q, VALK_GC_MARK_QUEUE_INITIAL_SIZE);
}

void valk_gc_mark_queue_destroy(valk_gc_mark_queue_t* q) {
  valk_chase_lev_destroy(q);
}

void valk_gc_mark_queue_push(valk_gc_mark_queue_t* q, valk_lval_t* val) {
  valk_chase_lev_push(q, val);
}

valk_lval_t* valk_gc_mark_queue_pop(valk_gc_mark_queue_t* q) {
  void *v = valk_chase_lev_pop(q);
  if (v == VALK_CHASE_LEV_EMPTY) return nullptr;
  return v;
}

valk_lval_t* valk_gc_mark_queue_steal(valk_gc_mark_queue_t* q) {
  void *v = valk_chase_lev_steal(q);
  if (v == VALK_CHASE_LEV_EMPTY || v == VALK_CHASE_LEV_ABORT) return nullptr;
  return v;
}

bool valk_gc_mark_queue_empty(valk_gc_mark_queue_t* q) {
  return valk_chase_lev_empty(q);
}

// ============================================================================
// Legacy Wrappers (thin shims for old call sites)
// ============================================================================

// LCOV_EXCL_BR_START - legacy wrapper branch coverage
void valk_gc_thread_register(void) {
  valk_system_register_thread(valk_sys, nullptr, nullptr);
}

void valk_gc_thread_unregister(void) {
  valk_system_unregister_thread(valk_sys);
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Safe Point Slow Path
// ============================================================================

// LCOV_EXCL_START - safe point slow path requires STW coordination from parallel GC
void valk_gc_safe_point_slow(void) {
  valk_gc_phase_e phase = atomic_load(&valk_gc_coord.phase);

  if (phase == VALK_GC_PHASE_CHECKPOINT_REQUESTED) {
    valk_barrier_wait(&valk_gc_coord.barrier);
    valk_barrier_wait(&valk_gc_coord.barrier);
    return;
  }

  if (phase == VALK_GC_PHASE_STW_REQUESTED) {
    if (valk_thread_ctx.scratch && valk_thread_ctx.scratch->offset > 0 &&
        valk_thread_ctx.heap && valk_thread_ctx.root_env) {
      valk_checkpoint(valk_thread_ctx.scratch,
                      valk_thread_ctx.heap,
                      valk_thread_ctx.root_env);
    }

    valk_barrier_wait(&valk_gc_coord.barrier);
    valk_gc_participate_in_parallel_gc();
  }
}
// LCOV_EXCL_STOP

// ============================================================================
// Root Enumeration
// ============================================================================

// LCOV_EXCL_BR_START - defensive null checks in root iteration
void valk_gc_visit_thread_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  valk_thread_context_t *tc = &valk_thread_ctx;

  if (tc->root_stack == nullptr) return;

  for (u64 i = 0; i < tc->root_stack_count; i++) {
    if (tc->root_stack[i] != nullptr) {
      visitor(tc->root_stack[i], ctx);
    }
  }
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - defensive null checks in env root iteration
void valk_gc_visit_env_roots(valk_lenv_t *env, valk_gc_root_visitor_t visitor, void *ctx) {
  if (env == nullptr) return;

  for (u64 i = 0; i < env->vals.count; i++) {
    if (env->vals.items[i] != nullptr) {
      visitor(env->vals.items[i], ctx);
    }
  }

  valk_gc_visit_env_roots(env->parent, visitor, ctx);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - defensive null checks in global root iteration
void valk_gc_visit_global_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  valk_handle_table_visit(&valk_global_handle_table, visitor, ctx);

  for (u64 i = 0; i < VALK_GC_MAX_THREADS; i++) {
    if (valk_gc_coord.threads[i].active && valk_gc_coord.threads[i].ctx != nullptr) {
      valk_thread_context_t *tc = valk_gc_coord.threads[i].ctx;
      if (tc->root_env != nullptr) {
        valk_gc_visit_env_roots(tc->root_env, visitor, ctx);
      }
    }
  }
}
// LCOV_EXCL_BR_STOP

void valk_gc_set_hard_limit(valk_gc_heap_t* heap, sz limit) {
  if (!heap) return;
  sz used = valk_gc_heap_used_bytes(heap);
  if (limit < used) {
    VALK_WARN("Cannot set hard limit below current usage (%zu < %zu)", limit, used);
    return;
  }
  heap->hard_limit = limit;
  heap->soft_limit = (limit * 3) / 4;
}

void valk_gc_set_root(valk_gc_heap_t* heap, valk_lenv_t* root_env) {
  if (heap) heap->root_env = root_env;
}

u8 valk_gc_heap_usage_pct(valk_gc_heap_t* heap) {
  if (!heap || heap->hard_limit == 0) return 0;
  sz used = valk_gc_heap_used_bytes(heap);
  u8 pct = (u8)((used * 100) / heap->hard_limit);
  return pct > 100 ? 100 : pct;
}

void valk_gc_set_thresholds(valk_gc_heap_t* heap,
                            u8 threshold_pct,
                            u8 target_pct,
                            u32 min_interval_ms) {
  if (!heap) return;
  heap->gc_threshold_pct = threshold_pct > 0 ? threshold_pct : 75;
  heap->gc_target_pct = target_pct > 0 ? target_pct : 50;
  heap->min_gc_interval_ms = min_interval_ms;
}

// LCOV_EXCL_BR_START - rate limiting branches depend on timing state
bool valk_gc_should_collect(valk_gc_heap_t* heap) {
  if (!heap) return false;
  u8 usage_pct = valk_gc_heap_usage_pct(heap);
  if (usage_pct < heap->gc_threshold_pct) return false;
  if (heap->min_gc_interval_ms > 0 && heap->last_gc_time_us > 0) {
    u64 now_us = uv_hrtime() / 1000;
    u64 elapsed_ms = (now_us - heap->last_gc_time_us) / 1000;
    if (elapsed_ms < heap->min_gc_interval_ms) return false;
  }
  return true;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Pointer Map - hashmap for src->dst tracking during evacuation
// ============================================================================

// LCOV_EXCL_BR_START - internal hash map operations with collision handling
static inline sz valk_ptr_hash(void *ptr) {
  uptr p = (uptr)ptr;
  p = (p ^ (p >> 30)) * 0xbf58476d1ce4e5b9ULL;
  p = (p ^ (p >> 27)) * 0x94d049bb133111ebULL;
  return (sz)(p ^ (p >> 31));
}

void valk_ptr_map_init(valk_ptr_map_t *map) {
  map->capacity = VALK_PTR_MAP_INIT_CAPACITY;
  map->count = 0;
  map->entries = calloc(map->capacity, sizeof(valk_ptr_map_entry_t));
}

void valk_ptr_map_free(valk_ptr_map_t *map) {
  if (map->entries) {
    free(map->entries);
    map->entries = nullptr;
  }
  map->count = 0;
  map->capacity = 0;
}

static void valk_ptr_map_grow(valk_ptr_map_t *map) {
  sz old_cap = map->capacity;
  valk_ptr_map_entry_t *old_entries = map->entries;

  map->capacity = old_cap * 2;
  map->entries = calloc(map->capacity, sizeof(valk_ptr_map_entry_t));
  map->count = 0;

  for (sz i = 0; i < old_cap; i++) {
    if (old_entries[i].src != nullptr) {
      valk_ptr_map_put(map, old_entries[i].src, old_entries[i].dst);
    }
  }

  free(old_entries);
}

void valk_ptr_map_put(valk_ptr_map_t *map, void *src, void *dst) {
  if ((float)map->count / map->capacity >= VALK_PTR_MAP_LOAD_FACTOR) {
    valk_ptr_map_grow(map);
  }

  sz idx = valk_ptr_hash(src) % map->capacity;
  while (map->entries[idx].src != nullptr) {
    if (map->entries[idx].src == src) {
      map->entries[idx].dst = dst;
      return;
    }
    idx = (idx + 1) % map->capacity;
  }

  map->entries[idx].src = src;
  map->entries[idx].dst = dst;
  map->count++;
}

void *valk_ptr_map_get(valk_ptr_map_t *map, void *src) {
  if (map->count == 0) return nullptr;

  sz idx = valk_ptr_hash(src) % map->capacity;
  sz start = idx;

  while (map->entries[idx].src != nullptr) {
    if (map->entries[idx].src == src) {
      return map->entries[idx].dst;
    }
    idx = (idx + 1) % map->capacity;
    if (idx == start) break;
  }

  return nullptr;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Handle Table
// ============================================================================

// LCOV_EXCL_BR_START - handle table internal defensive checks


void valk_handle_table_init(valk_handle_table_t *table) {
  pthread_mutex_init(&table->lock, nullptr);
  table->capacity = VALK_HANDLE_TABLE_INIT_SIZE;
  table->count = 0;
  table->free_head = UINT32_MAX;
  table->slots = calloc(table->capacity, sizeof(valk_lval_t *));
  table->generations = calloc(table->capacity, sizeof(u32));
}

void valk_handle_table_free(valk_handle_table_t *table) {
  pthread_mutex_lock(&table->lock);
  if (table->slots) {
    free(table->slots);
    table->slots = nullptr;
  }
  if (table->generations) {
    free(table->generations);
    table->generations = nullptr;
  }
  table->capacity = 0;
  table->count = 0;
  table->free_head = UINT32_MAX;
  pthread_mutex_unlock(&table->lock);
  pthread_mutex_destroy(&table->lock);
}

static void valk_handle_table_grow(valk_handle_table_t *table) {
  u32 old_cap = table->capacity;
  u32 new_cap = old_cap * 2;

  valk_lval_t **new_slots = realloc(table->slots, new_cap * sizeof(valk_lval_t *));
  u32 *new_gens = realloc(table->generations, new_cap * sizeof(u32));

  // LCOV_EXCL_BR_START - handle table realloc OOM
  if (!new_slots || !new_gens) {
    VALK_ERROR("Failed to grow handle table");
    return;
  }
  // LCOV_EXCL_BR_STOP

  table->slots = new_slots;
  table->generations = new_gens;

  for (u32 i = old_cap; i < new_cap; i++) {
    table->slots[i] = nullptr;
    table->generations[i] = 0;
  }

  table->capacity = new_cap;
}

valk_handle_t valk_handle_create(valk_handle_table_t *table, valk_lval_t *val) {
  pthread_mutex_lock(&table->lock);

  u32 idx;
  if (table->free_head != UINT32_MAX) {
    idx = table->free_head;
    table->free_head = (u32)(uptr)table->slots[idx];
  } else {
    if (table->count >= table->capacity) {
      valk_handle_table_grow(table);
    }
    idx = table->count++;
  }

  table->slots[idx] = val;
  table->generations[idx]++;

  valk_handle_t h = {.index = idx, .generation = table->generations[idx]};
  pthread_mutex_unlock(&table->lock);
  return h;
}

valk_lval_t *valk_handle_resolve(valk_handle_table_t *table, valk_handle_t h) {
  pthread_mutex_lock(&table->lock);
  valk_lval_t *result = nullptr;
  if (h.index < table->capacity && table->generations[h.index] == h.generation) {
    result = table->slots[h.index];
  }
  pthread_mutex_unlock(&table->lock);
  return result;
}

void valk_handle_release(valk_handle_table_t *table, valk_handle_t h) {
  pthread_mutex_lock(&table->lock);
  if (h.index < table->capacity && table->generations[h.index] == h.generation) {
    table->slots[h.index] = (valk_lval_t *)(uptr)table->free_head;
    table->free_head = h.index;
  }
  pthread_mutex_unlock(&table->lock);
}

void valk_handle_table_visit(valk_handle_table_t *table,
                             void (*visitor)(valk_lval_t*, void*), void *ctx) {
  if (!table || !table->slots) return;

  pthread_mutex_lock(&table->lock);
  for (u32 i = 0; i < table->count; i++) {
    valk_lval_t *val = table->slots[i];
    if (val != nullptr && ((uptr)val > table->capacity)) {
      visitor(val, ctx);
    }
  }
  pthread_mutex_unlock(&table->lock);
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Fork Safety - Reset global state after fork() in child process
// ============================================================================

// LCOV_EXCL_START - fork safety function requires actual fork() which is unsafe in test harness
void valk_gc_reset_after_fork(void) {
  if (valk_sys) {
    __system_init_coordinator(valk_sys);
  }

  valk_gc_mark_reset_after_fork();
  valk_gc_heap_reset_after_fork();

  valk_thread_ctx.heap = nullptr;
  valk_thread_ctx.system = nullptr;
  valk_thread_ctx.scratch = nullptr;
  valk_thread_ctx.root_env = nullptr;
  valk_thread_ctx.gc_registered = false;
  valk_thread_ctx.gc_thread_id = 0;
  valk_thread_ctx.eval_stack = nullptr;
  valk_thread_ctx.eval_expr = nullptr;
  valk_thread_ctx.eval_value = nullptr;

  if (valk_thread_ctx.root_stack) {
    free(valk_thread_ctx.root_stack);
    valk_thread_ctx.root_stack = nullptr;
  }
  valk_thread_ctx.root_stack_count = 0;
  valk_thread_ctx.root_stack_capacity = 0;
}
// LCOV_EXCL_STOP
