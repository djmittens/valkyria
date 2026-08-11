#include "gc.h"
#include "parser.h"
#include "conc_map.h"
#include "memory.h"
#include "metrics_v2.h"
#include "eval_internal.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <sched.h>
#include <unistd.h>
#include <uv.h>

// ============================================================================
// System Lifecycle
// ============================================================================

static valk_system_t __system_storage = {0};
valk_system_t *valk_sys = &__system_storage;

static void __system_init_coordinator(valk_system_t *sys) {
  atomic_store(&sys->phase, VALK_GC_PHASE_IDLE);
  atomic_store(&sys->threads_registered, 0);
  pthread_mutex_init(&sys->thread_mutex, nullptr);
  sys->thread_free_count = 0;
  sys->next_fresh_idx = 0;
  sys->barrier_initialized = false;

  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    sys->threads[i].ctx = nullptr;
    sys->threads[i].active = false;
    sys->threads[i].wake_fn = nullptr;
    sys->threads[i].wake_ctx = nullptr;
    memset(&sys->threads[i].mark_queue, 0, sizeof(sys->threads[i].mark_queue));
  }

  atomic_store(&sys->parallel_cycles, 0);
  atomic_store(&sys->parallel_pause_ns_total, 0);
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
  pthread_mutex_destroy(&sys->thread_mutex);

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

void valk_system_initiate_shutdown(valk_system_t *sys, int exit_code) {
  if (!sys) return;
  sys->exit_code = exit_code;
  atomic_store(&sys->shutting_down, true);

  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++) {
    if (sys->subsystems[i].stop)
      sys->subsystems[i].stop(sys->subsystems[i].ctx);
  }
  pthread_mutex_unlock(&sys->subsystems_lock);
}

void valk_system_shutdown(valk_system_t *sys, u64 deadline_ms) {
  if (!sys) return;
  valk_system_initiate_shutdown(sys, sys->exit_code);

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

  pthread_mutex_lock(&sys->thread_mutex);

  u64 idx;
  if (sys->thread_free_count > 0) {
    idx = sys->thread_free_list[--sys->thread_free_count];
  } else {
    idx = sys->next_fresh_idx;
    if (idx >= VALK_SYSTEM_MAX_THREADS) {
      pthread_mutex_unlock(&sys->thread_mutex);
      VALK_ERROR("Too many threads registered (max %d)", VALK_SYSTEM_MAX_THREADS);
      return;
    }
    sys->next_fresh_idx++;
  }

  // Fully initialize the slot and thread context BEFORE making the thread
  // visible (active=true / count increment). Stealers and the termination
  // scan may touch the mark queue of any active slot at any time, and the
  // coordinator may flag any active thread the instant the mutex drops.
  valk_thread_ctx.gc_thread_id = idx;
  valk_thread_ctx.gc_registered = true;
  atomic_store(&valk_thread_ctx.safepoint_flags, 0);
  valk_thread_ctx.root_stack = malloc(sizeof(valk_lval_t*) * 256);
  valk_thread_ctx.root_stack_capacity = 256;
  valk_thread_ctx.root_stack_count = 0;
  valk_thread_ctx.env_root_stack = malloc(sizeof(valk_lenv_t*) * 256);
  valk_thread_ctx.env_root_stack_capacity = 256;
  valk_thread_ctx.env_root_stack_count = 0;
  valk_gc_mark_queue_init(&sys->threads[idx].mark_queue);

  sys->threads[idx].ctx = &valk_thread_ctx;
  sys->threads[idx].thread_id = pthread_self();
  sys->threads[idx].wake_fn = wake_fn;
  sys->threads[idx].wake_ctx = wake_ctx;

  // A GC cycle in flight froze its participant set without us. We are not
  // counted in its barriers, so we must not run until it finishes: self-set
  // the STW flag (our stw_epoch != sys epoch marks us as a late registrant,
  // so the safepoint slow path waits for IDLE instead of joining barriers).
  if (atomic_load_explicit(&sys->phase, memory_order_acquire) !=
      VALK_GC_PHASE_IDLE) {
    atomic_store(&valk_thread_ctx.stw_epoch,
                 atomic_load(&sys->stw_epoch) - 1);
    atomic_fetch_or_explicit(&valk_thread_ctx.safepoint_flags, VALK_SP_STW,
                              memory_order_release);
  }

  sys->threads[idx].active = true;
  atomic_fetch_add(&sys->threads_registered, 1);

  pthread_mutex_unlock(&sys->thread_mutex);

  VALK_DEBUG("Thread registered: idx=%llu", (unsigned long long)idx);
}

void valk_system_unregister_thread(valk_system_t *sys) {
  if (!valk_thread_ctx.gc_registered) return;

  u64 idx = valk_thread_ctx.gc_thread_id;

  for (;;) {
    VALK_GC_SAFE_POINT();

    pthread_mutex_lock(&sys->thread_mutex);

    valk_gc_phase_e cur_phase = atomic_load_explicit(&sys->phase,
                                                      memory_order_acquire);
    if (cur_phase != VALK_GC_PHASE_IDLE) {
      pthread_mutex_unlock(&sys->thread_mutex);
      sched_yield();
      continue;
    }

    sys->threads[idx].active = false;
    sys->threads[idx].ctx = nullptr;
    sys->threads[idx].wake_fn = nullptr;
    sys->threads[idx].wake_ctx = nullptr;
    // Phase is IDLE and we hold thread_mutex: no marker or stealer can be
    // touching this queue. Registration re-inits it on slot reuse.
    valk_gc_mark_queue_destroy(&sys->threads[idx].mark_queue);
    atomic_fetch_sub(&sys->threads_registered, 1);
    sys->thread_free_list[sys->thread_free_count++] = idx;

    pthread_mutex_unlock(&sys->thread_mutex);
    break;
  }

  if (valk_thread_ctx.root_stack) {
    free(valk_thread_ctx.root_stack);
    valk_thread_ctx.root_stack = nullptr;
  }
  if (valk_thread_ctx.env_root_stack) {
    free(valk_thread_ctx.env_root_stack);
    valk_thread_ctx.env_root_stack = nullptr;
    valk_thread_ctx.env_root_stack_count = 0;
    valk_thread_ctx.env_root_stack_capacity = 0;
  }
  valk_gc_tlab_release_thread();
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
  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
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

void valk_gc_mark_queue_reset(valk_gc_mark_queue_t* q) {
  valk_chase_lev_reset(q);
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

valk_lval_t* valk_gc_mark_queue_pop_solo(valk_gc_mark_queue_t* q) {
  void *v = valk_chase_lev_pop_solo(q);
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
  u32 flags = atomic_load_explicit(&valk_thread_ctx.safepoint_flags,
                                    memory_order_acquire);

  if (flags & VALK_SP_STW) {
    atomic_fetch_and(&valk_thread_ctx.safepoint_flags, ~(u32)VALK_SP_STW);

    for (;;) {
      valk_gc_phase_e phase = atomic_load_explicit(&valk_sys->phase,
                                                     memory_order_acquire);
      if (phase == VALK_GC_PHASE_IDLE) return;

      u64 my_epoch = atomic_load(&valk_thread_ctx.stw_epoch);
      u64 sys_epoch = atomic_load(&valk_sys->stw_epoch);

      if (my_epoch == sys_epoch) {
        // Counted participant: the coordinator froze us into this cycle's
        // barriers. PREPARING resolves to STW_REQUESTED; the coordinator
        // cannot advance past STW_REQUESTED until we join.
        if (phase == VALK_GC_PHASE_STW_REQUESTED) {
          valk_barrier_wait(&valk_sys->barrier);
          valk_gc_participate_in_parallel_gc();
          return;
        }
        sched_yield();
        continue;
      }

      // Late registrant: not in this cycle's barrier count. Wait until the
      // cycle finishes (phase IDLE) or a new cycle counts us (epoch match).
      sched_yield();
    }
  }

  if (flags & VALK_SP_GC_COLLECT) {
    atomic_fetch_and(&valk_thread_ctx.safepoint_flags, ~(u32)VALK_SP_GC_COLLECT);
    valk_gc_heap_t *heap = valk_thread_ctx.heap;
    if (heap) {
      valk_gc_heap_collect(heap);
      // Do NOT clear VALK_SP_STW here. The collect above set it on this
      // thread (request_stw flags every registered thread, including the
      // coordinator); that stale self-flag is absorbed harmlessly by the
      // STW branch at the next safepoint (phase is IDLE by then). But a
      // NEW cycle started by another thread in the window after collect
      // returns also sets the flag — clearing it here erased that cycle's
      // flag while its coordinator counted us as a participant, and the
      // barrier waited forever for a thread parked in epoll (observed as
      // the test runner deadlocking with 24/25 threads at the barrier).
    }
  }
}
// LCOV_EXCL_STOP

// ============================================================================
// Root Enumeration
// ============================================================================

// ============================================================================
// Remembered Set — mutable immortals referencing GC-heap data
// ============================================================================
// Image-baked (immortal) lvals can be MUTATED at runtime: a dict lval
// serialized into the image gets grown by dict/set! and its data block moves
// onto the GC heap. The marker skips immortal lvals entirely, so those heap
// blocks/values have no other reference and are swept while live (observed
// as munmapped dict blocks under the LSP). Classic old-gen -> young-gen
// pointer problem; the write barrier in the dict builtins registers mutated
// immortal lvals here, and rank-0 marks their children every cycle. Entries
// are immortal so they are never removed; the set stays small (distinct
// image dicts mutated at runtime).

#define VALK_REMEMBERED_MAX 1024
static pthread_mutex_t __remembered_lock = PTHREAD_MUTEX_INITIALIZER;
static valk_lval_t *__remembered[VALK_REMEMBERED_MAX];
static u64 __remembered_count = 0;

void valk_gc_remember_immortal(valk_lval_t *v) {
  if (!v) return;
  pthread_mutex_lock(&__remembered_lock);
  for (u64 i = 0; i < __remembered_count; i++) {
    if (__remembered[i] == v) {
      pthread_mutex_unlock(&__remembered_lock);
      return;
    }
  }
  // LCOV_EXCL_START - remembered set overflow requires >1024 distinct mutated immortals
  if (__remembered_count >= VALK_REMEMBERED_MAX) {
    VALK_ERROR("GC remembered set full; immortal %p not tracked", (void *)v);
    pthread_mutex_unlock(&__remembered_lock);
    return;
  }
  // LCOV_EXCL_STOP
  __remembered[__remembered_count++] = v;
  pthread_mutex_unlock(&__remembered_lock);
}

void valk_gc_visit_remembered(valk_gc_root_visitor_t visitor, void *ctx) {
  pthread_mutex_lock(&__remembered_lock);
  for (u64 i = 0; i < __remembered_count; i++) {
    visitor(__remembered[i], ctx);
  }
  pthread_mutex_unlock(&__remembered_lock);
}

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
typedef struct {
  valk_gc_root_visitor_t visitor;
  void *ctx;
} valk_env_root_visit_t;

static void valk_env_root_cmap_cb(char *key, _Atomic(valk_lval_t *) *slot,
                                  void *ctx) {
  (void)key;
  valk_env_root_visit_t *v = ctx;
  valk_lval_t *val = atomic_load(slot);
  if (val != nullptr) v->visitor(val, v->ctx);
}

void valk_gc_visit_env_roots(valk_lenv_t *env, valk_gc_root_visitor_t visitor, void *ctx) {
  for (; env != nullptr; env = env->parent) {
    if (env->cmap) {
      valk_env_root_visit_t v = {.visitor = visitor, .ctx = ctx};
      valk_cmap_foreach((valk_cmap_t *)env->cmap, valk_env_root_cmap_cb, &v);
    }

    for (u64 i = 0; i < env->vals.count; i++) {
      if (env->vals.items[i] != nullptr) {
        visitor(env->vals.items[i], ctx);
      }
    }
  }
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - defensive null checks in global root iteration
void valk_gc_visit_global_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  valk_handle_table_visit(&valk_sys->handle_table, visitor, ctx);

  extern valk_lenv_t *valk_macro_env(void);
  valk_lenv_t *menv = valk_macro_env();
  if (menv) valk_gc_visit_env_roots(menv, visitor, ctx);

  extern void valk_parse_cache_visit_roots(valk_gc_root_visitor_t, void *);
  valk_parse_cache_visit_roots(visitor, ctx);

  // thread_mutex: late registrants may mutate the registry concurrently
  // with this scan (they are excluded from the cycle but not from
  // registering). Their critical section is bounded and never waits on GC.
  pthread_mutex_lock(&valk_sys->thread_mutex);
  for (u64 i = 0; i < VALK_GC_MAX_THREADS; i++) {
    if (valk_sys->threads[i].active && valk_sys->threads[i].ctx != nullptr) {
      valk_thread_context_t *tc = valk_sys->threads[i].ctx;
      valk_lenv_t *root_env = atomic_load(&tc->root_env);
      if (root_env != nullptr) {
        valk_gc_visit_env_roots(root_env, visitor, ctx);
      }
    }
  }
  pthread_mutex_unlock(&valk_sys->thread_mutex);
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
                            u8 target_pct) {
  if (!heap) return;
  heap->gc_threshold_pct = threshold_pct > 0 ? threshold_pct : 75;
  heap->gc_target_pct = target_pct > 0 ? target_pct : 50;
}

bool valk_gc_should_collect(valk_gc_heap_t* heap) {
  if (!heap) return false;

  // Primary: growth relative to the live set surviving the last collection.
  // Pause time and RSS stay proportional to live data regardless of the
  // configured hard limit (see VALK_GC_GROWTH_FACTOR in gc_heap.h).
  sz used = valk_gc_heap_used_bytes(heap);
  sz trigger = heap->live_after_gc * VALK_GC_GROWTH_FACTOR;
  if (trigger < VALK_GC_MIN_COLLECT_BYTES) trigger = VALK_GC_MIN_COLLECT_BYTES;
  if (used >= trigger) return true;

  // Backstop: percent of hard limit (also the only trigger before the
  // first collection establishes a live-set baseline on tiny heaps).
  return valk_gc_heap_usage_pct(heap) >= heap->gc_threshold_pct;
}

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
  table->next_free = calloc(table->capacity, sizeof(u32));
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
  if (table->next_free) {
    free(table->next_free);
    table->next_free = nullptr;
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
  u32 *new_free = realloc(table->next_free, new_cap * sizeof(u32));

  // LCOV_EXCL_BR_START - handle table realloc OOM
  if (!new_slots || !new_gens || !new_free) {
    VALK_ERROR("Failed to grow handle table");
    return;
  }
  // LCOV_EXCL_BR_STOP

  table->slots = new_slots;
  table->generations = new_gens;
  table->next_free = new_free;

  for (u32 i = old_cap; i < new_cap; i++) {
    table->slots[i] = nullptr;
    table->generations[i] = 0;
    table->next_free[i] = 0;
  }

  table->capacity = new_cap;
}

valk_handle_t valk_handle_create(valk_handle_table_t *table, valk_lval_t *val) {
  pthread_mutex_lock(&table->lock);

  u32 idx;
  if (table->free_head != UINT32_MAX) {
    idx = table->free_head;
    table->free_head = table->next_free[idx];
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
    table->slots[h.index] = nullptr;
    table->next_free[h.index] = table->free_head;
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
    if (val != nullptr) {
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

  if (valk_thread_ctx.env_root_stack) {
    free(valk_thread_ctx.env_root_stack);
    valk_thread_ctx.env_root_stack = nullptr;
  }
  valk_thread_ctx.env_root_stack_count = 0;
  valk_thread_ctx.env_root_stack_capacity = 0;
}
// LCOV_EXCL_STOP

void valk_gc_root_push_fn(valk_lval_t *val) {
  valk_gc_root_push(val);
}

sz valk_gc_root_save(void) {
  return valk_thread_ctx.root_stack_count;
}

void valk_gc_root_restore(sz count) {
  valk_thread_ctx.root_stack_count = count;
}

// Env-root stack: see the field comment in memory.h. Called from compiled
// function prologues and the interpreter's call-env construction.
void valk_gc_env_root_push(valk_lenv_t *env) {
  valk_thread_context_t *ctx = &valk_thread_ctx;
  if (ctx->env_root_stack == nullptr) return;
  if (ctx->env_root_stack_count >= ctx->env_root_stack_capacity) {
    ctx->env_root_stack_capacity *= 2;
    ctx->env_root_stack = realloc(ctx->env_root_stack,
        sizeof(valk_lenv_t*) * ctx->env_root_stack_capacity);
  }
  ctx->env_root_stack[ctx->env_root_stack_count++] = env;
}

sz valk_gc_env_root_save(void) {
  return valk_thread_ctx.env_root_stack_count;
}

void valk_gc_env_root_restore(sz count) {
  valk_thread_ctx.env_root_stack_count = count;
}

void valk_gc_safepoint_fn(void) {
  VALK_GC_SAFE_POINT();
}
