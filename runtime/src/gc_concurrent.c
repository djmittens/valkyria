#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <uv.h>

// ============================================================================
// Concurrent Mark Coordinator (SATB)
// ============================================================================
// A dedicated marker thread traces the heap while mutators run. The cycle:
//
//   pause 1 (CONC_START): rendezvous; every mutator snapshots its own roots
//     into its mark queue and blackens its TLAB remainders; the marker scans
//     global roots; SATB barrier goes active; mutators resume.
//   concurrent: the marker drains all queues (work-stealing) and consumes
//     SATB overflow chunks; mutators log overwritten pointers (SATB) and
//     allocate black (batch-blackened TLAB refills, black large objects).
//   pause 2 (CONC_FINAL): rendezvous; every participant flushes its SATB
//     partial buffer into its own queue; parallel OWST drain of the residue;
//     parallel sweep; page-list fixup; IDLE.
//
// STW time is pause 1 + pause 2; the trace runs concurrently.

// LCOV_EXCL_START - concurrent GC coordination requires multi-threaded timing

_Atomic bool valk_gc_satb_active = false;

// ============================================================================
// SATB Buffers
// ============================================================================

#define VALK_SATB_LOCAL_CAP 256
#define VALK_SATB_CHUNK_CAP 256

typedef struct valk_satb_chunk {
  struct valk_satb_chunk *next;
  u32 count;
  valk_lval_t *vals[VALK_SATB_CHUNK_CAP];
} valk_satb_chunk_t;

static pthread_mutex_t __satb_lock = PTHREAD_MUTEX_INITIALIZER;
static valk_satb_chunk_t *__satb_chunks = nullptr;
// Envs logged for the marker (overwritten parents, evacuation-shared envs).
// The fixed array gives cheap dedup for the common case; overflow spills
// into a chunk list. The old code SILENTLY DROPPED overflow - dropping an
// env log is unsound the same way dropping a value log is: the env (or its
// bindings) can be reachable only through born-black objects and gets swept
// while live.
#define VALK_SATB_ENV_MAX 256
static valk_lenv_t *__satb_envs[VALK_SATB_ENV_MAX];
static u32 __satb_env_count = 0;

typedef struct valk_satb_env_chunk {
  struct valk_satb_env_chunk *next;
  u32 count;
  valk_lenv_t *envs[VALK_SATB_CHUNK_CAP];
} valk_satb_env_chunk_t;

static valk_satb_env_chunk_t *__satb_env_chunks = nullptr;

static void __satb_push_chunk_locked(valk_lval_t **vals, u32 count) {
  valk_satb_chunk_t *chunk = malloc(sizeof(valk_satb_chunk_t));
  VALK_ASSERT(chunk != nullptr, "SATB chunk allocation failed"); // dropping entries is unsound
  chunk->count = count;
  memcpy(chunk->vals, vals, count * sizeof(valk_lval_t *));
  chunk->next = __satb_chunks;
  __satb_chunks = chunk;
}

// Only heap-resident objects may be logged: old values living in scratch
// arenas are owned by the mutating thread and can be reset (reused as raw
// memory) long before the marker consumes the log. Snapshot reachability of
// scratch graphs is covered by the pause-1 root scan; heap objects never
// point into scratch (evacuation invariant), so a scratch old-value can
// only come from mutating a scratch container, and its heap children were
// either scanned at pause 1 or are covered by their own barriers.
static inline bool __satb_in_heap(void *p) {
  valk_gc_heap_t *heap = valk_thread_ctx.heap;
  if (!heap) heap = valk_sys ? valk_sys->heap : nullptr;
  if (!heap || !heap->base) return false;
  return (u8 *)p >= (u8 *)heap->base &&
         (u8 *)p < (u8 *)heap->base + heap->reserved;
}

void valk_gc_satb_log_lval(valk_lval_t *old) {
  if (!__satb_in_heap(old)) return;
  valk_thread_context_t *tc = &valk_thread_ctx;

  // Late registrants (not counted into this cycle) skip the CONC_FINAL
  // pause, so nothing would ever flush their local buffer: log straight to
  // the global list the marker drains.
  if (!tc->gc_registered ||
      atomic_load(&tc->stw_epoch) != atomic_load(&valk_sys->stw_epoch)) {
    pthread_mutex_lock(&__satb_lock);
    __satb_push_chunk_locked(&old, 1);
    pthread_mutex_unlock(&__satb_lock);
    return;
  }

  if (tc->satb_buf == nullptr) {
    tc->satb_buf = malloc(sizeof(valk_lval_t *) * VALK_SATB_LOCAL_CAP);
    VALK_ASSERT(tc->satb_buf != nullptr, "SATB buffer allocation failed");
    tc->satb_count = 0;
  }
  tc->satb_buf[tc->satb_count++] = old;
  if (tc->satb_count >= VALK_SATB_LOCAL_CAP) {
    pthread_mutex_lock(&__satb_lock);
    __satb_push_chunk_locked(tc->satb_buf, tc->satb_count);
    pthread_mutex_unlock(&__satb_lock);
    tc->satb_count = 0;
  }
}

void valk_gc_satb_log_env(valk_lenv_t *old) {
  if (!__satb_in_heap(old)) return;
  pthread_mutex_lock(&__satb_lock);
  bool found = false;
  for (u32 i = 0; i < __satb_env_count; i++) {
    if (__satb_envs[i] == old) { found = true; break; }
  }
  if (!found) {
    if (__satb_env_count < VALK_SATB_ENV_MAX) {
      __satb_envs[__satb_env_count++] = old;
    } else {
      valk_satb_env_chunk_t *chunk = __satb_env_chunks;
      if (chunk == nullptr || chunk->count >= VALK_SATB_CHUNK_CAP) {
        chunk = malloc(sizeof(valk_satb_env_chunk_t));
        VALK_ASSERT(chunk != nullptr, "SATB env chunk allocation failed"); // LCOV_EXCL_BR_LINE
        chunk->count = 0;
        chunk->next = __satb_env_chunks;
        __satb_env_chunks = chunk;
      }
      chunk->envs[chunk->count++] = old;
    }
  }
  pthread_mutex_unlock(&__satb_lock);
}

// Flush this thread's partial SATB buffer into its own mark queue. Runs
// inside the CONC_FINAL pause (all threads stopped).
void valk_gc_satb_flush_local(void) {
  valk_thread_context_t *tc = &valk_thread_ctx;
  if (tc->satb_buf == nullptr || tc->satb_count == 0) return;
  valk_gc_heap_t *heap = valk_gc_current_cycle_heap();
  for (u32 i = 0; i < tc->satb_count; i++) {
    valk_gc_mark_value_local(heap, tc->satb_buf[i]);
  }
  tc->satb_count = 0;
}

// Consume all queued overflow chunks and logged envs, marking their
// contents into the calling thread's mark queue.
u64 valk_gc_satb_drain_global(valk_gc_heap_t *heap) {
  u64 n = 0;
  for (;;) {
    pthread_mutex_lock(&__satb_lock);
    valk_satb_chunk_t *chunk = __satb_chunks;
    if (chunk) __satb_chunks = chunk->next;
    valk_satb_env_chunk_t *echunk = nullptr;
    valk_lenv_t *env = nullptr;
    if (!chunk) {
      echunk = __satb_env_chunks;
      if (echunk) {
        __satb_env_chunks = echunk->next;
      } else if (__satb_env_count > 0) {
        env = __satb_envs[--__satb_env_count];
      }
    }
    pthread_mutex_unlock(&__satb_lock);

    if (chunk) {
      for (u32 i = 0; i < chunk->count; i++) {
        valk_gc_mark_value_local(heap, chunk->vals[i]);
      }
      n += chunk->count;
      free(chunk);
    } else if (echunk) {
      for (u32 i = 0; i < echunk->count; i++) {
        valk_gc_mark_env_local(heap, echunk->envs[i]);
      }
      n += echunk->count;
      free(echunk);
    } else if (env) {
      valk_gc_mark_env_local(heap, env);
      n++;
    } else {
      break;
    }
  }
  return n;
}

bool valk_gc_satb_global_empty(void) {
  pthread_mutex_lock(&__satb_lock);
  bool empty = (__satb_chunks == nullptr) && (__satb_env_chunks == nullptr) &&
               (__satb_env_count == 0);
  pthread_mutex_unlock(&__satb_lock);
  return empty;
}

// ============================================================================
// Participant Protocols
// ============================================================================

void valk_gc_participate_concurrent(valk_gc_cycle_kind_e kind) {
  valk_gc_heap_t *heap = valk_gc_current_cycle_heap();

  if (kind == VALK_GC_CYCLE_CONC_START) {
    valk_barrier_wait(&valk_sys->barrier);
    if (heap) {
      valk_gc_conc_scan_local_roots(heap);
      valk_gc_tlab_blacken_remainder();
    }
    valk_barrier_wait(&valk_sys->barrier);
    return;
  }

  // VALK_GC_CYCLE_CONC_FINAL
  valk_barrier_wait(&valk_sys->barrier);
  if (heap) valk_gc_satb_flush_local();
  valk_barrier_wait(&valk_sys->barrier);
  if (heap) valk_gc_conc_drain_owst(heap);
  valk_barrier_wait(&valk_sys->barrier);
  // Marking is complete but sweep must not start yet: the coordinator runs
  // the pre-sweep root verifier in this window, and sweeping would consume
  // the very mark bits it checks.
  valk_barrier_wait(&valk_sys->barrier);
  if (heap) valk_gc_heap_parallel_sweep(heap);
  valk_barrier_wait(&valk_sys->barrier);
  valk_barrier_wait(&valk_sys->barrier);
}

// ============================================================================
// Marker Thread
// ============================================================================

static pthread_t __marker_thread;
static pthread_mutex_t __marker_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t __marker_cond = PTHREAD_COND_INITIALIZER;
static _Atomic bool __marker_running = false;
static _Atomic bool __marker_stop = false;
static _Atomic bool __marker_spawned = false;
static _Atomic bool __cycle_requested = false;
static valk_gc_heap_t *_Atomic __cycle_heap = nullptr;

static void __marker_wake(void *ctx) {
  (void)ctx;
  pthread_mutex_lock(&__marker_lock);
  pthread_cond_signal(&__marker_cond);
  pthread_mutex_unlock(&__marker_lock);
}

// Which counted participant reached the barrier last, and how long after the
// STW request started. Coordinator-only, between request_stw returning and
// the next cycle's request. Diagnostic for rendezvous-latency spikes.
static u64 __slowest_arriver(u64 t_req, u64 *out_delay_ns) {
  u64 max_ns = 0, idx = (u64)-1;
  u64 epoch = atomic_load(&valk_sys->stw_epoch);
  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    if (!valk_sys->threads[i].active) continue;
    valk_thread_context_t *tc = valk_sys->threads[i].ctx;
    if (!tc || atomic_load(&tc->stw_epoch) != epoch) continue;
    u64 at = valk_sys->threads[i].last_rdv_ns;
    if (at > t_req && at > max_ns) {
      max_ns = at;
      idx = i;
    }
  }
  *out_delay_ns = max_ns > t_req ? max_ns - t_req : 0;
  return idx;
}

static void __run_concurrent_cycle(valk_gc_heap_t *heap) {
  u64 t0 = uv_hrtime();
  u64 slow1_ns = 0, slow2_ns = 0;

  // ---- Pause 1: root snapshot ----
  atomic_store(&valk_gc_satb_active, true);
  if (!valk_gc_heap_request_stw_kind(heap, VALK_GC_PHASE_IDLE,
                                     VALK_GC_CYCLE_CONC_START)) {
    atomic_store(&valk_gc_satb_active, false);
    return;
  }
  // request_stw_kind returns once every participant reached the barrier, so
  // this minus t0 is pure rendezvous latency; the rest of p1 is root-scan work.
  u64 t_rdv1 = uv_hrtime();
  u64 slow1_idx = __slowest_arriver(t0, &slow1_ns);

  atomic_store(&heap->gc_in_progress, true);
  atomic_fetch_add(&heap->collections, 1);
  u64 bytes_before = valk_gc_heap_used_bytes(heap);

  valk_barrier_wait(&valk_sys->barrier);
  // All participants are scanning their local roots now; do ours + globals.
  valk_gc_phase_transition(VALK_GC_PHASE_STW_REQUESTED,
                           VALK_GC_PHASE_CONC_MARK);
  valk_gc_conc_scan_local_roots(heap);
  valk_gc_conc_scan_global_roots(heap);
  valk_gc_tlab_blacken_remainder();
  valk_barrier_wait(&valk_sys->barrier);

  u64 t1 = uv_hrtime();

  // ---- Concurrent trace ----
  for (;;) {
    u64 traced = valk_gc_conc_drain(heap);
    u64 flushed = valk_gc_satb_drain_global(heap);
    if (traced == 0 && flushed == 0 && valk_gc_all_mark_queues_empty() &&
        valk_gc_satb_global_empty()) {
      break;
    }
    if (atomic_load(&valk_sys->shutting_down)) break;
  }

  u64 t2 = uv_hrtime();

  // ---- Pause 2: SATB residue + sweep ----
  u64 t_rdv2_start = uv_hrtime();
  valk_gc_owst_reset();
  if (!valk_gc_heap_request_stw_kind(heap, VALK_GC_PHASE_CONC_MARK,
                                     VALK_GC_CYCLE_CONC_FINAL)) {
    // Shutdown raced the cycle. Restore IDLE so unregister/refill gates and
    // late registrants stop spinning; mark bits are stale but no further
    // cycle will run before exit.
    atomic_store(&valk_gc_satb_active, false);
    atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);
    atomic_store(&heap->gc_in_progress, false);
    return;
  }

  u64 t_rdv2 = uv_hrtime();
  u64 slow2_idx = __slowest_arriver(t_rdv2_start, &slow2_ns);

  valk_barrier_wait(&valk_sys->barrier);
  valk_gc_phase_transition(VALK_GC_PHASE_STW_REQUESTED, VALK_GC_PHASE_MARKING);
  valk_gc_satb_flush_local();
  valk_gc_satb_drain_global(heap);
  valk_barrier_wait(&valk_sys->barrier);
  valk_gc_conc_drain_owst(heap);
  valk_barrier_wait(&valk_sys->barrier);

  // Participants are parked at the next barrier, NOT sweeping yet: the
  // verifier must read mark bits before any sweeper consumes and clears
  // them. (Verifying after that barrier raced the participants' sweep and
  // produced phantom whole-pages-unmarked reports.)
  valk_gc_verify_conc_roots_marked(heap);
  valk_barrier_wait(&valk_sys->barrier);

  // Tracing is complete; stores no longer need logging. All mutators are
  // stopped, so nothing races this flip before sweep begins.
  atomic_store(&valk_gc_satb_active, false);
  valk_gc_phase_transition(VALK_GC_PHASE_MARKING, VALK_GC_PHASE_SWEEPING);
  valk_gc_heap_parallel_sweep(heap);
  valk_barrier_wait(&valk_sys->barrier);

  heap->generation = valk_gc_heap_next_generation();

  valk_gc_verify_heap_post_sweep(heap);

  valk_gc_phase_transition(VALK_GC_PHASE_SWEEPING, VALK_GC_PHASE_IDLE);
  valk_barrier_wait(&valk_sys->barrier);

  u64 t3 = uv_hrtime();

  // Page-list fixup runs OUTSIDE the pause: both walks take each class's
  // list lock, which is the same lock TLAB refill uses, so they are safe
  // against concurrent allocation. Stale partial lists until then only
  // cost the allocator a fresh page in the worst case.
  valk_gc_rebuild_partial_lists(heap);
  valk_gc_reclaim_empty_pages(heap);

  u64 bytes_after = valk_gc_heap_used_bytes(heap);
  u64 reclaimed = bytes_before > bytes_after ? bytes_before - bytes_after : 0;
  __atomic_store_n(&heap->live_after_gc, bytes_after, __ATOMIC_RELAXED);
  atomic_fetch_add(&heap->bytes_reclaimed_total, reclaimed);
  atomic_store(&heap->gc_in_progress, false);

  u64 pause_ns = (t1 - t0) + (t3 - t2);
  heap->last_gc_time_us = t3 / 1000;

  atomic_fetch_add(&heap->runtime_metrics.cycles_total, 1);
  atomic_fetch_add(&heap->runtime_metrics.pause_ns_total, pause_ns);
  atomic_fetch_add(&heap->runtime_metrics.reclaimed_bytes_total, reclaimed);
  atomic_store(&heap->runtime_metrics.last_heap_before_gc, bytes_before);
  atomic_store(&heap->runtime_metrics.last_reclaimed, reclaimed);

  u64 current_max = atomic_load(&heap->runtime_metrics.pause_ns_max);
  while (pause_ns > current_max) {
    if (atomic_compare_exchange_weak(&heap->runtime_metrics.pause_ns_max,
                                     &current_max, pause_ns)) {
      break;
    }
  }

  u64 pause_us = pause_ns / 1000;
  if (pause_us < 1000)
    atomic_fetch_add(&heap->runtime_metrics.pause_0_1ms, 1);
  else if (pause_us < 5000)
    atomic_fetch_add(&heap->runtime_metrics.pause_1_5ms, 1);
  else if (pause_us < 10000)
    atomic_fetch_add(&heap->runtime_metrics.pause_5_10ms, 1);
  else if (pause_us < 16000)
    atomic_fetch_add(&heap->runtime_metrics.pause_10_16ms, 1);
  else
    atomic_fetch_add(&heap->runtime_metrics.pause_16ms_plus, 1);

  atomic_fetch_add(&valk_sys->parallel_cycles, 1);
  atomic_fetch_add(&valk_sys->parallel_pause_ns_total, pause_ns);

  static bool log_cycles = false;
  static bool log_checked = false;
  if (!log_checked) {
    const char *env = getenv("VALK_GC_LOG");
    log_cycles = env && env[0] == '1';
    log_checked = true;
  }
  if (log_cycles || pause_us > 10000) {
    fprintf(stderr,
            "[gc] conc cycle #%llu: pause=%llu.%03llums "
            "(p1=%llu.%03llums[rdv=%llu.%03llums slow=t%lld/%llums] "
            "conc=%llums "
            "p2=%llu.%03llums[rdv=%llu.%03llums slow=t%lld/%llums], "
            "reclaimed %llu bytes, %llu -> %llu)\n",
            (unsigned long long)atomic_load(&heap->runtime_metrics.cycles_total),
            (unsigned long long)(pause_us / 1000),
            (unsigned long long)(pause_us % 1000),
            (unsigned long long)((t1 - t0) / 1000000),
            (unsigned long long)((t1 - t0) / 1000 % 1000),
            (unsigned long long)((t_rdv1 - t0) / 1000000),
            (unsigned long long)((t_rdv1 - t0) / 1000 % 1000),
            (long long)slow1_idx, (unsigned long long)(slow1_ns / 1000000),
            (unsigned long long)((t2 - t1) / 1000000),
            (unsigned long long)((t3 - t2) / 1000000),
            (unsigned long long)((t3 - t2) / 1000 % 1000),
            (unsigned long long)((t_rdv2 - t_rdv2_start) / 1000000),
            (unsigned long long)((t_rdv2 - t_rdv2_start) / 1000 % 1000),
            (long long)slow2_idx, (unsigned long long)(slow2_ns / 1000000),
            (unsigned long long)reclaimed,
            (unsigned long long)bytes_before,
            (unsigned long long)bytes_after);
  }
}

static void *__marker_main(void *arg) {
  (void)arg;
  valk_system_register_thread(valk_sys, __marker_wake, nullptr);

  for (;;) {
    if (atomic_load(&__marker_stop) || atomic_load(&valk_sys->shutting_down)) {
      break;
    }

    u32 flags = atomic_load_explicit(&valk_thread_ctx.safepoint_flags,
                                     memory_order_acquire);
    if (flags & VALK_SP_STW) {
      valk_gc_safe_point_slow();
      continue;
    }

    if (atomic_exchange(&__cycle_requested, false)) {
      valk_gc_heap_t *heap = atomic_load(&__cycle_heap);
      if (heap) __run_concurrent_cycle(heap);
      continue;
    }

    pthread_mutex_lock(&__marker_lock);
    if (!atomic_load(&__cycle_requested) && !atomic_load(&__marker_stop) &&
        !(atomic_load(&valk_thread_ctx.safepoint_flags) & VALK_SP_STW)) {
      struct timespec ts;
      clock_gettime(CLOCK_REALTIME, &ts);
      ts.tv_nsec += 10000000; // 10ms tick: absorbs missed wakeups
      if (ts.tv_nsec >= 1000000000) { ts.tv_sec++; ts.tv_nsec -= 1000000000; }
      pthread_cond_timedwait(&__marker_cond, &__marker_lock, &ts);
    }
    pthread_mutex_unlock(&__marker_lock);
  }

  valk_system_unregister_thread(valk_sys);
  atomic_store(&__marker_running, false);
  return nullptr;
}

// ============================================================================
// Public API
// ============================================================================

static bool __concurrent_enabled(void) {
  static _Atomic int enabled = -1;
  int e = atomic_load_explicit(&enabled, memory_order_relaxed);
  if (e < 0) {
    const char *env = getenv("VALK_GC_CONCURRENT");
    e = (env && env[0] == '0') ? 0 : 1;
    atomic_store_explicit(&enabled, e, memory_order_relaxed);
  }
  return e == 1;
}

bool valk_gc_request_concurrent_collect(valk_gc_heap_t *heap) {
  if (!heap || !__concurrent_enabled()) return false;
  if (atomic_load(&valk_sys->shutting_down)) return false;

  if (!atomic_load(&__marker_spawned)) {
    pthread_mutex_lock(&__marker_lock);
    if (!atomic_load(&__marker_spawned)) {
      atomic_store(&__marker_stop, false);
      if (pthread_create(&__marker_thread, nullptr, __marker_main, nullptr) != 0) {
        pthread_mutex_unlock(&__marker_lock);
        return false;
      }
      atomic_store(&__marker_running, true);
      atomic_store(&__marker_spawned, true);
    }
    pthread_mutex_unlock(&__marker_lock);
  }

  // A cycle in any phase absorbs this request; the trigger fires again on
  // the next TLAB refill if the heap is still above the threshold.
  if (atomic_load_explicit(&valk_sys->phase, memory_order_acquire) !=
      VALK_GC_PHASE_IDLE) {
    return true;
  }

  atomic_store(&__cycle_heap, heap);
  atomic_store(&__cycle_requested, true);
  __marker_wake(nullptr);
  return true;
}

void valk_gc_concurrent_shutdown(void) {
  if (!atomic_load(&__marker_spawned)) return;
  atomic_store(&__marker_stop, true);
  __marker_wake(nullptr);
  pthread_join(__marker_thread, nullptr);
  atomic_store(&__marker_spawned, false);
}

void valk_gc_concurrent_reset_after_fork(void) {
  atomic_store(&__marker_spawned, false);
  atomic_store(&__marker_running, false);
  atomic_store(&__marker_stop, false);
  atomic_store(&__cycle_requested, false);
  atomic_store(&__cycle_heap, nullptr);
  atomic_store(&valk_gc_satb_active, false);
  pthread_mutex_init(&__marker_lock, nullptr);
  pthread_cond_init(&__marker_cond, nullptr);
  pthread_mutex_init(&__satb_lock, nullptr);
  __satb_chunks = nullptr;
  __satb_env_chunks = nullptr;
  __satb_env_count = 0;
}

// LCOV_EXCL_STOP
