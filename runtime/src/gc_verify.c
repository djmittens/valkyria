#include "gc.h"
#include "parser.h"
#include "eval_internal.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>

// ============================================================================
// Post-Sweep Heap Verification
// ============================================================================
// Runs at the end of a collection, inside the pause window where only the
// coordinator is active and every mutator is parked at the final barrier.
// Checks GC-internal accounting invariants that do not require interpreting
// object contents:
//
//   1. Every mark bitmap is zero (sweep consumed and cleared it).
//   2. No alloc bit is set past slots_per_page (trailing-byte hygiene).
//   3. popcount(alloc bitmap) == page->num_allocated.
//   4. Sum of page->num_allocated == list->used_slots per size class.
//   5. Reclaimed pages have num_allocated == 0.
//   6. No surviving large object is still marked; sum of large object sizes
//      == heap->large_object_bytes.
//
// Corruption in any of these means sweep, TLAB accounting, or the mark
// bitmaps went wrong THIS cycle - at the collection after the bug, not three
// tests later. Gated by VALK_GC_VERIFY=1 (the test runner sets it).

// LCOV_EXCL_BR_START - verification failure branches never fire in healthy runs
static bool __verify_enabled(void) {
  static _Atomic int enabled = -1;
  int e = atomic_load_explicit(&enabled, memory_order_relaxed);
  if (e < 0) {
    const char *env = getenv("VALK_GC_VERIFY");
    e = (env && env[0] == '1') ? 1 : 0;
    atomic_store_explicit(&enabled, e, memory_order_relaxed);
  }
  return e == 1;
}

// Pre-sweep root-marking check for concurrent cycles. Must run while every
// participant is parked at the pre-sweep barrier: sweep consumes and clears
// the mark bits this reads, so verifying concurrently with sweep reports
// phantom whole-pages-unmarked failures (the original "page-level hole" was
// exactly this verifier/sweep race, not a collector bug).
static bool __verify_roots_enabled(void) {
  static _Atomic int enabled = -1;
  int e = atomic_load_explicit(&enabled, memory_order_relaxed);
  if (e < 0) {
    const char *env = getenv("VALK_GC_VERIFY_ROOTS");
    e = (env && env[0] == '1') ? 1 : 0;
    atomic_store_explicit(&enabled, e, memory_order_relaxed);
  }
  return e == 1;
}

static void __verify_page(valk_gc_page_t *page, u8 size_class, sz *out_allocated) {
  u8 *alloc_bitmap = valk_gc_page_alloc_bitmap(page);
  u8 *mark_bitmap = valk_gc_page_mark_bitmap(page);
  u16 bm_bytes = page->bitmap_bytes;
  u16 slots = page->slots_per_page;

  sz allocated = 0;
  for (u16 i = 0; i < bm_bytes; i++) {
    VALK_ASSERT(mark_bitmap[i] == 0,
                "GC verify: class %u page %u mark bitmap byte %u is 0x%02x "
                "after sweep (mark bits leaked)",
                size_class, page->page_id, i, mark_bitmap[i]);

    u8 alloc_byte = alloc_bitmap[i];
    u32 first_slot = (u32)i * 8;
    if (first_slot + 8 > slots) {
      u8 valid = (u8)((slots > first_slot) ? ((1u << (slots - first_slot)) - 1u) : 0u);
      VALK_ASSERT((alloc_byte & (u8)~valid) == 0,
                  "GC verify: class %u page %u alloc bit set past "
                  "slots_per_page=%u (byte %u = 0x%02x)",
                  size_class, page->page_id, slots, i, alloc_byte);
    }
    allocated += (sz)__builtin_popcount((unsigned)alloc_byte);
  }

  u32 num_allocated = atomic_load(&page->num_allocated);
  VALK_ASSERT(allocated == (sz)num_allocated,
              "GC verify: class %u page %u alloc bitmap has %zu bits set but "
              "num_allocated=%u (accounting drift)",
              size_class, page->page_id, allocated, num_allocated);

  if (page->reclaimed) {
    VALK_ASSERT(num_allocated == 0,
                "GC verify: class %u page %u is reclaimed but has "
                "num_allocated=%u", size_class, page->page_id, num_allocated);
  }

  *out_allocated = allocated;
}

void valk_gc_verify_heap_post_sweep(valk_gc_heap_t *heap) {
  if (!heap || !__verify_enabled()) return;

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    sz class_allocated = 0;

    for (valk_gc_page_t *page = list->all_pages; page != nullptr;
         page = page->next) {
      sz page_allocated = 0;
      __verify_page(page, c, &page_allocated);
      class_allocated += page_allocated;
    }

    sz used = atomic_load(&list->used_slots);
    VALK_ASSERT(class_allocated == used,
                "GC verify: class %u pages hold %zu allocated slots but "
                "used_slots=%zu (per-class accounting drift)",
                c, class_allocated, used);
  }

  pthread_mutex_lock(&heap->large_lock);
  sz large_bytes = 0;
  for (valk_gc_large_obj_t *obj = heap->large_objects; obj != nullptr;
       obj = obj->next) {
    VALK_ASSERT(!obj->marked,
                "GC verify: large object %p (%zu bytes) still marked after "
                "sweep", obj->data, obj->size);
    large_bytes += obj->size;
  }
  pthread_mutex_unlock(&heap->large_lock);

  sz tracked = atomic_load(&heap->large_object_bytes);
  VALK_ASSERT(large_bytes == tracked,
              "GC verify: large object list holds %zu bytes but "
              "large_object_bytes=%zu", large_bytes, tracked);
}

// ============================================================================
// Refill Provenance Ring
// ============================================================================

#define VERIFY_REFILL_RING 512

typedef struct {
  valk_gc_page_t *page;
  u64 thread_id;
  u32 start_slot;
  u32 num_slots;
  u8 size_class;
  bool satb_on;
} verify_refill_rec_t;

static verify_refill_rec_t __refill_ring[VERIFY_REFILL_RING];
static _Atomic u64 __refill_ring_next = 0;

void valk_gc_verify_log_refill(valk_gc_page_t *page, u8 size_class,
                               u32 start_slot, u32 num_slots, bool satb_on) {
  if (!__verify_roots_enabled()) return;
  u64 i = atomic_fetch_add(&__refill_ring_next, 1) % VERIFY_REFILL_RING;
  __refill_ring[i] = (verify_refill_rec_t){
      .page = page,
      .thread_id = valk_thread_ctx.gc_registered ? valk_thread_ctx.gc_thread_id
                                                 : (u64)-1,
      .start_slot = start_slot,
      .num_slots = num_slots,
      .size_class = size_class,
      .satb_on = satb_on,
  };
}

static void __dump_refills_for_page(valk_gc_page_t *page) {
  fprintf(stderr, "[GC-VERIFY] recent refills for page %p:\n", (void *)page);
  u64 end = atomic_load(&__refill_ring_next);
  u64 start = end > VERIFY_REFILL_RING ? end - VERIFY_REFILL_RING : 0;
  for (u64 i = start; i < end; i++) {
    verify_refill_rec_t *r = &__refill_ring[i % VERIFY_REFILL_RING];
    if (r->page != page) continue;
    fprintf(stderr,
            "  seq=%llu thread=%llu class=%u slots=[%u,%u) satb_on=%d\n",
            (unsigned long long)i, (unsigned long long)r->thread_id,
            r->size_class, r->start_slot, r->start_slot + r->num_slots,
            r->satb_on);
  }
}

// ============================================================================
// Pre-Sweep Root-Marking Verification (concurrent cycles)
// ============================================================================
// Runs at the CONC_FINAL pause after all marking is complete and before
// sweep. Every env chain reachable from a counted participant's roots must
// be marked; an unmarked one is about to be swept while live - the exact
// corruption that produces vanished bindings and cyclic parent chains.

static void __dump_env_chain(valk_gc_heap_t *heap, valk_lenv_t *env,
                             u64 thread_idx, const char *root_kind) {
  fprintf(stderr, "[GC-VERIFY] chain (thread %llu, root=%s):\n",
          (unsigned long long)thread_idx, root_kind);
  u32 hops = 0;
  for (; env != nullptr && hops < 40; env = env->parent, hops++) {
    valk_gc_ptr_location_t eloc, aloc;
    bool in_heap = valk_gc_ptr_to_location(heap, env, &eloc);
    int env_mark = in_heap ? valk_gc_page_is_marked(eloc.page, eloc.slot) : -1;
    bool arr_in_heap =
        env->symbols.items &&
        valk_gc_ptr_to_location(heap, env->symbols.items, &aloc);
    int arr_mark =
        arr_in_heap ? valk_gc_page_is_marked(aloc.page, aloc.slot) : -1;
    fprintf(stderr,
            "  hop %u: env=%p in_heap=%d mark=%d nsyms=%llu cmap=%d "
            "sym_arr=%p sym_arr_mark=%d\n",
            hops, (void *)env, in_heap, env_mark,
            (unsigned long long)env->symbols.count, env->cmap != nullptr,
            (void *)env->symbols.items, arr_mark);
    if (arr_in_heap) {
      u8 *mb = valk_gc_page_mark_bitmap(aloc.page);
      u8 *ab = valk_gc_page_alloc_bitmap(aloc.page);
      u32 marked = 0, allocd = 0;
      for (u16 b = 0; b < aloc.page->bitmap_bytes; b++) {
        marked += (u32)__builtin_popcount((unsigned)mb[b]);
        allocd += (u32)__builtin_popcount((unsigned)ab[b]);
      }
      fprintf(stderr,
              "    arr page=%p class=%u slot=%u alloc_bit=%d page_marked=%u "
              "page_alloc=%u slots=%u\n",
              (void *)aloc.page, aloc.size_class, aloc.slot,
              valk_gc_page_is_allocated(aloc.page, aloc.slot), marked, allocd,
              aloc.page->slots_per_page);
    }
    if (env->cmap) break;
  }
}

static void __verify_env_marked(valk_gc_heap_t *heap, valk_lenv_t *root_env,
                                u64 thread_idx, const char *root_kind) {
  u32 hops = 0;
  valk_lenv_t *env = root_env;
  for (; env != nullptr && hops < 10000; env = env->parent, hops++) {
    valk_gc_ptr_location_t loc;
    if (!valk_gc_ptr_to_location(heap, env, &loc)) return;
    if (!valk_gc_page_is_marked(loc.page, loc.slot)) {
      __dump_env_chain(heap, root_env, thread_idx, root_kind);
    }
    VALK_ASSERT(valk_gc_page_is_marked(loc.page, loc.slot),
                "GC verify: LIVE env %p (thread %llu, root=%s, hop %u, "
                "nsyms=%llu) is UNMARKED before concurrent sweep",
                (void *)env, (unsigned long long)thread_idx, root_kind, hops,
                (unsigned long long)env->symbols.count);
    if (env->symbols.items &&
        valk_gc_ptr_to_location(heap, env->symbols.items, &loc)) {
      if (!valk_gc_page_is_marked(loc.page, loc.slot)) {
        __dump_env_chain(heap, root_env, thread_idx, root_kind);
        __dump_refills_for_page(loc.page);
      }
      VALK_ASSERT(valk_gc_page_is_marked(loc.page, loc.slot),
                  "GC verify: symbols array %p of live env %p (thread %llu, "
                  "root=%s) is UNMARKED before concurrent sweep",
                  (void *)env->symbols.items, (void *)env,
                  (unsigned long long)thread_idx, root_kind);
    }
    if (env->vals.items &&
        valk_gc_ptr_to_location(heap, env->vals.items, &loc)) {
      VALK_ASSERT(valk_gc_page_is_marked(loc.page, loc.slot),
                  "GC verify: vals array %p of live env %p (thread %llu, "
                  "root=%s) is UNMARKED before concurrent sweep",
                  (void *)env->vals.items, (void *)env,
                  (unsigned long long)thread_idx, root_kind);
      for (u64 i = 0; i < env->vals.count; i++) {
        valk_lval_t *val = env->vals.items[i];
        if (val == nullptr || (val->flags & LVAL_FLAG_IMMORTAL)) continue;
        valk_gc_ptr_location_t vloc;
        if (!valk_gc_ptr_to_location(heap, val, &vloc)) continue;
        if (!valk_gc_page_is_marked(vloc.page, vloc.slot)) {
          u8 *mb = valk_gc_page_mark_bitmap(vloc.page);
          u32 marked = 0;
          for (u16 b = 0; b < vloc.page->bitmap_bytes; b++)
            marked += (u32)__builtin_popcount((unsigned)mb[b]);
          valk_gc_ptr_location_t eloc;
          int env_mark = valk_gc_ptr_to_location(heap, env, &eloc)
                             ? valk_gc_page_is_marked(eloc.page, eloc.slot)
                             : -1;
          fprintf(stderr,
                  "[GC-VERIFY] white value %p type=%d env=%p env_mark=%d "
                  "val_page=%p class=%u slot=%u page_marked=%u\n",
                  (void *)val, (int)(val->flags & 0xFF), (void *)env, env_mark,
                  (void *)vloc.page, vloc.size_class, vloc.slot, marked);
          __dump_env_chain(heap, root_env, thread_idx, root_kind);
          __dump_refills_for_page(vloc.page);
        }
        VALK_ASSERT(valk_gc_page_is_marked(vloc.page, vloc.slot),
                    "GC verify: value %p (binding %llu '%s') of live env %p "
                    "(thread %llu, root=%s) is UNMARKED before concurrent "
                    "sweep",
                    (void *)val, (unsigned long long)i,
                    env->symbols.items ? env->symbols.items[i] : "?",
                    (void *)env, (unsigned long long)thread_idx, root_kind);
      }
    }
  }
  VALK_ASSERT(hops < 10000,
              "GC verify: env parent chain from thread %llu root=%s exceeds "
              "10000 hops (cyclic chain)",
              (unsigned long long)thread_idx, root_kind);
}

void valk_gc_verify_conc_roots_marked(valk_gc_heap_t *heap) {
  if (!heap || !__verify_roots_enabled()) return;

  u64 sys_epoch = atomic_load(&valk_sys->stw_epoch);
  for (u64 t = 0; t < VALK_SYSTEM_MAX_THREADS; t++) {
    if (!valk_sys->threads[t].active || valk_sys->threads[t].ctx == nullptr)
      continue;
    valk_thread_context_t *tc = valk_sys->threads[t].ctx;
    if (atomic_load(&tc->stw_epoch) != sys_epoch) continue;

    for (sz i = 0; i < tc->env_root_stack_count; i++) {
      __verify_env_marked(heap, tc->env_root_stack[i], t, "env_root_stack");
    }
    __verify_env_marked(heap, tc->eval_env, t, "eval_env");
    for (u32 i = 0; i < tc->eval_stack_depth; i++) {
      __verify_env_marked(heap, tc->saved_eval_envs[i], t, "saved_eval_env");
      valk_eval_stack_t *stack = (valk_eval_stack_t *)tc->eval_stacks[i];
      if (!stack) continue;
      for (u64 f = 0; f < stack->count; f++) {
        __verify_env_marked(heap, stack->frames[f].env, t, "frame_env");
        if (stack->frames[f].kind == CONT_BODY_NEXT) {
          __verify_env_marked(heap, stack->frames[f].body_next.call_env, t,
                              "frame_call_env");
        }
      }
    }
  }
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Full-Heap Mark Verification (concurrent cycles)
// ============================================================================
// The strongest check: save the concurrent marker's result, re-mark the
// entire world solo from every root (the world is stopped), and diff.
// Any object the remark reaches that the concurrent cycle did NOT mark is
// live data about to be swept - a marker hole - reported with its exact
// address and type at the guilty collection. Objects marked by the cycle
// but unreached by the remark are floating garbage (allocate-black,
// SATB retention) and are fine.
//
// Gated by VALK_GC_VERIFY_FULL=1: a full solo mark per cycle is too slow
// for the default test run but turns any 1-in-N corruption flake into a
// deterministic assert with a core dump.

// LCOV_EXCL_START - verifier-only, opt-in via VALK_GC_VERIFY_FULL
static bool __verify_full_enabled(void) {
  static _Atomic int enabled = -1;
  int e = atomic_load_explicit(&enabled, memory_order_relaxed);
  if (e < 0) {
    const char *env = getenv("VALK_GC_VERIFY_FULL");
    e = (env && env[0] == '1') ? 1 : 0;
    atomic_store_explicit(&enabled, e, memory_order_relaxed);
  }
  return e == 1;
}

typedef struct {
  valk_gc_page_t *page;
  u8 *saved;
} verify_saved_bitmap_t;

typedef struct {
  valk_gc_large_obj_t *obj;
  bool saved_marked;
} verify_saved_large_t;

static void __report_missed_slot(valk_gc_page_t *page, u8 size_class,
                                 u32 slot) {
  void *ptr = valk_gc_page_slot_ptr(page, slot);
  u16 slot_size = valk_gc_size_classes[size_class];
  int type = -1;
  int src_pos = 0;
  if (slot_size >= sizeof(valk_lval_t)) {
    valk_lval_t *lv = ptr;
    type = (int)(lv->flags & 0xFF);
    src_pos = LVAL_SRC_POS(lv);
  }
  fprintf(stderr,
          "[GC-VERIFY-FULL] MISSED object %p class=%u slot=%u page=%p "
          "type=%d src_pos=%d (reachable at pre-sweep, unmarked by "
          "concurrent cycle)\n",
          ptr, size_class, slot, (void *)page, type, src_pos);
  if (type == 7) {
    valk_lval_t *lv = ptr;
    fprintf(stderr, "[GC-VERIFY-FULL]   cons head=%p tail=%p quoted=%d\n",
            (void *)lv->cons.head, (void *)lv->cons.tail,
            (lv->flags & LVAL_FLAG_QUOTED) != 0);
  } else if (type == 2 || type == 3) {
    valk_lval_t *lv = ptr;
    fprintf(stderr, "[GC-VERIFY-FULL]   str=\"%.60s\" interned=%d\n",
            lv->str ? lv->str : "(null)",
            (lv->flags & LVAL_FLAG_INTERNED) != 0);
  }
}

// Brute-force referencer scan: find every word in the live heap (and large
// blocks) equal to `target` and print the containing object. Identifies the
// guilty edge without needing rr: the referencer's type + mark state says
// which barrier/trace path failed to cover it. depth>0 recurses one level
// into referencers-of-referencers to expose the owning container.
static void __report_referencers_depth(valk_gc_heap_t *heap, void *target,
                                       int depth);

static void __report_referencers(valk_gc_heap_t *heap, void *target) {
  __report_referencers_depth(heap, target, 1);
}

static void __report_referencers_depth(valk_gc_heap_t *heap, void *target,
                                       int depth) {
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    u16 slot_size = valk_gc_size_classes[c];
    for (valk_gc_page_t *p = heap->classes[c].all_pages; p; p = p->next) {
      if (p->reclaimed) continue;
      for (u32 s = 0; s < p->slots_per_page; s++) {
        if (!valk_gc_page_is_allocated(p, s)) continue;
        void **words = valk_gc_page_slot_ptr(p, s);
        for (u16 w = 0; w < slot_size / sizeof(void *); w++) {
          if (words[w] == target) {
            int rtype = -1;
            int rsrc = 0;
            if (slot_size >= sizeof(valk_lval_t)) {
              rtype = (int)(((valk_lval_t *)words)->flags & 0xFF);
              rsrc = LVAL_SRC_POS((valk_lval_t *)words);
            }
            fprintf(stderr,
                    "[GC-VERIFY-FULL]   %*sreferencer %p class=%u slot=%u "
                    "word=%u type=%d src_pos=%d marked=%d\n",
                    (2 - depth) * 2, "", (void *)words, c, s, w, rtype, rsrc,
                    valk_gc_page_is_marked(p, s));
            if (depth > 0) {
              __report_referencers_depth(heap, words, depth - 1);
            }
          }
        }
      }
    }
  }
  pthread_mutex_lock(&heap->large_lock);
  for (valk_gc_large_obj_t *o = heap->large_objects; o; o = o->next) {
    void **words = o->data;
    for (sz w = 0; w < o->size / sizeof(void *); w++) {
      if (words[w] == target) {
        fprintf(stderr,
                "[GC-VERIFY-FULL]   referencer large=%p (%zu bytes) word=%zu "
                "marked=%d\n",
                o->data, o->size, w, o->marked);
      }
    }
  }
  pthread_mutex_unlock(&heap->large_lock);
}

void valk_gc_verify_full_mark(valk_gc_heap_t *heap) {
  if (!heap || !__verify_full_enabled()) return;

  // 1. Save and clear the concurrent cycle's mark state.
  sz n_pages = 0;
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    for (valk_gc_page_t *p = heap->classes[c].all_pages; p; p = p->next)
      n_pages++;
  }
  verify_saved_bitmap_t *saved = malloc(n_pages * sizeof(*saved));
  VALK_ASSERT(saved != nullptr, "verify-full: OOM saving bitmaps");
  sz pi = 0;
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    for (valk_gc_page_t *p = heap->classes[c].all_pages; p; p = p->next) {
      u8 *mb = valk_gc_page_mark_bitmap(p);
      saved[pi].page = p;
      saved[pi].saved = malloc(p->bitmap_bytes);
      VALK_ASSERT(saved[pi].saved != nullptr, "verify-full: OOM");
      memcpy(saved[pi].saved, mb, p->bitmap_bytes);
      memset(mb, 0, p->bitmap_bytes);
      pi++;
    }
  }

  pthread_mutex_lock(&heap->large_lock);
  sz n_large = 0;
  for (valk_gc_large_obj_t *o = heap->large_objects; o; o = o->next) n_large++;
  verify_saved_large_t *lsaved =
      n_large ? malloc(n_large * sizeof(*lsaved)) : nullptr;
  sz li = 0;
  for (valk_gc_large_obj_t *o = heap->large_objects; o; o = o->next) {
    lsaved[li].obj = o;
    lsaved[li].saved_marked = o->marked;
    o->marked = false;
    li++;
  }
  pthread_mutex_unlock(&heap->large_lock);

  // 2. Solo remark of the whole world.
  valk_gc_remark_world_solo(heap);

  // 3. Diff: remark-reachable must be a subset of concurrently-marked.
  u64 missed = 0;
  void *missed_ptrs[8];
  for (sz i = 0; i < n_pages; i++) {
    valk_gc_page_t *p = saved[i].page;
    u8 *mb = valk_gc_page_mark_bitmap(p);
    for (u16 b = 0; b < p->bitmap_bytes; b++) {
      u8 hole = (u8)(mb[b] & ~saved[i].saved[b]);
      while (hole) {
        u32 bit = (u32)__builtin_ctz(hole);
        __report_missed_slot(p, p->size_class, (u32)b * 8 + bit);
        if (missed < 8)
          missed_ptrs[missed] = valk_gc_page_slot_ptr(p, (u32)b * 8 + bit);
        missed++;
        hole = (u8)(hole & (hole - 1));
      }
    }
  }
  for (sz i = 0; i < n_large; i++) {
    if (lsaved[i].obj->marked && !lsaved[i].saved_marked) {
      fprintf(stderr,
              "[GC-VERIFY-FULL] MISSED large object %p (%zu bytes) "
              "(reachable at pre-sweep, unmarked by concurrent cycle)\n",
              lsaved[i].obj->data, lsaved[i].obj->size);
      if (missed < 8) missed_ptrs[missed] = lsaved[i].obj->data;
      missed++;
    }
  }

  // 4. Restore the real state (verified: remark-reachable is covered by it,
  // so sweeping with the restored bitmaps is safe when missed == 0).
  for (sz i = 0; i < n_pages; i++) {
    memcpy(valk_gc_page_mark_bitmap(saved[i].page), saved[i].saved,
           saved[i].page->bitmap_bytes);
    free(saved[i].saved);
  }
  free(saved);
  for (sz i = 0; i < n_large; i++) {
    lsaved[i].obj->marked = lsaved[i].saved_marked;
  }
  free(lsaved);

  // 5. With the CONCURRENT mark state restored, show who references each
  // missed object: a marked referencer means the edge was created after the
  // referencer was traced (missing barrier); an unmarked one extends the
  // missed subgraph toward its root.
  for (u64 i = 0; i < missed && i < 8; i++) {
    fprintf(stderr, "[GC-VERIFY-FULL] referencers of %p:\n", missed_ptrs[i]);
    __report_referencers(heap, missed_ptrs[i]);
  }

  VALK_ASSERT(missed == 0,
              "GC verify-full: concurrent mark missed %llu live object(s) "
              "before sweep (see [GC-VERIFY-FULL] report above)",
              (unsigned long long)missed);
}
// LCOV_EXCL_STOP
