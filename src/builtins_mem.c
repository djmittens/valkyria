#include "builtins_internal.h"

#include <strings.h>
#include <time.h>

#include "gc.h"
#include "log.h"

static valk_lval_t* valk_builtin_time_us(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);

  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  long us = ts.tv_sec * 1000000 + ts.tv_nsec / 1000;

  return valk_lval_num(us);
}

static valk_lval_t* valk_builtin_sleep(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* arg = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, arg, LVAL_NUM);

  long ms = arg->num;
  if (ms > 0) {
    struct timespec ts = {
      .tv_sec = ms / 1000,
      .tv_nsec = (ms % 1000) * 1000000
    };
    nanosleep(&ts, NULL);
  }
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_stack_depth(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  return valk_lval_num((long)valk_thread_ctx.call_depth);
}

static valk_lval_t* valk_builtin_memory_stats(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_mem_arena_t* scratch = valk_thread_ctx.scratch;
  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;
  valk_memory_print_stats(scratch, heap, stdout);
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_heap_usage(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;
  return valk_lval_num((long)valk_gc_heap_used_bytes(heap));
}

static valk_lval_t* valk_builtin_gc_stats(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;
  valk_gc_print_stats(heap);
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_gc_collect(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;
  u64 reclaimed =
      valk_gc_heap_collect(heap);
  return valk_lval_num((long)reclaimed);
}

static valk_lval_t* valk_builtin_heap_hard_limit(valk_lenv_t* e,
                                                 valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;
  return valk_lval_num((long)heap->hard_limit);
}

static valk_lval_t* valk_builtin_set_heap_hard_limit(valk_lenv_t* e,
                                                     valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);

  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;

  u64 new_limit = (u64)valk_lval_list_nth(a, 0)->num;
  u64 old_limit = heap->hard_limit;

  if (new_limit < valk_gc_heap_used_bytes(heap)) {
    return valk_lval_err(
        "Cannot set hard limit below current usage (%zu < %zu)", new_limit,
        valk_gc_heap_used_bytes(heap));
  }

  valk_gc_set_hard_limit(heap, new_limit);
  return valk_lval_num((long)old_limit);
}

static valk_lval_t* valk_builtin_gc_threshold_pct(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;
  return valk_lval_num((long)heap->gc_threshold_pct);
}

static valk_lval_t* valk_builtin_set_gc_threshold_pct(valk_lenv_t* e,
                                                       valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);

  long new_pct = valk_lval_list_nth(a, 0)->num;
  if (new_pct < 1) new_pct = 1;
  if (new_pct > 100) new_pct = 100;

  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;

  u8 old_pct = heap->gc_threshold_pct;
  heap->gc_threshold_pct = (u8)new_pct;
  return valk_lval_num((long)old_pct);
}

static valk_lval_t* valk_builtin_gc_usage_pct(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;
  return valk_lval_num((long)valk_gc_heap_usage_pct(heap));
}

static valk_lval_t* valk_builtin_gc_min_interval(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;
  return valk_lval_num((long)heap->min_gc_interval_ms);
}

static valk_lval_t* valk_builtin_set_gc_min_interval(valk_lenv_t* e,
                                                      valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);

  long new_ms = valk_lval_list_nth(a, 0)->num;
  if (new_ms < 0) new_ms = 0;

  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;

  u32 old_ms = heap->min_gc_interval_ms;
  heap->min_gc_interval_ms = (u32)new_ms;
  return valk_lval_num((long)old_ms);
}

static valk_lval_t* valk_builtin_set_log_level(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* s = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, s, LVAL_STR);

  const char* v = s->str;
  valk_log_level_e lvl = VALK_LOG_WARN;
  if (strcasecmp(v, "error") == 0)
    lvl = VALK_LOG_ERROR;
  else if (strcasecmp(v, "warn") == 0 || strcasecmp(v, "warning") == 0)
    lvl = VALK_LOG_WARN;
  else if (strcasecmp(v, "info") == 0)
    lvl = VALK_LOG_INFO;
  else if (strcasecmp(v, "debug") == 0)
    lvl = VALK_LOG_DEBUG;
  else if (strcasecmp(v, "trace") == 0)
    lvl = VALK_LOG_TRACE;

  valk_log_set_level(lvl);
  return valk_lval_str(s->str);
}

static valk_lval_t* valk_builtin_checkpoint_stats(valk_lenv_t* e,
                                                  valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);

  valk_mem_arena_t* scratch = valk_thread_ctx.scratch;
  valk_gc_heap_t* heap = (valk_gc_heap_t*)valk_thread_ctx.heap;

  valk_lval_t* stats[4] = {
      valk_lval_num((long)scratch->stats.num_checkpoints),
      valk_lval_num((long)scratch->stats.values_evacuated),
      valk_lval_num((long)scratch->stats.bytes_evacuated),
      valk_lval_num((long)heap->stats.evacuation_pointer_fixups)};
  return valk_lval_list(stats, 4);
}

static valk_lval_t* valk_builtin_arena_usage(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);

  valk_mem_arena_t* scratch = valk_thread_ctx.scratch;
  return valk_lval_num((long)scratch->offset);
}

static valk_lval_t* valk_builtin_arena_capacity(valk_lenv_t* e,
                                                valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);

  valk_mem_arena_t* scratch = valk_thread_ctx.scratch;
  return valk_lval_num((long)scratch->capacity);
}

static valk_lval_t* valk_builtin_arena_high_water(valk_lenv_t* e,
                                                  valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);

  valk_mem_arena_t* scratch = valk_thread_ctx.scratch;
  return valk_lval_num((long)scratch->stats.high_water_mark);
}

void valk_register_mem_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "time-us", valk_builtin_time_us);
  valk_lenv_put_builtin(env, "sleep", valk_builtin_sleep);
  valk_lenv_put_builtin(env, "stack-depth", valk_builtin_stack_depth);
  valk_lenv_put_builtin(env, "mem/stats", valk_builtin_memory_stats);
  valk_lenv_put_builtin(env, "mem/heap/usage", valk_builtin_heap_usage);
  valk_lenv_put_builtin(env, "mem/heap/hard-limit",
                        valk_builtin_heap_hard_limit);
  valk_lenv_put_builtin(env, "mem/heap/set-hard-limit",
                        valk_builtin_set_heap_hard_limit);
  valk_lenv_put_builtin(env, "mem/gc/stats", valk_builtin_gc_stats);
  valk_lenv_put_builtin(env, "mem/gc/collect", valk_builtin_gc_collect);
  valk_lenv_put_builtin(env, "mem/gc/threshold", valk_builtin_gc_threshold_pct);
  valk_lenv_put_builtin(env, "mem/gc/set-threshold",
                        valk_builtin_set_gc_threshold_pct);
  valk_lenv_put_builtin(env, "mem/gc/usage", valk_builtin_gc_usage_pct);
  valk_lenv_put_builtin(env, "mem/gc/min-interval", valk_builtin_gc_min_interval);
  valk_lenv_put_builtin(env, "mem/gc/set-min-interval",
                        valk_builtin_set_gc_min_interval);
  valk_lenv_put_builtin(env, "mem/arena/usage", valk_builtin_arena_usage);
  valk_lenv_put_builtin(env, "mem/arena/capacity", valk_builtin_arena_capacity);
  valk_lenv_put_builtin(env, "mem/arena/high-water",
                        valk_builtin_arena_high_water);
  valk_lenv_put_builtin(env, "mem/checkpoint/stats",
                        valk_builtin_checkpoint_stats);
  valk_lenv_put_builtin(env, "sys/log/set-level", valk_builtin_set_log_level);
}
