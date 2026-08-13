// Allocation + GC benchmark on the real GC heap.
//
// bench_jit uses malloc and only small ints in [-1,256], so it hits the
// small-int cache and never exercises value construction or the collector.
// This one does: every measured value falls outside the cache.
//
// Reports construction throughput and, for the frame-loop cases, the GC pause
// distribution against a frame budget.
//
// Not linked into make test - run manually: build/bench_alloc

#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/gc.h"

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static double now_sec(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

typedef struct {
  u64 cycles;
  u64 pause_ns_total;
  u64 pause_ns_max;
  sz heap_used;
} gc_snapshot_t;

static gc_snapshot_t gc_snap(valk_gc_heap_t *heap) {
  gc_snapshot_t s = {0};
  sz reclaimed, total;
  valk_gc_get_runtime_metrics(heap, &s.cycles, &s.pause_ns_total,
                              &s.pause_ns_max, &reclaimed, &s.heap_used, &total);
  return s;
}

// ---------------------------------------------------------------------------
// Construction microbenchmarks. These are what B.1 (atomic flags) and
// B.2 (struct size) move directly.
// ---------------------------------------------------------------------------

static double bench_num_uncached(long n) {
  double t0 = now_sec();
  volatile long sink = 0;
  for (long i = 0; i < n; i++) {
    // 1000+ is outside the [-1,256] cache, so this really allocates.
    valk_lval_t *v = valk_lval_num(1000 + (i & 0xFFFF));
    sink += v->num;
    VALK_GC_SAFE_POINT();
  }
  double t1 = now_sec();
  (void)sink;
  return t1 - t0;
}

static double bench_cons(long n) {
  double t0 = now_sec();
  volatile long sink = 0;
  for (long i = 0; i < n; i++) {
    valk_lval_t *a = valk_lval_num(1000 + (i & 0xFFFF));
    valk_lval_t *c = valk_lval_cons(a, valk_lval_nil());
    sink += (long)(uintptr_t)c;
    VALK_GC_SAFE_POINT();
  }
  double t1 = now_sec();
  (void)sink;
  return t1 - t0;
}

static double bench_str(long n) {
  double t0 = now_sec();
  volatile long sink = 0;
  for (long i = 0; i < n; i++) {
    valk_lval_t *s = valk_lval_str("entity_position_component");
    sink += (long)(uintptr_t)s;
    VALK_GC_SAFE_POINT();
  }
  double t1 = now_sec();
  (void)sink;
  return t1 - t0;
}

// ---------------------------------------------------------------------------
// Synthetic frame loop: evaluate a per-entity expression N times per frame,
// for M frames, and report the pause distribution against the frame budget.
// ---------------------------------------------------------------------------

static void bench_frame_loop(valk_lenv_t *env, valk_gc_heap_t *heap,
                             const char *src, long entities, long frames,
                             double budget_ms) {
  valk_lval_t *ast = valk_parse_text(src);
  valk_lval_t *expr = ast->cons.head;

  double *frame_ms = malloc((size_t)frames * sizeof(double));
  gc_snapshot_t before = gc_snap(heap);

  for (long f = 0; f < frames; f++) {
    double t0 = now_sec();
    for (long e = 0; e < entities; e++) {
      valk_lval_eval(env, expr);
      VALK_GC_SAFE_POINT();
    }
    frame_ms[f] = (now_sec() - t0) * 1e3;
  }

  gc_snapshot_t after = gc_snap(heap);

  // frame stats
  double sum = 0, worst = 0;
  long over = 0;
  for (long f = 0; f < frames; f++) {
    sum += frame_ms[f];
    if (frame_ms[f] > worst) worst = frame_ms[f];
    if (frame_ms[f] > budget_ms) over++;
  }

  // p99 via sort
  for (long i = 1; i < frames; i++) {
    double k = frame_ms[i];
    long j = i - 1;
    while (j >= 0 && frame_ms[j] > k) { frame_ms[j + 1] = frame_ms[j]; j--; }
    frame_ms[j + 1] = k;
  }
  double p50 = frame_ms[frames / 2];
  double p99 = frame_ms[(long)((double)frames * 0.99)];

  u64 cycles = after.cycles - before.cycles;
  u64 pause_total_ns = after.pause_ns_total - before.pause_ns_total;

  printf("\n  %s   (%ld entities x %ld frames, budget %.2f ms)\n",
         src, entities, frames, budget_ms);
  printf("    frame ms      mean %6.3f   p50 %6.3f   p99 %6.3f   max %6.3f\n",
         sum / (double)frames, p50, p99, worst);
  printf("    over budget   %ld / %ld frames (%.1f%%)\n",
         over, frames, 100.0 * (double)over / (double)frames);
  printf("    gc            %llu cycles, %.3f ms total pause, %.3f ms max pause\n",
         (unsigned long long)cycles,
         (double)pause_total_ns / 1e6,
         (double)after.pause_ns_max / 1e6);
  printf("    heap used     %.1f MiB\n", (double)after.heap_used / (1024.0 * 1024.0));

  free(frame_ms);
}

static void report(const char *label, long n, double elapsed) {
  printf("  %-26s %8.3f ms total   %8.1f ns/op   (n=%ld)\n",
         label, elapsed * 1e3, (elapsed * 1e9) / (double)n, n);
}

int main(void) {
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);
  if (!sys) {
    fprintf(stderr, "failed to create system\n");
    return EXIT_FAILURE;
  }
  valk_lval_init_singletons();

  valk_gc_heap_t *heap = sys->heap;

  u64 scratch_bytes = 128ULL * 1024 * 1024;
  valk_mem_arena_t *scratch = malloc(scratch_bytes);
  valk_mem_arena_init(scratch, scratch_bytes - sizeof(*scratch));
  valk_thread_ctx.allocator = (void *)heap;
  valk_thread_ctx.scratch = scratch;

  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  valk_gc_set_root(heap, env);
  valk_thread_ctx.root_env = env;

  printf("sizeof(valk_lval_t) = %zu  -> size class slot = %u bytes\n",
         sizeof(valk_lval_t),
         (unsigned)valk_gc_size_classes[valk_gc_size_class(sizeof(valk_lval_t))]);

  printf("\n== construction (outside the [-1,256] small-int cache) ==\n");
  report("valk_lval_num",  2000000, bench_num_uncached(2000000));
  report("valk_lval_cons", 2000000, bench_cons(2000000));
  report("valk_lval_str",  2000000, bench_str(2000000));

  printf("\n== synthetic frame loop ==");
  // 16.6 ms = 60 Hz. Numbers chosen to land outside the small-int cache.
  bench_frame_loop(env, heap, "(+ 1000 2000)",              1000, 600, 16.6);
  bench_frame_loop(env, heap, "(+ (* 300 400) (- 900 200))", 1000, 600, 16.6);
  bench_frame_loop(env, heap, "(do (def {x} 700) x)",        1000, 600, 16.6);

  gc_snapshot_t final = gc_snap(heap);
  u64 p0, p1, p5, p10, p16;
  valk_gc_get_pause_histogram(heap, &p0, &p1, &p5, &p10, &p16);
  printf("\n== gc totals ==\n");
  printf("  cycles %llu   max pause %.3f ms\n",
         (unsigned long long)final.cycles, (double)final.pause_ns_max / 1e6);
  printf("  pause buckets: <1ms=%llu 1-5ms=%llu 5-10ms=%llu 10-16ms=%llu >16ms=%llu\n",
         (unsigned long long)p0, (unsigned long long)p1,
         (unsigned long long)p5, (unsigned long long)p10,
         (unsigned long long)p16);

  return 0;
}
