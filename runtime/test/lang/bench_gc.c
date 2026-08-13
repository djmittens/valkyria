// GC pause characterisation.
//
// Builds a controlled live set, forces a collection, and times it. Sweeping
// live-set size answers the question the frame-loop benchmark can only hint
// at: is the pause proportional to live data (textbook mark-sweep) or is it
// dominated by a fixed cost?
//
// Not linked into make test - run manually: build/bench_gc

#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/gc.h"
#include "../src/gc_heap.h"

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e3 + (double)ts.tv_nsec / 1e6;
}

// Retain `n` lvals by chaining them into a list hung off the root env, so the
// marker has to walk exactly that much live data.
static void build_live_set(valk_lenv_t *env, long n) {
  valk_lval_t *list = valk_lval_nil();
  for (long i = 0; i < n; i++) {
    list = valk_lval_cons(valk_lval_num(1000 + (i & 0xFFFF)), list);
  }
  valk_lenv_def(env, valk_lval_sym("live-set"), list);
}

int main(void) {
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);
  if (!sys) { fprintf(stderr, "failed to create system\n"); return EXIT_FAILURE; }
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

  printf("live objects |  heap used |  collect ms | ms per 100k live\n");
  printf("-------------+------------+-------------+-----------------\n");

  const long sizes[] = {0, 1000, 10000, 50000, 100000, 250000, 500000, 1000000};
  const int nsizes = (int)(sizeof(sizes) / sizeof(sizes[0]));

  for (int s = 0; s < nsizes; s++) {
    long n = sizes[s];
    build_live_set(env, n);

    // Settle: collect once so the measured cycle sees a stable live set.
    valk_gc_heap_collect(heap);

    double best = 1e9;
    for (int rep = 0; rep < 3; rep++) {
      double t0 = now_ms();
      valk_gc_heap_collect(heap);
      double dt = now_ms() - t0;
      if (dt < best) best = dt;
    }

    sz used, total, reclaimed;
    u64 cycles, pt, pm;
    valk_gc_get_runtime_metrics(heap, &cycles, &pt, &pm, &reclaimed, &used, &total);

    printf("%12ld | %7.1f MB | %9.3f  | %14.3f\n",
           n, (double)used / (1024.0 * 1024.0), best,
           n > 0 ? best / ((double)n / 100000.0) : 0.0);
  }

  return 0;
}
