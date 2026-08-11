// Game-loop shaped benchmark.
//
// The other benchmarks have transient live sets. A game does not: entities
// persist across frames, so every collection re-traces the whole world. This
// models that, plus the extraction pass a renderer needs to read script
// results out into plain C memory.
//
// Per frame, for each entity:
//   update  - functional update of (x y vx vy), which allocates
//   extract - copy x,y into a plain float array (what a renderer consumes)
//
// Usage: build/bench_game [entities] [frames]
// Not linked into make test.

#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/gc.h"
#include "../src/gc_heap.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e3 + (double)ts.tv_nsec / 1e6;
}

static int cmp_double(const void *a, const void *b) {
  double x = *(const double *)a, y = *(const double *)b;
  return (x > y) - (x < y);
}

// entity = (x y vx vy) as a 4-cell cons list of nums.
static valk_lval_t *make_entity(long i) {
  valk_lval_t *vy = valk_lval_cons(valk_lval_num(1000 + (i % 7)), valk_lval_nil());
  valk_lval_t *vx = valk_lval_cons(valk_lval_num(1000 + (i % 5)), vy);
  valk_lval_t *y  = valk_lval_cons(valk_lval_num(2000 + i), vx);
  return valk_lval_cons(valk_lval_num(1000 + i), y);
}

static valk_lval_t *build_world(long n) {
  valk_lval_t *world = valk_lval_nil();
  for (long i = 0; i < n; i++) {
    world = valk_lval_cons(make_entity(i), world);
  }
  return world;
}

// Functional update: allocates a fresh entity per frame, like script code
// returning new values rather than mutating in place.
static valk_lval_t *update_world(valk_lval_t *world) {
  valk_lval_t *out = valk_lval_nil();
  for (valk_lval_t *e = world; e && LVAL_TYPE(e) == LVAL_CONS; e = e->cons.tail) {
    valk_lval_t *ent = e->cons.head;
    if (!ent || LVAL_TYPE(ent) != LVAL_CONS) continue;

    valk_lval_t *x  = ent->cons.head;
    valk_lval_t *r1 = ent->cons.tail;
    valk_lval_t *y  = r1->cons.head;
    valk_lval_t *r2 = r1->cons.tail;
    valk_lval_t *vx = r2->cons.head;
    valk_lval_t *r3 = r2->cons.tail;
    valk_lval_t *vy = r3->cons.head;

    long nx = x->num + vx->num;
    long ny = y->num + vy->num;
    if (nx > 100000) nx -= 100000;
    if (ny > 100000) ny -= 100000;

    valk_lval_t *nvy = valk_lval_cons(vy, valk_lval_nil());
    valk_lval_t *nvx = valk_lval_cons(vx, nvy);
    valk_lval_t *ny_ = valk_lval_cons(valk_lval_num(ny), nvx);
    valk_lval_t *nent = valk_lval_cons(valk_lval_num(nx), ny_);
    out = valk_lval_cons(nent, out);
  }
  return out;
}

// What the render loop does: pull script results into plain C memory.
static void extract_positions(valk_lval_t *world, float *xs, float *ys, long n) {
  long i = 0;
  for (valk_lval_t *e = world; e && LVAL_TYPE(e) == LVAL_CONS && i < n;
       e = e->cons.tail, i++) {
    valk_lval_t *ent = e->cons.head;
    if (!ent || LVAL_TYPE(ent) != LVAL_CONS) continue;
    xs[i] = (float)ent->cons.head->num;
    ys[i] = (float)ent->cons.tail->cons.head->num;
  }
}

int main(int argc, char **argv) {
  long entities = argc > 1 ? strtol(argv[1], nullptr, 10) : 10000;
  long frames   = argc > 2 ? strtol(argv[2], nullptr, 10) : 600;

  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);
  if (!sys) { fprintf(stderr, "system create failed\n"); return EXIT_FAILURE; }
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

  valk_lval_t *world = build_world(entities);
  valk_lenv_def(env, valk_lval_sym("world"), world);
  world = valk_lenv_get(env, valk_lval_sym("world"));

  float *xs = malloc((size_t)entities * sizeof(float));
  float *ys = malloc((size_t)entities * sizeof(float));

  double *frame_ms   = malloc((size_t)frames * sizeof(double));
  double *update_ms  = malloc((size_t)frames * sizeof(double));
  double *extract_ms = malloc((size_t)frames * sizeof(double));

  u64 c0, pt0, pm0; sz rec0, used0, tot0;
  valk_gc_get_runtime_metrics(heap, &c0, &pt0, &pm0, &rec0, &used0, &tot0);

  for (long f = 0; f < frames; f++) {
    double t0 = now_ms();
    world = update_world(world);
    valk_lenv_def(env, valk_lval_sym("world"), world);
    double t1 = now_ms();
    extract_positions(world, xs, ys, entities);
    double t2 = now_ms();
    // The collector runs at the safepoint, so it must be inside the frame
    // measurement - that is exactly the hitch a game would feel.
    VALK_GC_SAFE_POINT();
    double t3 = now_ms();

    update_ms[f]  = t1 - t0;
    extract_ms[f] = t2 - t1;
    frame_ms[f]   = t3 - t0;
  }

  u64 c1, pt1, pm1; sz rec1, used1, tot1;
  valk_gc_get_runtime_metrics(heap, &c1, &pt1, &pm1, &rec1, &used1, &tot1);
  u64 p0b, p1b, p5b, p10b, p16b;
  valk_gc_get_pause_histogram(heap, &p0b, &p1b, &p5b, &p10b, &p16b);

  double sum = 0, worst = 0, usum = 0, esum = 0;
  long over60 = 0, over120 = 0;
  for (long f = 0; f < frames; f++) {
    sum += frame_ms[f]; usum += update_ms[f]; esum += extract_ms[f];
    if (frame_ms[f] > worst) worst = frame_ms[f];
    if (frame_ms[f] > 16.6) over60++;
    if (frame_ms[f] > 8.3)  over120++;
  }
  qsort(frame_ms, (size_t)frames, sizeof(double), cmp_double);

  u64 cycles = c1 - c0;
  printf("\n=== %ld entities, %ld frames ===\n", entities, frames);
  printf("  script update   mean %7.3f ms\n", usum / (double)frames);
  printf("  extract to C    mean %7.3f ms\n", esum / (double)frames);
  printf("  frame total     mean %7.3f  p50 %7.3f  p99 %7.3f  max %7.3f ms\n",
         sum / (double)frames, frame_ms[frames / 2],
         frame_ms[(long)((double)frames * 0.99)], worst);
  printf("  budget          over 16.6ms: %ld/%ld    over 8.3ms: %ld/%ld\n",
         over60, frames, over120, frames);
  printf("  gc              %llu cycles (every %.1f frames), max pause %.3f ms\n",
         (unsigned long long)cycles,
         cycles ? (double)frames / (double)cycles : 0.0,
         (double)pm1 / 1e6);
  printf("  gc pause spread <1ms=%llu 1-5ms=%llu 5-10ms=%llu 10-16ms=%llu >16ms=%llu\n",
         (unsigned long long)p0b, (unsigned long long)p1b,
         (unsigned long long)p5b, (unsigned long long)p10b,
         (unsigned long long)p16b);
  printf("  heap used       %.1f MiB\n", (double)used1 / (1024.0 * 1024.0));

  return 0;
}
