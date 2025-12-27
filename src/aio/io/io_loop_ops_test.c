#include "io_loop_ops.h"
#include "io_timer_ops.h"
#include <stdlib.h>
#include <string.h>

typedef struct valk_test_loop_state {
  bool running;
  bool should_stop;
  valk_test_timer_state_t timer_state;
  uint64_t current_time_ms;
  uint64_t current_hrtime;
} valk_test_loop_state_t;

static valk_test_loop_state_t *g_test_loop_state = nullptr;

static int test_loop_init(valk_aio_system_t *sys) {
  (void)sys;
  if (!g_test_loop_state) {
    g_test_loop_state = calloc(1, sizeof(valk_test_loop_state_t));
    if (!g_test_loop_state) return -1;
    valk_test_timer_init_state(&g_test_loop_state->timer_state);
  }
  return 0;
}

static void test_loop_destroy(valk_aio_system_t *sys) {
  (void)sys;
  if (g_test_loop_state) {
    valk_test_timer_reset_state();
    free(g_test_loop_state);
    g_test_loop_state = nullptr;
  }
}

static int test_loop_run(valk_aio_system_t *sys, valk_io_run_mode_e mode) {
  (void)sys;
  if (!g_test_loop_state) return -1;
  
  g_test_loop_state->running = true;
  g_test_loop_state->should_stop = false;

  while (g_test_loop_state->running && !g_test_loop_state->should_stop) {
    size_t pending = valk_test_timer_pending_count();
    if (pending == 0 && mode != VALK_IO_RUN_DEFAULT) break;

    if (mode == VALK_IO_RUN_NOWAIT) break;
    if (mode == VALK_IO_RUN_ONCE) break;
    
    if (pending == 0) break;
  }

  g_test_loop_state->running = false;
  return 0;
}

static void test_loop_stop(valk_aio_system_t *sys) {
  (void)sys;
  if (g_test_loop_state) {
    g_test_loop_state->should_stop = true;
  }
}

static bool test_loop_alive(valk_aio_system_t *sys) {
  (void)sys;
  return valk_test_timer_pending_count() > 0;
}

static void test_loop_walk(valk_aio_system_t *sys, valk_io_walk_cb cb, void *arg) {
  (void)sys;
  (void)cb;
  (void)arg;
}

static uint64_t test_loop_now(valk_aio_system_t *sys) {
  (void)sys;
  return g_test_loop_state ? g_test_loop_state->current_time_ms : 0;
}

static uint64_t test_hrtime(void) {
  return g_test_loop_state ? g_test_loop_state->current_hrtime : 0;
}

const valk_io_loop_ops_t valk_io_loop_ops_test = {
  .init = test_loop_init,
  .destroy = test_loop_destroy,
  .run = test_loop_run,
  .stop = test_loop_stop,
  .alive = test_loop_alive,
  .walk = test_loop_walk,
  .now = test_loop_now,
  .hrtime = test_hrtime,
};
