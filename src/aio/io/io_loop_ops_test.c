#include "io_loop_ops.h"
#include <stdlib.h>
#include <string.h>

struct valk_io_loop {
  bool running;
  bool should_stop;
  valk_test_timer_state_t timer_state;
};

static valk_io_loop_t *test_loop_create(void) {
  valk_io_loop_t *loop = malloc(sizeof(valk_io_loop_t));
  if (!loop) return nullptr;
  
  memset(loop, 0, sizeof(*loop));
  loop->running = false;
  loop->should_stop = false;
  valk_test_timer_init_state(&loop->timer_state);
  
  return loop;
}

static void test_loop_destroy(valk_io_loop_t *loop) {
  if (!loop) return;
  valk_test_timer_reset_state();
  free(loop);
}

static int test_loop_run(valk_io_loop_t *loop, valk_io_run_mode_e mode) {
  loop->running = true;
  loop->should_stop = false;

  while (loop->running && !loop->should_stop) {
    size_t pending = valk_test_timer_pending_count();
    if (pending == 0 && mode != VALK_IO_RUN_DEFAULT) break;

    if (mode == VALK_IO_RUN_NOWAIT) break;
    if (mode == VALK_IO_RUN_ONCE) {
      break;
    }
    
    if (pending == 0) break;
  }

  loop->running = false;
  return 0;
}

static void test_loop_stop(valk_io_loop_t *loop) {
  loop->should_stop = true;
}

static bool test_loop_alive(valk_io_loop_t *loop) {
  (void)loop;
  return valk_test_timer_pending_count() > 0;
}

static void test_loop_walk(valk_io_loop_t *loop, valk_io_walk_cb cb, void *arg) {
  (void)loop;
  (void)cb;
  (void)arg;
}

const valk_io_loop_ops_t valk_io_loop_ops_test = {
  .create = test_loop_create,
  .destroy = test_loop_destroy,
  .run = test_loop_run,
  .stop = test_loop_stop,
  .alive = test_loop_alive,
  .walk = test_loop_walk,
  .timer = &valk_io_timer_ops_test,
  .loop_size = sizeof(valk_io_loop_t),
};
