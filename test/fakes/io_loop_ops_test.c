#include "aio/io/io_loop_ops.h"
#include "aio/io/io_timer_ops.h"
#include <stdlib.h>

typedef struct valk_test_loop_state {
  u64 current_time_ms;
} valk_test_loop_state_t;

static valk_test_loop_state_t *g_test_loop_state = nullptr;

void valk_test_loop_init_state(void) {
  if (!g_test_loop_state) {
    g_test_loop_state = calloc(1, sizeof(valk_test_loop_state_t));
  }
}

void valk_test_loop_set_time(u64 time_ms) {
  if (g_test_loop_state) g_test_loop_state->current_time_ms = time_ms;
}

static void test_loop_destroy(valk_aio_system_t *sys) {
  (void)sys;
  if (g_test_loop_state) {
    valk_test_timer_reset_state();
    free(g_test_loop_state);
    g_test_loop_state = nullptr;
  }
}

static u64 test_loop_now(valk_aio_system_t *sys) {
  (void)sys;
  return g_test_loop_state ? g_test_loop_state->current_time_ms : 0;
}

const valk_io_loop_ops_t valk_io_loop_ops_test = {
  .destroy = test_loop_destroy,
  .now = test_loop_now,
};
