#include "builtins_internal.h"

#include <string.h>

#include "debugger.h"

#ifdef VALK_SRC_LOC

// Optional trailing thread-id argument shared by the inspection builtins:
// absent means "the first paused thread" (tid -1).
static i64 __opt_tid(valk_lval_t* a, u64 pos) {
  if (valk_lval_list_count(a) <= pos) return -1;
  valk_lval_t* t = valk_lval_list_nth(a, pos);
  if (LVAL_TYPE(t) != LVAL_NUM) return -1;
  return t->num;
}

static valk_lval_t* valk_builtin_debug_enable(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_debug_enable();
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_debug_disable(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_debug_disable();
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_debug_break(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* path = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, path, LVAL_STR);
  valk_lval_t* line = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, line, LVAL_NUM);
  // LCOV_EXCL_BR_STOP
  u32 id = valk_debug_break_set(path->str, (u16)line->num);
  if (id == 0) {
    return valk_lval_err("debug/break: breakpoint table full");
  }
  return valk_lval_num(id);
}

static valk_lval_t* valk_builtin_debug_unbreak(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* id = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, id, LVAL_NUM);
  // LCOV_EXCL_BR_STOP
  return valk_lval_num(valk_debug_break_clear((u32)id->num) ? 1 : 0);
}

static valk_lval_t* valk_builtin_debug_breakpoints(valk_lenv_t* e,
                                                  valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  return valk_debug_breakpoints();
}

static valk_lval_t* valk_builtin_debug_paused(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  return valk_lval_num(valk_debug_paused() ? 1 : 0);
}

static valk_lval_t* valk_builtin_debug_pause(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  valk_debug_pause_request();
  return valk_lval_num(1);
}

static valk_lval_t* valk_builtin_debug_threads(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  UNUSED(a);
  return valk_debug_threads();
}

static valk_lval_t* valk_builtin_debug_state(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_debug_state_tid(__opt_tid(a, 0));
}

static valk_lval_t* valk_builtin_debug_frames(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  return valk_debug_frames_tid(__opt_tid(a, 0));
}

static valk_lval_t* valk_builtin_debug_frame_env(valk_lenv_t* e,
                                                 valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_GE(a, a, 1);
  valk_lval_t* idx = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, idx, LVAL_NUM);
  // LCOV_EXCL_BR_STOP
  valk_lenv_t* env = valk_debug_frame_env_tid(__opt_tid(a, 1), (u64)idx->num);
  if (env == NULL) {
    return valk_lval_err("debug/frame-env: no frame %li (paused? %d)",
                         idx->num, valk_debug_paused() ? 1 : 0);
  }
  return valk_lval_env_ref(env);
}

static valk_lval_t* valk_builtin_debug_continue(valk_lenv_t* e,
                                                valk_lval_t* a) {
  UNUSED(e);
  i64 tid = __opt_tid(a, 0);
  return valk_lval_num(
      valk_debug_resume_tid(tid, VALK_DEBUG_RESUME_CONTINUE) ? 1 : 0);
}

static valk_lval_t* valk_builtin_debug_step(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  valk_debug_resume_e mode = VALK_DEBUG_RESUME_STEP_IN;
  if (valk_lval_list_count(a) > 0) {
    valk_lval_t* m = valk_lval_list_nth(a, 0);
    // LCOV_EXCL_BR_START - arg validation
    LVAL_ASSERT(a, LVAL_TYPE(m) == LVAL_SYM || LVAL_TYPE(m) == LVAL_STR,
                "debug/step: mode must be :in, :over or :out");
    // LCOV_EXCL_BR_STOP
    const char* s = m->str[0] == ':' ? m->str + 1 : m->str;
    if (strcmp(s, "over") == 0) {
      mode = VALK_DEBUG_RESUME_STEP_OVER;
    } else if (strcmp(s, "out") == 0) {
      mode = VALK_DEBUG_RESUME_STEP_OUT;
    } else if (strcmp(s, "in") != 0) {
      return valk_lval_err("debug/step: unknown mode %s", m->str);
    }
  }
  return valk_lval_num(valk_debug_resume_tid(__opt_tid(a, 1), mode) ? 1 : 0);
}

#endif

void valk_register_debug_builtins(valk_lenv_t* env) {
#ifdef VALK_SRC_LOC
  valk_lenv_put_builtin(env, "debug/enable", valk_builtin_debug_enable);
  valk_lenv_put_builtin(env, "debug/disable", valk_builtin_debug_disable);
  valk_lenv_put_builtin(env, "debug/break", valk_builtin_debug_break);
  valk_lenv_put_builtin(env, "debug/unbreak", valk_builtin_debug_unbreak);
  valk_lenv_put_builtin(env, "debug/breakpoints", valk_builtin_debug_breakpoints);
  valk_lenv_put_builtin(env, "debug/paused?", valk_builtin_debug_paused);
  valk_lenv_put_builtin(env, "debug/pause", valk_builtin_debug_pause);
  valk_lenv_put_builtin(env, "debug/threads", valk_builtin_debug_threads);
  valk_lenv_put_builtin(env, "debug/state", valk_builtin_debug_state);
  valk_lenv_put_builtin(env, "debug/frames", valk_builtin_debug_frames);
  valk_lenv_put_builtin(env, "debug/frame-env", valk_builtin_debug_frame_env);
  valk_lenv_put_builtin(env, "debug/continue", valk_builtin_debug_continue);
  valk_lenv_put_builtin(env, "debug/step", valk_builtin_debug_step);
#else
  UNUSED(env);
#endif
}
