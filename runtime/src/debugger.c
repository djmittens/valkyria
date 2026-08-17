#include "debugger.h"

#ifdef VALK_SRC_LOC

#include <limits.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

#include "eval_internal.h"
#include "gc.h"
#include "memory.h"
#include "source_loc.h"
#include "valk_thread.h"

#define VALK_DEBUG_MAX_BREAKPOINTS 64
#define VALK_DEBUG_MAX_FRAMES 128

_Atomic u32 valk_debug_active = 0;

typedef struct {
  u32 id;
  u16 file_id;
  u16 line;
} valk_debug_bp_t;

static struct {
  valk_mutex_t lock;
  bool lock_init;
  _Atomic bool enabled;

  valk_debug_bp_t bps[VALK_DEBUG_MAX_BREAKPOINTS];
  _Atomic u32 bp_count;
  u32 next_bp_id;

  // Single paused thread (v1).
  _Atomic int paused;
  _Atomic u32 resume_action;  // 0 none, else valk_debug_resume_e + 1
  u64 paused_tid;
  u16 paused_file;
  u16 paused_line;
  char paused_expr[128];
  valk_handle_t frames_handle;
  valk_lenv_t *frame_envs[VALK_DEBUG_MAX_FRAMES];
  u64 frame_count;

  // Post-resume suppression and step state, each packed into one atomic
  // word so the hook (which runs on every debugging thread) reads them
  // race-free: 0 = none, else ((tid+1) << 32) | (file_id << 16) | line.
  _Atomic u64 suppress_key;
  _Atomic u64 step_key;
  // Step mode and the call depth captured at resume. Written by the paused
  // thread before it publishes step_key and read back only by that same
  // thread (the hook checks the tid in step_key first), so plain fields.
  valk_debug_resume_e step_mode;
  u64 step_depth;
} g_dbg;

static u64 __dbg_key(u64 tid, u16 fid, u16 line) {
  return ((tid + 1) << 32) | ((u64)fid << 16) | (u64)line;
}

static void __dbg_lock_init(void) {
  if (!g_dbg.lock_init) {
    valk_mutex_init(&g_dbg.lock);
    g_dbg.lock_init = true;
  }
}

static void __dbg_update_active(void) {
  bool on = atomic_load(&g_dbg.enabled) &&
            (atomic_load(&g_dbg.bp_count) > 0 ||
             atomic_load(&g_dbg.step_key) != 0);
  atomic_store(&valk_debug_active, on ? 1 : 0);
}

void valk_debug_enable(void) {
  __dbg_lock_init();
  atomic_store(&g_dbg.enabled, true);
  __dbg_update_active();
}

void valk_debug_disable(void) {
  atomic_store(&g_dbg.enabled, false);
  atomic_store(&g_dbg.step_key, 0);
  __dbg_update_active();
  if (atomic_load(&g_dbg.paused)) {
    valk_debug_resume(VALK_DEBUG_RESUME_CONTINUE);
  }
}

bool valk_debug_enabled(void) { return atomic_load(&g_dbg.enabled); }

u32 valk_debug_break_set(const char *path, u16 line) {
  __dbg_lock_init();
  char resolved[PATH_MAX];
  const char *use = path;
  if (realpath(path, resolved) != NULL) use = resolved;
  u16 fid = valk_source_register_file(use);

  valk_mutex_lock(&g_dbg.lock);
  u32 id = 0;
  u32 n = atomic_load(&g_dbg.bp_count);
  for (u32 i = 0; i < n; i++) {
    if (g_dbg.bps[i].file_id == 0) {
      g_dbg.bps[i].file_id = fid;
      g_dbg.bps[i].line = line;
      id = g_dbg.bps[i].id = ++g_dbg.next_bp_id;
      break;
    }
  }
  if (id == 0 && n < VALK_DEBUG_MAX_BREAKPOINTS) {
    g_dbg.bps[n].file_id = fid;
    g_dbg.bps[n].line = line;
    id = g_dbg.bps[n].id = ++g_dbg.next_bp_id;
    atomic_store(&g_dbg.bp_count, n + 1);
  }
  valk_mutex_unlock(&g_dbg.lock);
  __dbg_update_active();
  return id;
}

bool valk_debug_break_clear(u32 id) {
  __dbg_lock_init();
  valk_mutex_lock(&g_dbg.lock);
  bool found = false;
  u32 n = atomic_load(&g_dbg.bp_count);
  for (u32 i = 0; i < n; i++) {
    if (g_dbg.bps[i].id == id && g_dbg.bps[i].file_id != 0) {
      g_dbg.bps[i].file_id = 0;
      found = true;
      break;
    }
  }
  valk_mutex_unlock(&g_dbg.lock);
  return found;
}

valk_lval_t *valk_debug_breakpoints(void) {
  __dbg_lock_init();
  valk_mutex_lock(&g_dbg.lock);
  valk_lval_t *res = valk_lval_nil();
  u32 n = atomic_load(&g_dbg.bp_count);
  for (u32 i = 0; i < n; i++) {
    if (g_dbg.bps[i].file_id == 0) continue;
    const char *fname = valk_source_get_filename(g_dbg.bps[i].file_id);
    valk_lval_t *entry = valk_lval_cons(valk_lval_sym(":id"),
      valk_lval_cons(valk_lval_num(g_dbg.bps[i].id),
      valk_lval_cons(valk_lval_sym(":file"),
      valk_lval_cons(valk_lval_str(fname ? fname : "?"),
      valk_lval_cons(valk_lval_sym(":line"),
      valk_lval_cons(valk_lval_num(g_dbg.bps[i].line), valk_lval_nil()))))));
    entry->flags |= LVAL_FLAG_QUOTED;
    res = valk_lval_qcons(entry, res);
  }
  valk_mutex_unlock(&g_dbg.lock);
  return res;
}

static bool __bp_match(u16 fid, u16 line) {
  u32 n = atomic_load_explicit(&g_dbg.bp_count, memory_order_acquire);
  for (u32 i = 0; i < n; i++) {
    if (g_dbg.bps[i].file_id == fid && g_dbg.bps[i].line == line) return true;
  }
  return false;
}

// --- frame snapshot (built on the paused thread before parking) -----------

static void __expr_summary(valk_lval_t *expr, char *buf, sz cap) {
  if (expr == NULL) {
    snprintf(buf, cap, "?");
    return;
  }
  switch (LVAL_TYPE(expr)) {
    case LVAL_SYM: snprintf(buf, cap, "%s", expr->str); break;
    case LVAL_NUM: snprintf(buf, cap, "%li", expr->num); break;
    case LVAL_STR: snprintf(buf, cap, "\"%.32s\"", expr->str); break;
    case LVAL_FUN:
      snprintf(buf, cap, "%s", expr->fun.name ? expr->fun.name : "\\");
      break;
    case LVAL_CONS:
      if (expr->cons.head && LVAL_TYPE(expr->cons.head) == LVAL_SYM) {
        snprintf(buf, cap, "(%s ...)", expr->cons.head->str);
      } else {
        snprintf(buf, cap, "(...)");
      }
      break;
    default: snprintf(buf, cap, "<%d>", LVAL_TYPE(expr)); break;
  }
}

static const char *__cont_kind_name(valk_cont_kind_e kind) {
  switch (kind) {
    case CONT_DONE: return "done";
    case CONT_EVAL_ARGS: return "eval-args";
    case CONT_COLLECT_ARG: return "call";
    case CONT_APPLY_FUNC: return "apply";
    case CONT_IF_BRANCH: return "if";
    case CONT_DO_NEXT: return "do";
    case CONT_SELECT_CHECK: return "select";
    case CONT_BODY_NEXT: return "body";
    case CONT_SINGLE_ELEM: return "single";
    case CONT_LAMBDA_DONE: return "lambda";
    case CONT_CTX_DEADLINE: return "ctx-deadline";
    case CONT_CTX_WITH: return "ctx-with";
    case CONT_CTX_BODY: return "ctx-body";
    case CONT_LOGIC_NEXT: return "logic";
    default: return "?";
  }
}

static valk_lval_t *__frame_entry(const char *kind, const char *fn,
                                  u16 fid, u16 line) {
  const char *fname = fid ? valk_source_get_filename(fid) : NULL;
  valk_lval_t *entry = valk_lval_cons(valk_lval_sym(":kind"),
    valk_lval_cons(valk_lval_str(kind),
    valk_lval_cons(valk_lval_sym(":fn"),
    valk_lval_cons(valk_lval_str(fn ? fn : ""),
    valk_lval_cons(valk_lval_sym(":file"),
    valk_lval_cons(valk_lval_str(fname ? fname : ""),
    valk_lval_cons(valk_lval_sym(":line"),
    valk_lval_cons(valk_lval_num(line), valk_lval_nil()))))))));
  entry->flags |= LVAL_FLAG_QUOTED;
  return entry;
}

static valk_lval_t *__frame_from_cont(valk_cont_frame_t *frame) {
  valk_lval_t *fn_val = NULL;
  switch (frame->kind) {
    case CONT_EVAL_ARGS: fn_val = frame->eval_args.func; break;
    case CONT_COLLECT_ARG: fn_val = frame->collect_arg.func; break;
    default: break;
  }
  char fn_buf[64] = "";
  u16 fid = 0;
  u16 line = 0;
  if (fn_val != NULL) {
    __expr_summary(fn_val, fn_buf, sizeof(fn_buf));
    fid = fn_val->cov_file_id;
    line = fn_val->cov_line;
  }
  return __frame_entry(__cont_kind_name(frame->kind), fn_buf, fid, line);
}

// Builds the snapshot into g_dbg (frames data via the handle table, env
// pointers in a C array). Runs on the paused thread; envs stay valid while
// parked because this thread's GC participation keeps marking them.
static void __publish_snapshot(valk_lval_t *expr, valk_lenv_t *env) {
  g_dbg.frame_count = 0;
  valk_lval_t *frames = valk_lval_nil();

  char expr_buf[128];
  __expr_summary(expr, expr_buf, sizeof(expr_buf));
  snprintf(g_dbg.paused_expr, sizeof(g_dbg.paused_expr), "%s", expr_buf);

  // Frame 0: the paused expression itself.
  valk_lval_t *entries[VALK_DEBUG_MAX_FRAMES];
  valk_lenv_t *envs[VALK_DEBUG_MAX_FRAMES];
  u64 count = 0;
  entries[count] = __frame_entry("current", expr_buf,
                                 expr->cov_file_id, expr->cov_line);
  envs[count] = env;
  count++;

  // Walk the continuation stacks, innermost eval first, frames top-down.
  for (i64 d = (i64)valk_thread_ctx.eval_stack_depth - 1; d >= 0; d--) {
    valk_eval_stack_t *stack = valk_thread_ctx.eval_stacks[d];
    if (stack == NULL) continue;
    for (i64 i = (i64)stack->count - 1; i >= 0; i--) {
      if (count >= VALK_DEBUG_MAX_FRAMES) break;
      valk_cont_frame_t *frame = &stack->frames[i];
      entries[count] = __frame_from_cont(frame);
      envs[count] = frame->env;
      count++;
    }
  }

  for (i64 i = (i64)count - 1; i >= 0; i--) {
    frames = valk_lval_qcons(entries[i], frames);
  }

  valk_lval_t *heap_frames = valk_evacuate_to_heap(frames);
  valk_mutex_lock(&g_dbg.lock);
  g_dbg.frames_handle = valk_handle_create(&valk_sys->handle_table, heap_frames);
  memcpy(g_dbg.frame_envs, envs, count * sizeof(valk_lenv_t *));
  g_dbg.frame_count = count;
  valk_mutex_unlock(&g_dbg.lock);
}

static void __clear_snapshot(void) {
  valk_mutex_lock(&g_dbg.lock);
  valk_handle_release(&valk_sys->handle_table, g_dbg.frames_handle);
  g_dbg.frames_handle = (valk_handle_t){0, 0};
  g_dbg.frame_count = 0;
  valk_mutex_unlock(&g_dbg.lock);
}

// --- the hook --------------------------------------------------------------

void valk_debug_eval_hook(void) {
  valk_lval_t *expr = valk_thread_ctx.eval_expr;
  if (expr == NULL || LVAL_TYPE(expr) != LVAL_CONS ||
      (expr->flags & LVAL_FLAG_QUOTED)) {
    return;
  }
  u16 fid = expr->cov_file_id;
  u16 line = expr->cov_line;
  if (fid == 0 || line == 0) return;

  u64 tid = valk_thread_ctx.gc_registered ? valk_thread_ctx.gc_thread_id
                                          : (u64)0xFFFF;
  u64 me = __dbg_key(tid, fid, line);

  u64 sup = atomic_load_explicit(&g_dbg.suppress_key, memory_order_relaxed);
  if (sup != 0 && (sup >> 32) == (tid + 1) && sup != me) {
    atomic_store_explicit(&g_dbg.suppress_key, 0, memory_order_relaxed);
    sup = 0;
  }

  bool hit = false;
  u64 stepk = atomic_load_explicit(&g_dbg.step_key, memory_order_acquire);
  if (stepk != 0 && (stepk >> 32) == (tid + 1)) {
    u64 depth = valk_thread_ctx.call_depth;
    bool depth_ok =
        g_dbg.step_mode == VALK_DEBUG_RESUME_STEP_OVER
            ? depth <= g_dbg.step_depth
            : (g_dbg.step_mode == VALK_DEBUG_RESUME_STEP_OUT
                   ? depth < g_dbg.step_depth
                   : true);
    bool line_ok = stepk != me || g_dbg.step_mode == VALK_DEBUG_RESUME_STEP_OUT;
    if (depth_ok && line_ok) {
      atomic_store(&g_dbg.step_key, 0);
      hit = true;
    }
  } else if (__bp_match(fid, line)) {
    hit = (sup != me);
  }
  if (!hit) return;

  int expected = 0;
  if (!atomic_compare_exchange_strong(&g_dbg.paused, &expected, 1)) {
    return;  // another thread is paused; v1 pauses one thread at a time
  }

  g_dbg.paused_tid = tid;
  g_dbg.paused_file = fid;
  g_dbg.paused_line = line;
  atomic_store(&g_dbg.resume_action, 0);
  __publish_snapshot(expr, valk_thread_ctx.eval_env);
  atomic_store(&g_dbg.paused, 2);  // 2 = paused with snapshot published

  // GC-transparent park (the aio/run pattern): STW wakes us, we participate
  // in the collection via the safepoint, then re-park until resumed.
  for (;;) {
    u64 seq = valk_gc_park_prepare();
    VALK_GC_SAFE_POINT();
    if (atomic_load_explicit(&g_dbg.resume_action, memory_order_acquire) != 0) {
      break;
    }
    valk_gc_thread_park_seq(seq, 100);
  }

  u32 action = atomic_exchange(&g_dbg.resume_action, 0);
  __clear_snapshot();

  atomic_store_explicit(&g_dbg.suppress_key, me, memory_order_relaxed);
  valk_debug_resume_e mode = (valk_debug_resume_e)(action - 1);
  if (mode != VALK_DEBUG_RESUME_CONTINUE) {
    g_dbg.step_mode = mode;
    g_dbg.step_depth = valk_thread_ctx.call_depth;
    atomic_store(&g_dbg.step_key, me);
  }
  __dbg_update_active();
  atomic_store(&g_dbg.paused, 0);
}

// --- controller side -------------------------------------------------------

bool valk_debug_paused(void) { return atomic_load(&g_dbg.paused) == 2; }

valk_lval_t *valk_debug_state(void) {
  if (!valk_debug_paused()) return valk_lval_nil();
  valk_mutex_lock(&g_dbg.lock);
  const char *fname = valk_source_get_filename(g_dbg.paused_file);
  valk_lval_t *res = valk_lval_cons(valk_lval_sym(":file"),
    valk_lval_cons(valk_lval_str(fname ? fname : "?"),
    valk_lval_cons(valk_lval_sym(":line"),
    valk_lval_cons(valk_lval_num(g_dbg.paused_line),
    valk_lval_cons(valk_lval_sym(":expr"),
    valk_lval_cons(valk_lval_str(g_dbg.paused_expr), valk_lval_nil()))))));
  res->flags |= LVAL_FLAG_QUOTED;
  valk_mutex_unlock(&g_dbg.lock);
  return res;
}

valk_lval_t *valk_debug_frames(void) {
  if (!valk_debug_paused()) return valk_lval_nil();
  valk_mutex_lock(&g_dbg.lock);
  valk_lval_t *frames = valk_handle_resolve(&valk_sys->handle_table,
                                            g_dbg.frames_handle);
  valk_mutex_unlock(&g_dbg.lock);
  return frames ? frames : valk_lval_nil();
}

valk_lenv_t *valk_debug_frame_env(u64 index) {
  if (!valk_debug_paused()) return NULL;
  valk_mutex_lock(&g_dbg.lock);
  valk_lenv_t *env =
      index < g_dbg.frame_count ? g_dbg.frame_envs[index] : NULL;
  valk_mutex_unlock(&g_dbg.lock);
  return env;
}

bool valk_debug_resume(valk_debug_resume_e mode) {
  if (atomic_load(&g_dbg.paused) != 2) return false;
  atomic_store(&g_dbg.resume_action, (u32)mode + 1);
  if (valk_sys) valk_system_wake_parked(valk_sys);
  return true;
}

#endif
