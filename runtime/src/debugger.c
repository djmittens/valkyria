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
#define VALK_DEBUG_MAX_PAUSED 16

_Atomic u32 valk_debug_active = 0;

typedef struct {
  u32 id;
  u16 file_id;
  u16 line;
} valk_debug_bp_t;

// One pause slot per concurrently-paused thread. Claimed by the pausing
// thread via CAS on state (0 free -> 1 claiming -> 2 paused -> 0).
typedef struct {
  _Atomic int state;
  _Atomic u32 resume_action;  // 0 none, else valk_debug_resume_e + 1
  u64 tid;
  u16 file;
  u16 line;
  char expr[128];
  valk_handle_t frames_handle;
  valk_lenv_t *frame_envs[VALK_DEBUG_MAX_FRAMES];
  u64 frame_count;
} valk_debug_pause_slot_t;

// Per-thread step/suppress state, claimed once per thread (owner = tid+1,
// never released). Keys pack ((tid+1) << 32) | (file_id << 16) | line so
// the hook reads them race-free. step_mode/step_depth are written by the
// owning thread before it publishes step_key and read back only by that
// same thread, so plain fields.
typedef struct {
  _Atomic u64 owner;
  _Atomic u64 step_key;
  _Atomic u64 suppress_key;
  valk_debug_resume_e step_mode;
  u64 step_depth;
} valk_debug_thread_state_t;

static struct {
  valk_mutex_t lock;
  bool lock_init;
  _Atomic bool enabled;

  valk_debug_bp_t bps[VALK_DEBUG_MAX_BREAKPOINTS];
  _Atomic u32 bp_count;
  u32 next_bp_id;

  valk_debug_pause_slot_t slots[VALK_DEBUG_MAX_PAUSED];
  valk_debug_thread_state_t tstates[VALK_DEBUG_MAX_PAUSED];
  _Atomic u32 step_active;
  // Pending async pause: requester tid+1 (0 = none). The requesting thread
  // never consumes its own request, so a single-threaded debug server can
  // pause the app without parking itself.
  _Atomic u64 pause_request;
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
             atomic_load(&g_dbg.step_active) > 0 ||
             atomic_load(&g_dbg.pause_request) != 0);
  atomic_store(&valk_debug_active, on ? 1 : 0);
}

static valk_debug_thread_state_t *__thread_state(u64 tid) {
  for (u32 i = 0; i < VALK_DEBUG_MAX_PAUSED; i++) {
    if (atomic_load_explicit(&g_dbg.tstates[i].owner, memory_order_acquire) ==
        tid + 1) {
      return &g_dbg.tstates[i];
    }
  }
  for (u32 i = 0; i < VALK_DEBUG_MAX_PAUSED; i++) {
    u64 expected = 0;
    if (atomic_compare_exchange_strong(&g_dbg.tstates[i].owner, &expected,
                                       tid + 1)) {
      return &g_dbg.tstates[i];
    }
  }
  return NULL;  // LCOV_EXCL_LINE more than MAX_PAUSED distinct eval threads
}

void valk_debug_enable(void) {
  __dbg_lock_init();
  atomic_store(&g_dbg.enabled, true);
  __dbg_update_active();
}

void valk_debug_disable(void) {
  atomic_store(&g_dbg.enabled, false);
  for (u32 i = 0; i < VALK_DEBUG_MAX_PAUSED; i++) {
    if (atomic_exchange(&g_dbg.tstates[i].step_key, 0) != 0) {
      atomic_fetch_sub(&g_dbg.step_active, 1);
    }
  }
  atomic_store(&g_dbg.pause_request, 0);
  __dbg_update_active();
  while (valk_debug_paused()) {
    valk_debug_resume_tid(-1, VALK_DEBUG_RESUME_CONTINUE);
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

void valk_debug_pause_request(void) {
  u64 tid = valk_thread_ctx.gc_registered ? valk_thread_ctx.gc_thread_id
                                          : (u64)0xFFFF;
  atomic_store(&g_dbg.pause_request, tid + 1);
  __dbg_update_active();
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

// Builds the snapshot into the slot (frames data via the handle table, env
// pointers in a C array). Runs on the paused thread; envs stay valid while
// parked because this thread's GC participation keeps marking them.
static void __publish_snapshot(valk_debug_pause_slot_t *slot,
                               valk_lval_t *expr, valk_lenv_t *env) {
  slot->frame_count = 0;
  valk_lval_t *frames = valk_lval_nil();

  char expr_buf[128];
  __expr_summary(expr, expr_buf, sizeof(expr_buf));
  snprintf(slot->expr, sizeof(slot->expr), "%s", expr_buf);

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
  slot->frames_handle = valk_handle_create(&valk_sys->handle_table, heap_frames);
  memcpy(slot->frame_envs, envs, count * sizeof(valk_lenv_t *));
  slot->frame_count = count;
  valk_mutex_unlock(&g_dbg.lock);
}

static void __clear_snapshot(valk_debug_pause_slot_t *slot) {
  valk_mutex_lock(&g_dbg.lock);
  valk_handle_release(&valk_sys->handle_table, slot->frames_handle);
  slot->frames_handle = (valk_handle_t){0, 0};
  slot->frame_count = 0;
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

  valk_debug_thread_state_t *ts = __thread_state(tid);
  if (ts == NULL) return;  // LCOV_EXCL_LINE thread-state table exhausted

  u64 sup = atomic_load_explicit(&ts->suppress_key, memory_order_relaxed);
  if (sup != 0 && sup != me) {
    atomic_store_explicit(&ts->suppress_key, 0, memory_order_relaxed);
    sup = 0;
  }

  bool hit = false;
  u64 stepk = atomic_load_explicit(&ts->step_key, memory_order_acquire);
  if (stepk != 0) {
    u64 depth = valk_thread_ctx.call_depth;
    bool depth_ok =
        ts->step_mode == VALK_DEBUG_RESUME_STEP_OVER
            ? depth <= ts->step_depth
            : (ts->step_mode == VALK_DEBUG_RESUME_STEP_OUT
                   ? depth < ts->step_depth
                   : true);
    bool line_ok = stepk != me || ts->step_mode == VALK_DEBUG_RESUME_STEP_OUT;
    if (depth_ok && line_ok) {
      atomic_store(&ts->step_key, 0);
      atomic_fetch_sub(&g_dbg.step_active, 1);
      hit = true;
    }
  } else if (__bp_match(fid, line)) {
    hit = (sup != me);
  }
  if (!hit) {
    u64 pr = atomic_load_explicit(&g_dbg.pause_request, memory_order_relaxed);
    if (pr != 0 && pr != tid + 1 &&
        atomic_compare_exchange_strong(&g_dbg.pause_request, &pr, 0)) {
      hit = true;
    }
  }
  if (!hit) return;

  valk_debug_pause_slot_t *slot = NULL;
  for (u32 i = 0; i < VALK_DEBUG_MAX_PAUSED; i++) {
    int expected = 0;
    if (atomic_compare_exchange_strong(&g_dbg.slots[i].state, &expected, 1)) {
      slot = &g_dbg.slots[i];
      break;
    }
  }
  if (slot == NULL) {
    return;  // LCOV_EXCL_LINE all pause slots taken; skip through
  }

  slot->tid = tid;
  slot->file = fid;
  slot->line = line;
  atomic_store(&slot->resume_action, 0);
  __publish_snapshot(slot, expr, valk_thread_ctx.eval_env);
  atomic_store(&slot->state, 2);  // 2 = paused with snapshot published

  // GC-transparent park (the aio/run pattern): STW wakes us, we participate
  // in the collection via the safepoint, then re-park until resumed.
  for (;;) {
    u64 seq = valk_gc_park_prepare();
    VALK_GC_SAFE_POINT();
    if (atomic_load_explicit(&slot->resume_action, memory_order_acquire) != 0) {
      break;
    }
    valk_gc_thread_park_seq(seq, 100);
  }

  u32 action = atomic_exchange(&slot->resume_action, 0);
  __clear_snapshot(slot);

  atomic_store_explicit(&ts->suppress_key, me, memory_order_relaxed);
  valk_debug_resume_e mode = (valk_debug_resume_e)(action - 1);
  if (mode != VALK_DEBUG_RESUME_CONTINUE) {
    ts->step_mode = mode;
    ts->step_depth = valk_thread_ctx.call_depth;
    atomic_store(&ts->step_key, me);
    atomic_fetch_add(&g_dbg.step_active, 1);
  }
  __dbg_update_active();
  atomic_store(&slot->state, 0);
}

// --- controller side -------------------------------------------------------

// tid < 0 selects the first paused thread (lowest slot index).
static valk_debug_pause_slot_t *__find_paused(i64 tid) {
  for (u32 i = 0; i < VALK_DEBUG_MAX_PAUSED; i++) {
    if (atomic_load(&g_dbg.slots[i].state) != 2) continue;
    if (tid < 0 || g_dbg.slots[i].tid == (u64)tid) return &g_dbg.slots[i];
  }
  return NULL;
}

bool valk_debug_paused(void) { return __find_paused(-1) != NULL; }

static valk_lval_t *__slot_state(valk_debug_pause_slot_t *slot) {
  const char *fname = valk_source_get_filename(slot->file);
  valk_lval_t *res = valk_lval_cons(valk_lval_sym(":tid"),
    valk_lval_cons(valk_lval_num((i64)slot->tid),
    valk_lval_cons(valk_lval_sym(":file"),
    valk_lval_cons(valk_lval_str(fname ? fname : "?"),
    valk_lval_cons(valk_lval_sym(":line"),
    valk_lval_cons(valk_lval_num(slot->line),
    valk_lval_cons(valk_lval_sym(":expr"),
    valk_lval_cons(valk_lval_str(slot->expr), valk_lval_nil()))))))));
  res->flags |= LVAL_FLAG_QUOTED;
  return res;
}

valk_lval_t *valk_debug_state_tid(i64 tid) {
  valk_mutex_lock(&g_dbg.lock);
  valk_debug_pause_slot_t *slot = __find_paused(tid);
  valk_lval_t *res = slot ? __slot_state(slot) : valk_lval_nil();
  valk_mutex_unlock(&g_dbg.lock);
  return res;
}

valk_lval_t *valk_debug_state(void) { return valk_debug_state_tid(-1); }

valk_lval_t *valk_debug_threads(void) {
  valk_mutex_lock(&g_dbg.lock);
  valk_lval_t *res = valk_lval_nil();
  for (i64 i = VALK_DEBUG_MAX_PAUSED - 1; i >= 0; i--) {
    valk_debug_pause_slot_t *slot = &g_dbg.slots[i];
    if (atomic_load(&slot->state) != 2) continue;
    res = valk_lval_qcons(__slot_state(slot), res);
  }
  valk_mutex_unlock(&g_dbg.lock);
  return res;
}

valk_lval_t *valk_debug_frames_tid(i64 tid) {
  valk_mutex_lock(&g_dbg.lock);
  valk_debug_pause_slot_t *slot = __find_paused(tid);
  valk_lval_t *frames = slot ? valk_handle_resolve(&valk_sys->handle_table,
                                                   slot->frames_handle)
                             : NULL;
  valk_mutex_unlock(&g_dbg.lock);
  return frames ? frames : valk_lval_nil();
}

valk_lval_t *valk_debug_frames(void) { return valk_debug_frames_tid(-1); }

valk_lenv_t *valk_debug_frame_env_tid(i64 tid, u64 index) {
  valk_mutex_lock(&g_dbg.lock);
  valk_debug_pause_slot_t *slot = __find_paused(tid);
  valk_lenv_t *env = (slot && index < slot->frame_count)
                         ? slot->frame_envs[index]
                         : NULL;
  valk_mutex_unlock(&g_dbg.lock);
  return env;
}

valk_lenv_t *valk_debug_frame_env(u64 index) {
  return valk_debug_frame_env_tid(-1, index);
}

bool valk_debug_resume_tid(i64 tid, valk_debug_resume_e mode) {
  valk_debug_pause_slot_t *slot = __find_paused(tid);
  if (slot == NULL) return false;
  atomic_store(&slot->resume_action, (u32)mode + 1);
  if (valk_sys) valk_system_wake_parked(valk_sys);
  return true;
}

bool valk_debug_resume(valk_debug_resume_e mode) {
  return valk_debug_resume_tid(-1, mode);
}

#endif
