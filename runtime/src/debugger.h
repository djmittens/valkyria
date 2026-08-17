#pragma once

#include "parser.h"

// Valk debugger runtime (ide/DESIGN.md section 5.2): breakpoint table keyed
// (file_id, line), an eval-loop hook that parks the hitting thread
// GC-transparently, and a frame snapshot for cross-thread inspection.
// Requires VALK_SRC_LOC (source positions on lvals).

#ifdef VALK_SRC_LOC

// Hot-path flag read once per eval iteration (same cost profile as the
// GC safepoint check).
extern _Atomic u32 valk_debug_active;

// Called from the eval loop when valk_debug_active is set. May park the
// calling thread until resumed; callers must reload eval state from
// valk_thread_ctx afterwards (GC may run while parked).
void valk_debug_eval_hook(void);

void valk_debug_enable(void);
void valk_debug_disable(void);
bool valk_debug_enabled(void);

// Breakpoints. Path is canonicalized with realpath when possible so it
// matches the loader's resolved paths. Returns breakpoint id.
u32 valk_debug_break_set(const char *path, u16 line);
bool valk_debug_break_clear(u32 id);
// List as lval data: ({:id N :file Str :line N} ...)
valk_lval_t *valk_debug_breakpoints(void);

// Paused-state inspection (any thread). Returns nil when not paused.
bool valk_debug_paused(void);
valk_lval_t *valk_debug_state(void);   // {:file Str :line N :expr Str} | nil
valk_lval_t *valk_debug_frames(void);  // ({:kind Str :fn Str :line N :file Str} ...) | nil
valk_lenv_t *valk_debug_frame_env(u64 index);  // env of frame i, or NULL

// Resume modes. Step modes re-pause the same thread at the next expression:
//   STEP_IN   on a different source line, any call depth;
//   STEP_OVER on a different source line at the same or shallower call depth;
//   STEP_OUT  at a strictly shallower call depth (any line).
typedef enum {
  VALK_DEBUG_RESUME_CONTINUE = 0,
  VALK_DEBUG_RESUME_STEP_IN,
  VALK_DEBUG_RESUME_STEP_OVER,
  VALK_DEBUG_RESUME_STEP_OUT,
} valk_debug_resume_e;

// Resume the paused thread with the given mode.
bool valk_debug_resume(valk_debug_resume_e mode);

#endif
