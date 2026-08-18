#pragma once

#include <uv.h>

#include "aio/aio.h"
#include "gc.h"

// The "pipe" LVAL_REF payload shared by the pipe builtins (builtins_pipe.c)
// and proc/spawn (builtins_proc.c): a uv pipe end whose lifetime is managed
// by explicit pipe/close, not by GC (the ref destructor is a no-op).
typedef struct valk_pipe {
  uv_pipe_t uv;
  valk_aio_system_t *sys;
  valk_handle_t callback_handle;
  bool callback_set;
  bool closed;
} valk_pipe_t;
