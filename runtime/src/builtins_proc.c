#include "builtins_internal.h"

#include <signal.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/aio_internal.h"
#include "gc.h"
#include "pipe_internal.h"

// proc/spawn — interactive subprocess (ide/DESIGN.md section 8, primitive
// #2): uv_spawn with all three stdio streams piped. Returns
// {:proc P :stdin Pipe :stdout Pipe :stderr Pipe :wait Handle}; the pipes
// work with the existing pipe/write, pipe/on-data and pipe/close builtins,
// and the wait handle completes with {:exit-code N :term-signal N} when the
// child exits. proc/kill sends a signal; proc/pid reads the child pid.

typedef struct valk_proc {
  uv_process_t uv;
  valk_aio_system_t *sys;
  valk_async_handle_t *wait_handle;
  valk_pipe_t *in_pipe;
  valk_pipe_t *out_pipe;
  valk_pipe_t *err_pipe;
  char **argv;
  int argc;
  _Atomic int refs;  // uv process handle + lisp ref
  _Atomic bool exited;
  _Atomic i64 pid;
} valk_proc_t;

static void __proc_unref(valk_proc_t *proc) {
  if (atomic_fetch_sub(&proc->refs, 1) != 1) return;
  for (int i = 0; i < proc->argc; i++) free(proc->argv[i]);
  free(proc->argv);
  free(proc);
}

// LCOV_EXCL_START - GC destructor: called non-deterministically during sweep
static void __proc_ref_free(void *ptr) { __proc_unref(ptr); }
// LCOV_EXCL_STOP

static void __proc_close_cb(uv_handle_t *h) { __proc_unref(h->data); }

static void __proc_exit_cb(uv_process_t *uvproc, int64_t exit_status,
                           int term_signal) {
  valk_proc_t *proc = uvproc->data;
  atomic_store(&proc->exited, true);

  valk_lval_t *result;
  VALK_WITH_ALLOC((void *)valk_thread_ctx.heap) {
    valk_lval_t *fields[4] = {
      valk_lval_sym(":exit-code"), valk_lval_num((i64)exit_status),
      valk_lval_sym(":term-signal"), valk_lval_num(term_signal),
    };
    result = valk_lval_qlist(fields, 4);
  }
  valk_async_handle_complete(proc->wait_handle, result);
  uv_close((uv_handle_t *)&proc->uv, __proc_close_cb);
}

static void __proc_spawn_on_loop(void *arg) {
  VALK_GC_SAFE_POINT();
  valk_proc_t *proc = arg;
  uv_loop_t *loop = proc->sys->loops[0].uv_loop;

  uv_pipe_init(loop, &proc->in_pipe->uv, 0);
  uv_pipe_init(loop, &proc->out_pipe->uv, 0);
  uv_pipe_init(loop, &proc->err_pipe->uv, 0);
  proc->uv.data = proc;

  uv_stdio_container_t stdio[3] = {
    { .flags = UV_CREATE_PIPE | UV_READABLE_PIPE,
      .data.stream = (uv_stream_t *)&proc->in_pipe->uv },
    { .flags = UV_CREATE_PIPE | UV_WRITABLE_PIPE,
      .data.stream = (uv_stream_t *)&proc->out_pipe->uv },
    { .flags = UV_CREATE_PIPE | UV_WRITABLE_PIPE,
      .data.stream = (uv_stream_t *)&proc->err_pipe->uv },
  };
  uv_process_options_t options = {
    .file = proc->argv[0],
    .args = proc->argv,
    .stdio_count = 3,
    .stdio = stdio,
    .exit_cb = __proc_exit_cb,
  };

  int r = uv_spawn(loop, &proc->uv, &options);
  if (r != 0) {
    atomic_store(&proc->exited, true);
    proc->in_pipe->closed = true;
    proc->out_pipe->closed = true;
    proc->err_pipe->closed = true;
    valk_lval_t *err;
    VALK_WITH_ALLOC((void *)valk_thread_ctx.heap) {
      err = valk_lval_err("proc/spawn: uv_spawn failed: %s", uv_strerror(r));
    }
    valk_async_handle_fail(proc->wait_handle, err);
    uv_close((uv_handle_t *)&proc->uv, __proc_close_cb);
    uv_close((uv_handle_t *)&proc->in_pipe->uv, NULL);
    uv_close((uv_handle_t *)&proc->out_pipe->uv, NULL);
    uv_close((uv_handle_t *)&proc->err_pipe->uv, NULL);
    return;
  }
  atomic_store(&proc->pid, (i64)proc->uv.pid);
}

#define LVAL_ASSERT_PROC(args, _ref) \
  do { \
    if (LVAL_TYPE(_ref) != LVAL_REF || \
        strcmp((_ref)->ref.type, "proc") != 0) { \
      LVAL_RAISE(args, "Expected proc reference"); \
    } \
  } while (0)

static valk_lval_t *valk_builtin_proc_spawn(valk_lenv_t *e, valk_lval_t *a) {
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_GE(a, a, 2);
  LVAL_ASSERT_AIO_SYSTEM(a, valk_lval_list_nth(a, 0));
  u64 nargs = valk_lval_list_count(a);
  for (u64 i = 1; i < nargs; i++) {
    valk_lval_t *arg_i = valk_lval_list_nth(a, i);
    LVAL_ASSERT_TYPE(a, arg_i, LVAL_STR);
  }
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t *sys = valk_lval_list_nth(a, 0)->ref.ptr;
  int argc = (int)(nargs - 1);

  valk_proc_t *proc = calloc(1, sizeof(valk_proc_t));
  // LCOV_EXCL_START
  if (!proc) return valk_lval_err("proc/spawn: allocation failed");
  // LCOV_EXCL_STOP
  proc->sys = sys;
  proc->argc = argc;
  proc->argv = calloc((size_t)argc + 1, sizeof(char *));
  for (int i = 0; i < argc; i++) {
    proc->argv[i] = strdup(valk_lval_list_nth(a, i + 1)->str);
  }
  proc->argv[argc] = NULL;
  atomic_store(&proc->refs, 2);

  proc->in_pipe = calloc(1, sizeof(valk_pipe_t));
  proc->out_pipe = calloc(1, sizeof(valk_pipe_t));
  proc->err_pipe = calloc(1, sizeof(valk_pipe_t));
  proc->in_pipe->sys = sys;
  proc->out_pipe->sys = sys;
  proc->err_pipe->sys = sys;

  proc->wait_handle = valk_async_handle_new(sys, e);
  // LCOV_EXCL_START
  if (!proc->wait_handle) {
    LVAL_RAISE(a, "proc/spawn: handle alloc failed");
  }
  // LCOV_EXCL_STOP
  atomic_store_explicit(&proc->wait_handle->status, VALK_ASYNC_RUNNING,
                        memory_order_release);

  valk_aio_enqueue_task(sys, __proc_spawn_on_loop, proc);

  valk_lval_t *proc_ref;
  valk_lval_t *in_ref;
  valk_lval_t *out_ref;
  valk_lval_t *err_ref;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)valk_thread_ctx.heap) {
    proc_ref = valk_lval_ref("proc", proc, __proc_ref_free);
    in_ref = valk_lval_ref("pipe", proc->in_pipe, NULL);
    out_ref = valk_lval_ref("pipe", proc->out_pipe, NULL);
    err_ref = valk_lval_ref("pipe", proc->err_pipe, NULL);
  }
  valk_lval_t *fields[10] = {
    valk_lval_sym(":proc"), proc_ref,
    valk_lval_sym(":stdin"), in_ref,
    valk_lval_sym(":stdout"), out_ref,
    valk_lval_sym(":stderr"), err_ref,
    valk_lval_sym(":wait"), valk_lval_handle(proc->wait_handle),
  };
  return valk_lval_qlist(fields, 10);
}

typedef struct {
  valk_proc_t *proc;
  int signum;
} proc_kill_ctx_t;

static void __proc_kill_on_loop(void *arg) {
  proc_kill_ctx_t *ctx = arg;
  valk_proc_t *proc = ctx->proc;
  if (!atomic_load(&proc->exited) &&
      !uv_is_closing((uv_handle_t *)&proc->uv)) {
    uv_process_kill(&proc->uv, ctx->signum);
  }
  free(ctx);
}

static valk_lval_t *valk_builtin_proc_kill(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_GE(a, a, 1);
  valk_lval_t *proc_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_PROC(a, proc_ref);
  // LCOV_EXCL_BR_STOP
  int signum = SIGTERM;
  if (valk_lval_list_count(a) > 1) {
    valk_lval_t *sig_arg = valk_lval_list_nth(a, 1);
    LVAL_ASSERT_TYPE(a, sig_arg, LVAL_NUM);
    signum = (int)sig_arg->num;
  }

  valk_proc_t *proc = proc_ref->ref.ptr;
  proc_kill_ctx_t *ctx = malloc(sizeof(proc_kill_ctx_t));
  ctx->proc = proc;
  ctx->signum = signum;
  valk_aio_enqueue_task(proc->sys, __proc_kill_on_loop, ctx);
  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_proc_wait(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *proc_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_PROC(a, proc_ref);
  // LCOV_EXCL_BR_STOP
  valk_proc_t *proc = proc_ref->ref.ptr;
  return valk_lval_handle(proc->wait_handle);
}

static valk_lval_t *valk_builtin_proc_pid(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *proc_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_PROC(a, proc_ref);
  // LCOV_EXCL_BR_STOP
  valk_proc_t *proc = proc_ref->ref.ptr;
  return valk_lval_num(atomic_load(&proc->pid));
}

void valk_register_proc_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "proc/spawn", valk_builtin_proc_spawn);
  valk_lenv_put_builtin(env, "proc/kill", valk_builtin_proc_kill);
  valk_lenv_put_builtin(env, "proc/wait", valk_builtin_proc_wait);
  valk_lenv_put_builtin(env, "proc/pid", valk_builtin_proc_pid);
}
