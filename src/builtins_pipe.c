#include "builtins_internal.h"

#include <stdlib.h>
#include <string.h>
#include <uv.h>

#include "aio/aio.h"
#include "aio/aio_internal.h"
#include "gc.h"

#define PIPE_READ_BUF_INIT 4096

typedef struct valk_pipe {
  uv_pipe_t uv;
  valk_aio_system_t *sys;
  valk_handle_t callback_handle;
  bool callback_set;
  bool closed;
} valk_pipe_t;

typedef struct {
  uv_write_t req;
  char *data;
} pipe_write_req_t;

typedef struct valk_lsp_reader {
  valk_pipe_t *pipe;
  valk_handle_t callback_handle;
  char *buf;
  sz buf_len;
  sz buf_cap;
  i64 content_length;
  bool in_body;
} valk_lsp_reader_t;

typedef struct {
  valk_aio_system_t *sys;
  valk_handle_t fn_handle;
  valk_handle_t arg_handle;
  valk_handle_t cb_handle;
} dispatch_ctx_t;

typedef struct {
  valk_aio_system_t *sys;
  valk_handle_t cb_handle;
  valk_handle_t result_handle;
} dispatch_completion_t;

static _Atomic(u64) g_dispatch_rr = 0;

static void __pipe_free(void *ptr) { // LCOV_EXCL_LINE
  (void)ptr;                        // LCOV_EXCL_LINE
}                                   // LCOV_EXCL_LINE

static void __pipe_alloc_cb(uv_handle_t *handle, size_t suggested, uv_buf_t *buf) {
  (void)handle;
  (void)suggested;
  buf->base = malloc(PIPE_READ_BUF_INIT);
  buf->len = PIPE_READ_BUF_INIT;
}

static void __pipe_read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
  VALK_GC_SAFE_POINT();

  valk_pipe_t *pipe = (valk_pipe_t *)stream;

  // LCOV_EXCL_START — UV_EOF/error paths triggered by peer close, not testable in fork-based tests
  if (nread == UV_EOF || nread == 0) {
    free(buf->base);
    if (nread == UV_EOF && !pipe->closed) {
      pipe->closed = true;
      if (pipe->callback_set) {
        valk_lval_t *cb = valk_handle_resolve(&valk_sys->handle_table, pipe->callback_handle);
        if (cb) {
          valk_lval_t *args = valk_lval_cons(valk_lval_nil(), valk_lval_nil());
          valk_lval_t *result = valk_lval_eval_call(cb->fun.env, cb, args);
          (void)result;
        }
      }
    }
    return;
  }

  if (nread < 0) {
    free(buf->base);
    return;
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_START — callback_set always true (read starts via pipe/on-data which sets it); cb null = handle table race
  if (pipe->callback_set) {
    valk_lval_t *cb = valk_handle_resolve(&valk_sys->handle_table, pipe->callback_handle);
    if (cb) {
      // LCOV_EXCL_STOP
      char *copy = malloc(nread + 1);
      memcpy(copy, buf->base, nread);
      copy[nread] = '\0';
      valk_lval_t *chunk = valk_lval_str(copy);
      free(copy);
      valk_lval_t *args = valk_lval_cons(chunk, valk_lval_nil());
      valk_lval_t *result = valk_lval_eval_call(cb->fun.env, cb, args);
      (void)result;
    }
  }

  free(buf->base);
}

typedef struct {
  valk_aio_system_t *sys;
  valk_pipe_t *pipe;
  int fd;
} pipe_init_ctx_t;

static void __pipe_init_on_loop(void *ctx) {
  pipe_init_ctx_t *init = (pipe_init_ctx_t *)ctx;
  valk_pipe_t *pipe = init->pipe;

  uv_pipe_init(init->sys->eventloop, &pipe->uv, 0);
  uv_pipe_open(&pipe->uv, init->fd);

  free(init);
}

static valk_lval_t *valk_builtin_pipe_stdin_open(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);

  valk_aio_system_t *sys = sys_arg->ref.ptr;

  valk_pipe_t *pipe = calloc(1, sizeof(valk_pipe_t));
  // LCOV_EXCL_START
  if (!pipe) return valk_lval_err("pipe/stdin-open: allocation failed");
  // LCOV_EXCL_STOP
  pipe->sys = sys;

  pipe_init_ctx_t *ctx = malloc(sizeof(pipe_init_ctx_t));
  ctx->sys = sys;
  ctx->pipe = pipe;
  ctx->fd = 0;
  valk_aio_enqueue_task(sys, __pipe_init_on_loop, ctx);

  valk_lval_t *ref;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)valk_thread_ctx.heap) {
    ref = valk_lval_ref("pipe", pipe, __pipe_free);
  }
  return ref;
}

static valk_lval_t *valk_builtin_pipe_stdout_open(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);

  valk_aio_system_t *sys = sys_arg->ref.ptr;

  valk_pipe_t *pipe = calloc(1, sizeof(valk_pipe_t));
  // LCOV_EXCL_START
  if (!pipe) return valk_lval_err("pipe/stdout-open: allocation failed");
  // LCOV_EXCL_STOP
  pipe->sys = sys;

  pipe_init_ctx_t *ctx = malloc(sizeof(pipe_init_ctx_t));
  ctx->sys = sys;
  ctx->pipe = pipe;
  ctx->fd = 1;
  valk_aio_enqueue_task(sys, __pipe_init_on_loop, ctx);

  valk_lval_t *ref;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)valk_thread_ctx.heap) {
    ref = valk_lval_ref("pipe", pipe, __pipe_free);
  }
  return ref;
}

#define LVAL_ASSERT_PIPE(args, _ref) \
  do { \
    if (LVAL_TYPE(_ref) != LVAL_REF || strcmp((_ref)->ref.type, "pipe") != 0) { \
      LVAL_RAISE(args, "Expected pipe reference"); \
    } \
  } while (0)

static void __pipe_write_cb(uv_write_t *req, int status) {
  (void)status;
  pipe_write_req_t *wr = (pipe_write_req_t *)req;
  free(wr->data);
  free(wr);
}

typedef struct {
  valk_pipe_t *pipe;
  char *data;
  sz len;
} pipe_write_ctx_t;

static void __pipe_write_on_loop(void *ctx) {
  pipe_write_ctx_t *wctx = (pipe_write_ctx_t *)ctx;

  pipe_write_req_t *req = malloc(sizeof(pipe_write_req_t));
  req->data = wctx->data;
  req->req.data = req;

  uv_buf_t buf = uv_buf_init(wctx->data, wctx->len);
  uv_write(&req->req, (uv_stream_t *)&wctx->pipe->uv, &buf, 1, __pipe_write_cb);

  free(wctx);
}

static valk_lval_t *valk_builtin_pipe_write(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *pipe_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *str_arg = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_PIPE(a, pipe_ref);
  LVAL_ASSERT_TYPE(a, str_arg, LVAL_STR);

  valk_pipe_t *pipe = pipe_ref->ref.ptr;
  const char *s = str_arg->str;
  sz slen = strlen(s);

  char *copy = malloc(slen);
  memcpy(copy, s, slen);

  pipe_write_ctx_t *ctx = malloc(sizeof(pipe_write_ctx_t));
  ctx->pipe = pipe;
  ctx->data = copy;
  ctx->len = slen;
  valk_aio_enqueue_task(pipe->sys, __pipe_write_on_loop, ctx);

  return valk_lval_nil();
}

static void __pipe_start_read_on_loop(void *ctx) {
  valk_pipe_t *pipe = (valk_pipe_t *)ctx;
  uv_read_start((uv_stream_t *)&pipe->uv, __pipe_alloc_cb, __pipe_read_cb);
}

static valk_lval_t *valk_builtin_pipe_on_data(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *pipe_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *cb_arg = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_PIPE(a, pipe_ref);
  LVAL_ASSERT_TYPE(a, cb_arg, LVAL_FUN);

  valk_pipe_t *pipe = pipe_ref->ref.ptr;

  valk_lval_t *heap_cb = valk_evacuate_to_heap(cb_arg);
  pipe->callback_handle = valk_handle_create(&valk_sys->handle_table, heap_cb);
  pipe->callback_set = true;

  valk_aio_enqueue_task(pipe->sys, __pipe_start_read_on_loop, pipe);

  return valk_lval_nil();
}

static void __pipe_close_handle_cb(uv_handle_t *handle) { // LCOV_EXCL_LINE
  (void)handle;                                           // LCOV_EXCL_LINE
}                                                         // LCOV_EXCL_LINE

typedef struct {
  valk_pipe_t *pipe;
} pipe_close_ctx_t;

static void __pipe_close_on_loop(void *ctx) {
  pipe_close_ctx_t *cctx = (pipe_close_ctx_t *)ctx;
  valk_pipe_t *pipe = cctx->pipe;

  if (!uv_is_closing((uv_handle_t *)&pipe->uv)) {
    uv_close((uv_handle_t *)&pipe->uv, __pipe_close_handle_cb);
  }

  if (pipe->callback_set) {
    valk_handle_release(&valk_sys->handle_table, pipe->callback_handle);
    pipe->callback_set = false;
  }

  free(cctx);
}

static valk_lval_t *valk_builtin_pipe_close(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *pipe_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_PIPE(a, pipe_ref);

  valk_pipe_t *pipe = pipe_ref->ref.ptr;
  pipe->closed = true;

  pipe_close_ctx_t *ctx = malloc(sizeof(pipe_close_ctx_t));
  ctx->pipe = pipe;
  valk_aio_enqueue_task(pipe->sys, __pipe_close_on_loop, ctx);

  return valk_lval_nil();
}

static void __lsp_reader_try_parse(valk_lsp_reader_t *reader) {
  while (reader->buf_len > 0) {
    if (!reader->in_body) {
      char *header_end = memmem(reader->buf, reader->buf_len, "\r\n\r\n", 4);
      if (!header_end) return;

      char *cl = memmem(reader->buf, header_end - reader->buf, "Content-Length: ", 16);
      if (!cl) {
        sz skip = (header_end + 4) - reader->buf;
        reader->buf_len -= skip;
        memmove(reader->buf, header_end + 4, reader->buf_len);
        continue;
      }

      reader->content_length = strtol(cl + 16, NULL, 10);
      if (reader->content_length <= 0) {
        sz skip = (header_end + 4) - reader->buf;
        reader->buf_len -= skip;
        memmove(reader->buf, header_end + 4, reader->buf_len);
        continue;
      }

      sz header_size = (header_end + 4) - reader->buf;
      reader->buf_len -= header_size;
      memmove(reader->buf, header_end + 4, reader->buf_len);
      reader->in_body = true;
    }

    if (reader->in_body) {
      if ((i64)reader->buf_len < reader->content_length) return;

      char saved = reader->buf[reader->content_length];
      reader->buf[reader->content_length] = '\0';

      // LCOV_EXCL_START — cb null = handle table race; callback_handle set at reader creation
      valk_lval_t *cb = valk_handle_resolve(&valk_sys->handle_table, reader->callback_handle);
      if (cb) {
      // LCOV_EXCL_STOP
      valk_lval_t *body_str = valk_lval_str(reader->buf);
        valk_lval_t *args = valk_lval_cons(body_str, valk_lval_nil());
        valk_lval_t *result = valk_lval_eval_call(cb->fun.env, cb, args);
        if (LVAL_TYPE(result) == LVAL_ERR) {
          fprintf(stderr, "[valk-lsp] handler error: %s\n", result->str);
        }
      }

      reader->buf[reader->content_length] = saved;
      sz consumed = reader->content_length;
      reader->buf_len -= consumed;
      memmove(reader->buf, reader->buf + consumed, reader->buf_len);
      reader->content_length = -1;
      reader->in_body = false;
    }
  }
}

static void __lsp_reader_alloc_cb(uv_handle_t *handle, size_t suggested, uv_buf_t *buf) {
  (void)handle;
  (void)suggested;
  buf->base = malloc(PIPE_READ_BUF_INIT);
  buf->len = PIPE_READ_BUF_INIT;
}

static void __lsp_reader_read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
  VALK_GC_SAFE_POINT();

  valk_pipe_t *pipe = (valk_pipe_t *)stream;
  valk_lsp_reader_t *reader = pipe->uv.data;

  // LCOV_EXCL_START — UV_EOF triggers shutdown, not testable without real editor connection
  if (nread == UV_EOF || nread == 0) {
    free(buf->base);
    if (nread == UV_EOF) {
      pipe->closed = true;
      valk_aio_system_t *sys = pipe->sys;
      if (sys && !sys->shuttingDown) {
        valk_system_initiate_shutdown(valk_sys, 0);
      }
    }
    return;
  }

  if (nread < 0) {
    free(buf->base);
    return;
  }
  // LCOV_EXCL_STOP

  sz needed = reader->buf_len + nread;
  if (needed > reader->buf_cap) {
    while (reader->buf_cap < needed) reader->buf_cap *= 2;
    reader->buf = realloc(reader->buf, reader->buf_cap);
  }
  memcpy(reader->buf + reader->buf_len, buf->base, nread);
  reader->buf_len += nread;
  free(buf->base);

  __lsp_reader_try_parse(reader);
}

typedef struct {
  valk_aio_system_t *sys;
  valk_pipe_t *pipe;
  valk_lsp_reader_t *reader;
} lsp_reader_init_ctx_t;

static void __lsp_reader_init_on_loop(void *ctx) {
  lsp_reader_init_ctx_t *init = (lsp_reader_init_ctx_t *)ctx;
  valk_pipe_t *pipe = init->pipe;

  pipe->uv.data = init->reader;
  uv_read_start((uv_stream_t *)&pipe->uv, __lsp_reader_alloc_cb, __lsp_reader_read_cb);

  free(init);
}

static valk_lval_t *valk_builtin_pipe_lsp_reader(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *pipe_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *cb_arg = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_PIPE(a, pipe_ref);
  LVAL_ASSERT_TYPE(a, cb_arg, LVAL_FUN);

  valk_pipe_t *pipe = pipe_ref->ref.ptr;

  valk_lsp_reader_t *reader = calloc(1, sizeof(valk_lsp_reader_t));
  // LCOV_EXCL_START
  if (!reader) return valk_lval_err("pipe/lsp-reader: allocation failed");
  // LCOV_EXCL_STOP
  reader->pipe = pipe;
  reader->buf = malloc(PIPE_READ_BUF_INIT);
  reader->buf_cap = PIPE_READ_BUF_INIT;
  reader->buf_len = 0;
  reader->content_length = -1;
  reader->in_body = false;

  valk_lval_t *heap_cb = valk_evacuate_to_heap(cb_arg);
  reader->callback_handle = valk_handle_create(&valk_sys->handle_table, heap_cb);

  lsp_reader_init_ctx_t *ctx = malloc(sizeof(lsp_reader_init_ctx_t));
  ctx->sys = pipe->sys;
  ctx->pipe = pipe;
  ctx->reader = reader;
  valk_aio_enqueue_task(pipe->sys, __lsp_reader_init_on_loop, ctx);

  valk_lval_t *ref;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)valk_thread_ctx.heap) {
    ref = valk_lval_ref("lsp_reader", reader, NULL);
  }
  return ref;
}

static void __dispatch_completion_on_loop0(void *ctx) {
  VALK_GC_SAFE_POINT();

  dispatch_completion_t *comp = (dispatch_completion_t *)ctx;

  // cb and result are kept GC-reachable via the handle table (walked
  // by valk_handle_table_visit in visit_global_roots) until their
  // handles are released below. The intermediate `args` cons is walked
  // via eval_calling_args once valk_lval_eval_call → apply_func_iter
  // entry sets it. The window between cons construction and eval_call
  // is straight-line C with no allocator calls. No manual roots needed.
  valk_lval_t *cb = valk_handle_resolve(&valk_sys->handle_table, comp->cb_handle);
  valk_lval_t *result = valk_handle_resolve(&valk_sys->handle_table, comp->result_handle);

  // LCOV_EXCL_START — handles just created in dispatch; null = handle table race
  if (cb && result) {
    // LCOV_EXCL_STOP
    valk_lval_t *args = valk_lval_cons(result, valk_lval_nil());
    valk_lval_t *r = valk_lval_eval_call(cb->fun.env, cb, args);
    if (LVAL_TYPE(r) == LVAL_ERR) {
      fprintf(stderr, "[aio/dispatch] callback error: %s\n", r->str);
    }
  }

  valk_handle_release(&valk_sys->handle_table, comp->cb_handle);
  valk_handle_release(&valk_sys->handle_table, comp->result_handle);
  free(comp);
}

static void __dispatch_worker(void *ctx) {
  VALK_GC_SAFE_POINT();

  dispatch_ctx_t *dctx = (dispatch_ctx_t *)ctx;

  // fn and arg stay reachable via the handle table (walked by
  // valk_handle_table_visit) until released below. `args` (the cons)
  // and intermediate locals are reachable via the conservative
  // native-stack scan (gc_mark.c::scan_thread_native_stack). Parking
  // `result`/`heap_result` in eval_value covers them across
  // handle_release + evacuate_to_heap + handle_create — those can
  // each transitively touch the allocator + safepoint.
  valk_lval_t *fn = valk_handle_resolve(&valk_sys->handle_table, dctx->fn_handle);
  valk_lval_t *arg = valk_handle_resolve(&valk_sys->handle_table, dctx->arg_handle);

  valk_lval_t *args = valk_lval_cons(arg, valk_lval_nil());
  valk_lval_t *result = valk_lval_eval_call(fn->fun.env, fn, args);
  valk_thread_ctx.eval_value = result;

  valk_handle_release(&valk_sys->handle_table, dctx->fn_handle);
  valk_handle_release(&valk_sys->handle_table, dctx->arg_handle);

  valk_lval_t *heap_result = valk_evacuate_to_heap(result);
  valk_thread_ctx.eval_value = heap_result;

  dispatch_completion_t *comp = malloc(sizeof(dispatch_completion_t));
  comp->sys = dctx->sys;
  comp->cb_handle = dctx->cb_handle;
  comp->result_handle = valk_handle_create(&valk_sys->handle_table, heap_result);

  valk_thread_ctx.eval_value = NULL;

  valk_aio_loop_enqueue_task(&dctx->sys->loops[0], __dispatch_completion_on_loop0, comp);

  free(dctx);
}

static valk_lval_t *valk_builtin_aio_dispatch(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 4);
  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  valk_lval_t *fn_arg = valk_lval_list_nth(a, 1);
  valk_lval_t *arg_val = valk_lval_list_nth(a, 2);
  valk_lval_t *cb_arg = valk_lval_list_nth(a, 3);

  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);
  LVAL_ASSERT_TYPE(a, fn_arg, LVAL_FUN);
  LVAL_ASSERT_TYPE(a, cb_arg, LVAL_FUN);

  valk_aio_system_t *sys = sys_arg->ref.ptr;

  valk_lval_t *heap_fn = valk_evacuate_to_heap(fn_arg);
  valk_lval_t *heap_arg = valk_evacuate_to_heap(arg_val);
  valk_lval_t *heap_cb = valk_evacuate_to_heap(cb_arg);

  dispatch_ctx_t *ctx = malloc(sizeof(dispatch_ctx_t));
  // LCOV_EXCL_START
  if (!ctx) return valk_lval_err("aio/dispatch: allocation failed");
  // LCOV_EXCL_STOP
  ctx->sys = sys;
  ctx->fn_handle = valk_handle_create(&valk_sys->handle_table, heap_fn);
  ctx->arg_handle = valk_handle_create(&valk_sys->handle_table, heap_arg);
  ctx->cb_handle = valk_handle_create(&valk_sys->handle_table, heap_cb);

  u32 num_loops = sys->num_loops;
  valk_aio_loop_t *target;
  if (num_loops > 1) {
    u64 idx = atomic_fetch_add(&g_dispatch_rr, 1);
    target = &sys->loops[1 + (idx % (num_loops - 1))];
  } else {
    target = &sys->loops[0];
  }

  valk_aio_loop_enqueue_task(target, __dispatch_worker, ctx);

  return valk_lval_nil();
}

void valk_register_pipe_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "pipe/stdin-open", valk_builtin_pipe_stdin_open);
  valk_lenv_put_builtin(env, "pipe/stdout-open", valk_builtin_pipe_stdout_open);
  valk_lenv_put_builtin(env, "pipe/write", valk_builtin_pipe_write);
  valk_lenv_put_builtin(env, "pipe/on-data", valk_builtin_pipe_on_data);
  valk_lenv_put_builtin(env, "pipe/close", valk_builtin_pipe_close);
  valk_lenv_put_builtin(env, "pipe/lsp-reader", valk_builtin_pipe_lsp_reader);
  valk_lenv_put_builtin(env, "aio/dispatch", valk_builtin_aio_dispatch);
}
