#include "builtins_internal.h"

#include <stdatomic.h>
#include <string.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/http2/aio_http2_client.h"
#include "gc.h"
#include "log.h"

extern valk_lval_t* valk_async_handle_await(valk_async_handle_t* handle);

// LCOV_EXCL_START - HTTP/2 server/client builtins require SSL/nghttp2 integration tests

static valk_lval_t* valk_builtin_http2_server_listen(valk_lenv_t* e,
                                                     valk_lval_t* a) {
  u64 argc = valk_lval_list_count(a);
  LVAL_ASSERT(a, argc >= 3 && argc <= 4,
              "http2/server-listen expects 3 or 4 arguments, got %zu", argc);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 2), LVAL_FUN);

  valk_aio_system_t* sys = valk_lval_list_nth(a, 0)->ref.ptr;
  int port = (int)valk_lval_list_nth(a, 1)->num;
  valk_lval_t* handler_fn = valk_lval_list_nth(a, 2);

  valk_http_server_config_t config = valk_http_server_config_default();

  if (argc == 4) {
    valk_lval_t* config_qexpr = valk_lval_list_nth(a, 3);
    LVAL_ASSERT_TYPE(a, config_qexpr, LVAL_QEXPR);

    valk_lval_t* val;

    val = valk_plist_get(config_qexpr, ":error-handler");
    if (val && LVAL_TYPE(val) == LVAL_FUN) {
      valk_lval_t* args_arr[] = { valk_lval_num(503) };
      valk_lval_t* args = valk_lval_list(args_arr, 1);

      valk_lval_t* result = valk_lval_eval_call(e, val, args);

      if (LVAL_TYPE(result) == LVAL_STR) {
        VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
          u64 len = strlen(result->str);
          char* body_copy = valk_mem_alloc(len + 1);
          memcpy(body_copy, result->str, len + 1);
          config.error_503_body = body_copy;
          config.error_503_body_len = len;
        }
      } else if (LVAL_TYPE(result) == LVAL_ERR) {
        VALK_WARN("Error handler returned error: %s, using default 503 page",
                  result->str);
      } else {
        VALK_WARN("Error handler must return string, got %s, using default 503 page",
                  valk_ltype_name(LVAL_TYPE(result)));
      }
    }
  }

  valk_lval_t* heap_handler;
  VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
    heap_handler = valk_lval_copy(handler_fn);
  }

  valk_async_handle_t* handle =
      valk_aio_http2_listen_with_config(sys,
                            "0.0.0.0",
                            port, "build/server.key", "build/server.crt",
                            NULL,
                            heap_handler,
                            &config
      );

  return valk_lval_handle(handle);
}

static valk_lval_t* valk_builtin_http2_server_port(valk_lenv_t* e,
                                                   valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  valk_lval_t* arg = valk_lval_list_nth(a, 0);
  valk_lval_t* server_ref = NULL;

  if (LVAL_TYPE(arg) == LVAL_HANDLE) {
    valk_async_handle_t* handle = arg->async.handle;
    valk_async_status_t status = valk_async_handle_get_status(handle);
    if (status != VALK_ASYNC_COMPLETED) {
      server_ref = valk_async_handle_await(handle);
      if (LVAL_TYPE(server_ref) == LVAL_ERR) {
        return server_ref;
      }
    } else {
      server_ref = atomic_load_explicit(&handle->result, memory_order_acquire);
    }
    if (!server_ref || LVAL_TYPE(server_ref) != LVAL_REF) {
      return valk_lval_err("http2/server-port: handle result is not a server ref");
    }
  } else if (LVAL_TYPE(arg) == LVAL_REF) {
    server_ref = arg;
  } else {
    return valk_lval_err("http2/server-port: expected Handle or Reference, got %s",
                         valk_ltype_name(LVAL_TYPE(arg)));
  }

  valk_aio_http_server* srv = (valk_aio_http_server*)server_ref->ref.ptr;
  if (valk_aio_http2_server_is_stopped(srv)) {
    return valk_lval_err("http2/server-port: server is stopped");
  }
  return valk_lval_num(valk_aio_http2_server_get_port(srv));
}

static valk_lval_t* valk_builtin_http2_server_stop(valk_lenv_t* e,
                                                   valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  valk_lval_t* arg = valk_lval_list_nth(a, 0);
  valk_lval_t* server_ref = NULL;

  if (LVAL_TYPE(arg) == LVAL_HANDLE) {
    valk_async_handle_t* handle = arg->async.handle;
    valk_async_status_t status = valk_async_handle_get_status(handle);
    if (status != VALK_ASYNC_COMPLETED) {
      server_ref = valk_async_handle_await(handle);
      if (LVAL_TYPE(server_ref) == LVAL_ERR) {
        return server_ref;
      }
    } else {
      server_ref = atomic_load_explicit(&handle->result, memory_order_acquire);
    }
    if (!server_ref || LVAL_TYPE(server_ref) != LVAL_REF) {
      return valk_lval_err("http2/server-stop: handle result is not a server ref");
    }
  } else if (LVAL_TYPE(arg) == LVAL_REF) {
    server_ref = arg;
  } else {
    return valk_lval_err("http2/server-stop: expected Handle or Reference, got %s",
                         valk_ltype_name(LVAL_TYPE(arg)));
  }

  valk_aio_http_server* srv = (valk_aio_http_server*)server_ref->ref.ptr;
  if (valk_aio_http2_server_is_stopped(srv)) {
    valk_aio_system_t* sys = srv->sys;
    valk_async_handle_t* handle = valk_async_handle_new(sys, nullptr);
    valk_async_handle_complete(handle, valk_lval_nil());
    return valk_lval_handle(handle);
  }

  valk_async_handle_t* stop_handle = valk_aio_http2_stop(srv);
  return valk_lval_handle(stop_handle);
}

static valk_lval_t* valk_builtin_http2_server_handle(valk_lenv_t* e,
                                                     valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_FUN);

  valk_lval_t* server_ref = valk_lval_list_nth(a, 0);
  valk_lval_t* handler_fn = valk_lval_list_nth(a, 1);

  valk_aio_http_server* server = (valk_aio_http_server*)server_ref->ref.ptr;
  if (valk_aio_http2_server_is_stopped(server)) {
    return valk_lval_err("http2/server-handle: server is stopped");
  }

  valk_lval_t* heap_handler;
  VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
    heap_handler = valk_lval_copy(handler_fn);
  }

  valk_aio_http2_server_set_handler(server, heap_handler);

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_http2_client_request(valk_lenv_t* e,
                                                       valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 4);

  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, aio_ref, LVAL_REF);
  LVAL_ASSERT(a, strcmp(aio_ref->ref.type, "aio_system") == 0,
              "First argument must be aio_system");

  valk_lval_t* host_arg = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, host_arg, LVAL_STR);

  valk_lval_t* port_arg = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, port_arg, LVAL_NUM);

  valk_lval_t* path_arg = valk_lval_list_nth(a, 3);
  LVAL_ASSERT_TYPE(a, path_arg, LVAL_STR);

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  const char* host = host_arg->str;
  int port = (int)port_arg->num;
  const char* path = path_arg->str;

  return valk_http2_client_request_impl(e, sys, host, port, path);
}

static valk_lval_t* valk_builtin_http2_client_request_with_headers(valk_lenv_t* e,
                                                                    valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 5);

  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, aio_ref, LVAL_REF);
  LVAL_ASSERT(a, strcmp(aio_ref->ref.type, "aio_system") == 0,
              "First argument must be aio_system");

  valk_lval_t* host_arg = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, host_arg, LVAL_STR);

  valk_lval_t* port_arg = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, port_arg, LVAL_NUM);

  valk_lval_t* path_arg = valk_lval_list_nth(a, 3);
  LVAL_ASSERT_TYPE(a, path_arg, LVAL_STR);

  valk_lval_t* headers_arg = valk_lval_list_nth(a, 4);
  LVAL_ASSERT_TYPE(a, headers_arg, LVAL_QEXPR);

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  const char* host = host_arg->str;
  int port = (int)port_arg->num;
  const char* path = path_arg->str;

  return valk_http2_client_request_with_headers_impl(e, sys, host, port, path, headers_arg);
}

static void valk_http2_connect_done_callback(valk_async_handle_t* handle, void* ctx_ptr) {
  VALK_GC_SAFE_POINT();

  valk_handle_t callback_handle = {.index = (u32)(uintptr_t)ctx_ptr, .generation = 0};
  valk_lval_t* cb = valk_handle_resolve(&valk_global_handle_table, callback_handle);
  if (!cb) {
    valk_handle_release(&valk_global_handle_table, callback_handle);
    return;
  }

  valk_async_status_t status = valk_async_handle_get_status(handle);
  valk_lval_t* result;

  if (status != VALK_ASYNC_COMPLETED) {
    valk_lval_t* err = atomic_load_explicit(&handle->error, memory_order_acquire);
    result = err ? err : valk_lval_err("Connection failed");
  } else {
    valk_lval_t* res = atomic_load_explicit(&handle->result, memory_order_acquire);
    result = res ? res : valk_lval_err("No connection result");
  }

  valk_lval_t* args = valk_lval_cons(result, valk_lval_nil());
  valk_lval_eval_call(cb->fun.env, cb, args);
  valk_handle_release(&valk_global_handle_table, callback_handle);
}

static valk_lval_t* valk_builtin_http2_connect(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 4);

  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, aio_ref, LVAL_REF);
  LVAL_ASSERT(a, strcmp(aio_ref->ref.type, "aio_system") == 0,
              "First argument must be aio_system");

  valk_lval_t* host_arg = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, host_arg, LVAL_STR);

  valk_lval_t* port_arg = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, port_arg, LVAL_NUM);

  valk_lval_t* callback = valk_lval_list_nth(a, 3);
  LVAL_ASSERT_TYPE(a, callback, LVAL_FUN);

  valk_aio_system_t* sys = aio_ref->ref.ptr;
  const char* host = host_arg->str;
  int port = (int)port_arg->num;

  valk_lval_t* heap_callback = valk_evacuate_to_heap(callback);
  valk_handle_t callback_handle = valk_handle_create(&valk_global_handle_table, heap_callback);

  valk_async_handle_t* connect_handle = valk_aio_http2_connect_host(sys, host, port, host);
  if (!connect_handle) {
    valk_handle_release(&valk_global_handle_table, callback_handle);
    return valk_lval_err("Failed to initiate connection");
  }

  connect_handle->on_done = valk_http2_connect_done_callback;
  connect_handle->on_done_ctx = (void*)(uintptr_t)callback_handle.index;

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_http2_request_on_conn(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 3);

  valk_lval_t* client_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, client_ref, LVAL_REF);
  LVAL_ASSERT(a, strcmp(client_ref->ref.type, "http2_client") == 0,
              "First argument must be http2_client");

  valk_lval_t* path_arg = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, path_arg, LVAL_STR);

  valk_lval_t* callback = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, callback, LVAL_FUN);

  valk_aio_http2_client* client = client_ref->ref.ptr;
  const char* path = path_arg->str;

  return valk_http2_client_request_on_conn_impl(e, client, path, callback);
}
// LCOV_EXCL_STOP

void valk_register_server_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "http2/server-listen",
                        valk_builtin_http2_server_listen);
  valk_lenv_put_builtin(env, "http2/server-port",
                        valk_builtin_http2_server_port);
  valk_lenv_put_builtin(env, "http2/server-stop",
                        valk_builtin_http2_server_stop);
  valk_lenv_put_builtin(env, "http2/server-handle",
                        valk_builtin_http2_server_handle);
  valk_lenv_put_builtin(env, "http2/client-request",
                        valk_builtin_http2_client_request);
  valk_lenv_put_builtin(env, "http2/client-request-with-headers",
                        valk_builtin_http2_client_request_with_headers);
  valk_lenv_put_builtin(env, "http2/connect",
                        valk_builtin_http2_connect);
  valk_lenv_put_builtin(env, "http2/request-on-conn",
                        valk_builtin_http2_request_on_conn);
}
