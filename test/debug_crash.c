// debug_crash.c - Direct test without fork for debugging SIGSEGV
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "collections.h"
#include "common.h"
#include "memory.h"
#include "parser.h"

typedef struct {
  int connectedCount;
  int disconnectedCount;
} valk_srv_state_t;

static void cb_onConnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->connectedCount, 1, __ATOMIC_RELAXED);
  printf("[DEBUG] Client connected (count=%d)\n", handler->connectedCount);
}

static void cb_onDisconnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->disconnectedCount, 1, __ATOMIC_RELAXED);
  printf("[DEBUG] Client disconnected (count=%d)\n", handler->disconnectedCount);
}

static void cb_onHeader(void *arg, valk_aio_handle_t *conn, u64 stream,
                        char *name, char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

static void cb_onBody(void *arg, valk_aio_handle_t *conn, u64 stream,
                      u8 flags, valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}

int main(void) {
  printf("[DEBUG] Starting test_demo_socket_server (no fork)\n");

  valk_mem_init_malloc();
  valk_aio_system_t *sys = valk_aio_start();

  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  alignas(max_align_t) u8 buf[sizeof(valk_mem_arena_t) + (24048 + (int)8e6)];
  valk_mem_arena_t *arena = (void *)buf;
  valk_mem_arena_init(arena, (24048 + (int)8e6));
  valk_http2_request_t *req;

  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)arena;
    req->method = "GET";
    req->scheme = "https";
    req->authority = "google.com";
    req->path = "/";
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  printf("[DEBUG] Starting server on port 6969...\n");
  valk_async_handle_t *hserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 6969, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", &handler, nullptr);

  valk_lval_t *server_result = valk_async_handle_await(hserv);
  if (LVAL_TYPE(server_result) == LVAL_ERR) {
    fprintf(stderr, "Failed to start server: %s\n", server_result->str);
    return 1;
  }
  printf("[DEBUG] Server started\n");

  printf("[DEBUG] Connecting client...\n");
  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", 6969, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);

  if (LVAL_TYPE(client_result) == LVAL_ERR) {
    fprintf(stderr, "Error creating client: %s\n", client_result->str);
    return 1;
  }

  valk_aio_http2_client *client = client_result->ref.ptr;
  printf("[DEBUG] Client connected, sending request...\n");

  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  printf("[DEBUG] Awaiting response...\n");
  valk_lval_t *res = valk_async_handle_await(hres);

  if (LVAL_TYPE(res) == LVAL_ERR) {
    fprintf(stderr, "Request failed: %s\n", res->str);
    return 1;
  }

  valk_http2_response_t *response = res->ref.ptr;
  printf("[DEBUG] Response received: %s\n", (char *)response->body);

  if (strcmp((char *)response->body, VALK_HTTP_MOTD) != 0) {
    fprintf(stderr, "Did not receive the expected result from the server "
                    "Expected: [%s] Actual: [%s]\n",
            VALK_HTTP_MOTD, (char *)response->body);
    return 1;
  }

  printf("[DEBUG] Response matches expected MOTD\n");

  printf("[DEBUG] Stopping AIO system...\n");
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  printf("[DEBUG] Test completed successfully!\n");
  return 0;
}
