// debug_crash.c - Direct test without fork for debugging SIGSEGV
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "aio.h"
#include "collections.h"
#include "common.h"
#include "concurrency.h"
#include "memory.h"

#define VALK_HTTP_MOTD "Valkyria HTTP/2 Server"

typedef struct {
  int connectedCount;
  int disconnectedCount;
} valk_srv_state_t;

static void cb_onConnect(void *arg, valk_aio_http_conn *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->connectedCount, 1, __ATOMIC_RELAXED);
  printf("[DEBUG] Client connected (count=%d)\n", handler->connectedCount);
}

static void cb_onDisconnect(void *arg, valk_aio_http_conn *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->disconnectedCount, 1, __ATOMIC_RELAXED);
  printf("[DEBUG] Client disconnected (count=%d)\n", handler->disconnectedCount);
}

static void cb_onHeader(void *arg, valk_aio_http_conn *conn, size_t stream,
                        char *name, char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

static void cb_onBody(void *arg, valk_aio_http_conn *conn, size_t stream,
                      uint8_t flags, valk_buffer_t *buf) {
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

  uint8_t buf[sizeof(valk_mem_arena_t) + (24048 + (int)8e6)];
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
    req->body = (uint8_t *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  printf("[DEBUG] Starting server on port 6969...\n");
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 6969, "build/server.key", "build/server.crt", &handler, NULL);

  valk_arc_box *server = valk_future_await(fserv);
  if (server->type != VALK_SUC) {
    fprintf(stderr, "Failed to start server: %s\n", (char *)server->item);
    return 1;
  }
  printf("[DEBUG] Server started\n");

  printf("[DEBUG] Connecting client...\n");
  valk_future *fut = valk_aio_http2_connect(sys, "127.0.0.1", 6969, "");
  printf("[DEBUG] Arc count of fut: %ld\n", fut->refcount);
  valk_arc_box *clientBox = valk_future_await(fut);

  printf("[DEBUG] Arc count of fut after await: %ld\n", fut->refcount);
  printf("[DEBUG] Arc count of box: %ld\n", clientBox->refcount);

  valk_arc_release(fut);
  if (clientBox->type != VALK_SUC) {
    fprintf(stderr, "Error creating client: %s\n", (char *)clientBox->item);
    return 1;
  }

  valk_aio_http2_client *client = clientBox->item;
  printf("[DEBUG] Client connected, sending request...\n");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  printf("[DEBUG] Awaiting response...\n");
  valk_arc_box *res = valk_future_await(fres);

  if (res->type != VALK_SUC) {
    fprintf(stderr, "Request failed: %s\n", (char *)res->item);
    return 1;
  }

  valk_http2_response_t *response = res->item;
  printf("[DEBUG] Response received: %s\n", (char *)response->body);

  if (strcmp((char *)response->body, VALK_HTTP_MOTD) != 0) {
    fprintf(stderr, "Did not receive the expected result from the server "
                    "Expected: [%s] Actual: [%s]\n",
            VALK_HTTP_MOTD, (char *)response->body);
    return 1;
  }

  printf("[DEBUG] Response matches expected MOTD\n");

  printf("[DEBUG] Releasing resources...\n");
  valk_arc_release(res);
  valk_arc_release(clientBox);

  size_t count = __atomic_load_n(&server->refcount, __ATOMIC_ACQUIRE);
  printf("[DEBUG] Server refcount: %ld\n", count);
  valk_arc_release(server);

  valk_arc_release(fserv);
  valk_arc_release(fres);

  printf("[DEBUG] Stopping AIO system...\n");
  valk_aio_stop(sys);

  printf("[DEBUG] Test completed successfully!\n");
  return 0;
}
