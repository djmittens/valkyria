#include <unistd.h>
#include <signal.h>
#include "aio.h"
#include "memory.h"

int main() {
  valk_mem_init_malloc();

  valk_aio_system_t *sys = valk_aio_start();
  valk_http2_handler_t *handler = valk_aio_http2_demo_handler();

  valk_future *fut = valk_aio_http2_listen(
    sys,
    "0.0.0.0",
    8443,
    "build/server.key",
    "build/server.crt",
    handler
  );

  printf("Server started, sleeping forever...\n");

  while (1) {
    sleep(1);
  }

  return 0;
}
