#include "aio.h"
#include <string.h>

void valk_server_demo(void) {}

char *valk_client_demo(const char *domain, const char *port) {
  return strdup("");
}

valk_aio_system *valk_aio_start(void);
void valk_aio_stop(valk_aio_system *sys);

valk_future *valk_aio_read_file(valk_aio_system *sys, const char *filename);

valk_arc_box *valk_aio_http_listen(valk_aio_system *sys, const char *host,
                                   const char *port);

void valk_aio_hangup(valk_aio_socket *socket);
