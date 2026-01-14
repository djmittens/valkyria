#pragma once

#include "aio_internal.h"

valk_async_handle_t *valk_aio_http2_listen(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler);

valk_async_handle_t *valk_aio_http2_listen_with_config(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler,
                                   valk_http_server_config_t *config);

void valk_aio_http2_server_set_handler(valk_aio_http_server *srv, void *handler_fn);

int valk_aio_http2_server_get_port(valk_aio_http_server *srv);
valk_aio_http_server* valk_aio_http2_server_from_ref(struct valk_lval_t *server_ref);
int valk_aio_http2_server_get_port_from_ref(struct valk_lval_t *server_ref);

valk_async_handle_t *valk_aio_http2_stop(valk_aio_http_server *srv,
                                         struct valk_arc_box *box);

void valk_http2_server_metrics_init(valk_aio_system_t* sys, 
                                     valk_server_metrics_t* m,
                                     const char* name, int port, 
                                     const char* protocol,
                                     const char* loop_name);
