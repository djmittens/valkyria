#pragma once

#include "aio.h"

struct valk_lval_t;
struct valk_lenv_t;

valk_future *valk_aio_http2_listen(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler);

valk_future *valk_aio_http2_listen_with_config(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler,
                                   valk_http_server_config_t *config);

void valk_aio_http2_server_set_handler(valk_aio_http_server *srv, void *handler_fn);

int valk_aio_http2_server_get_port(valk_aio_http_server *srv);

valk_future *valk_aio_http2_connect(valk_aio_system_t *sys,
                                    const char *interface, const int port,
                                    const char *certfile);

valk_future *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                         const char *ip, const int port,
                                         const char *hostname);

valk_future *valk_aio_http2_request_send(valk_http2_request_t *req,
                                         valk_aio_http2_client *client);

struct valk_lval_t *valk_http2_client_request_impl(struct valk_lenv_t *e,
                                                    valk_aio_system_t *sys,
                                                    const char *host, int port,
                                                    const char *path,
                                                    struct valk_lval_t *callback);

struct valk_lval_t *valk_http2_client_request_with_headers_impl(struct valk_lenv_t *e,
                                                    valk_aio_system_t *sys,
                                                    const char *host, int port,
                                                    const char *path,
                                                    struct valk_lval_t *headers,
                                                    struct valk_lval_t *callback);

int valk_http2_stream_reset(valk_aio_handle_t *conn, int32_t stream_id, uint32_t error_code);

int valk_http2_submit_goaway(valk_aio_handle_t *conn, uint32_t error_code);

void valk_http2_flush_pending(valk_aio_handle_t *conn);
