#pragma once

#include "aio_internal.h"

valk_async_handle_t *valk_aio_http2_connect(valk_aio_system_t *sys,
                                             const char *interface, const int port,
                                             const char *certfile);

valk_async_handle_t *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                                   const char *ip, const int port,
                                                   const char *hostname);

valk_async_handle_t *valk_aio_http2_connect_host_with_done(valk_aio_system_t *sys,
                                                            const char *ip, const int port,
                                                            const char *hostname,
                                                            valk_async_done_fn on_done,
                                                            void *on_done_ctx);

valk_async_handle_t *valk_aio_http2_request_send(valk_http2_request_t *req,
                                                   valk_aio_http2_client *client);

valk_async_handle_t *valk_aio_http2_request_send_with_done(valk_http2_request_t *req,
                                                            valk_aio_http2_client *client,
                                                            valk_async_done_fn on_done,
                                                            void *on_done_ctx);

valk_lval_t *valk_http2_client_request_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path);

valk_lval_t *valk_http2_client_request_with_headers_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path,
                                             valk_lval_t *headers);


