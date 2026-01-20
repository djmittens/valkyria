#pragma once

#include "aio_internal.h"

valk_async_handle_t *valk_aio_http2_connect(valk_aio_system_t *sys,
                                             const char *interface, const int port,
                                             const char *certfile);

valk_async_handle_t *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                                  const char *ip, const int port,
                                                  const char *hostname);

valk_async_handle_t *valk_aio_http2_request_send(valk_http2_request_t *req,
                                                  valk_aio_http2_client *client);

valk_lval_t *valk_http2_client_request_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path);

valk_lval_t *valk_http2_client_request_with_headers_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path,
                                             valk_lval_t *headers);

// LCOV_EXCL_START unused connection reuse API - reserved for future use
valk_lval_t *valk_http2_client_request_on_conn_impl(valk_lenv_t *e,
                                                     valk_aio_http2_client *client,
                                                     const char *path,
                                                     valk_lval_t *callback);
// LCOV_EXCL_STOP
