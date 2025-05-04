#pragma once

#include "common.h"
#include "memory.h"

#include <stddef.h>

#include <openssl/bio.h>
#include <openssl/conf.h>
#include <openssl/err.h>
#include <openssl/ssl.h>

typedef struct valk_aio_ssl_t {
  SSL *ssl;
  BIO *read_bio;
  BIO *write_bio;
} valk_aio_ssl_t;

void valk_aio_ssl_start();

valk_err_e valk_aio_ssl_server_init(SSL_CTX **ssl_ctx, const char *keyfile,
                                    const char *certfile);

valk_err_e valk_aio_ssl_client_init(SSL_CTX **ssl_ctx);


void valk_aio_ssl_connect(valk_aio_ssl_t *ssl, SSL_CTX *ssl_ctx);
void valk_aio_ssl_accept(valk_aio_ssl_t *ssl, SSL_CTX *ssl_ctx);

void valk_aio_ssl_free(valk_aio_ssl_t *ssl);

valk_err_e valk_aio_ssl_handshake(valk_aio_ssl_t *ssl, valk_buffer_t *Out);


valk_err_e valk_aio_ssl_on_read(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out, void *arg,
                                void(onRead)(void *, const valk_buffer_t *));

valk_err_e valk_aio_ssl_encrypt(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out);

void valk_aio_ssl_print_state(valk_aio_ssl_t *ssl);
void valk_aio_ssl_print_error(valk_aio_ssl_t *ssl);
