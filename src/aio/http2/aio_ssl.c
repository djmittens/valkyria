#include "aio_ssl.h"
#include "aio_alloc.h"
#include "common.h"
#include "log.h"
#include "memory.h"
#include <errno.h>
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/ssl.h>

static int ssl_uninitialized = true;

void valk_aio_ssl_start() {
  if (ssl_uninitialized) {
    ssl_uninitialized = false;
    // Initialize tracking allocators - must be called FIRST before any SSL call
    valk_aio_alloc_init();
    SSL_library_init();
    OpenSSL_add_all_algorithms();
    ERR_load_crypto_strings();
  }
}

void valk_aio_ssl_fork_reset() {
  ssl_uninitialized = true;
  valk_aio_alloc_fork_reset();
  OPENSSL_cleanup();
#if OPENSSL_VERSION_NUMBER >= 0x10100000L
  RAND_poll();
#endif
}

valk_err_e valk_aio_ssl_server_init(SSL_CTX **ssl_ctx, const char *keyfile,
                                    const char *certfile) {

  *ssl_ctx = SSL_CTX_new(TLS_server_method());
  // LCOV_EXCL_START - OpenSSL API failure (OOM or library init failure)
  if (!*ssl_ctx) {
    fprintf(stderr, "Could not create SSL/TLS context: %s\n",
            ERR_error_string(ERR_get_error(), nullptr));
    return VALK_ERR_SSL_INIT;
  }
  // LCOV_EXCL_STOP

  SSL_CTX_set_options(*ssl_ctx,
                      SSL_OP_ALL | SSL_OP_NO_SSLv2 | SSL_OP_NO_SSLv3 |
                          SSL_OP_NO_COMPRESSION |
                          SSL_OP_NO_SESSION_RESUMPTION_ON_RENEGOTIATION);

  // Session caching is safe since we have a single event loop thread handling
  // all SSL operations. This improves performance by allowing session resumption.
  SSL_CTX_set_session_cache_mode(*ssl_ctx, SSL_SESS_CACHE_SERVER);
// LCOV_EXCL_START - OpenSSL curve setup failure (P-256 always available)
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
  if (SSL_CTX_set1_curves_list(*ssl_ctx, "P-256") != 1) {
    fprintf(stderr, "SSL_CTX_set1_curves_list failed: %s\n",
            ERR_error_string(ERR_get_error(), nullptr));
    SSL_CTX_free(*ssl_ctx);
    *ssl_ctx = nullptr;
    return VALK_ERR_SSL_INIT;
  }
#else  /* !(OPENSSL_VERSION_NUMBER >= 0x30000000L) */
  {
    EC_KEY *ecdh;
    ecdh = EC_KEY_new_by_curve_name(NID_X9_62_prime256v1);
    if (!ecdh) {
      fprintf(stderr, "EC_KEY_new_by_curv_name failed: %s\n",
              ERR_error_string(ERR_get_error(), nullptr));
      SSL_CTX_free(*ssl_ctx);
      *ssl_ctx = nullptr;
      return VALK_ERR_SSL_INIT;
    }
    SSL_CTX_set_tmp_ecdh(*ssl_ctx, ecdh);
    EC_KEY_free(ecdh);
  }
#endif /* !(OPENSSL_VERSION_NUMBER >= 0x30000000L) */
// LCOV_EXCL_STOP

  if (SSL_CTX_use_PrivateKey_file(*ssl_ctx, keyfile, SSL_FILETYPE_PEM) != 1) {
    fprintf(stderr, "Could not read private key file %s\n", keyfile);
    SSL_CTX_free(*ssl_ctx);
    *ssl_ctx = nullptr;

    return VALK_ERR_SSL_INIT;
  }

  if (SSL_CTX_use_certificate_chain_file(*ssl_ctx, certfile) != 1) {
    fprintf(stderr, "Could not read certificate file %s\n", certfile);
    SSL_CTX_free(*ssl_ctx);
    *ssl_ctx = nullptr;

    return VALK_ERR_SSL_INIT;
  }

  return VALK_ERR_SUCCESS;
}

valk_err_e valk_aio_ssl_client_init(SSL_CTX **ssl_ctx) {

  *ssl_ctx = SSL_CTX_new(TLS_client_method());
  // LCOV_EXCL_START - OpenSSL API failure (OOM or library init failure)
  if (!*ssl_ctx) {
    fprintf(stderr, "Could not create SSL/TLS context: %s\n",
            ERR_error_string(ERR_get_error(), nullptr));
    return VALK_ERR_SSL_INIT;
  }
  // LCOV_EXCL_STOP

  SSL_CTX_set_options(*ssl_ctx,
                      SSL_OP_ALL | SSL_OP_NO_SSLv2 | SSL_OP_NO_SSLv3 |
                          SSL_OP_NO_COMPRESSION |
                          SSL_OP_NO_SESSION_RESUMPTION_ON_RENEGOTIATION);
// LCOV_EXCL_START - OpenSSL curve setup failure (P-256 always available)
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
  if (SSL_CTX_set1_curves_list(*ssl_ctx, "P-256") != 1) {
    fprintf(stderr, "SSL_CTX_set1_curves_list failed: %s\n",
            ERR_error_string(ERR_get_error(), nullptr));
    SSL_CTX_free(*ssl_ctx);
    ssl_ctx = nullptr;
    return VALK_ERR_SSL_INIT;
  }
#else  /* !(OPENSSL_VERSION_NUMBER >= 0x30000000L) */
  {
    EC_KEY *ecdh;
    ecdh = EC_KEY_new_by_curve_name(NID_X9_62_prime256v1);
    if (!ecdh) {
      fprintf(stderr, "EC_KEY_new_by_curv_name failed: %s\n",
              ERR_error_string(ERR_get_error(), nullptr));
      SSL_CTX_free(ctx->ssl_ctx);
      ctx->ssl_ctx = nullptr;
      return VALK_ERR_SSL_INIT;
    }
    SSL_CTX_set_tmp_ecdh(ssl_ctx, ecdh);
    EC_KEY_free(ecdh);
  }
#endif /* !(OPENSSL_VERSION_NUMBER >= 0x30000000L) */
// LCOV_EXCL_STOP

  return VALK_ERR_SUCCESS;
}

int valk_aio_ssl_accept(valk_aio_ssl_t *ssl, SSL_CTX *ssl_ctx) {
  if (!ssl_ctx) {
    VALK_ERROR("valk_aio_ssl_accept: ssl_ctx is nullptr");
    ssl->ssl = nullptr;
    return -1;
  }

  ssl->ssl = SSL_new(ssl_ctx);
  // LCOV_EXCL_START - OpenSSL API failure (OOM)
  if (!ssl->ssl) {
    VALK_ERROR("valk_aio_ssl_accept: SSL_new failed: %s",
               ERR_error_string(ERR_get_error(), nullptr));
    return -1;
  }
  // LCOV_EXCL_STOP

  ssl->read_bio = BIO_new(BIO_s_mem());
  ssl->write_bio = BIO_new(BIO_s_mem());

  SSL_set_bio(ssl->ssl, ssl->read_bio, ssl->write_bio);
  SSL_alloc_buffers(ssl->ssl);

  SSL_set_accept_state(ssl->ssl);
  return 0;
}

int valk_aio_ssl_connect(valk_aio_ssl_t *ssl, SSL_CTX *ssl_ctx) {
  if (!ssl_ctx) {
    VALK_ERROR("valk_aio_ssl_connect: ssl_ctx is nullptr");
    ssl->ssl = nullptr;
    return -1;
  }

  ssl->ssl = SSL_new(ssl_ctx);
  // LCOV_EXCL_START - OpenSSL API failure (OOM)
  if (!ssl->ssl) {
    VALK_ERROR("valk_aio_ssl_connect: SSL_new failed: %s",
               ERR_error_string(ERR_get_error(), nullptr));
    return -1;
  }
  // LCOV_EXCL_STOP

  ssl->read_bio = BIO_new(BIO_s_mem());
  ssl->write_bio = BIO_new(BIO_s_mem());

  SSL_set_bio(ssl->ssl, ssl->read_bio, ssl->write_bio);
  SSL_alloc_buffers(ssl->ssl);

  SSL_set_connect_state(ssl->ssl);
  return 0;
}

void valk_aio_ssl_free(valk_aio_ssl_t *ssl) {
  if (!ssl || !ssl->ssl) {
    return;
  }

  SSL_free_buffers(ssl->ssl);
  SSL_free(ssl->ssl);

  ssl->ssl = nullptr;
  ssl->read_bio = nullptr;
  ssl->write_bio = nullptr;
}

// LCOV_EXCL_START - internal helper, branches depend on OpenSSL internal state
static valk_err_e ssl_drain_write_bio(BIO *write_bio, valk_buffer_t *Out) {
  int n;
  do {
    u64 space = Out->capacity - Out->count;
    if (space == 0) break;

    u64 pending = BIO_ctrl_pending(write_bio);
    if (pending == 0) break;

    u64 to_read = (space > pending) ? pending : space;
    n = BIO_read(write_bio, &((char *)Out->items)[Out->count], to_read);
    if (n > 0) {
      Out->count += n;
    } else if (!BIO_should_retry(write_bio)) {
      return VALK_ERR_SSL_READ;
    }
  } while (n > 0);
  return VALK_ERR_SUCCESS;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START - SSL_ERROR_SYSCALL handler, requires real network errors
static valk_err_e ssl_handle_syscall_error(int n, const char *op) {
  unsigned long err_code = ERR_get_error();
  if (err_code != 0) {
    char err_buf[256];
    ERR_error_string_n(err_code, err_buf, sizeof(err_buf));
    VALK_ERROR("SSL %s SYSCALL error: %s", op, err_buf);
    return VALK_ERR_SSL_SYSCALL;
  }
  if (n == 0) {
    VALK_DEBUG("SSL %s: peer closed connection", op);
    return VALK_ERR_SSL_PEER_CLOSED;
  }
  if (errno == EAGAIN || errno == EWOULDBLOCK) {
    return VALK_ERR_SUCCESS;
  }
  if (errno == 0) {
    VALK_DEBUG("SSL %s: connection reset by peer", op);
    return VALK_ERR_SSL_PEER_CLOSED;
  }
  VALK_ERROR("SSL %s: I/O error (errno=%d: %s)", op, errno, strerror(errno));
  return VALK_ERR_SSL_SYSCALL;
}
// LCOV_EXCL_STOP

static bool ssl_context_valid(valk_aio_ssl_t *ssl) {
  return ssl && ssl->ssl && ssl->read_bio && ssl->write_bio; // LCOV_EXCL_BR_LINE - defensive validation
}

static bool ssl_buffer_valid(valk_buffer_t *buf) {
  return buf && buf->items && buf->capacity > 0 && buf->count <= buf->capacity; // LCOV_EXCL_BR_LINE - defensive validation
}

valk_err_e valk_aio_ssl_handshake(valk_aio_ssl_t *ssl, valk_buffer_t *Out) {
  if (!ssl_context_valid(ssl)) return VALK_ERR_SSL_INVALID;
  if (!ssl_buffer_valid(Out)) {
    VALK_ERROR("SSL handshake: invalid output buffer");
    return VALK_ERR_SSL_INVALID;
  }

  int n = SSL_do_handshake(ssl->ssl);
  int ssl_err = SSL_get_error(ssl->ssl, n);

  switch (ssl_err) {
  case SSL_ERROR_WANT_WRITE:
  case SSL_ERROR_WANT_READ: {
    valk_err_e drain_err = ssl_drain_write_bio(ssl->write_bio, Out);
    if (drain_err != VALK_ERR_SUCCESS) return drain_err; // LCOV_EXCL_BR_LINE - drain failure
    break;
  }
  // LCOV_EXCL_START - SYSCALL errors require real network I/O failures
  case SSL_ERROR_SYSCALL: {
    valk_err_e syscall_err = ssl_handle_syscall_error(n, "handshake");
    if (syscall_err != VALK_ERR_SUCCESS) return syscall_err;
    break;
  }
  // LCOV_EXCL_STOP
  case SSL_ERROR_SSL: {
    unsigned long err_code = ERR_get_error();
    char err_buf[256];
    ERR_error_string_n(err_code, err_buf, sizeof(err_buf));
    VALK_ERROR("SSL handshake protocol error: %s", err_buf);
    return VALK_ERR_SSL_PROTOCOL;
  }
  case SSL_ERROR_ZERO_RETURN:
  case SSL_ERROR_NONE:
    break;
  }
  return VALK_ERR_SUCCESS;
}

valk_err_e valk_aio_ssl_on_read(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out, void *arg,
                                void(onRead)(void *, const valk_buffer_t *)) {
  if (!ssl_context_valid(ssl)) return VALK_ERR_SSL_INVALID;

  int n, err;

  if (In->count > 0) {
    n = BIO_write(ssl->read_bio, In->items, In->count);
    VALK_ASSERT(n >= 0, "OpenSSL BIO_write failed: %d", n); // LCOV_EXCL_BR_LINE - OpenSSL internal failure
    VALK_ASSERT((size_t)n == In->count, "BIO_write partial: %d of %llu", // LCOV_EXCL_BR_LINE - memory BIO always accepts full write
                n, (unsigned long long)In->count);
    In->count = 0;
  } else {
    int ssl_pending = SSL_pending(ssl->ssl);
    int bio_pending = (int)BIO_ctrl_pending(ssl->read_bio);
    if (ssl_pending == 0 && bio_pending == 0 && !SSL_is_init_finished(ssl->ssl)) { // LCOV_EXCL_BR_LINE - early return when no data pending
      return VALK_ERR_SUCCESS;
    }
  }

  if (!SSL_is_init_finished(ssl->ssl)) {
    err = valk_aio_ssl_handshake(ssl, Out);
    if (err) return err;
    if (!SSL_is_init_finished(ssl->ssl)) return VALK_ERR_SSL_RE_NEGOTIATE;
  }

  do {
    n = In->count = SSL_read(ssl->ssl, In->items, In->capacity);
    if (n > 0) onRead(arg, In);
  } while (n > 0);

  In->count = 0;

  switch (SSL_get_error(ssl->ssl, n)) {
  case SSL_ERROR_WANT_READ:
  case SSL_ERROR_WANT_WRITE: {
    valk_err_e drain_err = ssl_drain_write_bio(ssl->write_bio, Out);
    if (drain_err != VALK_ERR_SUCCESS) return drain_err; // LCOV_EXCL_BR_LINE - drain failure
    break;
  }
  // LCOV_EXCL_START - SSL_ERROR_SYSCALL requires real network I/O failures
  case SSL_ERROR_SYSCALL: {
    unsigned long err_code = ERR_get_error();
    if (err_code != 0) {
      char err_buf[256];
      ERR_error_string_n(err_code, err_buf, sizeof(err_buf));
      VALK_ERROR("SSL read error: %s", err_buf);
    } else if (n == 0) {
      VALK_WARN("SSL connection closed unexpectedly (EOF)");
    } else if (n == -1) {
      VALK_ERROR("SSL read I/O error: %s", strerror(errno));
    }
    return VALK_ERR_SSL_READ;
  }
  // LCOV_EXCL_STOP
  case SSL_ERROR_ZERO_RETURN:
  case SSL_ERROR_NONE:
    break;
  }
  return VALK_ERR_SUCCESS;
}

// LCOV_EXCL_START - internal helper, partial consumption requires buffer backpressure
static void update_input_buffer(valk_buffer_t *In, u64 consumed) {
  if (consumed < In->count) {
    memmove(In->items, &((char *)In->items)[consumed], In->count - consumed);
    In->count -= consumed;
  } else {
    In->count = 0;
  }
}
// LCOV_EXCL_STOP

valk_err_e valk_aio_ssl_encrypt(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out) {
  if (!ssl || !ssl->ssl || !ssl->write_bio) {
    VALK_ERROR("SSL encrypt: invalid SSL context");
    return VALK_ERR_SSL_INVALID;
  }
  if (!In || !In->items) {
    VALK_ERROR("SSL encrypt: invalid input buffer");
    return VALK_ERR_SSL_INVALID;
  }
  if (!ssl_buffer_valid(Out)) {
    VALK_ERROR("SSL encrypt: invalid output buffer");
    return VALK_ERR_SSL_INVALID;
  }

  if (!SSL_is_init_finished(ssl->ssl)) return VALK_ERR_SUCCESS;

  const u64 SSL_HEADROOM = 1024;
  u64 len = In->count;
  u64 consumed = 0;

  while (len > 0) {
    if (Out->count + SSL_HEADROOM >= Out->capacity) { // LCOV_EXCL_BR_LINE - buffer backpressure path
      VALK_TRACE("SSL encrypt: buffer near capacity, stopping"); // LCOV_EXCL_LINE
      break; // LCOV_EXCL_LINE
    }

    int n = SSL_write(ssl->ssl, &((char *)In->items)[consumed], len);

    switch (SSL_get_error(ssl->ssl, n)) {
    case SSL_ERROR_NONE:
    case SSL_ERROR_WANT_WRITE:
    case SSL_ERROR_WANT_READ:
      break;
    default: // LCOV_EXCL_LINE - SSL_write error other than WANT_READ/WRITE
      In->count = 0; // LCOV_EXCL_LINE
      return VALK_ERR_SSL_ENCRYPT; // LCOV_EXCL_LINE
    }

    if (n > 0) {
      len -= n;
      consumed += n;
      valk_err_e drain_err = ssl_drain_write_bio(ssl->write_bio, Out);
      if (drain_err != VALK_ERR_SUCCESS) { // LCOV_EXCL_BR_LINE - drain failure
        update_input_buffer(In, consumed); // LCOV_EXCL_LINE
        return drain_err; // LCOV_EXCL_LINE
      }
    }
    if (n == 0) break; // LCOV_EXCL_BR_LINE - SSL_write returns 0 only on fatal error
  }

  update_input_buffer(In, consumed);
  return VALK_ERR_SUCCESS;
}

void valk_aio_ssl_print_state(valk_aio_ssl_t *ssl) {
  if (!ssl || !ssl->ssl) {
    printf("SSL-State: [nullptr SSL object at %p]\n", (void *)ssl);
    return;
  }
  const char *st = SSL_state_string_long(ssl->ssl);
  printf("SSL-State[%p]: %s\n", (void *)ssl, st);
}
