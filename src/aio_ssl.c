#include "aio_ssl.h"
#include "aio_alloc.h"
#include "common.h"
#include "log.h"
#include "memory.h"
#include <errno.h>
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/ssl.h>

void valk_aio_ssl_start() {
  static int uninitialized = true;
  if (uninitialized) {
    uninitialized = false;
    // Initialize tracking allocators - must be called FIRST before any SSL call
    valk_aio_alloc_init();
    SSL_library_init();
    OpenSSL_add_all_algorithms();
    ERR_load_crypto_strings();
  }
}

valk_err_e valk_aio_ssl_server_init(SSL_CTX **ssl_ctx, const char *keyfile,
                                    const char *certfile) {

  *ssl_ctx = SSL_CTX_new(TLS_server_method());
  if (!*ssl_ctx) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Could not create SSL/TLS context: %s\n",
            ERR_error_string(ERR_get_error(), nullptr));
    return VALK_ERR_SSL_INIT;
  }

  SSL_CTX_set_options(*ssl_ctx,
                      SSL_OP_ALL | SSL_OP_NO_SSLv2 | SSL_OP_NO_SSLv3 |
                          SSL_OP_NO_COMPRESSION |
                          SSL_OP_NO_SESSION_RESUMPTION_ON_RENEGOTIATION);

  // Session caching is safe since we have a single event loop thread handling
  // all SSL operations. This improves performance by allowing session resumption.
  SSL_CTX_set_session_cache_mode(*ssl_ctx, SSL_SESS_CACHE_SERVER);
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
  if (SSL_CTX_set1_curves_list(*ssl_ctx, "P-256") != 1) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
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
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      fprintf(stderr, "EC_KEY_new_by_curv_name failed: %s\n",
              ERR_error_string(ERR_get_error(), NULL));
      SSL_CTX_free(*ssl_ctx);
      *ssl_ctx = NULL;
      return VALK_ERR_SSL_INIT;
    }
    SSL_CTX_set_tmp_ecdh(*ssl_ctx, ecdh);
    EC_KEY_free(ecdh);
  }
#endif /* !(OPENSSL_VERSION_NUMBER >= 0x30000000L) */

  if (SSL_CTX_use_PrivateKey_file(*ssl_ctx, keyfile, SSL_FILETYPE_PEM) != 1) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Could not read private key file %s\n", keyfile);
    SSL_CTX_free(*ssl_ctx);
    *ssl_ctx = nullptr;

    return VALK_ERR_SSL_INIT;
  }

  if (SSL_CTX_use_certificate_chain_file(*ssl_ctx, certfile) != 1) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Could not read certificate file %s\n", certfile);
    SSL_CTX_free(*ssl_ctx);
    *ssl_ctx = nullptr;

    return VALK_ERR_SSL_INIT;
  }

  return VALK_ERR_SUCCESS;
}

valk_err_e valk_aio_ssl_client_init(SSL_CTX **ssl_ctx) {

  *ssl_ctx = SSL_CTX_new(TLS_client_method());
  if (!*ssl_ctx) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Could not create SSL/TLS context: %s\n",
            ERR_error_string(ERR_get_error(), nullptr));
    return VALK_ERR_SSL_INIT;
  }

  SSL_CTX_set_options(*ssl_ctx,
                      SSL_OP_ALL | SSL_OP_NO_SSLv2 | SSL_OP_NO_SSLv3 |
                          SSL_OP_NO_COMPRESSION |
                          SSL_OP_NO_SESSION_RESUMPTION_ON_RENEGOTIATION);
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
  if (SSL_CTX_set1_curves_list(*ssl_ctx, "P-256") != 1) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
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
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      fprintf(stderr, "EC_KEY_new_by_curv_name failed: %s\n",
              ERR_error_string(ERR_get_error(), NULL));
      SSL_CTX_free(ctx->ssl_ctx);
      ctx->ssl_ctx = NULL;
      return VALK_ERR_SSL_INIT;
    }
    SSL_CTX_set_tmp_ecdh(ssl_ctx, ecdh);
    EC_KEY_free(ecdh);
  }
#endif /* !(OPENSSL_VERSION_NUMBER >= 0x30000000L) */

  return VALK_ERR_SUCCESS;
}

int valk_aio_ssl_accept(valk_aio_ssl_t *ssl, SSL_CTX *ssl_ctx) {
  if (!ssl_ctx) {
    VALK_ERROR("valk_aio_ssl_accept: ssl_ctx is NULL");
    ssl->ssl = NULL;
    return -1;
  }

  ssl->ssl = SSL_new(ssl_ctx);
  if (!ssl->ssl) {
    VALK_ERROR("valk_aio_ssl_accept: SSL_new failed: %s",
               ERR_error_string(ERR_get_error(), NULL));
    return -1;
  }

  ssl->read_bio = BIO_new(BIO_s_mem());
  ssl->write_bio = BIO_new(BIO_s_mem());

  SSL_set_bio(ssl->ssl, ssl->read_bio, ssl->write_bio);
  SSL_alloc_buffers(ssl->ssl);

  SSL_set_accept_state(ssl->ssl);
  return 0;
}

int valk_aio_ssl_connect(valk_aio_ssl_t *ssl, SSL_CTX *ssl_ctx) {
  if (!ssl_ctx) {
    VALK_ERROR("valk_aio_ssl_connect: ssl_ctx is NULL");
    ssl->ssl = NULL;
    return -1;
  }

  ssl->ssl = SSL_new(ssl_ctx);
  if (!ssl->ssl) {
    VALK_ERROR("valk_aio_ssl_connect: SSL_new failed: %s",
               ERR_error_string(ERR_get_error(), NULL));
    return -1;
  }

  ssl->read_bio = BIO_new(BIO_s_mem());
  ssl->write_bio = BIO_new(BIO_s_mem());

  SSL_set_bio(ssl->ssl, ssl->read_bio, ssl->write_bio);
  SSL_alloc_buffers(ssl->ssl);

  SSL_set_connect_state(ssl->ssl);
  return 0;
}

void valk_aio_ssl_free(valk_aio_ssl_t *ssl) {
  if (!ssl || !ssl->ssl) {
    return;  // Already freed or never initialized
  }

  SSL_free_buffers(ssl->ssl);

  // Seems like the ssl object itself frees the bio's associated?
  // I hate this library desing, should try wolf ssl or something with better
  // memory management BIO_free_all(ssl->write_bio);
  // BIO_free_all(ssl->read_bio);

  SSL_free(ssl->ssl);

  // Clear all pointers to prevent use-after-free
  ssl->ssl = nullptr;
  ssl->read_bio = nullptr;   // Freed by SSL_free
  ssl->write_bio = nullptr;  // Freed by SSL_free
}

valk_err_e valk_aio_ssl_handshake(valk_aio_ssl_t *ssl, valk_buffer_t *Out) {
  // Null safety check - prevent use-after-free crashes
  if (!ssl || !ssl->ssl || !ssl->read_bio || !ssl->write_bio) {
    return VALK_ERR_SSL_INVALID;
  }

  // Validate output buffer
  if (!Out || !Out->items || Out->capacity == 0) {
    VALK_ERROR("SSL handshake: invalid output buffer (Out=%p, items=%p, cap=%zu)",
               (void *)Out, Out ? Out->items : NULL, Out ? Out->capacity : 0);
    return VALK_ERR_SSL_INVALID;
  }

  // Check for buffer overflow condition
  if (Out->count > Out->capacity) {
    VALK_ERROR("SSL handshake: buffer count (%zu) exceeds capacity (%zu)",
               Out->count, Out->capacity);
    return VALK_ERR_SSL_INVALID;
  }

  int n = SSL_do_handshake(ssl->ssl);
  int ssl_err = SSL_get_error(ssl->ssl, n);

  switch (ssl_err) {
  case SSL_ERROR_WANT_WRITE:
  case SSL_ERROR_WANT_READ: {
    // Check how much data is pending in write BIO before reading
    size_t pending = BIO_ctrl_pending(ssl->write_bio);
    if (pending == 0) {
      // No data to read, just return
      break;
    }

    do {
      size_t available = Out->capacity - Out->count;
      if (available == 0) {
        VALK_ERROR("SSL handshake: output buffer full (count=%zu, cap=%zu)",
                   Out->count, Out->capacity);
        return VALK_ERR_SSL_BUFFER_FULL;
      }

      // Limit read size to what's actually pending to avoid reading garbage
      size_t to_read = (available > pending) ? pending : available;

      n = BIO_read(ssl->write_bio, &((char *)Out->items)[Out->count], to_read);
      if (n > 0) {
        Out->count += n;
        pending = BIO_ctrl_pending(ssl->write_bio);  // Update pending for next iteration
      } else if (!BIO_should_retry(ssl->write_bio)) {
        return VALK_ERR_SSL_READ;
      }
    } while (n > 0 && pending > 0);
    break;
  }
  case SSL_ERROR_SYSCALL: {
    unsigned long err_code = ERR_get_error();
    if (err_code != 0) {
      char err_buf[256];
      ERR_error_string_n(err_code, err_buf, sizeof(err_buf));
      VALK_ERROR("SSL handshake SYSCALL error: %s", err_buf);
      return VALK_ERR_SSL_SYSCALL;
    } else if (n == 0) {
      // Peer closed connection - not an error under load, just cleanup
      VALK_DEBUG("SSL handshake: peer closed connection");
      return VALK_ERR_SSL_PEER_CLOSED;
    } else if (errno == EAGAIN || errno == EWOULDBLOCK) {
      // Non-blocking socket needs more data - not an error
      break;
    } else if (errno == 0) {
      // Peer reset connection - common under load testing
      VALK_DEBUG("SSL handshake: connection reset by peer");
      return VALK_ERR_SSL_PEER_CLOSED;
    } else {
      VALK_ERROR("SSL handshake: I/O error (errno=%d: %s)", errno, strerror(errno));
      return VALK_ERR_SSL_SYSCALL;
    }
  }
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
  // Null safety checks - prevent use-after-free crashes
  if (!ssl || !ssl->ssl || !ssl->read_bio || !ssl->write_bio) {
    return VALK_ERR_SSL_INVALID;
  }

  int n, err;

  if (In->count > 0) {
    n = BIO_write(ssl->read_bio, In->items, In->count);
    VALK_ASSERT(n >= 0,
                "OpenSSL BIO_write must be able to write, got error %d",
                n);

    VALK_ASSERT((size_t)n == In->count,
                "OpenSSL BIO_write, should write exactly once, because it should "
                "grow to accomodate %ld out of %ld",
                (size_t)n, In->count);

    In->count = 0;
  } else {
    // No new data - check if there's pending data to process
    // SSL_pending: data already decrypted, waiting to be read
    // BIO_ctrl_pending: data still encrypted in read BIO
    int ssl_pending = SSL_pending(ssl->ssl);
    int bio_pending = (int)BIO_ctrl_pending(ssl->read_bio);
    if (ssl_pending == 0 && bio_pending == 0 && !SSL_is_init_finished(ssl->ssl)) {
      return VALK_ERR_SUCCESS;
    }
    // If there IS pending data (encrypted or decrypted), fall through to process it
  }

  if (!SSL_is_init_finished(ssl->ssl)) {
    err = valk_aio_ssl_handshake(ssl, Out);
    if (err) {
      return err;
    }
    if (!SSL_is_init_finished(ssl->ssl)) {
      // Still need to do init
      return VALK_ERR_SSL_RE_NEGOTIATE;
    }
  }

  do {
    // Reuse the incoming data buffer, now that we no longer need it
    n = In->count = SSL_read(ssl->ssl, In->items, In->capacity);
    if (n > 0) {
      onRead(arg, In);
    }
  } while (n > 0);

  // Consume the incoming buffer
  In->count = 0;

  switch (SSL_get_error(ssl->ssl, n)) {
  case SSL_ERROR_WANT_READ:
  case SSL_ERROR_WANT_WRITE:
    do {
      VALK_ASSERT(!valk_buffer_is_full(Out),
                  "Output buffer is full to append %zu", Out->count);
      n = BIO_read(ssl->write_bio, &((char *)Out->items)[Out->count],
                   Out->capacity - Out->count);
      if (n > 0) {
        Out->count += n;
        VALK_ASSERT(!valk_buffer_is_full(Out),
                    "Output buffer is too full after append %zu",
                    Out->count + n);
      } else if (!BIO_should_retry(ssl->write_bio)) {
        return VALK_ERR_SSL_READ;
      }
    } while (n > 0);
    break;
  case SSL_ERROR_SYSCALL:
    // TODO(networking): get proper string for this error
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "OpenSSL error during read SSL_ERROR_SYSCALL\n");
    return VALK_ERR_SSL_READ;
    break;
  case SSL_ERROR_ZERO_RETURN:
  case SSL_ERROR_NONE:
  }
  return VALK_ERR_SUCCESS;
}

valk_err_e valk_aio_ssl_encrypt(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out) {
  // Null safety checks - prevent use-after-free crashes
  if (!ssl || !ssl->ssl || !ssl->write_bio) {
    VALK_ERROR("SSL encrypt: invalid SSL context (ssl=%p, ssl->ssl=%p, write_bio=%p)",
               (void *)ssl, ssl ? (void *)ssl->ssl : NULL,
               ssl ? (void *)ssl->write_bio : NULL);
    return VALK_ERR_SSL_INVALID;
  }

  // Validate input buffer
  if (!In || !In->items) {
    VALK_ERROR("SSL encrypt: invalid input buffer");
    return VALK_ERR_SSL_INVALID;
  }

  // Validate output buffer
  if (!Out || !Out->items || Out->capacity == 0) {
    VALK_ERROR("SSL encrypt: invalid output buffer (Out=%p, items=%p, cap=%zu)",
               (void *)Out, Out ? Out->items : NULL, Out ? Out->capacity : 0);
    return VALK_ERR_SSL_INVALID;
  }

  // Check for buffer overflow condition
  if (Out->count > Out->capacity) {
    VALK_ERROR("SSL encrypt: buffer count (%zu) exceeds capacity (%zu)",
               Out->count, Out->capacity);
    return VALK_ERR_SSL_INVALID;
  }

  if (!SSL_is_init_finished(ssl->ssl)) {
    return VALK_ERR_SUCCESS;
  }

  // Reserve some headroom for SSL overhead (records, padding, MAC)
  // TLS 1.3 record overhead is ~22 bytes per record, but we use a larger
  // margin to be safe with fragmentation
  const size_t SSL_HEADROOM = 1024;

  size_t len = In->count;
  size_t consumed = 0;
  while (len > 0) {
    // Check if output buffer is getting full - stop early to avoid overflow
    if (Out->count + SSL_HEADROOM >= Out->capacity) {
      VALK_TRACE("SSL encrypt: output buffer near capacity (%zu/%zu), "
                 "stopping with %zu bytes remaining",
                 Out->count, Out->capacity, len);
      break;
    }

    int n = SSL_write(ssl->ssl, &((char *)In->items)[consumed], len);

    switch (SSL_get_error(ssl->ssl, n)) {
    case SSL_ERROR_NONE:
    case SSL_ERROR_WANT_WRITE:
    case SSL_ERROR_WANT_READ:
      break;
    default:
      // we just drop everything
      In->count = 0;
      return VALK_ERR_SSL_ENCRYPT;
    }

    if (n > 0) {
      len -= n;
      consumed += n;
      // Now stuff the encrypted result into the output buffer
      do {
        size_t space = Out->capacity - Out->count;
        if (space == 0) {
          // Output buffer completely full - stop here
          // Remaining encrypted data stays in BIO for next call
          VALK_TRACE("SSL encrypt: output buffer full, %zu bytes consumed",
                     consumed);
          // Update In to reflect how much we consumed
          if (consumed < In->count) {
            memmove(In->items, &((char *)In->items)[consumed],
                    In->count - consumed);
            In->count -= consumed;
          } else {
            In->count = 0;
          }
          return VALK_ERR_SUCCESS;
        }

        // Check pending data in BIO before reading
        size_t pending = BIO_ctrl_pending(ssl->write_bio);
        if (pending == 0) {
          break;  // No data to read
        }

        // Limit read to available space
        if (space > pending) {
          space = pending;
        }

        n = BIO_read(ssl->write_bio, &((char *)Out->items)[Out->count], space);
        if (n > 0) {
          Out->count += n;
        } else if (!BIO_should_retry(ssl->write_bio)) {
          VALK_ERROR("SSL encrypt: BIO_read failed");
          return VALK_ERR_SSL_READ;
        }
      } while (n > 0);
    }
    // TODO(networking): Why do i need this here ? i guess ill find out
    if (n == 0)
      break;
  }

  // Update In to reflect how much we consumed
  if (consumed < In->count) {
    memmove(In->items, &((char *)In->items)[consumed], In->count - consumed);
    In->count -= consumed;
  } else {
    In->count = 0;
  }

  return VALK_ERR_SUCCESS;
}

void valk_aio_ssl_print_state(valk_aio_ssl_t *ssl) {
  if (!ssl || !ssl->ssl) {
    printf("SSL-State: [NULL SSL object at %p]\n", (void *)ssl);
    return;
  }
  const char *st = SSL_state_string_long(ssl->ssl);
  printf("SSL-State[%p]: %s\n", (void *)ssl, st);
}
