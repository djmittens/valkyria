#include "aio_ssl.h"
#include "common.h"
#include "memory.h"
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/ssl.h>

// Use libc allocator for all OpenSSL allocations to avoid cross-thread
// allocator mismatches and reallocation of arena/slab pointers.
void *__CRYPTO_malloc_fn(size_t num, const char *file, int line) {
  UNUSED(file);
  UNUSED(line);
  return malloc(num);
}

void *__CRYPTO_realloc_fn(void *addr, size_t num, const char *file, int line) {
  UNUSED(file);
  UNUSED(line);
  return realloc(addr, num);
}

void __CRYPTO_free_fn(void *addr, const char *file, int line) {
  UNUSED(file);
  UNUSED(line);
  free(addr);
}

void valk_aio_ssl_start() {
  static int uninitialized = true;
  if (uninitialized) {
    // !!!! must be called first before any other ssl call !!!!
    CRYPTO_set_mem_functions(__CRYPTO_malloc_fn, __CRYPTO_realloc_fn,
                             __CRYPTO_free_fn);
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

void valk_aio_ssl_accept(valk_aio_ssl_t *ssl, SSL_CTX *ssl_ctx) {
  ssl->ssl = SSL_new(ssl_ctx);

  ssl->read_bio = BIO_new(BIO_s_mem());
  ssl->write_bio = BIO_new(BIO_s_mem());

  SSL_set_bio(ssl->ssl, ssl->read_bio, ssl->write_bio);
  SSL_alloc_buffers(ssl->ssl);

  SSL_set_accept_state(ssl->ssl);
}

void valk_aio_ssl_connect(valk_aio_ssl_t *ssl, SSL_CTX *ssl_ctx) {
  ssl->ssl = SSL_new(ssl_ctx);

  ssl->read_bio = BIO_new(BIO_s_mem());
  ssl->write_bio = BIO_new(BIO_s_mem());

  SSL_set_bio(ssl->ssl, ssl->read_bio, ssl->write_bio);
  SSL_alloc_buffers(ssl->ssl);

  SSL_set_connect_state(ssl->ssl);
}

void valk_aio_ssl_free(valk_aio_ssl_t *ssl) {
  SSL_free_buffers(ssl->ssl);

  // Seems like the ssl object itself frees the bio's associated?
  // I hate this library desing, should try wolf ssl or something with better
  // memory management BIO_free_all(ssl->write_bio);
  // BIO_free_all(ssl->read_bio);

  SSL_free(ssl->ssl);

  ssl->ssl = nullptr;
}

valk_err_e valk_aio_ssl_handshake(valk_aio_ssl_t *ssl, valk_buffer_t *Out) {
  valk_aio_ssl_print_state(ssl);
  int n = SSL_do_handshake(ssl->ssl);
  valk_aio_ssl_print_state(ssl);

  switch (SSL_get_error(ssl->ssl, n)) {
  case SSL_ERROR_WANT_WRITE:
  case SSL_ERROR_WANT_READ:
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
    fprintf(stderr, "OpenSSL error during handshake %d\n",
            SSL_get_error(ssl->ssl, n));
    break;
  case SSL_ERROR_ZERO_RETURN:
  case SSL_ERROR_NONE:
  }
  return VALK_ERR_SUCCESS;
}

valk_err_e valk_aio_ssl_on_read(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out, void *arg,
                                void(onRead)(void *, const valk_buffer_t *)) {
  if (In->count == 0) {
    printf("Didnt receive any data ??? just return then i guess\n");
    return VALK_ERR_SUCCESS;
  }

  int n, err;
  n = BIO_write(ssl->read_bio, In->items, In->count);
  // TODO(networking): need proper error handling in case this  fails
  // Since i am assuming BIO_s_mem() here, it should never fail.
  VALK_ASSERT(n >= 0,
              "OpenSSL BIO_write must be able to write !!! what the heck, got "
              "an error instead %d",
              n);

  VALK_ASSERT((size_t)n == In->count,
              "OpenSSL BIO_write, should write exactly once, because it should "
              "grow to accomodate %ld out of %ld",
              (size_t)n, In->count);

  In->count = 0;

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

  if (!SSL_is_init_finished(ssl->ssl)) {
    return VALK_ERR_SUCCESS;
  }

  size_t len = In->count;
  while (len > 0) {
    int n = SSL_write(ssl->ssl, &((char *)In->items)[In->count - len], len);

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
      // Now stuff the encrypted result into the output buffer
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
    }
    // TODO(networking): Why do i need this here ? i guess ill find out
    if (n == 0)
      break;
  }
  return VALK_ERR_SUCCESS;
}

void valk_aio_ssl_print_state(valk_aio_ssl_t *ssl) {
  const char *st = SSL_state_string_long(ssl->ssl);
  printf("SSL-State: %s\n", st);
}
