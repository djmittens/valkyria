#include "../testing.h"
#include "../../src/aio/http2/aio_ssl.h"
#include "../../src/memory.h"
#include "../../src/common.h"

#include <string.h>
#include <stdlib.h>

void test_ssl_start(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  valk_aio_ssl_start();
  
  VALK_PASS();
}

void test_ssl_server_init_invalid_files(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_server_init(&ctx, "/nonexistent/key.pem", "/nonexistent/cert.pem");
  ASSERT_EQ(err, VALK_ERR_SSL_INIT);
  ASSERT_NULL(ctx);
  
  VALK_PASS();
}

void test_ssl_server_init_valid_key_invalid_cert(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_server_init(&ctx, 
    "vendor/nghttp2/src/test.example.com-key.pem",
    "/nonexistent/cert.pem");
  ASSERT_EQ(err, VALK_ERR_SSL_INIT);
  ASSERT_NULL(ctx);
  
  VALK_PASS();
}

void test_ssl_handshake_null_ssl(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  char buf[1024];
  valk_buffer_t out = {.items = buf, .count = 0, .capacity = sizeof(buf)};
  
  valk_err_e err = valk_aio_ssl_handshake(nullptr, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  VALK_PASS();
}

void test_ssl_handshake_invalid_ssl_fields(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  char buf[1024];
  valk_buffer_t out = {.items = buf, .count = 0, .capacity = sizeof(buf)};
  
  valk_aio_ssl_t ssl = {0};
  ssl.ssl = nullptr;
  ssl.read_bio = nullptr;
  ssl.write_bio = nullptr;
  
  valk_err_e err = valk_aio_ssl_handshake(&ssl, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  VALK_PASS();
}

void test_ssl_handshake_null_output_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  ASSERT_NOT_NULL(ssl.ssl);
  
  valk_err_e err = valk_aio_ssl_handshake(&ssl, nullptr);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_handshake_invalid_output_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  ASSERT_NOT_NULL(ssl.ssl);
  
  valk_buffer_t out = {.items = nullptr, .count = 0, .capacity = 0};
  valk_err_e err = valk_aio_ssl_handshake(&ssl, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_handshake_buffer_overflow_condition(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char buf[1024];
  valk_buffer_t out = {.items = buf, .count = 2000, .capacity = 1024};
  valk_err_e err = valk_aio_ssl_handshake(&ssl, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_on_read_null_ssl(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  char ibuf[256], obuf[256];
  valk_buffer_t in = {.items = ibuf, .count = 0, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};
  
  valk_err_e err = valk_aio_ssl_on_read(nullptr, &in, &out, nullptr, nullptr);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  VALK_PASS();
}

void test_ssl_on_read_invalid_ssl_fields(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  char ibuf[256], obuf[256];
  valk_buffer_t in = {.items = ibuf, .count = 0, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};
  
  valk_aio_ssl_t ssl = {0};
  valk_err_e err = valk_aio_ssl_on_read(&ssl, &in, &out, nullptr, nullptr);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  VALK_PASS();
}

void test_ssl_encrypt_null_ssl(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  char ibuf[256], obuf[256];
  valk_buffer_t in = {.items = ibuf, .count = 10, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};
  
  valk_err_e err = valk_aio_ssl_encrypt(nullptr, &in, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  VALK_PASS();
}

void test_ssl_encrypt_invalid_ssl_fields(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  char ibuf[256], obuf[256];
  valk_buffer_t in = {.items = ibuf, .count = 10, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};
  
  valk_aio_ssl_t ssl = {0};
  valk_err_e err = valk_aio_ssl_encrypt(&ssl, &in, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  VALK_PASS();
}

void test_ssl_encrypt_null_input_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char obuf[256];
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};
  
  valk_err_e err = valk_aio_ssl_encrypt(&ssl, nullptr, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_encrypt_null_input_items(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  valk_buffer_t in = {.items = nullptr, .count = 10, .capacity = 256};
  char obuf[256];
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};
  
  valk_err_e err = valk_aio_ssl_encrypt(&ssl, &in, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_encrypt_null_output_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char ibuf[256];
  valk_buffer_t in = {.items = ibuf, .count = 10, .capacity = sizeof(ibuf)};
  
  valk_err_e err = valk_aio_ssl_encrypt(&ssl, &in, nullptr);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_encrypt_invalid_output_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char ibuf[256];
  valk_buffer_t in = {.items = ibuf, .count = 10, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = nullptr, .count = 0, .capacity = 0};
  
  valk_err_e err = valk_aio_ssl_encrypt(&ssl, &in, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_encrypt_output_buffer_overflow(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char ibuf[256], obuf[256];
  valk_buffer_t in = {.items = ibuf, .count = 10, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 500, .capacity = 256};
  
  valk_err_e err = valk_aio_ssl_encrypt(&ssl, &in, &out);
  ASSERT_EQ(err, VALK_ERR_SSL_INVALID);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_free(nullptr);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_free(&ssl);
  
  VALK_PASS();
}

void test_ssl_free_double_free(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  ASSERT_NOT_NULL(ssl.ssl);
  
  valk_aio_ssl_free(&ssl);
  ASSERT_NULL(ssl.ssl);
  ASSERT_NULL(ssl.read_bio);
  ASSERT_NULL(ssl.write_bio);
  
  valk_aio_ssl_free(&ssl);
  
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_print_state_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_print_state(nullptr);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_print_state(&ssl);
  
  VALK_PASS();
}

void test_ssl_print_state_valid(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(ctx);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  valk_aio_ssl_print_state(&ssl);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_accept_and_connect(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *client_ctx = SSL_CTX_new(TLS_client_method());
  ASSERT_NOT_NULL(client_ctx);
  
  SSL_CTX *server_ctx = SSL_CTX_new(TLS_server_method());
  ASSERT_NOT_NULL(server_ctx);
  
  valk_aio_ssl_t client_ssl = {0};
  valk_aio_ssl_connect(&client_ssl, client_ctx);
  ASSERT_NOT_NULL(client_ssl.ssl);
  ASSERT_NOT_NULL(client_ssl.read_bio);
  ASSERT_NOT_NULL(client_ssl.write_bio);
  
  valk_aio_ssl_t server_ssl = {0};
  valk_aio_ssl_accept(&server_ssl, server_ctx);
  ASSERT_NOT_NULL(server_ssl.ssl);
  ASSERT_NOT_NULL(server_ssl.read_bio);
  ASSERT_NOT_NULL(server_ssl.write_bio);
  
  valk_aio_ssl_free(&client_ssl);
  valk_aio_ssl_free(&server_ssl);
  SSL_CTX_free(client_ctx);
  SSL_CTX_free(server_ctx);
  
  VALK_PASS();
}

void test_ssl_client_init(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  ASSERT_NOT_NULL(ctx);
  
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_handshake_empty_output(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char buf[16384];
  valk_buffer_t out = {.items = buf, .count = 0, .capacity = sizeof(buf)};
  
  err = valk_aio_ssl_handshake(&ssl, &out);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_on_read_empty_input(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char ibuf[256], obuf[16384];
  valk_buffer_t in = {.items = ibuf, .count = 0, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};
  
  err = valk_aio_ssl_on_read(&ssl, &in, &out, nullptr, nullptr);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_encrypt_not_finished(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char ibuf[256], obuf[16384];
  memset(ibuf, 'A', sizeof(ibuf));
  valk_buffer_t in = {.items = ibuf, .count = 100, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};
  
  err = valk_aio_ssl_encrypt(&ssl, &in, &out);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_handshake_tiny_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char buf[1];
  valk_buffer_t out = {.items = buf, .count = 0, .capacity = sizeof(buf)};
  
  err = valk_aio_ssl_handshake(&ssl, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SUCCESS || err == VALK_ERR_SSL_BUFFER_FULL,
                   "Expected SUCCESS or BUFFER_FULL, got %d", err);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_handshake_full_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_ssl_start();
  
  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  
  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);
  
  char buf[1024];
  valk_buffer_t out = {.items = buf, .count = 1024, .capacity = 1024};
  
  err = valk_aio_ssl_handshake(&ssl, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SUCCESS || err == VALK_ERR_SSL_BUFFER_FULL,
                   "Expected SUCCESS or BUFFER_FULL, got %d", err);
  
  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  
  VALK_PASS();
}

void test_ssl_on_read_with_garbage_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);

  char ibuf[256], obuf[16384];
  memset(ibuf, 0, sizeof(ibuf));
  valk_buffer_t in = {.items = ibuf, .count = 100, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};

  err = valk_aio_ssl_on_read(&ssl, &in, &out, nullptr, nullptr);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_PROTOCOL || err == VALK_ERR_SSL_RE_NEGOTIATE,
                   "Expected PROTOCOL error or RE_NEGOTIATE with garbage data, got %d", err);

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_fork_reset(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();
  valk_aio_ssl_fork_reset();
  valk_aio_ssl_start();

  VALK_PASS();
}

void test_ssl_accept_null_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_t ssl = {0};
  int ret = valk_aio_ssl_accept(&ssl, nullptr);
  ASSERT_EQ(ret, -1);
  ASSERT_NULL(ssl.ssl);

  VALK_PASS();
}

void test_ssl_connect_null_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_t ssl = {0};
  int ret = valk_aio_ssl_connect(&ssl, nullptr);
  ASSERT_EQ(ret, -1);
  ASSERT_NULL(ssl.ssl);

  VALK_PASS();
}

void test_ssl_server_init_valid(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_server_init(&ctx,
    "vendor/nghttp2/src/test.example.com-key.pem",
    "vendor/nghttp2/src/test.example.com.pem");
  ASSERT_EQ(err, VALK_ERR_SUCCESS);
  ASSERT_NOT_NULL(ctx);

  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_encrypt_near_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);

  char ibuf[256], obuf[2048];
  memset(ibuf, 'A', sizeof(ibuf));
  valk_buffer_t in = {.items = ibuf, .count = 100, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 1500, .capacity = sizeof(obuf)};

  err = valk_aio_ssl_encrypt(&ssl, &in, &out);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);

  VALK_PASS();
}

static void dummy_on_read(void *arg, const valk_buffer_t *buf) {
  (void)arg;
  (void)buf;
}

void test_ssl_on_read_with_data_and_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = nullptr;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  valk_aio_ssl_t ssl = {0};
  valk_aio_ssl_connect(&ssl, ctx);

  char ibuf[256], obuf[16384];
  memset(ibuf, 0xFF, sizeof(ibuf));
  valk_buffer_t in = {.items = ibuf, .count = 50, .capacity = sizeof(ibuf)};
  valk_buffer_t out = {.items = obuf, .count = 0, .capacity = sizeof(obuf)};

  err = valk_aio_ssl_on_read(&ssl, &in, &out, nullptr, dummy_on_read);
  (void)err;

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_bidirectional_handshake(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *server_ctx = nullptr;
  valk_err_e err = valk_aio_ssl_server_init(&server_ctx,
    "vendor/nghttp2/src/test.example.com-key.pem",
    "vendor/nghttp2/src/test.example.com.pem");
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  SSL_CTX *client_ctx = nullptr;
  err = valk_aio_ssl_client_init(&client_ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  valk_aio_ssl_t server_ssl = {0};
  valk_aio_ssl_accept(&server_ssl, server_ctx);

  valk_aio_ssl_t client_ssl = {0};
  valk_aio_ssl_connect(&client_ssl, client_ctx);

  char client_out_buf[16384], server_out_buf[16384];
  char client_in_buf[16384], server_in_buf[16384];
  valk_buffer_t client_out = {.items = client_out_buf, .count = 0, .capacity = sizeof(client_out_buf)};
  valk_buffer_t server_out = {.items = server_out_buf, .count = 0, .capacity = sizeof(server_out_buf)};
  valk_buffer_t client_in = {.items = client_in_buf, .count = 0, .capacity = sizeof(client_in_buf)};
  valk_buffer_t server_in = {.items = server_in_buf, .count = 0, .capacity = sizeof(server_in_buf)};

  err = valk_aio_ssl_handshake(&client_ssl, &client_out);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  if (client_out.count > 0) {
    memcpy(server_in.items, client_out.items, client_out.count);
    server_in.count = client_out.count;
    client_out.count = 0;
  }

  err = valk_aio_ssl_on_read(&server_ssl, &server_in, &server_out, nullptr, nullptr);
  (void)err;

  if (server_out.count > 0) {
    memcpy(client_in.items, server_out.items, server_out.count);
    client_in.count = server_out.count;
    server_out.count = 0;
  }

  for (int i = 0; i < 10 && !SSL_is_init_finished(client_ssl.ssl); i++) {
    err = valk_aio_ssl_on_read(&client_ssl, &client_in, &client_out, nullptr, nullptr);
    (void)err;

    if (client_out.count > 0) {
      memcpy(server_in.items, client_out.items, client_out.count);
      server_in.count = client_out.count;
      client_out.count = 0;

      err = valk_aio_ssl_on_read(&server_ssl, &server_in, &server_out, nullptr, nullptr);
      (void)err;

      if (server_out.count > 0) {
        memcpy(client_in.items, server_out.items, server_out.count);
        client_in.count = server_out.count;
        server_out.count = 0;
      }
    }
  }

  valk_aio_ssl_free(&server_ssl);
  valk_aio_ssl_free(&client_ssl);
  SSL_CTX_free(server_ctx);
  SSL_CTX_free(client_ctx);

  VALK_PASS();
}

void test_ssl_encrypt_after_handshake(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *server_ctx = nullptr;
  valk_err_e err = valk_aio_ssl_server_init(&server_ctx,
    "vendor/nghttp2/src/test.example.com-key.pem",
    "vendor/nghttp2/src/test.example.com.pem");
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  SSL_CTX *client_ctx = nullptr;
  err = valk_aio_ssl_client_init(&client_ctx);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  valk_aio_ssl_t server_ssl = {0};
  valk_aio_ssl_accept(&server_ssl, server_ctx);

  valk_aio_ssl_t client_ssl = {0};
  valk_aio_ssl_connect(&client_ssl, client_ctx);

  char client_out_buf[16384], server_out_buf[16384];
  char client_in_buf[16384], server_in_buf[16384];
  valk_buffer_t client_out = {.items = client_out_buf, .count = 0, .capacity = sizeof(client_out_buf)};
  valk_buffer_t server_out = {.items = server_out_buf, .count = 0, .capacity = sizeof(server_out_buf)};
  valk_buffer_t client_in = {.items = client_in_buf, .count = 0, .capacity = sizeof(client_in_buf)};
  valk_buffer_t server_in = {.items = server_in_buf, .count = 0, .capacity = sizeof(server_in_buf)};

  err = valk_aio_ssl_handshake(&client_ssl, &client_out);
  ASSERT_EQ(err, VALK_ERR_SUCCESS);

  for (int i = 0; i < 20 && (!SSL_is_init_finished(client_ssl.ssl) || !SSL_is_init_finished(server_ssl.ssl)); i++) {
    if (client_out.count > 0) {
      memcpy(server_in.items, client_out.items, client_out.count);
      server_in.count = client_out.count;
      client_out.count = 0;

      err = valk_aio_ssl_on_read(&server_ssl, &server_in, &server_out, nullptr, nullptr);
      (void)err;
    }

    if (server_out.count > 0) {
      memcpy(client_in.items, server_out.items, server_out.count);
      client_in.count = server_out.count;
      server_out.count = 0;

      err = valk_aio_ssl_on_read(&client_ssl, &client_in, &client_out, nullptr, nullptr);
      (void)err;
    }

    if (client_in.count == 0 && server_in.count == 0 &&
        client_out.count == 0 && server_out.count == 0) {
      break;
    }
  }

  if (SSL_is_init_finished(client_ssl.ssl)) {
    char plaintext[256];
    memset(plaintext, 'X', sizeof(plaintext));
    valk_buffer_t plain_in = {.items = plaintext, .count = 100, .capacity = sizeof(plaintext)};
    client_out.count = 0;

    err = valk_aio_ssl_encrypt(&client_ssl, &plain_in, &client_out);
    ASSERT_EQ(err, VALK_ERR_SUCCESS);
    ASSERT_TRUE(client_out.count > 0);
  }

  valk_aio_ssl_free(&server_ssl);
  valk_aio_ssl_free(&client_ssl);
  SSL_CTX_free(server_ctx);
  SSL_CTX_free(client_ctx);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  
  valk_testsuite_add_test(suite, "test_ssl_server_init_valid", test_ssl_server_init_valid);
  valk_testsuite_add_test(suite, "test_ssl_start", test_ssl_start);
  valk_testsuite_add_test(suite, "test_ssl_server_init_invalid_files", test_ssl_server_init_invalid_files);
  valk_testsuite_add_test(suite, "test_ssl_server_init_valid_key_invalid_cert", test_ssl_server_init_valid_key_invalid_cert);
  valk_testsuite_add_test(suite, "test_ssl_handshake_null_ssl", test_ssl_handshake_null_ssl);
  valk_testsuite_add_test(suite, "test_ssl_handshake_invalid_ssl_fields", test_ssl_handshake_invalid_ssl_fields);
  valk_testsuite_add_test(suite, "test_ssl_handshake_null_output_buffer", test_ssl_handshake_null_output_buffer);
  valk_testsuite_add_test(suite, "test_ssl_handshake_invalid_output_buffer", test_ssl_handshake_invalid_output_buffer);
  valk_testsuite_add_test(suite, "test_ssl_handshake_buffer_overflow_condition", test_ssl_handshake_buffer_overflow_condition);
  valk_testsuite_add_test(suite, "test_ssl_on_read_null_ssl", test_ssl_on_read_null_ssl);
  valk_testsuite_add_test(suite, "test_ssl_on_read_invalid_ssl_fields", test_ssl_on_read_invalid_ssl_fields);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_null_ssl", test_ssl_encrypt_null_ssl);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_invalid_ssl_fields", test_ssl_encrypt_invalid_ssl_fields);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_null_input_buffer", test_ssl_encrypt_null_input_buffer);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_null_input_items", test_ssl_encrypt_null_input_items);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_null_output_buffer", test_ssl_encrypt_null_output_buffer);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_invalid_output_buffer", test_ssl_encrypt_invalid_output_buffer);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_output_buffer_overflow", test_ssl_encrypt_output_buffer_overflow);
  valk_testsuite_add_test(suite, "test_ssl_free_null", test_ssl_free_null);
  valk_testsuite_add_test(suite, "test_ssl_free_double_free", test_ssl_free_double_free);
  valk_testsuite_add_test(suite, "test_ssl_print_state_null", test_ssl_print_state_null);
  valk_testsuite_add_test(suite, "test_ssl_print_state_valid", test_ssl_print_state_valid);
  valk_testsuite_add_test(suite, "test_ssl_accept_and_connect", test_ssl_accept_and_connect);
  valk_testsuite_add_test(suite, "test_ssl_client_init", test_ssl_client_init);
  valk_testsuite_add_test(suite, "test_ssl_handshake_empty_output", test_ssl_handshake_empty_output);
  valk_testsuite_add_test(suite, "test_ssl_on_read_empty_input", test_ssl_on_read_empty_input);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_not_finished", test_ssl_encrypt_not_finished);
  valk_testsuite_add_test(suite, "test_ssl_handshake_tiny_buffer", test_ssl_handshake_tiny_buffer);
  valk_testsuite_add_test(suite, "test_ssl_handshake_full_buffer", test_ssl_handshake_full_buffer);
  valk_testsuite_add_test(suite, "test_ssl_on_read_with_garbage_data", test_ssl_on_read_with_garbage_data);
  valk_testsuite_add_test(suite, "test_ssl_accept_null_ctx", test_ssl_accept_null_ctx);
  valk_testsuite_add_test(suite, "test_ssl_connect_null_ctx", test_ssl_connect_null_ctx);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_near_capacity", test_ssl_encrypt_near_capacity);
  valk_testsuite_add_test(suite, "test_ssl_on_read_with_data_and_callback", test_ssl_on_read_with_data_and_callback);
  valk_testsuite_add_test(suite, "test_ssl_bidirectional_handshake", test_ssl_bidirectional_handshake);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_after_handshake", test_ssl_encrypt_after_handshake);
  valk_testsuite_add_test(suite, "test_ssl_fork_reset", test_ssl_fork_reset);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  
  return result;
}
