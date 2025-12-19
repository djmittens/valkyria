#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio_ssl.h"
#include "../../src/common.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_ssl_start_idempotent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();
  valk_aio_ssl_start();
  valk_aio_ssl_start();

  VALK_PASS();
}

void test_ssl_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_free(NULL);

  valk_aio_ssl_t ssl = {0};
  ssl.ssl = NULL;
  valk_aio_ssl_free(&ssl);

  VALK_PASS();
}

void test_ssl_handshake_null_ssl(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_buffer_t out;
  valk_buffer_alloc(&out, 1024);

  valk_err_e err = valk_aio_ssl_handshake(NULL, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "NULL ssl should return INVALID");

  valk_mem_free(out.items);

  VALK_PASS();
}

void test_ssl_handshake_null_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_err_e init_err = valk_aio_ssl_client_init(&ctx);
  VALK_TEST_ASSERT(init_err == VALK_ERR_SUCCESS, "Client init should succeed");
  VALK_TEST_ASSERT(ctx != NULL, "CTX should be created");

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);

  valk_err_e err = valk_aio_ssl_handshake(&ssl, NULL);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "NULL buffer should return INVALID");

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_handshake_invalid_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_err_e init_err = valk_aio_ssl_client_init(&ctx);
  VALK_TEST_ASSERT(init_err == VALK_ERR_SUCCESS, "Client init should succeed");

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);

  valk_buffer_t out = {0};
  out.items = NULL;
  out.capacity = 0;
  out.count = 0;

  valk_err_e err = valk_aio_ssl_handshake(&ssl, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "Zero capacity buffer should return INVALID");

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_handshake_buffer_overflow(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_err_e init_err = valk_aio_ssl_client_init(&ctx);
  VALK_TEST_ASSERT(init_err == VALK_ERR_SUCCESS, "Client init should succeed");

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);

  valk_buffer_t out;
  valk_buffer_alloc(&out, 1024);
  out.count = 2000;

  valk_err_e err = valk_aio_ssl_handshake(&ssl, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "Overflow buffer should return INVALID");

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  valk_mem_free(out.items);

  VALK_PASS();
}

void test_ssl_encrypt_null_ssl(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_buffer_t in, out;
  valk_buffer_alloc(&in, 1024);
  valk_buffer_alloc(&out, 1024);

  valk_err_e err = valk_aio_ssl_encrypt(NULL, &in, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "NULL ssl should return INVALID");

  valk_mem_free(in.items);
  valk_mem_free(out.items);

  VALK_PASS();
}

void test_ssl_encrypt_null_input(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);

  valk_buffer_t out;
  valk_buffer_alloc(&out, 1024);

  valk_err_e err = valk_aio_ssl_encrypt(&ssl, NULL, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "NULL input buffer should return INVALID");

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  valk_mem_free(out.items);

  VALK_PASS();
}

void test_ssl_encrypt_null_output(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);

  valk_buffer_t in;
  valk_buffer_alloc(&in, 1024);

  valk_err_e err = valk_aio_ssl_encrypt(&ssl, &in, NULL);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "NULL output buffer should return INVALID");

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  valk_mem_free(in.items);

  VALK_PASS();
}

void test_ssl_encrypt_output_overflow(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);

  valk_buffer_t in, out;
  valk_buffer_alloc(&in, 1024);
  valk_buffer_alloc(&out, 1024);
  out.count = 2000;

  valk_err_e err = valk_aio_ssl_encrypt(&ssl, &in, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "Overflow output should return INVALID");

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);
  valk_mem_free(in.items);
  valk_mem_free(out.items);

  VALK_PASS();
}

void test_ssl_on_read_null_ssl(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_buffer_t in, out;
  valk_buffer_alloc(&in, 1024);
  valk_buffer_alloc(&out, 1024);

  valk_err_e err = valk_aio_ssl_on_read(NULL, &in, &out, NULL, NULL);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "NULL ssl should return INVALID");

  valk_mem_free(in.items);
  valk_mem_free(out.items);

  VALK_PASS();
}

void test_ssl_client_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_err_e err = valk_aio_ssl_client_init(&ctx);
  VALK_TEST_ASSERT(err == VALK_ERR_SUCCESS, "Client init should succeed");
  VALK_TEST_ASSERT(ctx != NULL, "CTX should be created");

  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_connect_creates_bios(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);

  VALK_TEST_ASSERT(ssl.ssl != NULL, "SSL should be created");
  VALK_TEST_ASSERT(ssl.read_bio != NULL, "read_bio should be created");
  VALK_TEST_ASSERT(ssl.write_bio != NULL, "write_bio should be created");

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_accept_creates_bios(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_server_init(&ctx, "localhost.key", "localhost.crt");
  if (ctx == NULL) {
    VALK_SKIP("No server cert files available");
    return;
  }

  valk_aio_ssl_t ssl;
  valk_aio_ssl_accept(&ssl, ctx);

  VALK_TEST_ASSERT(ssl.ssl != NULL, "SSL should be created");
  VALK_TEST_ASSERT(ssl.read_bio != NULL, "read_bio should be created");
  VALK_TEST_ASSERT(ssl.write_bio != NULL, "write_bio should be created");

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_free_clears_pointers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);
  valk_aio_ssl_free(&ssl);

  VALK_TEST_ASSERT(ssl.ssl == NULL, "ssl should be NULL after free");
  VALK_TEST_ASSERT(ssl.read_bio == NULL, "read_bio should be NULL after free");
  VALK_TEST_ASSERT(ssl.write_bio == NULL, "write_bio should be NULL after free");

  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_free_idempotent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);
  valk_aio_ssl_free(&ssl);
  valk_aio_ssl_free(&ssl);
  valk_aio_ssl_free(&ssl);

  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_print_state_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_print_state(NULL);

  valk_aio_ssl_t ssl = {0};
  ssl.ssl = NULL;
  valk_aio_ssl_print_state(&ssl);

  VALK_PASS();
}

void test_ssl_print_state_valid(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);

  valk_aio_ssl_print_state(&ssl);

  valk_aio_ssl_free(&ssl);
  SSL_CTX_free(ctx);

  VALK_PASS();
}

void test_ssl_server_init_bad_keyfile(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_err_e err = valk_aio_ssl_server_init(&ctx, "/nonexistent/key.pem", "cert.pem");
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INIT, "Should fail with bad keyfile");
  VALK_TEST_ASSERT(ctx == NULL, "CTX should be NULL on failure");

  VALK_PASS();
}

void test_ssl_server_init_bad_certfile(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  FILE *f = fopen("/tmp/test_key.pem", "w");
  if (!f) {
    VALK_SKIP("Cannot create temp key file");
    return;
  }
  fprintf(f, "-----BEGIN PRIVATE KEY-----\n");
  fprintf(f, "MIIEvAIBADANBgkqhkiG9w0BAQEFAASCBKYwggSiAgEAAoIBAQC7fLQEkG+sZ3uK\n");
  fclose(f);

  SSL_CTX *ctx = NULL;
  valk_err_e err = valk_aio_ssl_server_init(&ctx, "/tmp/test_key.pem", "/nonexistent/cert.pem");
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INIT, "Should fail with bad certfile");

  remove("/tmp/test_key.pem");

  VALK_PASS();
}

void test_ssl_handshake_freed_ssl(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);
  valk_aio_ssl_free(&ssl);

  valk_buffer_t out;
  valk_buffer_alloc(&out, 1024);

  valk_err_e err = valk_aio_ssl_handshake(&ssl, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "Freed ssl should return INVALID");

  SSL_CTX_free(ctx);
  valk_mem_free(out.items);

  VALK_PASS();
}

void test_ssl_encrypt_freed_ssl(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);
  valk_aio_ssl_free(&ssl);

  valk_buffer_t in, out;
  valk_buffer_alloc(&in, 1024);
  valk_buffer_alloc(&out, 1024);

  valk_err_e err = valk_aio_ssl_encrypt(&ssl, &in, &out);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "Freed ssl should return INVALID");

  SSL_CTX_free(ctx);
  valk_mem_free(in.items);
  valk_mem_free(out.items);

  VALK_PASS();
}

void test_ssl_on_read_freed_ssl(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_ssl_start();

  SSL_CTX *ctx = NULL;
  valk_aio_ssl_client_init(&ctx);

  valk_aio_ssl_t ssl;
  valk_aio_ssl_connect(&ssl, ctx);
  valk_aio_ssl_free(&ssl);

  valk_buffer_t in, out;
  valk_buffer_alloc(&in, 1024);
  valk_buffer_alloc(&out, 1024);

  valk_err_e err = valk_aio_ssl_on_read(&ssl, &in, &out, NULL, NULL);
  VALK_TEST_ASSERT(err == VALK_ERR_SSL_INVALID, "Freed ssl should return INVALID");

  SSL_CTX_free(ctx);
  valk_mem_free(in.items);
  valk_mem_free(out.items);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_ssl_start_idempotent", test_ssl_start_idempotent);
  valk_testsuite_add_test(suite, "test_ssl_free_null", test_ssl_free_null);
  valk_testsuite_add_test(suite, "test_ssl_handshake_null_ssl", test_ssl_handshake_null_ssl);
  valk_testsuite_add_test(suite, "test_ssl_handshake_null_buffer", test_ssl_handshake_null_buffer);
  valk_testsuite_add_test(suite, "test_ssl_handshake_invalid_buffer", test_ssl_handshake_invalid_buffer);
  valk_testsuite_add_test(suite, "test_ssl_handshake_buffer_overflow", test_ssl_handshake_buffer_overflow);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_null_ssl", test_ssl_encrypt_null_ssl);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_null_input", test_ssl_encrypt_null_input);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_null_output", test_ssl_encrypt_null_output);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_output_overflow", test_ssl_encrypt_output_overflow);
  valk_testsuite_add_test(suite, "test_ssl_on_read_null_ssl", test_ssl_on_read_null_ssl);
  valk_testsuite_add_test(suite, "test_ssl_client_init", test_ssl_client_init);
  valk_testsuite_add_test(suite, "test_ssl_connect_creates_bios", test_ssl_connect_creates_bios);
  valk_testsuite_add_test(suite, "test_ssl_accept_creates_bios", test_ssl_accept_creates_bios);
  valk_testsuite_add_test(suite, "test_ssl_free_clears_pointers", test_ssl_free_clears_pointers);
  valk_testsuite_add_test(suite, "test_ssl_free_idempotent", test_ssl_free_idempotent);
  valk_testsuite_add_test(suite, "test_ssl_print_state_null", test_ssl_print_state_null);
  valk_testsuite_add_test(suite, "test_ssl_print_state_valid", test_ssl_print_state_valid);
  valk_testsuite_add_test(suite, "test_ssl_server_init_bad_keyfile", test_ssl_server_init_bad_keyfile);
  valk_testsuite_add_test(suite, "test_ssl_server_init_bad_certfile", test_ssl_server_init_bad_certfile);
  valk_testsuite_add_test(suite, "test_ssl_handshake_freed_ssl", test_ssl_handshake_freed_ssl);
  valk_testsuite_add_test(suite, "test_ssl_encrypt_freed_ssl", test_ssl_encrypt_freed_ssl);
  valk_testsuite_add_test(suite, "test_ssl_on_read_freed_ssl", test_ssl_on_read_freed_ssl);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
