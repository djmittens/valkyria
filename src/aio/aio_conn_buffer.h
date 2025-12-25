#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define VALK_CONN_ENCRYPTED_SIZE (32 * 1024)
#define VALK_CONN_DECRYPTED_SIZE (32 * 1024)
#define VALK_CONN_BUFFER_SIZE (VALK_CONN_ENCRYPTED_SIZE + VALK_CONN_DECRYPTED_SIZE)

typedef struct valk_conn_read_buf {
  uint8_t encrypted[VALK_CONN_ENCRYPTED_SIZE];
  size_t encrypted_len;
  size_t encrypted_consumed;

  uint8_t decrypted[VALK_CONN_DECRYPTED_SIZE];
  size_t decrypted_len;
  size_t decrypted_consumed;
} valk_conn_read_buf_t;

void valk_conn_read_buf_init(valk_conn_read_buf_t *buf);

uint8_t *valk_conn_read_buf_get_encrypted_ptr(valk_conn_read_buf_t *buf, size_t *available);

void valk_conn_read_buf_commit_encrypted(valk_conn_read_buf_t *buf, size_t len);

const uint8_t *valk_conn_read_buf_get_encrypted(valk_conn_read_buf_t *buf, size_t *len);

void valk_conn_read_buf_consume_encrypted(valk_conn_read_buf_t *buf, size_t len);

uint8_t *valk_conn_read_buf_get_decrypted_ptr(valk_conn_read_buf_t *buf, size_t *available);

void valk_conn_read_buf_commit_decrypted(valk_conn_read_buf_t *buf, size_t len);

const uint8_t *valk_conn_read_buf_get_decrypted(valk_conn_read_buf_t *buf, size_t *len);

void valk_conn_read_buf_consume_decrypted(valk_conn_read_buf_t *buf, size_t len);

void valk_conn_read_buf_compact(valk_conn_read_buf_t *buf);

size_t valk_conn_read_buf_encrypted_available(const valk_conn_read_buf_t *buf);
size_t valk_conn_read_buf_decrypted_available(const valk_conn_read_buf_t *buf);
