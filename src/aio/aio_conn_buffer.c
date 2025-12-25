#include "aio_conn_buffer.h"
#include <string.h>

void valk_conn_read_buf_init(valk_conn_read_buf_t *buf) {
  buf->encrypted_len = 0;
  buf->encrypted_consumed = 0;
  buf->decrypted_len = 0;
  buf->decrypted_consumed = 0;
}

uint8_t *valk_conn_read_buf_get_encrypted_ptr(valk_conn_read_buf_t *buf, size_t *available) {
  size_t used = buf->encrypted_len;
  if (used >= VALK_CONN_ENCRYPTED_SIZE) {
    *available = 0;
    return nullptr;
  }
  *available = VALK_CONN_ENCRYPTED_SIZE - used;
  return buf->encrypted + used;
}

void valk_conn_read_buf_commit_encrypted(valk_conn_read_buf_t *buf, size_t len) {
  buf->encrypted_len += len;
  if (buf->encrypted_len > VALK_CONN_ENCRYPTED_SIZE) {
    buf->encrypted_len = VALK_CONN_ENCRYPTED_SIZE;
  }
}

const uint8_t *valk_conn_read_buf_get_encrypted(valk_conn_read_buf_t *buf, size_t *len) {
  *len = buf->encrypted_len - buf->encrypted_consumed;
  return buf->encrypted + buf->encrypted_consumed;
}

void valk_conn_read_buf_consume_encrypted(valk_conn_read_buf_t *buf, size_t len) {
  buf->encrypted_consumed += len;
  if (buf->encrypted_consumed > buf->encrypted_len) {
    buf->encrypted_consumed = buf->encrypted_len;
  }
}

uint8_t *valk_conn_read_buf_get_decrypted_ptr(valk_conn_read_buf_t *buf, size_t *available) {
  size_t used = buf->decrypted_len;
  if (used >= VALK_CONN_DECRYPTED_SIZE) {
    *available = 0;
    return nullptr;
  }
  *available = VALK_CONN_DECRYPTED_SIZE - used;
  return buf->decrypted + used;
}

void valk_conn_read_buf_commit_decrypted(valk_conn_read_buf_t *buf, size_t len) {
  buf->decrypted_len += len;
  if (buf->decrypted_len > VALK_CONN_DECRYPTED_SIZE) {
    buf->decrypted_len = VALK_CONN_DECRYPTED_SIZE;
  }
}

const uint8_t *valk_conn_read_buf_get_decrypted(valk_conn_read_buf_t *buf, size_t *len) {
  *len = buf->decrypted_len - buf->decrypted_consumed;
  return buf->decrypted + buf->decrypted_consumed;
}

void valk_conn_read_buf_consume_decrypted(valk_conn_read_buf_t *buf, size_t len) {
  buf->decrypted_consumed += len;
  if (buf->decrypted_consumed > buf->decrypted_len) {
    buf->decrypted_consumed = buf->decrypted_len;
  }
}

void valk_conn_read_buf_compact(valk_conn_read_buf_t *buf) {
  if (buf->encrypted_consumed > 0) {
    size_t remaining = buf->encrypted_len - buf->encrypted_consumed;
    if (remaining > 0) {
      memmove(buf->encrypted, buf->encrypted + buf->encrypted_consumed, remaining);
    }
    buf->encrypted_len = remaining;
    buf->encrypted_consumed = 0;
  }

  if (buf->decrypted_consumed > 0) {
    size_t remaining = buf->decrypted_len - buf->decrypted_consumed;
    if (remaining > 0) {
      memmove(buf->decrypted, buf->decrypted + buf->decrypted_consumed, remaining);
    }
    buf->decrypted_len = remaining;
    buf->decrypted_consumed = 0;
  }
}

size_t valk_conn_read_buf_encrypted_available(const valk_conn_read_buf_t *buf) {
  return buf->encrypted_len - buf->encrypted_consumed;
}

size_t valk_conn_read_buf_decrypted_available(const valk_conn_read_buf_t *buf) {
  return buf->decrypted_len - buf->decrypted_consumed;
}
