#include "lsp_io.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

bool lsp_read_message(lsp_message_t *msg) {
  int content_length = -1;
  char line[4096];

  while (fgets(line, sizeof(line), stdin)) {
    if (strncmp(line, "Content-Length:", 15) == 0) {
      content_length = atoi(line + 15);
    }
    if (strcmp(line, "\r\n") == 0 || strcmp(line, "\n") == 0)
      break;
  }

  if (content_length <= 0) return false;

  msg->body = malloc(content_length + 1);
  if (!msg->body) return false;

  size_t total = 0;
  while (total < (size_t)content_length) {
    size_t n = fread(msg->body + total, 1, content_length - total, stdin);
    if (n == 0) {
      free(msg->body);
      msg->body = nullptr;
      return false;
    }
    total += n;
  }
  msg->body[content_length] = '\0';
  msg->len = content_length;
  return true;
}

static void lsp_write_raw(const char *body, size_t len) {
  fprintf(stdout, "Content-Length: %zu\r\n\r\n", len);
  fwrite(body, 1, len, stdout);
  fflush(stdout);
}

void lsp_send_response(int id, const char *result_json) {
  char buf[65536];
  int n = snprintf(buf, sizeof(buf),
                   "{\"jsonrpc\":\"2.0\",\"id\":%d,\"result\":%s}", id,
                   result_json);
  if (n > 0 && (size_t)n < sizeof(buf))
    lsp_write_raw(buf, n);
}

void lsp_send_error(int id, int code, const char *message) {
  char buf[8192];
  int n = snprintf(buf, sizeof(buf),
                   "{\"jsonrpc\":\"2.0\",\"id\":%d,"
                   "\"error\":{\"code\":%d,\"message\":\"%s\"}}",
                   id, code, message);
  if (n > 0 && (size_t)n < sizeof(buf))
    lsp_write_raw(buf, n);
}

void lsp_send_notification(const char *method, const char *params_json) {
  char buf[65536];
  int n = snprintf(buf, sizeof(buf),
                   "{\"jsonrpc\":\"2.0\",\"method\":\"%s\",\"params\":%s}",
                   method, params_json);
  if (n > 0 && (size_t)n < sizeof(buf))
    lsp_write_raw(buf, n);
}

void lsp_message_free(lsp_message_t *msg) {
  free(msg->body);
  msg->body = nullptr;
  msg->len = 0;
}
