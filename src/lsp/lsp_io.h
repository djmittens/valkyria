#pragma once

#include <stdbool.h>
#include <stddef.h>

typedef struct {
  char *body;
  size_t len;
} lsp_message_t;

bool lsp_read_message(lsp_message_t *msg);
void lsp_send_response(int id, const char *result_json);
void lsp_send_error(int id, int code, const char *message);
void lsp_send_notification(const char *method, const char *params_json);
void lsp_message_free(lsp_message_t *msg);
