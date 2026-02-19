#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>

#define VALK_DIAG_ERROR   1
#define VALK_DIAG_WARNING 2
#define VALK_DIAG_INFO    3
#define VALK_DIAG_HINT    4

typedef struct {
  char *message;
  int offset;
  int len;
  int severity;
} valk_diag_t;

typedef struct {
  valk_diag_t *items;
  size_t count;
  size_t cap;
} valk_diag_list_t;

typedef struct {
  bool (*is_known)(const char *name, void *ctx);
  void *ctx;
} valk_name_resolver_t;

void valk_diag_init(valk_diag_list_t *list);
void valk_diag_add(valk_diag_list_t *list, const char *msg,
                   int offset, int len, int severity);
void valk_diag_free(valk_diag_list_t *list);
int valk_diag_error_count(valk_diag_list_t *list);
void valk_diag_fprint(valk_diag_list_t *list, const char *filename,
                      const char *text, FILE *out);

struct valk_lval_t;

valk_diag_list_t valk_check_text(const char *text,
                                  valk_name_resolver_t resolver,
                                  struct valk_lval_t **ast_out);
