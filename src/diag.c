#include "diag.h"

#include <stdlib.h>
#include <string.h>

void valk_diag_init(valk_diag_list_t *list) {
  *list = (valk_diag_list_t){0};
}

void valk_diag_add(valk_diag_list_t *list, const char *msg,
                   int offset, int len, int severity) {
  if (list->count >= list->cap) {
    list->cap = list->cap == 0 ? 16 : list->cap * 2;
    list->items = realloc(list->items, sizeof(valk_diag_t) * list->cap);
  }
  list->items[list->count++] = (valk_diag_t){
    .message = strdup(msg),
    .offset = offset,
    .len = len > 0 ? len : 1,
    .severity = severity,
  };
}

void valk_diag_free(valk_diag_list_t *list) {
  for (size_t i = 0; i < list->count; i++)
    free(list->items[i].message);
  free(list->items);
  *list = (valk_diag_list_t){0};
}

int valk_diag_error_count(valk_diag_list_t *list) {
  int n = 0;
  for (size_t i = 0; i < list->count; i++)
    if (list->items[i].severity == VALK_DIAG_ERROR)
      n++;
  return n;
}

void valk_diag_fprint(valk_diag_list_t *list, const char *filename,
                      const char *text, FILE *out) {
  for (size_t i = 0; i < list->count; i++) {
    int line = 1, col = 1;
    for (int j = 0; j < list->items[i].offset && text[j]; j++) {
      if (text[j] == '\n') { line++; col = 1; }
      else col++;
    }
    const char *sev = "info";
    if (list->items[i].severity == VALK_DIAG_ERROR) sev = "error";
    else if (list->items[i].severity == VALK_DIAG_WARNING) sev = "warning";
    fprintf(out, "%s:%d:%d: %s: %s\n",
            filename, line, col, sev, list->items[i].message);
  }
}
