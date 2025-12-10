#pragma once
#include <stdbool.h>
#include <stddef.h>

typedef struct {
  const char *filename;
  size_t eval_count;
} valk_coverage_file_t;

typedef struct {
  valk_coverage_file_t *files;
  size_t count;
  size_t capacity;
} valk_coverage_data_t;

void valk_coverage_init(void);
void valk_coverage_record_file(const char *filename);
void valk_coverage_report(const char *output_file);
void valk_coverage_reset(void);
void valk_coverage_save_on_exit(void);
bool valk_coverage_enabled(void);
