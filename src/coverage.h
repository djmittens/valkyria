#pragma once
#include <stdbool.h>
#include <stddef.h>

#define COVERAGE_HASH_SIZE 512
#define EXPR_HASH_SIZE 4096

typedef struct valk_coverage_file_t {
  const char *filename;
  size_t eval_count;
  struct valk_coverage_file_t *next;
} valk_coverage_file_t;

typedef struct {
  valk_coverage_file_t *buckets[COVERAGE_HASH_SIZE];
  size_t total_files;
  size_t total_evals;
} valk_coverage_data_t;

void valk_coverage_init(void);
void valk_coverage_record_file(const char *filename);
void valk_coverage_report(const char *output_file);
void valk_coverage_report_lcov(const char *output_file);
void valk_coverage_reset(void);
void valk_coverage_save_on_exit(void);
bool valk_coverage_enabled(void);
const char *valk_coverage_output_path(void);

#ifdef VALK_COVERAGE
#include "valk_thread.h"
#include <stdint.h>

typedef struct valk_branch_t {
  uint16_t line;
  uint32_t true_count;
  uint32_t false_count;
  struct valk_branch_t *next;
} valk_branch_t;

typedef struct valk_expr_t {
  uint16_t file_id;
  uint16_t line;
  uint16_t column;
  uint16_t end_column;
  uint32_t hit_count;
  struct valk_expr_t *next;
} valk_expr_t;

typedef struct valk_line_coverage_file_t {
  char *filename;
  uint16_t file_id;
  uint32_t *line_counts;
  size_t line_capacity;
  size_t lines_hit;
  valk_branch_t *branches;
  size_t branches_found;
  size_t branches_hit;
  valk_expr_t **expr_buckets;
  size_t exprs_found;
  size_t exprs_hit;
  struct valk_line_coverage_file_t *next;
} valk_line_coverage_file_t;

typedef struct {
  valk_line_coverage_file_t *buckets[COVERAGE_HASH_SIZE];
  size_t total_files;
  valk_mutex_t lock;
} valk_line_coverage_t;

extern valk_line_coverage_t g_line_coverage;

void valk_line_coverage_init(void);
void valk_coverage_record_line(uint16_t file_id, uint16_t line);
void valk_coverage_mark_line(uint16_t file_id, uint16_t line);
void valk_coverage_record_branch(uint16_t file_id, uint16_t line, bool taken);
valk_line_coverage_file_t *valk_coverage_get_file(uint16_t file_id);
void valk_line_coverage_reset(void);

void valk_coverage_mark_expr(uint16_t file_id, uint16_t line, uint16_t column, uint16_t end_column);
void valk_coverage_record_expr(uint16_t file_id, uint16_t line, uint16_t column);
size_t valk_coverage_get_line_expr_count(uint16_t file_id, uint16_t line, size_t *hit, size_t *total);

#define VALK_COVERAGE_RECORD_LINE(fid, line) valk_coverage_record_line(fid, line)
#define VALK_COVERAGE_MARK_LINE(fid, line) valk_coverage_mark_line(fid, line)
#define VALK_COVERAGE_RECORD_LVAL(lval) do { \
  if ((lval) != NULL && (lval)->cov_line > 0) { \
    valk_coverage_record_expr((lval)->cov_file_id, (lval)->cov_line, (lval)->cov_column); \
  } \
} while(0)
#define VALK_COVERAGE_MARK_LVAL(lval) do { \
  if ((lval) != NULL && (lval)->cov_line > 0) { \
    valk_coverage_mark_expr((lval)->cov_file_id, (lval)->cov_line, (lval)->cov_column, 0); \
  } \
} while(0)
#define VALK_COVERAGE_RECORD_BRANCH(fid, line, taken) valk_coverage_record_branch(fid, line, taken)

#else

#define VALK_COVERAGE_RECORD_LINE(fid, line) ((void)0)
#define VALK_COVERAGE_MARK_LINE(fid, line) ((void)0)
#define VALK_COVERAGE_RECORD_LVAL(lval) ((void)0)
#define VALK_COVERAGE_MARK_LVAL(lval) ((void)0)
#define VALK_COVERAGE_RECORD_BRANCH(fid, line, taken) ((void)0)

#endif
