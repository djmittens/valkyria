#pragma once

#include "types.h"
#include <stdbool.h>
#include <stddef.h>

#define COVERAGE_HASH_SIZE 512
#define EXPR_HASH_SIZE 4096

typedef struct valk_coverage_file_t {
  const char *filename;
  u64 eval_count;
  struct valk_coverage_file_t *next;
} valk_coverage_file_t;

typedef struct {
  valk_coverage_file_t *buckets[COVERAGE_HASH_SIZE];
  u64 total_files;
  u64 total_evals;
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

typedef struct valk_branch_t {
  u16 line;
  u32 true_count;
  u32 false_count;
  struct valk_branch_t *next;
} valk_branch_t;

typedef struct valk_expr_t {
  u16 file_id;
  u16 line;
  u16 column;
  u16 end_column;
  u32 hit_count;
  struct valk_expr_t *next;
} valk_expr_t;

typedef struct valk_line_coverage_file_t {
  char *filename;
  u16 file_id;
  u32 *line_counts;
  u64 line_capacity;
  u64 lines_hit;
  valk_branch_t *branches;
  u64 branches_found;
  u64 branches_hit;
  valk_expr_t **expr_buckets;
  u64 exprs_found;
  u64 exprs_hit;
  struct valk_line_coverage_file_t *next;
} valk_line_coverage_file_t;

typedef struct {
  valk_line_coverage_file_t *buckets[COVERAGE_HASH_SIZE];
  u64 total_files;
  valk_mutex_t lock;
} valk_line_coverage_t;

extern valk_line_coverage_t g_line_coverage;

void valk_line_coverage_init(void);
void valk_coverage_record_line(u16 file_id, u16 line);
void valk_coverage_mark_line(u16 file_id, u16 line);
void valk_coverage_record_branch(u16 file_id, u16 line, bool taken);
valk_line_coverage_file_t *valk_coverage_get_file(u16 file_id);
void valk_line_coverage_reset(void);

void valk_coverage_mark_expr(u16 file_id, u16 line, u16 column, u16 end_column);
void valk_coverage_record_expr(u16 file_id, u16 line, u16 column);
u64 valk_coverage_get_line_expr_count(u16 file_id, u16 line, u64 *hit, u64 *total);

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
