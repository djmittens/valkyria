#include "coverage.h"
#include "valk_thread.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef VALK_COVERAGE
#include "source_loc.h"

static valk_coverage_data_t g_coverage;
static const char *g_coverage_output = nullptr;
static valk_mutex_t g_coverage_lock;
static bool g_coverage_lock_initialized = false;

static void ensure_coverage_lock_init(void) {
  if (!g_coverage_lock_initialized) {
    valk_mutex_init(&g_coverage_lock);
    g_coverage_lock_initialized = true;
  }
}

static u32 coverage_hash(const char *str) {
  u32 hash = 5381;
  int c;
  while ((c = *str++)) {
    hash = ((hash << 5) + hash) + (u32)c;
  }
  return hash % COVERAGE_HASH_SIZE;
}

void valk_coverage_init(void) {
  const char *output_env = getenv("VALK_COVERAGE_OUTPUT");
  g_coverage_output = output_env ? output_env : "build-coverage/coverage-valk.txt";
  for (int i = 0; i < COVERAGE_HASH_SIZE; i++) {
    g_coverage.buckets[i] = nullptr;
  }
  g_coverage.total_files = 0;
  g_coverage.total_evals = 0;
}

bool valk_coverage_enabled(void) {
  return true;
}

const char *valk_coverage_output_path(void) {
  return g_coverage_output;
}

void valk_coverage_record_file(const char *filename) {
  ensure_coverage_lock_init();
  valk_mutex_lock(&g_coverage_lock);
  
  u32 bucket = coverage_hash(filename);
  valk_coverage_file_t *entry = g_coverage.buckets[bucket];
  
  while (entry != nullptr) {
    if (strcmp(entry->filename, filename) == 0) {
      entry->eval_count++;
      g_coverage.total_evals++;
      valk_mutex_unlock(&g_coverage_lock);
      return;
    }
    entry = entry->next;
  }
  
  valk_coverage_file_t *new_entry = malloc(sizeof(valk_coverage_file_t));
  if (new_entry == nullptr) {
    valk_mutex_unlock(&g_coverage_lock);
    return;
  }
  
  new_entry->filename = strdup(filename);
  if (new_entry->filename == nullptr) {
    free(new_entry);
    valk_mutex_unlock(&g_coverage_lock);
    return;
  }
  
  new_entry->eval_count = 1;
  new_entry->next = g_coverage.buckets[bucket];
  g_coverage.buckets[bucket] = new_entry;
  g_coverage.total_files++;
  g_coverage.total_evals++;
  
  valk_mutex_unlock(&g_coverage_lock);
}

static int compare_filenames(const void *a, const void *b) {
  const valk_coverage_file_t *fa = *(const valk_coverage_file_t **)a;
  const valk_coverage_file_t *fb = *(const valk_coverage_file_t **)b;
  return strcmp(fa->filename, fb->filename);
}

static valk_coverage_file_t **collect_sorted_files(u64 *count) {
  *count = g_coverage.total_files;
  if (*count == 0) return nullptr;
  
  valk_coverage_file_t **files = malloc(*count * sizeof(valk_coverage_file_t *));
  if (files == nullptr) return nullptr;
  
  u64 idx = 0;
  for (int i = 0; i < COVERAGE_HASH_SIZE && idx < *count; i++) {
    valk_coverage_file_t *entry = g_coverage.buckets[i];
    while (entry != nullptr && idx < *count) {
      files[idx++] = entry;
      entry = entry->next;
    }
  }
  
  qsort(files, *count, sizeof(valk_coverage_file_t *), compare_filenames);
  return files;
}

void valk_coverage_report(const char *output_file) {
  if (g_coverage.total_files == 0) return;
  
  ensure_coverage_lock_init();
  valk_mutex_lock(&g_coverage_lock);
  
  u64 count;
  valk_coverage_file_t **files = collect_sorted_files(&count);
  if (files == nullptr) {
    valk_mutex_unlock(&g_coverage_lock);
    return;
  }
  
  FILE *f = fopen(output_file, "a");
  if (!f) {
    fprintf(stderr, "Failed to open coverage file: %s\n", output_file);
    free(files);
    valk_mutex_unlock(&g_coverage_lock);
    return;
  }
  
  for (u64 i = 0; i < count; i++) {
    fprintf(f, "%s:%llu\n", files[i]->filename, (unsigned long long)files[i]->eval_count);
  }
  
  fclose(f);
  free(files);
  valk_mutex_unlock(&g_coverage_lock);
}

void valk_coverage_report_lcov(const char *output_file) {
  if (g_line_coverage.total_files == 0) return;
  valk_mutex_lock(&g_line_coverage.lock);
  
  FILE *f = fopen(output_file, "a");
  if (!f) {
    valk_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  
  fprintf(f, "TN:\n");
  
  for (int i = 0; i < COVERAGE_HASH_SIZE; i++) {
    valk_line_coverage_file_t *fc = g_line_coverage.buckets[i];
    while (fc != nullptr) {
      fprintf(f, "SF:%s\n", fc->filename);
      fprintf(f, "FNF:0\n");
      fprintf(f, "FNH:0\n");
      
      u64 lines_found = 0;
      u64 lines_hit = 0;
      for (u64 line = 1; line < fc->line_capacity; line++) {
        if (fc->line_counts[line] != UINT32_MAX) {
          fprintf(f, "DA:%llu,%u\n", (unsigned long long)line, fc->line_counts[line]);
          if (fc->expr_buckets != nullptr) {
            for (u32 b = 0; b < EXPR_HASH_SIZE; b++) {
              valk_expr_t *e = fc->expr_buckets[b];
              while (e != nullptr) {
                if (e->line == line) {
                  fprintf(f, "EXPRDATA:%llu,%u,%u,%u\n", (unsigned long long)line, e->column, e->end_column, e->hit_count);
                }
                e = e->next;
              }
            }
          }
          lines_found++;
          if (fc->line_counts[line] > 0) {
            lines_hit++;
          }
        }
      }
      
      u64 branches_found = 0;
      u64 branches_hit = 0;
      for (valk_branch_t *br = fc->branches; br != nullptr; br = br->next) {
        fprintf(f, "BRDA:%u,0,0,%s\n", br->line, br->true_count > 0 ? "1" : "-");
        fprintf(f, "BRDA:%u,0,1,%s\n", br->line, br->false_count > 0 ? "1" : "-");
        branches_found += 2;
        if (br->true_count > 0) branches_hit++;
        if (br->false_count > 0) branches_hit++;
      }
      
      fprintf(f, "BRF:%llu\n", (unsigned long long)branches_found);
      fprintf(f, "BRH:%llu\n", (unsigned long long)branches_hit);
      fprintf(f, "LF:%llu\n", (unsigned long long)(lines_found > 0 ? lines_found : 1));
      fprintf(f, "LH:%llu\n", (unsigned long long)lines_hit);
      fprintf(f, "end_of_record\n");
      
      fc = fc->next;
    }
  }
  
  fclose(f);
  valk_mutex_unlock(&g_line_coverage.lock);
}

void valk_coverage_reset(void) {
  ensure_coverage_lock_init();
  valk_mutex_lock(&g_coverage_lock);
  
  for (int i = 0; i < COVERAGE_HASH_SIZE; i++) {
    valk_coverage_file_t *entry = g_coverage.buckets[i];
    while (entry != nullptr) {
      valk_coverage_file_t *next = entry->next;
      free((char *)entry->filename);
      free(entry);
      entry = next;
    }
    g_coverage.buckets[i] = nullptr;
  }
  
  g_coverage.total_files = 0;
  g_coverage.total_evals = 0;
  
  valk_mutex_unlock(&g_coverage_lock);
}

void valk_coverage_save_on_exit(void) {
  bool has_data = g_coverage.total_files > 0 || g_line_coverage.total_files > 0;
  if (has_data) {
    valk_coverage_report(g_coverage_output);
    
    u64 len = strlen(g_coverage_output);
    char *lcov_path = malloc(len + 6);
    if (lcov_path != nullptr) {
      const char *ext = strrchr(g_coverage_output, '.');
      if (ext != nullptr) {
        u64 base_len = (u64)(ext - g_coverage_output);
        memcpy(lcov_path, g_coverage_output, base_len);
        // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.strcpy)
        strcpy(lcov_path + base_len, ".info");
      } else {
        // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.strcpy)
        strcpy(lcov_path, g_coverage_output);
        // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.strcpy)
        strcat(lcov_path, ".info");
      }
      valk_coverage_report_lcov(lcov_path);
      free(lcov_path);
    }
  }
}

valk_line_coverage_t g_line_coverage = {0};
static bool g_line_coverage_initialized = false;

static void ensure_line_coverage_init(void) {
  if (!g_line_coverage_initialized) {
    valk_mutex_init(&g_line_coverage.lock);
    g_line_coverage_initialized = true;
  }
}

void valk_line_coverage_init(void) {
  ensure_line_coverage_init();
  valk_mutex_lock(&g_line_coverage.lock);
  for (int i = 0; i < COVERAGE_HASH_SIZE; i++) {
    g_line_coverage.buckets[i] = nullptr;
  }
  g_line_coverage.total_files = 0;
  valk_mutex_unlock(&g_line_coverage.lock);
}

valk_line_coverage_file_t *valk_coverage_get_file(u16 file_id) {
  for (int i = 0; i < COVERAGE_HASH_SIZE; i++) {
    valk_line_coverage_file_t *fc = g_line_coverage.buckets[i];
    while (fc != nullptr) {
      if (fc->file_id == file_id) return fc;
      fc = fc->next;
    }
  }
  return nullptr;
}

static valk_line_coverage_file_t *get_or_create_file(u16 file_id) {
  valk_line_coverage_file_t *fc = valk_coverage_get_file(file_id);
  if (fc == nullptr) {
    fc = malloc(sizeof(valk_line_coverage_file_t));
    if (fc == nullptr) {
      return nullptr;
    }
    
    const char *filename = valk_source_get_filename(file_id);
    fc->filename = filename ? strdup(filename) : strdup("<unknown>");
    fc->file_id = file_id;
    fc->line_counts = nullptr;
    fc->line_capacity = 0;
    fc->lines_hit = 0;
    fc->branches = nullptr;
    fc->branches_found = 0;
    fc->branches_hit = 0;
    fc->expr_buckets = calloc(EXPR_HASH_SIZE, sizeof(valk_expr_t *));
    fc->exprs_found = 0;
    fc->exprs_hit = 0;
    
    fc->next = g_line_coverage.buckets[0];
    g_line_coverage.buckets[0] = fc;
    g_line_coverage.total_files++;
  }
  return fc;
}

static void ensure_line_capacity(valk_line_coverage_file_t *fc, u16 line) {
  if (line >= fc->line_capacity) {
    u64 new_cap = (line + 1) * 2;
    if (new_cap < 64) new_cap = 64;
    u64 old_cap = fc->line_capacity;
    fc->line_counts = realloc(fc->line_counts, new_cap * sizeof(u32));
    for (u64 i = old_cap; i < new_cap; i++) {
      fc->line_counts[i] = UINT32_MAX;
    }
    fc->line_capacity = new_cap;
  }
}

void valk_coverage_mark_line(u16 file_id, u16 line) {
  if (file_id == 0 || line == 0) return;
  ensure_line_coverage_init();
  
  valk_mutex_lock(&g_line_coverage.lock);
  
  valk_line_coverage_file_t *fc = get_or_create_file(file_id);
  if (fc == nullptr) {
    valk_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  
  ensure_line_capacity(fc, line);
  if (fc->line_counts[line] == UINT32_MAX) {
    fc->line_counts[line] = 0;
  }
  
  valk_mutex_unlock(&g_line_coverage.lock);
}

void valk_coverage_record_line(u16 file_id, u16 line) {
  if (file_id == 0 || line == 0) return;
  ensure_line_coverage_init();
  
  valk_mutex_lock(&g_line_coverage.lock);
  
  valk_line_coverage_file_t *fc = get_or_create_file(file_id);
  if (fc == nullptr) {
    valk_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  
  ensure_line_capacity(fc, line);
  
  if (fc->line_counts[line] == 0) {
    fc->lines_hit++;
  }
  fc->line_counts[line]++;
  
  valk_mutex_unlock(&g_line_coverage.lock);
}

static u32 expr_hash(u16 line, u16 column) {
  u32 h = ((u32)line << 16) | column;
  h ^= h >> 16;
  h *= 0x85ebca6b;
  h ^= h >> 13;
  return h % EXPR_HASH_SIZE;
}

void valk_coverage_mark_expr(u16 file_id, u16 line, u16 column, u16 end_column) {
  if (file_id == 0 || line == 0) return;
  ensure_line_coverage_init();
  
  valk_mutex_lock(&g_line_coverage.lock);
  
  valk_line_coverage_file_t *fc = get_or_create_file(file_id);
  if (fc == nullptr || fc->expr_buckets == nullptr) {
    valk_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  
  ensure_line_capacity(fc, line);
  if (fc->line_counts[line] == UINT32_MAX) {
    fc->line_counts[line] = 0;
  }
  
  u32 bucket = expr_hash(line, column);
  valk_expr_t *expr = fc->expr_buckets[bucket];
  while (expr != nullptr) {
    if (expr->line == line && expr->column == column) {
      valk_mutex_unlock(&g_line_coverage.lock);
      return;
    }
    expr = expr->next;
  }
  
  expr = malloc(sizeof(valk_expr_t));
  if (expr == nullptr) {
    valk_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  expr->file_id = file_id;
  expr->line = line;
  expr->column = column;
  expr->end_column = end_column;
  expr->hit_count = 0;
  expr->next = fc->expr_buckets[bucket];
  fc->expr_buckets[bucket] = expr;
  fc->exprs_found++;
  
  valk_mutex_unlock(&g_line_coverage.lock);
}

void valk_coverage_record_expr(u16 file_id, u16 line, u16 column) {
  if (file_id == 0 || line == 0) return;
  ensure_line_coverage_init();
  
  valk_mutex_lock(&g_line_coverage.lock);
  
  valk_line_coverage_file_t *fc = get_or_create_file(file_id);
  if (fc == nullptr || fc->expr_buckets == nullptr) {
    valk_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  
  ensure_line_capacity(fc, line);
  
  u32 bucket = expr_hash(line, column);
  valk_expr_t *expr = fc->expr_buckets[bucket];
  while (expr != nullptr) {
    if (expr->line == line && expr->column == column) {
      if (expr->hit_count == 0) {
        fc->exprs_hit++;
        if (fc->line_counts[line] == 0) {
          fc->lines_hit++;
        }
      }
      expr->hit_count++;
      fc->line_counts[line]++;
      valk_mutex_unlock(&g_line_coverage.lock);
      return;
    }
    expr = expr->next;
  }
  
  expr = malloc(sizeof(valk_expr_t));
  if (expr == nullptr) {
    valk_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  expr->file_id = file_id;
  expr->line = line;
  expr->column = column;
  expr->end_column = 0;
  expr->hit_count = 1;
  expr->next = fc->expr_buckets[bucket];
  fc->expr_buckets[bucket] = expr;
  fc->exprs_found++;
  fc->exprs_hit++;
  
  if (fc->line_counts[line] == 0) {
    fc->lines_hit++;
  }
  fc->line_counts[line]++;
  
  valk_mutex_unlock(&g_line_coverage.lock);
}

u64 valk_coverage_get_line_expr_count(u16 file_id, u16 line, u64 *hit, u64 *total) {
  if (file_id == 0 || line == 0) {
    if (hit) *hit = 0;
    if (total) *total = 0;
    return 0;
  }
  ensure_line_coverage_init();
  
  valk_mutex_lock(&g_line_coverage.lock);
  
  valk_line_coverage_file_t *fc = valk_coverage_get_file(file_id);
  if (fc == nullptr || fc->expr_buckets == nullptr) {
    valk_mutex_unlock(&g_line_coverage.lock);
    if (hit) *hit = 0;
    if (total) *total = 0;
    return 0;
  }
  
  u64 expr_hit = 0;
  u64 expr_total = 0;
  for (u32 i = 0; i < EXPR_HASH_SIZE; i++) {
    valk_expr_t *expr = fc->expr_buckets[i];
    while (expr != nullptr) {
      if (expr->line == line) {
        expr_total++;
        if (expr->hit_count > 0) expr_hit++;
      }
      expr = expr->next;
    }
  }
  
  valk_mutex_unlock(&g_line_coverage.lock);
  
  if (hit) *hit = expr_hit;
  if (total) *total = expr_total;
  return expr_total;
}

void valk_coverage_record_branch(u16 file_id, u16 line, bool taken) {
  if (file_id == 0 || line == 0) return;
  ensure_line_coverage_init();
  
  valk_mutex_lock(&g_line_coverage.lock);
  
  valk_line_coverage_file_t *fc = get_or_create_file(file_id);
  if (fc == nullptr) {
    valk_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  
  valk_branch_t *br = fc->branches;
  while (br != nullptr) {
    if (br->line == line) {
      if (taken) {
        if (br->true_count == 0) fc->branches_hit++;
        br->true_count++;
      } else {
        if (br->false_count == 0) fc->branches_hit++;
        br->false_count++;
      }
      valk_mutex_unlock(&g_line_coverage.lock);
      return;
    }
    br = br->next;
  }
  
  br = malloc(sizeof(valk_branch_t));
  if (br == nullptr) {
    valk_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  br->line = line;
  br->true_count = taken ? 1 : 0;
  br->false_count = taken ? 0 : 1;
  br->next = fc->branches;
  fc->branches = br;
  fc->branches_found += 2;
  fc->branches_hit++;
  
  valk_mutex_unlock(&g_line_coverage.lock);
}

void valk_line_coverage_reset(void) {
  ensure_line_coverage_init();
  valk_mutex_lock(&g_line_coverage.lock);
  
  for (int i = 0; i < COVERAGE_HASH_SIZE; i++) {
    valk_line_coverage_file_t *fc = g_line_coverage.buckets[i];
    while (fc != nullptr) {
      valk_line_coverage_file_t *next = fc->next;
      free(fc->filename);
      free(fc->line_counts);
      valk_branch_t *br = fc->branches;
      while (br != nullptr) {
        valk_branch_t *br_next = br->next;
        free(br);
        br = br_next;
      }
      if (fc->expr_buckets != nullptr) {
        for (u32 j = 0; j < EXPR_HASH_SIZE; j++) {
          valk_expr_t *expr = fc->expr_buckets[j];
          while (expr != nullptr) {
            valk_expr_t *expr_next = expr->next;
            free(expr);
            expr = expr_next;
          }
        }
        free(fc->expr_buckets);
      }
      free(fc);
      fc = next;
    }
    g_line_coverage.buckets[i] = nullptr;
  }
  g_line_coverage.total_files = 0;
  
  valk_mutex_unlock(&g_line_coverage.lock);
}

#else // !VALK_COVERAGE

void valk_coverage_init(void) {}
bool valk_coverage_enabled(void) { return false; }
const char *valk_coverage_output_path(void) { return nullptr; }
void valk_coverage_record_file(const char *filename) { (void)filename; }
void valk_coverage_report(const char *output_file) { (void)output_file; }
void valk_coverage_report_lcov(const char *output_file) { (void)output_file; }
void valk_coverage_reset(void) {}
void valk_coverage_save_on_exit(void) {}

#endif // VALK_COVERAGE
