#include "coverage.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static valk_coverage_data_t g_coverage = {nullptr, 0, 0};
static bool g_coverage_enabled = false;

void valk_coverage_init(void) {
  const char *env = getenv("VALK_COVERAGE");
  g_coverage_enabled = (env != nullptr && strcmp(env, "1") == 0);
  if (g_coverage_enabled) {
    g_coverage.capacity = 256;
    g_coverage.files = calloc(g_coverage.capacity, sizeof(valk_coverage_file_t));
    g_coverage.count = 0;
  }
}

bool valk_coverage_enabled(void) {
  return g_coverage_enabled;
}

void valk_coverage_record_file(const char *filename) {
  if (!g_coverage_enabled) return;
  
  for (size_t i = 0; i < g_coverage.count; i++) {
    if (strcmp(g_coverage.files[i].filename, filename) == 0) {
      g_coverage.files[i].eval_count++;
      return;
    }
  }
  
  if (g_coverage.count >= g_coverage.capacity) {
    g_coverage.capacity *= 2;
    g_coverage.files = realloc(g_coverage.files,
                               g_coverage.capacity * sizeof(valk_coverage_file_t));
  }
  
  g_coverage.files[g_coverage.count].filename = strdup(filename);
  g_coverage.files[g_coverage.count].eval_count = 1;
  g_coverage.count++;
}

static int compare_coverage_files(const void *a, const void *b) {
  const valk_coverage_file_t *fa = a;
  const valk_coverage_file_t *fb = b;
  return strcmp(fa->filename, fb->filename);
}

void valk_coverage_report(const char *output_file) {
  if (!g_coverage_enabled || g_coverage.count == 0) return;
  
  qsort(g_coverage.files, g_coverage.count, sizeof(valk_coverage_file_t),
        compare_coverage_files);
  
  FILE *f = fopen(output_file, "a");
  if (!f) {
    fprintf(stderr, "Failed to open coverage file: %s\n", output_file);
    return;
  }
  
  for (size_t i = 0; i < g_coverage.count; i++) {
    fprintf(f, "%s:%zu\n",
            g_coverage.files[i].filename,
            g_coverage.files[i].eval_count);
  }
  
  fclose(f);
}

void valk_coverage_reset(void) {
  if (!g_coverage_enabled) return;
  
  for (size_t i = 0; i < g_coverage.count; i++) {
    free((char*)g_coverage.files[i].filename);
  }
  free(g_coverage.files);
  g_coverage.files = nullptr;
  g_coverage.count = 0;
  g_coverage.capacity = 0;
}

void valk_coverage_save_on_exit(void) {
  if (g_coverage_enabled && g_coverage.count > 0) {
    valk_coverage_report("build-coverage/coverage-valk.txt");
  }
}
