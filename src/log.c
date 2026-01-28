#include "log.h"

#include <stdio.h>
#include <stdlib.h>
#if !defined(_WIN32)
#include <strings.h>
#endif

static valk_log_level_e __valk_log_level = VALK_LOG_WARN;
static int __valk_log_inited = 0;

valk_log_level_e valk_log_level_from_string(const char *s) {
  if (!s) return VALK_LOG_WARN;
  if (strcasecmp(s, "error") == 0) return VALK_LOG_ERROR;
  if (strcasecmp(s, "warn") == 0 || strcasecmp(s, "warning") == 0) return VALK_LOG_WARN;
  if (strcasecmp(s, "info") == 0) return VALK_LOG_INFO;
  if (strcasecmp(s, "debug") == 0) return VALK_LOG_DEBUG;
  if (strcasecmp(s, "trace") == 0) return VALK_LOG_TRACE;
  return VALK_LOG_WARN;
}

void valk_log_init(void) {
  if (__valk_log_inited) return;
  const char *env = getenv("VALK_LOG");
  __valk_log_level = valk_log_level_from_string(env);
  __valk_log_inited = 1;
}

void valk_log_set_level(valk_log_level_e lvl) {
  valk_log_init();
  __valk_log_level = lvl;
}

valk_log_level_e valk_log_get_level(void) {
  valk_log_init();
  return __valk_log_level;
}

int valk_log_would_log(valk_log_level_e lvl) {
  valk_log_init();
  return lvl <= __valk_log_level;
}

static const char *lvl_name(valk_log_level_e lvl) {
  switch (lvl) {
    case VALK_LOG_ERROR: return "ERROR";
    case VALK_LOG_WARN:  return "WARN";
    case VALK_LOG_INFO:  return "INFO";
    case VALK_LOG_DEBUG: return "DEBUG";
    case VALK_LOG_TRACE: return "TRACE";
  }
  return "?";
}

void valk_log(valk_log_level_e lvl, const char *file, int line,
              const char *func, const char *fmt, ...) {
  if (!valk_log_would_log(lvl)) return;
  FILE *out = (lvl <= VALK_LOG_WARN) ? stderr : stdout;
  fprintf(out, "[%s] %s:%d:%s | ", lvl_name(lvl), file, line, func);
  va_list va;
  va_start(va, fmt);
  vfprintf(out, fmt, va);
  va_end(va);  // NOLINT(clang-analyzer-valist.Uninitialized) - false positive: va_start called above
  fputc('\n', out);
}
