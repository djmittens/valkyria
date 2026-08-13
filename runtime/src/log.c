#include "log.h"

#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#if !defined(_WIN32)
#include <strings.h>
#endif

// Read on every log-site check from every thread; initialized lazily from
// any thread. Atomic level + pthread_once keeps the fast path a single
// relaxed load with no data race.
static _Atomic valk_log_level_e __valk_log_level = VALK_LOG_WARN;
static pthread_once_t __valk_log_once = PTHREAD_ONCE_INIT;

valk_log_level_e valk_log_level_from_string(const char *s) {
  if (!s) return VALK_LOG_WARN;
  if (strcasecmp(s, "error") == 0) return VALK_LOG_ERROR;
  if (strcasecmp(s, "warn") == 0 || strcasecmp(s, "warning") == 0) return VALK_LOG_WARN;
  if (strcasecmp(s, "info") == 0) return VALK_LOG_INFO;
  if (strcasecmp(s, "debug") == 0) return VALK_LOG_DEBUG;
  if (strcasecmp(s, "trace") == 0) return VALK_LOG_TRACE;
  return VALK_LOG_WARN;
}

static void __valk_log_init_once(void) {
  const char *env = getenv("VALK_LOG");
  atomic_store_explicit(&__valk_log_level, valk_log_level_from_string(env),
                        memory_order_relaxed);
}

void valk_log_init(void) {
  pthread_once(&__valk_log_once, __valk_log_init_once);
}

void valk_log_set_level(valk_log_level_e lvl) {
  valk_log_init();
  atomic_store_explicit(&__valk_log_level, lvl, memory_order_relaxed);
}

valk_log_level_e valk_log_get_level(void) {
  valk_log_init();
  return atomic_load_explicit(&__valk_log_level, memory_order_relaxed);
}

int valk_log_would_log(valk_log_level_e lvl) {
  valk_log_init();
  return lvl <= atomic_load_explicit(&__valk_log_level, memory_order_relaxed);
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
