#pragma once

#include <stdarg.h>

typedef enum {
  VALK_LOG_ERROR = 0,
  VALK_LOG_WARN = 1,
  VALK_LOG_INFO = 2,
  VALK_LOG_DEBUG = 3,
  VALK_LOG_TRACE = 4,
} valk_log_level_e;

// Initialize logging from env (VALK_LOG), e.g., "error|warn|info|debug|trace".
void valk_log_init(void);

// Set/Get current runtime log level
void valk_log_set_level(valk_log_level_e lvl);
valk_log_level_e valk_log_get_level(void);

// Parse log level from string (returns VALK_LOG_WARN for NULL or invalid)
valk_log_level_e valk_log_level_from_string(const char *s);

// True if a message at `lvl` would be emitted
int valk_log_would_log(valk_log_level_e lvl);

// Core logging function
void valk_log(valk_log_level_e lvl, const char *file, int line,
              const char *func, const char *fmt, ...);

#define VALK_LOG(_lvl, _fmt, ...) \
  valk_log((_lvl), __FILE_NAME__, __LINE__, __func__, (_fmt), ##__VA_ARGS__)

#define VALK_ERROR(_fmt, ...) VALK_LOG(VALK_LOG_ERROR, (_fmt), ##__VA_ARGS__)
#define VALK_WARN(_fmt, ...)  VALK_LOG(VALK_LOG_WARN,  (_fmt), ##__VA_ARGS__)
#define VALK_INFO(_fmt, ...)  VALK_LOG(VALK_LOG_INFO,  (_fmt), ##__VA_ARGS__)
#define VALK_DEBUG(_fmt, ...) VALK_LOG(VALK_LOG_DEBUG, (_fmt), ##__VA_ARGS__)
#define VALK_TRACE(_fmt, ...) VALK_LOG(VALK_LOG_TRACE, (_fmt), ##__VA_ARGS__)

