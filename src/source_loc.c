#include "source_loc.h"

#ifdef VALK_COVERAGE

#include <pthread.h>
#include <stdlib.h>
#include <string.h>

static struct {
  char *filenames[MAX_SOURCE_FILES];
  uint16_t count;
  pthread_mutex_t lock;
} source_registry = {
  .filenames = {NULL},
  .count = 0,
  .lock = PTHREAD_MUTEX_INITIALIZER
};

uint16_t valk_source_register_file(const char *filename) {
  if (!filename) return 0;

  pthread_mutex_lock(&source_registry.lock);

  for (uint16_t i = 1; i <= source_registry.count; i++) {
    if (strcmp(source_registry.filenames[i], filename) == 0) {
      pthread_mutex_unlock(&source_registry.lock);
      return i;
    }
  }

  if (source_registry.count >= MAX_SOURCE_FILES - 1) {
    pthread_mutex_unlock(&source_registry.lock);
    return 0;
  }

  source_registry.count++;
  uint16_t file_id = source_registry.count;
  source_registry.filenames[file_id] = strdup(filename);

  pthread_mutex_unlock(&source_registry.lock);
  return file_id;
}

const char *valk_source_get_filename(uint16_t file_id) {
  if (file_id == 0 || file_id > source_registry.count) return NULL;

  pthread_mutex_lock(&source_registry.lock);
  const char *filename = source_registry.filenames[file_id];
  pthread_mutex_unlock(&source_registry.lock);

  return filename;
}

void valk_source_registry_reset(void) {
  pthread_mutex_lock(&source_registry.lock);

  for (uint16_t i = 1; i <= source_registry.count; i++) {
    free(source_registry.filenames[i]);
    source_registry.filenames[i] = NULL;
  }
  source_registry.count = 0;

  pthread_mutex_unlock(&source_registry.lock);
}

#endif // VALK_COVERAGE
