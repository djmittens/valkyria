#include "source_loc.h"

#ifdef VALK_COVERAGE

#include "valk_thread.h"
#include <stdlib.h>
#include <string.h>

static struct {
  char *filenames[MAX_SOURCE_FILES];
  u16 count;
  valk_mutex_t lock;
} source_registry = {0};

static bool source_registry_initialized = false;

static void ensure_source_registry_init(void) {
  if (!source_registry_initialized) {
    valk_mutex_init(&source_registry.lock);
    source_registry_initialized = true;
  }
}

u16 valk_source_register_file(const char *filename) {
  if (!filename) return 0;
  ensure_source_registry_init();

  valk_mutex_lock(&source_registry.lock);

  for (u16 i = 1; i <= source_registry.count; i++) {
    if (strcmp(source_registry.filenames[i], filename) == 0) {
      valk_mutex_unlock(&source_registry.lock);
      return i;
    }
  }

  if (source_registry.count >= MAX_SOURCE_FILES - 1) {
    valk_mutex_unlock(&source_registry.lock);
    return 0;
  }

  source_registry.count++;
  u16 file_id = source_registry.count;
  source_registry.filenames[file_id] = strdup(filename);

  valk_mutex_unlock(&source_registry.lock);
  return file_id;
}

const char *valk_source_get_filename(u16 file_id) {
  if (file_id == 0 || file_id > source_registry.count) return NULL;
  ensure_source_registry_init();

  valk_mutex_lock(&source_registry.lock);
  const char *filename = source_registry.filenames[file_id];
  valk_mutex_unlock(&source_registry.lock);

  return filename;
}

void valk_source_registry_reset(void) {
  ensure_source_registry_init();
  valk_mutex_lock(&source_registry.lock);

  for (u16 i = 1; i <= source_registry.count; i++) {
    free(source_registry.filenames[i]);
    source_registry.filenames[i] = NULL;
  }
  source_registry.count = 0;

  valk_mutex_unlock(&source_registry.lock);
}

#endif // VALK_COVERAGE

typedef int source_loc_dummy_t;
