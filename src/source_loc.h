#pragma once

#ifdef VALK_COVERAGE

#include <stdint.h>

#define MAX_SOURCE_FILES 4096

uint16_t valk_source_register_file(const char *filename);
const char *valk_source_get_filename(uint16_t file_id);
void valk_source_registry_reset(void);

#endif // VALK_COVERAGE
