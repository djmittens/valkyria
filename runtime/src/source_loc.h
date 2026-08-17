#pragma once

#if defined(VALK_COVERAGE) || defined(VALK_DEBUG_INFO)

#include "types.h"

#define MAX_SOURCE_FILES 4096

u16 valk_source_register_file(const char *filename);
const char *valk_source_get_filename(u16 file_id);
void valk_source_registry_reset(void);

#endif // VALK_COVERAGE
