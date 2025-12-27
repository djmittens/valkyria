#pragma once

#include <stdint.h>
#include <stddef.h>
#include "aio_types.h"

#ifdef VALK_METRICS_ENABLED
uint16_t valk_owner_register(valk_aio_system_t *sys, const char *name, uint8_t type, void *ptr);
const char* valk_owner_get_name(valk_aio_system_t *sys, uint16_t idx);
size_t valk_owner_get_count(valk_aio_system_t *sys);
#endif
