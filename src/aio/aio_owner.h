#pragma once

#include <stddef.h>
#include "aio_types.h"

u16 valk_owner_register(valk_aio_system_t *sys, const char *name, u8 type, void *ptr);
const char* valk_owner_get_name(valk_aio_system_t *sys, u16 idx);
u64 valk_owner_get_count(valk_aio_system_t *sys);
