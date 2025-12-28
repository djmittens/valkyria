#include "aio_internal.h"

#ifdef VALK_METRICS_ENABLED

u16 valk_owner_register(valk_aio_system_t *sys, const char *name, u8 type, void *ptr) {
  if (!sys || sys->owner_registry.count >= VALK_MAX_OWNERS) {
    return UINT16_MAX;
  }

  u16 idx = sys->owner_registry.count++;
  valk_owner_entry_t *entry = &sys->owner_registry.entries[idx];

  strncpy(entry->name, name, sizeof(entry->name) - 1);
  entry->name[sizeof(entry->name) - 1] = '\0';
  entry->type = type;
  entry->ptr = ptr;

  return idx;
}

const char* valk_owner_get_name(valk_aio_system_t *sys, u16 idx) {
  if (!sys || idx >= sys->owner_registry.count) {
    return NULL;
  }
  return sys->owner_registry.entries[idx].name;
}

u64 valk_owner_get_count(valk_aio_system_t *sys) {
  if (!sys) return 0;
  return sys->owner_registry.count;
}

#endif
