#pragma once

#include <uv.h>
#include "aio_types.h"
#include "aio_metrics.h"
#include "memory.h"
#include "gc.h"

valk_aio_system_t *valk_aio_start(void);
valk_aio_system_t *valk_aio_start_with_config(valk_aio_system_config_t *config);

void valk_aio_stop(valk_aio_system_t *sys);
bool valk_aio_is_shutting_down(valk_aio_system_t *sys);
void valk_aio_wait_for_shutdown(valk_aio_system_t *sys);

const char *valk_aio_system_config_validate(const valk_aio_system_config_t *cfg);
int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg);

uv_loop_t* valk_aio_get_event_loop(valk_aio_system_t* sys);
const char* valk_aio_get_name(valk_aio_system_t* sys);
void valk_aio_set_name(valk_aio_system_t* sys, const char* name);
void valk_aio_update_loop_metrics(valk_aio_system_t* sys);

void valk_aio_update_queue_stats(valk_aio_system_t* sys);
valk_gc_malloc_heap_t* valk_aio_get_gc_heap(valk_aio_system_t* sys);
valk_mem_arena_t* valk_aio_get_scratch_arena(valk_aio_system_t* sys);
