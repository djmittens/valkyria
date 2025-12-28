#pragma once

#include <stddef.h>
#include <stdbool.h>
#include "aio_types.h"
#include "aio.h"
#include "memory.h"

#ifdef VALK_METRICS_ENABLED
valk_slab_t* valk_aio_get_tcp_buffer_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_handle_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_stream_arenas_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_http_servers_slab(valk_aio_system_t* sys);
valk_slab_t* valk_aio_get_http_clients_slab(valk_aio_system_t* sys);
bool valk_aio_get_handle_diag(valk_aio_system_t* sys, u64 slot_idx,
                               valk_handle_diag_t* out_diag);
valk_diag_handle_kind_e valk_aio_get_handle_kind(valk_aio_system_t* sys, u64 slot_idx);
#endif
