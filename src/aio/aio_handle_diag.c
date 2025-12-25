#include "aio_internal.h"

#ifdef VALK_METRICS_ENABLED

valk_slab_t* valk_aio_get_tcp_buffer_slab(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return sys->tcpBufferSlab;
}

valk_slab_t* valk_aio_get_handle_slab(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return sys->handleSlab;
}

valk_slab_t* valk_aio_get_stream_arenas_slab(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return sys->httpStreamArenas;
}

valk_slab_t* valk_aio_get_http_servers_slab(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return sys->httpServers;
}

valk_slab_t* valk_aio_get_http_clients_slab(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return sys->httpClients;
}

bool valk_aio_get_handle_diag(valk_aio_system_t* sys, size_t slot_idx,
                               valk_handle_diag_t* out_diag) {
  if (!sys || !out_diag) return false;

  valk_slab_t *slab = sys->handleSlab;
  if (!slab || slot_idx >= slab->numItems) return false;

  size_t stride = valk_slab_item_stride(slab->itemSize);
  valk_slab_item_t *item = (valk_slab_item_t *)&slab->heap[stride * slot_idx];
  valk_aio_handle_t *handle = (valk_aio_handle_t *)item->data;

  if (handle->kind != VALK_HNDL_HTTP_CONN) {
    return false;
  }

  *out_diag = handle->http.diag;
  return true;
}

valk_diag_handle_kind_e valk_aio_get_handle_kind(valk_aio_system_t* sys, size_t slot_idx) {
  if (!sys) return VALK_DIAG_HNDL_EMPTY;

  valk_slab_t *slab = sys->handleSlab;
  if (!slab || slot_idx >= slab->numItems) return VALK_DIAG_HNDL_EMPTY;

  size_t stride = valk_slab_item_stride(slab->itemSize);
  valk_slab_item_t *item = (valk_slab_item_t *)&slab->heap[stride * slot_idx];
  valk_aio_handle_t *handle = (valk_aio_handle_t *)item->data;

  switch (handle->kind) {
    case VALK_HNDL_EMPTY:     return VALK_DIAG_HNDL_EMPTY;
    case VALK_HNDL_TCP:       return VALK_DIAG_HNDL_TCP;
    case VALK_HNDL_TASK:      return VALK_DIAG_HNDL_TASK;
    case VALK_HNDL_TIMER:     return VALK_DIAG_HNDL_TIMER;
    case VALK_HNDL_HTTP_CONN: return VALK_DIAG_HNDL_HTTP_CONN;
    default:                  return VALK_DIAG_HNDL_EMPTY;
  }
}

#endif
