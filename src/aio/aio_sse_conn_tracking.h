#ifndef VALK_AIO_SSE_CONN_TRACKING_H
#define VALK_AIO_SSE_CONN_TRACKING_H

#include "aio_sse.h"

typedef struct valk_aio_handle_t valk_aio_handle_t;

void valk_sse_conn_stream_register(valk_sse_stream_t *stream);
void valk_sse_conn_stream_unregister(valk_sse_stream_t *stream);
void valk_sse_conn_close_all_streams(valk_aio_handle_t *conn);

#endif // VALK_AIO_SSE_CONN_TRACKING_H
