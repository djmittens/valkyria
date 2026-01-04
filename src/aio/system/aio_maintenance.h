#ifndef VALK_AIO_MAINTENANCE_H
#define VALK_AIO_MAINTENANCE_H

#include "types.h"

typedef struct valk_aio_system valk_aio_system_t;
typedef struct valk_aio_handle_t valk_aio_handle_t;

void valk_maintenance_timer_init(valk_aio_system_t *sys);
void valk_maintenance_timer_start(valk_aio_system_t *sys);
void valk_maintenance_timer_stop(valk_aio_system_t *sys);
void valk_maintenance_timer_close(valk_aio_system_t *sys);

void valk_maintenance_check_connection_timeouts(valk_aio_system_t *sys, u64 now);
void valk_maintenance_check_backpressure_timeouts(valk_aio_system_t *sys, u64 now);

#endif // VALK_AIO_MAINTENANCE_H
