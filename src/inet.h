#pragma once

#include "concurrency.h"
#include <unistd.h>

// Host TO Network Short
/* void htons(void); */
/**/
/* // Host TO Network Long */
/* void htonl(void); */
/**/
/* // Network TO Host Short */
/* void ntohs(void); */
/**/
/* // Network TO Host Long */
/* void ntohl(void); */

void valk_server_demo(void);

char *valk_client_demo(const char *domain, const char *port);

typedef struct valk_aio_system valk_aio_system;

valk_aio_system *valk_aio_start(void);
void valk_aio_stop(valk_aio_system *sys);

valk_future *valk_read_file(const char *filename);
valk_future *valk_aio_read_file(valk_aio_system *sys,
                                const char *filename);
