#pragma once

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

char* valk_client_demo(const char *domain, const char *port);

void valk_addr_demo(const char* domain);
