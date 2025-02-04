#include "networking.h"

//  Network shit
//  Mostly for linux
#include <arpa/inet.h>
#include <errno.h>
#include <netdb.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/types.h>

// std shit
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

void valk_server_demo(void) {
  int status, sockfd, connfd;
  struct addrinfo hints = {};
  struct addrinfo *servinfo; // result
  struct sockaddr_storage theirAddr;

  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;

  if ((status = getaddrinfo(NULL, "8080", &hints, &servinfo)) != 0) {
    fprintf(stderr, "getaddrinfo error: %s \n", gai_strerror(status));
    return;
  }

  if ((sockfd = socket(servinfo->ai_family, servinfo->ai_socktype,
                       servinfo->ai_protocol)) == -1) {
    fprintf(stderr, "socket() error: %s \n", strerror(errno));
    return;
  }

  // This binds the socket descriptor to an actual port on the OS level
  // Sometimes the port is already used, you can steal it... There is a command
  // for that something like
  //

  // lose the pesky "Address already in use" error message
  int yes = 1;
  // char yes='1'; // Solaris people use this
  if (setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof yes) == -1) {
    perror("setsockopt");
    exit(1);
  }

  if (bind(sockfd, servinfo->ai_addr, servinfo->ai_addrlen) == -1) {
    fprintf(stderr, "bind() error: %s \n", strerror(errno));
    close(sockfd);
    return;
  }

  if (listen(sockfd, 15) == -1) {
    fprintf(stderr, "listen() error: %s \n", strerror(errno));
    close(sockfd);
    return;
  }

  socklen_t addrSize = sizeof theirAddr;
  if ((connfd = accept(sockfd, (struct sockaddr *)&theirAddr, &addrSize)) ==
      -1) {
    fprintf(stderr, "accept() error: %s \n", strerror(errno));
    close(sockfd);
    return;
  }

  char res[512];
  if (recv(connfd, &res, sizeof(res), 0) == -1) {
    fprintf(stderr, "recv() error: %s \n", strerror(errno));
    close(connfd);
    close(sockfd);
    return;
  }
  printf("Server: Received from client \n %s \n", res);

  const char *request = "Hello World";
  if (send(connfd, request, strlen(request), 0) == -1) {
    fprintf(stderr, "send() error: %s \n", strerror(errno));
    close(connfd);
    close(sockfd);
    return;
  }
  close(connfd);
  close(sockfd);
  freeaddrinfo(servinfo);
}

char *valk_client_demo(const char *domain, const char *port) {
  int status, sockfd;
  struct addrinfo hints = {};
  struct addrinfo *servinfo; // result

  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  // This will cause it to bind to the ip of the host this is running on
  // Eg localhost, if you drop this it will bind to the passed in argument
  // hints.ai_flags = AI_PASSIVE;

  if (getaddrinfo(domain, port, &hints, &servinfo) != 0) {
    fprintf(stderr, "getaddrinfo() error: %s \n", gai_strerror(status));
    exit(1);
  }

  if ((sockfd = socket(servinfo->ai_family, servinfo->ai_socktype,
                       servinfo->ai_protocol)) == -1) {
    fprintf(stderr, "socket() error: %s \n", strerror(errno));
    exit(1);
  }

  // Try connecting, until  we succeed
  do {
    // Connect will call bind() underneath if its not  already bound, to find a
    // random free port to establish the connection. Meaning we get the bind
    // call for free when we call it
    if (connect(sockfd, servinfo->ai_addr, servinfo->ai_addrlen) == -1) {
      fprintf(stderr, "connect() error: %s \n", strerror(errno));
    } else {
      break;
    }
    usleep(1000);
  } while (1);

  const char *request = "GET / HTTP/1.1\r\n"
                        "Host: google.com\r\n"
                        "Connection: close\r\n"
                        "\r\n";
  if (send(sockfd, request, strlen(request), 0) == -1) {
    fprintf(stderr, "send() error: %s \n", strerror(errno));
    exit(1);
  }
  char res[512];
  recv(sockfd, &res, sizeof(res), 0);

  freeaddrinfo(servinfo);
  return strdup(res);
}

void valk_addr_demo(const char *domain) {
  int status;
  struct addrinfo hints = {};
  struct addrinfo *servinfo, *p; // result
  //
  char ipstr[INET6_ADDRSTRLEN];

  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;

  if ((status = getaddrinfo(domain, NULL, &hints, &servinfo)) != 0) {
    fprintf(stderr, "getaddrinfo error: %s \n", gai_strerror(status));
    exit(1);
  }

  printf("IP addressses for %s : \n", domain);
  for (p = servinfo; p != NULL; p = p->ai_next) {
    void *addr;
    char *ipver;

    if (p->ai_family == AF_INET) { // ipV4
      struct sockaddr_in *ipv4 = (struct sockaddr_in *)p->ai_addr;
      addr = &(ipv4->sin_addr);
      ipver = "IPv4";
    } else {
      struct sockaddr_in6 *ipv6 = (struct sockaddr_in6 *)p->ai_addr;
      addr = &(ipv6->sin6_addr);
      ipver = "IPv6";
    }

    inet_ntop(p->ai_family, addr, ipstr, sizeof ipstr);
    printf("  %s: %s\n", ipver, ipstr);
  }

  freeaddrinfo(servinfo);
}
