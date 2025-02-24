#include "inet.h"

#include "common.h"
#include "collections.h"

//  Network shit
//  Mostly for linux
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netdb.h>
#include <netinet/in.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <sys/types.h>

// Http n shit
#include <openssl/ssl.h>
#include <openssl/err.h>
#include <nghttp2/nghttp2.h>

// std shit
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>



// get sockaddr, IPv4 or IPv6:
void *get_in_addr(struct sockaddr *sa) {
  if (sa->sa_family == AF_INET) {
    return &(((struct sockaddr_in *)sa)->sin_addr);
  }

  return &(((struct sockaddr_in6 *)sa)->sin6_addr);
}
 
static int alpn_select_proto_cb(SSL *ssl, const unsigned char **out,
                                unsigned char *outlen, const unsigned char *in,
                                unsigned int inlen, void *arg) {
  UNUSED(ssl);
  UNUSED(arg);

  int rv;

  rv = nghttp2_select_alpn(out, outlen, in, inlen);

  if (rv != 1) {
    return SSL_TLSEXT_ERR_NOACK;
  }

  return SSL_TLSEXT_ERR_OK;
}



void valk_server_demo(void) {
  int status, sockfd, connfd, epollfd;
  struct addrinfo hints = {};
  struct addrinfo *servinfo; // result
  struct sockaddr_storage theirAddr;
  struct epoll_event ev, events[10];

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
  fcntl(sockfd, F_SETFL, O_NONBLOCK);
  // This binds the socket descriptor to an actual port on the OS level
  // Sometimes the port is already used, you can steal it... There is a command
  // for that something like
  //
  // lose the pesky "Address already in use" error message
  int yes = 1;
  // char yes='1'; // Solaris people use this
  if (setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof yes) == -1) {
    perror("setsockopt\n");
    close(sockfd);
    return;
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

  printf("Server: Created a socket... Waiting for client\n");

  epollfd = epoll_create1(0);

  if (epollfd == -1) {
    perror("epoll_create1");
    // exit(EXIT_FAILURE);
    close(sockfd);
    return;
  }

  ev.events = EPOLLIN;
  ev.data.fd = sockfd;

  if (epoll_ctl(epollfd, EPOLL_CTL_ADD, sockfd, &ev) == -1) {
    perror("epoll_ctl: sockfd");
    close(sockfd);
    return;
  }

  for (;;) {
    int num_fds = epoll_wait(epollfd, events, 10, -1);
    if (epollfd == -1) {
      perror("epoll_wait");
      // exit(EXIT_FAILURE);
      close(sockfd);
      close(epollfd);
      return;
    }
    for (int n = 0; n < num_fds; ++n) {
      if (events[n].data.fd == sockfd) {
        socklen_t addrSize = sizeof(theirAddr);
        if ((connfd = accept(sockfd, (struct sockaddr *)&theirAddr,
                             &addrSize)) == -1) {
          fprintf(stderr, "accept() error: %s \n", strerror(errno));
          close(sockfd);
          return;
        }
        char buf[addrSize];
        // This is convoluded as heck.
        // Essentially whats happening is, theirAddr is a storage container
        // which can hold the maximimum length of any address,  so now we need
        // to cast it to the appropriate socket type to get the internal address
        // of the right size, to be used with this function.
        // .... this is painful
        inet_ntop(theirAddr.ss_family,
                  get_in_addr((struct sockaddr *)&theirAddr), buf, sizeof(buf));
        printf("Server: Established connection with client: %s\n", buf);

        // lets reuse the ev
        memset(&ev, 0, sizeof(struct epoll_event));
        ev.events = EPOLLOUT | EPOLLIN;
        ev.data.fd = connfd;
        epoll_ctl(epollfd, EPOLL_CTL_ADD, connfd, &ev);

      } else {
        char res[512];
        printf("Server: Received from client \n %s \n", res);
        int numRead = read(events[n].data.fd, res, sizeof(res));
        res[numRead] = '\0';
        printf("Server: Received from client \n %s \n", res);
        const char *request = "Hello World";
        if (write(connfd, request, strlen(request)) == -1) {
          fprintf(stderr, "write() error: %s \n", strerror(errno));
          close(connfd);
          close(sockfd);
          return;
        }
      }
    }
  }

  close(connfd);
  close(sockfd);
  close(epollfd);
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

  if ((status = getaddrinfo(domain, port, &hints, &servinfo)) != 0) {
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
    usleep(100);
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
