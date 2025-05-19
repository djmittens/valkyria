#include "concurrency.h"

#include "collections.h"
#include "common.h"
#include "memory.h"

#include <asm-generic/socket.h>
#include <fcntl.h>
#include <liburing.h>
#include <liburing/io_uring.h>
#include <linux/fs.h>
#include <netdb.h>
#include <netinet/in.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <unistd.h>

#include <nghttp2/nghttp2.h>
typedef struct {
  off_t file_sz;
  struct iovec iovecs[];
} file_info;

typedef enum {
  VALK_AIO_READ,
  VALK_AIO_WRITE,
  VALK_AIO_ACCEPT,
  VALK_AIO_HANGUP,
  VALK_AIO_POISON
} valk_aio_request_type;

// typedef void(valk_aio_request_cb)(valk_aio_system *, valk_aio_request *);

typedef struct valk_aio_request {
  valk_aio_request_type type;
  int fd; // File descriptor, socket or something
  void *userData;
  valk_callback_void *freeUd;
  valk_buffer_t buffer;
} valk_aio_request;

void valk_aio_request_free(void *arg) {
  valk_aio_request *self = arg;
  close(self->fd);
  // free(self->buffer);
  self->freeUd(self->userData);

  if (self->buffer.items) {
    valk_mem_free(self->buffer.items);
  }
  valk_mem_free(self);
}

typedef struct valk_aio_system {
  struct io_uring uring;
  valk_worker_pool pool;
  pthread_t eventloop;
} valk_aio_system;

static off_t __get_file_size(int fd) {
  struct stat st;

  if (fstat(fd, &st) < 0) {
    perror("fstat");
    return -1;
  }
  if (S_ISBLK(st.st_mode)) {
    uint64_t bytes;
    if (ioctl(fd, BLKGETSIZE64, &bytes) != 0) {
      perror("fstat");
      return -1;
    }
    return bytes;
  } else if (S_ISREG(st.st_mode)) {
    return st.st_size;
  }
  return -1;
}

static void __no_free(void *arg) { UNUSED(arg); }

const int QUEUE_DEPTH = 10;
const size_t BLOCK_SZ = 1024;

typedef struct __conn_ctx {
  int listenFd;
  int connFd;
  struct sockaddr_in addr;
  socklen_t addrlen;
  void *userData;
} __conn_ctx;

static void __accept_connection(valk_aio_system *sys, int sockFd,
                                __conn_ctx *ctx) {

  // TODO(networking): Need to put a mutex around io uring get_sqe operations
  // multiple threads could collide in between creation and submission
  struct io_uring_sqe *sqe = io_uring_get_sqe(&sys->uring);

  ctx->listenFd = sockFd;
  io_uring_prep_accept(sqe, sockFd, (struct sockaddr *)&ctx->addr,
                       &ctx->addrlen, 0);

  valk_aio_request *req = valk_mem_alloc(sizeof(*req));
  req->type = VALK_AIO_ACCEPT;
  req->userData = ctx;
  req->freeUd = __no_free; // Context must not be cleaned up, direct leak should
                           // be detected?

  io_uring_sqe_set_data(sqe, req);
  io_uring_submit(&sys->uring);
}

static int __socket_listen(const char *host, const char *port) {
  int sock;

  int status;
  struct addrinfo hints = {};
  struct addrinfo *servinfo; // result
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;

  if ((status = getaddrinfo(host, port, &hints, &servinfo)) != 0) {
    fprintf(stderr, "getaddrinfo error: %s \n", gai_strerror(status));
    return -1;
  }

  if ((sock = socket(servinfo->ai_family, servinfo->ai_socktype,
                     servinfo->ai_protocol)) == -1) {
    fprintf(stderr, "socket() error: %s \n", strerror(errno));
    return -1;
  }

  int enable = 1;

  if (setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &enable, sizeof(int))) {
    // TODO(networking): should this function perhaps return a boxed result with
    // error instead?
    close(sock);
    return -1;
  }

  // make calls non blocking?
  // fcntl(sock, F_SETFL, O_NONBLOCK);

  if (bind(sock, servinfo->ai_addr, servinfo->ai_addrlen) == -1) {
    fprintf(stderr, "bind() error: %s \n", strerror(errno));
    close(sock);
    return -1;
  }

  if (listen(sock, 15) == -1) {
    fprintf(stderr, "listen() error: %s \n", strerror(errno));
    close(sock);
    return -1;
  }
  return sock;
}

typedef struct {
  size_t numFree;
  size_t capacity;
  __conn_ctx *items;
  size_t *free;
} __connection_pool;

static void *__event_loop(void *arg) {
  valk_aio_system *sys = arg;

  // Use malloc for now
  valk_mem_init_malloc();
  __connection_pool conPool;

  do {
    (&conPool)->numFree = (5) + 1;
    (&conPool)->capacity = (5) + 1;
    if ((&conPool)->items) {
      printf("Reinitializing the pool for some stupid reason, probably a "
             "memory leak, since items are not cleaned up\n");
    }
    (&conPool)->items = valk_mem_allocator_alloc(
        valk_thread_ctx.allocator, (sizeof((&conPool)->items[0]) * ((5) + 1)));
    (&conPool)->free = valk_mem_allocator_alloc(
        valk_thread_ctx.allocator, (sizeof((&conPool)->free[0]) * ((5) + 1)));
    for (size_t i = 0; i < (&conPool)->capacity; ++i) {
      (&conPool)->free[i] = i;
    }
  } while (0);

  do {

    struct io_uring_cqe *cqe;
    int ret = io_uring_wait_cqe(&sys->uring, &cqe);
    if (ret < 0) {
      perror("io_uring_wait_cqe");
      // crash
      return NULL;
    }

    if (cqe->res < 0) {
      fprintf(stderr, "Async read failed\n");
      // crash
      return NULL;
    }

    valk_aio_request *req = io_uring_cqe_get_data(cqe);
    switch (req->type) {
    case VALK_AIO_READ:
    case VALK_AIO_WRITE: {
      // TODO(networking): So this free should be using same context as it was
      // created in
      valk_arc_box *box = valk_arc_box_suc(req->buffer.items, valk_mem_free);
      req->buffer.items = NULL;
      // TODO(networking): figure out lifetimes here, probably should release
      valk_pool_resolve_promise(&sys->pool, req->userData, box);
      valk_aio_request_free(req);
      break;
    }
    case VALK_AIO_ACCEPT: {
      __conn_ctx *ctx = req->userData;
      // store the fd in the context
      ctx->connFd = cqe->res;

      // TODO(networking): maybe replace this with a copy constructor?
      __conn_ctx *newCtx = malloc(sizeof(*newCtx));
      memset(newCtx, 0, sizeof(*newCtx));

      // schedule the next accept
      __accept_connection(sys, req->fd, newCtx);

      valk_arc_box *box = valk_arc_box_suc(ctx, free);
      // repack the box, UNSAFE !!!
      // TODO(networking): I should shallow clone  or something, but i need to
      // unwrap the request inline

      free(req); // want to free the request, but leave the UD out.. eg unwrap,
                 // i should encapsulate this somehow

      // trampoline the request
      // TODO(networking): need to strip off internal datastructures before
      // trampolinning perhaps ?
      // valk_future *fut = valk_schedule(&sys->pool, box, ctx->onAccept);
      // valk_future_release(fut); // toss the result

      break;
    }
    case VALK_AIO_HANGUP:
      break;
    case VALK_AIO_POISON:
      printf("Arggh AIO is poisoned 💀\n");
      return NULL;
    }

    io_uring_cqe_seen(&sys->uring, cqe);
  } while (1);
  return NULL;
}

valk_aio_system *valk_aio_start(void) {
  valk_aio_system *sys = malloc(sizeof(valk_aio_system));
  if (valk_start_pool(&sys->pool)) {
    fprintf(stderr, "ERROR: could not initialize AIO worker pool\n");
    return NULL;
  }
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  // we keep it attached, that way we know things are finished
  // pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);

  // init uring
  io_uring_queue_init(QUEUE_DEPTH, &sys->uring, 0);

  int res = pthread_create(&sys->eventloop, &attr, __event_loop, sys);
  if (res) {
    perror("pthread_create");
    valk_free_pool(&sys->pool);
    return NULL;
  }

  return sys;
}

void valk_aio_stop(valk_aio_system *sys) {
  valk_free_pool(&sys->pool);
  // Triggers the event loop to wake from io
  struct io_uring_sqe *sqe = io_uring_get_sqe(&sys->uring);
  io_uring_prep_nop(sqe);
  valk_aio_request req;
  req.type = VALK_AIO_POISON;
  io_uring_sqe_set_data(sqe, &req);
  io_uring_submit(&sys->uring);
  // Wait for it to exit
  void *ret;
  pthread_join(sys->eventloop, &ret);
  io_uring_queue_exit(&sys->uring);
  free(sys);
}

valk_future *valk_aio_read_file(valk_aio_system *sys, const char *filename) {

  int fd = open(filename, O_RDONLY);
  if (fd < 0) {
    perror("open");
    return valk_future_done(valk_arc_box_err(1, "Open had an oopsie"));
  }

  valk_future *res = valk_future_new();
  // TODO(networking): need to establish a rule that :
  // if something plans to own a reference, eg promise, it must retain
  // internally if something is planning to only forward the reference, it must
  // release a dangling one so this retain should potentially turn into a
  // release (eg noop in this case because it returns it to the caller)
  valk_arc_retain(res);

  // TODO(networking): this is not freed yet
  valk_aio_request *req = valk_mem_alloc(sizeof(valk_aio_request));

  req->type = VALK_AIO_READ;
  req->userData = valk_promise_new(res);
  req->freeUd = (valk_callback_void *)valk_promise_release;

  valk_alloc_buffer(&req->buffer, __get_file_size(fd));

  printf("Allocated buffer for file, %s is %lu\n", filename,
         req->buffer.capacity);

  struct io_uring_sqe *sqe = io_uring_get_sqe(&sys->uring);
  io_uring_prep_read(sqe, fd, req->buffer.items, req->buffer.capacity, 0);
  io_uring_sqe_set_data(sqe, req);
  io_uring_submit(&sys->uring);

  return res;
}

void valk_server_demo(void) {
  valk_aio_system *aio = valk_aio_start();
  int sfd = __socket_listen("", "6969");

  nghttp2_session_del *session_data;

  __conn_ctx *ctx = valk_mem_alloc(sizeof(__conn_ctx));
  __accept_connection(aio, sfd, ctx);
  valk_aio_stop(aio);
}

char *valk_client_demo(const char *domain, const char *port) {
  // valk_read_file("Makefile");

  valk_aio_system *aio = valk_aio_start();
  valk_future *fres = valk_aio_read_file(aio, "Makefile");
  valk_arc_box *res = valk_future_await_timeout(fres, 5000); // wait for 5 secs

  if (res->type == VALK_ERR) {
    fprintf(stderr, "Got an error back: %s\n", res->err.msg);

  } else {
    // valk_aio_request *req = res->succ;
    printf("%s", (char *)res->succ);
  }

  valk_arc_box_release(res);
  valk_aio_stop(aio);
  return strdup("");
}
