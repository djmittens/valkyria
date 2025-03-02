#include "concurrency.h"
#include "inet.h"

#include "common.h"

#include <fcntl.h>
#include <liburing.h>
#include <linux/fs.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>

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

typedef struct valk_aio_request valk_aio_request;

// typedef void(valk_aio_request_cb)(valk_aio_system *, valk_aio_request *);

struct valk_aio_request {
  valk_aio_request_type type;
  int fd; // File descriptor, socket or something
  off_t size;
  void *buffer;
  void *userData;
  valk_callback_void *freeUd;
};

void valk_aio_request_free(void *arg) {
  valk_aio_request *self = arg;
  close(self->fd);
  // free(self->buffer);
  self->freeUd(self->userData);
  free(self);
}

struct valk_aio_system {
  struct io_uring uring;
  valk_worker_pool pool;
  pthread_t eventloop;
};

void valk_server_demo(void) {}

char *valk_client_demo(const char *domain, const char *port) {
  // valk_read_file("Makefile");

  valk_aio_system *aio = valk_aio_start();
  valk_future *fres = valk_aio_read_file(aio, "Makefile");
  valk_arc_box *res = valk_future_await_timeout(fres, 5000); // wait for 5 secs

  if (res->type == VALK_ERR) {
    fprintf(stderr, "Got an error back: %s\n", res->err.msg);
  } else {
    valk_aio_request *req = res->succ;
    printf("%s", (char *)req->buffer);
  }

  valk_arc_box_release(res);
  valk_aio_stop(aio);
  return strdup("");
}

static off_t get_file_size(int fd) {
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

static void *__event_loop(void *arg) {
  valk_aio_system *sys = arg;

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

    io_uring_cqe_get_data(cqe);

    valk_arc_box *box = io_uring_cqe_get_data(cqe);
    // TODO(networking): assert its a success
    valk_aio_request *req = box->succ;
    switch (req->type) {
    case VALK_AIO_READ:
    case VALK_AIO_WRITE:
      valk_pool_resolve_promise(&sys->pool, req->userData, box);
      break;
    case VALK_AIO_ACCEPT:
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
  io_uring_sqe_set_data(sqe, valk_arc_box_suc(&req, __no_free));
  io_uring_submit(&sys->uring);
  // Wait for it to exit
  void *ret;
  pthread_join(sys->eventloop, &ret);
  io_uring_queue_exit(&sys->uring);
  free(sys);
}

valk_future *valk_aio_read_file(valk_aio_system *sys, const char *filename) {
  valk_future *res = valk_future_new();

  int fd = open(filename, O_RDONLY);
  if (fd < 0) {
    perror("open");
    return valk_future_done(valk_arc_box_err(1, "Open had an oopsie"));
  }

  valk_aio_request *req = malloc(sizeof(valk_aio_request));

  req->type = VALK_AIO_READ;
  req->userData = valk_promise_new(res);
  req->freeUd = (valk_callback_void *)valk_promise_release;

  // TODO(networking): need to establish a rule that :
  // if something plans to own a reference, eg promise, it must retain
  // internally if something is planning to only forward the reference, it must
  // release a dangling one so this retain should potentially turn into a
  // release (eg noop in this case because it returns it to the caller)
  valk_arc_retain(res);
  req->size = get_file_size(fd);

  printf("Allocating buffer for file, %s is %lu\n", filename, req->size);
  req->buffer = malloc(req->size);

  struct io_uring_sqe *sqe = io_uring_get_sqe(&sys->uring);
  io_uring_prep_read(sqe, fd, req->buffer, req->size, 0);
  io_uring_sqe_set_data(sqe, valk_arc_box_suc(req, valk_aio_request_free));
  io_uring_submit(&sys->uring);

  return res;
}
