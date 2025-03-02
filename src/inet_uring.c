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

typedef struct {
  off_t size;
  valk_promise *promise;
  char *content;
} valk_file;

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
    printf("%s", (char*)res->succ);
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

valk_future *valk_read_file(const char *filename) {
  valk_future *res = valk_future_done(valk_arc_box_suc(NULL, __no_free));
  int fd = open(filename, O_RDONLY);
  if (fd < 0) {
    perror("open");
    return res;
  }

  struct io_uring ring;
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);

  off_t size = get_file_size(fd);
  printf("Filesize of, %s is %lu\n", filename, size);

  int blocks = (int)size / BLOCK_SZ;
  if (size % BLOCK_SZ)
    blocks++;

  // read command
  file_info *fi = malloc(sizeof(*fi) + (sizeof(struct iovec) * blocks));

  for (int i = 0; i < blocks; i++) {
    const int isLastBlock = i == (blocks - 1);
    const int remainder = size % BLOCK_SZ;

    fi->iovecs[i].iov_len = (isLastBlock) ? remainder : BLOCK_SZ;

    if (posix_memalign(&fi->iovecs[i].iov_base, BLOCK_SZ, BLOCK_SZ)) {
      perror("posix_memalign");
      return res;
    }
  }
  fi->file_sz = size;

  struct io_uring_sqe *sqe = io_uring_get_sqe(&ring);
  io_uring_prep_readv(sqe, fd, fi->iovecs, blocks, 0);
  io_uring_sqe_set_data(sqe, fi);
  io_uring_submit(&ring);

  // wait for response i guess ?

  struct io_uring_cqe *cqe;
  int ret = io_uring_wait_cqe(&ring, &cqe);
  if (ret < 0) {
    perror("io_uring_wait_cqe");
  }

  if (cqe->res < 0) {
    fprintf(stderr, "Async readv failed\n");
    return res;
  }

  fi = io_uring_cqe_get_data(cqe);
  for (int i = 0; i < blocks; i++) {
    printf("\nSTARTING BLOCK %d\n", i);
    for (size_t k = 0; k < fi->iovecs[i].iov_len; k++) {
      char *buf = fi->iovecs[i].iov_base;
      fputc(buf[k], stdout);
    }
  }
  io_uring_cqe_seen(&ring, cqe);

  return res;
}

static void *__event_loop(void *arg) {
  valk_aio_system *sys = arg;

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

  valk_file *file = io_uring_cqe_get_data(cqe);
  valk_promise_respond(file->promise, valk_arc_box_suc(file->content, free));
  valk_promise_release(file->promise);
  free(file);

  io_uring_cqe_seen(&sys->uring, cqe);
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

  valk_file *file = malloc(sizeof(valk_file));

  file->promise = valk_promise_new(res);
  // TODO(networking): need to establish a rule that :
  // if something plans to own a reference, eg promise, it must retain
  // internally if something is planning to only forward the reference, it must
  // release a dangling one so this retain should potentially turn into a
  // release (eg noop in this case because it returns it to the caller)
  valk_arc_retain(res);
  file->size = get_file_size(fd);

  printf("Allocating buffer for file, %s is %lu\n", filename, file->size);
  file->content = malloc(file->size);

  struct io_uring_sqe *sqe = io_uring_get_sqe(&sys->uring);
  io_uring_prep_read(sqe, fd, file->content, file->size, 0);
  io_uring_sqe_set_data(sqe, file);
  io_uring_submit(&sys->uring);

  return res;
}
