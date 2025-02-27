#include "concurrency.h"
#include "inet.h"

#include "common.h"

#include <liburing.h>
#include <linux/fs.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>

void valk_server_demo(void) {}

char *valk_client_demo(const char *domain, const char *port) {
  valk_read_file("Makefile");

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

valk_future *valk_read_file(const char *filename) {
  valk_future *res = valk_future_done(valk_arc_box_suc(NULL, __no_free));
  int fd = open(filename, O_RDONLY);
  if(fd < 0) {
    perror("open");
    return res;
  }
  off_t size = get_file_size(fd);
  printf("Filesize of, %s is %lu\n", filename, size);
  return res;
}
