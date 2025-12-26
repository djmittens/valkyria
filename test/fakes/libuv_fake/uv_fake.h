#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <sys/types.h>
#include <netinet/in.h>

#define UV_RUN_DEFAULT 0
#define UV_RUN_ONCE    1
#define UV_RUN_NOWAIT  2

#define UV_EOF (-4095)
#define UV_EAGAIN (-11)
#define UV_ENOBUFS (-105)
#define UV_ECANCELED (-125)

typedef struct uv_loop_s uv_loop_t;
typedef struct uv_handle_s uv_handle_t;
typedef struct uv_timer_s uv_timer_t;
typedef struct uv_tcp_s uv_tcp_t;
typedef struct uv_stream_s uv_stream_t;
typedef struct uv_write_s uv_write_t;
typedef struct uv_connect_s uv_connect_t;
typedef struct uv_async_s uv_async_t;
typedef struct uv_buf_s uv_buf_t;

typedef void (*uv_timer_cb)(uv_timer_t *handle);
typedef void (*uv_close_cb)(uv_handle_t *handle);
typedef void (*uv_alloc_cb)(uv_handle_t *handle, size_t suggested_size, uv_buf_t *buf);
typedef void (*uv_read_cb)(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf);
typedef void (*uv_write_cb)(uv_write_t *req, int status);
typedef void (*uv_connection_cb)(uv_stream_t *server, int status);
typedef void (*uv_connect_cb)(uv_connect_t *req, int status);
typedef void (*uv_async_cb)(uv_async_t *handle);
typedef void (*uv_walk_cb)(uv_handle_t *handle, void *arg);

struct uv_buf_s {
  char *base;
  size_t len;
};

typedef enum {
  UV_UNKNOWN_HANDLE = 0,
  UV_ASYNC,
  UV_CHECK,
  UV_FS_EVENT,
  UV_FS_POLL,
  UV_HANDLE,
  UV_IDLE,
  UV_NAMED_PIPE,
  UV_POLL,
  UV_PREPARE,
  UV_PROCESS,
  UV_STREAM,
  UV_TCP,
  UV_TIMER,
  UV_TTY,
  UV_UDP,
  UV_SIGNAL,
  UV_FILE,
  UV_HANDLE_TYPE_MAX
} uv_handle_type;

typedef enum {
  UV_UNKNOWN_REQ = 0,
  UV_REQ,
  UV_CONNECT,
  UV_WRITE,
  UV_SHUTDOWN,
  UV_UDP_SEND,
  UV_FS,
  UV_WORK,
  UV_GETADDRINFO,
  UV_GETNAMEINFO,
  UV_RANDOM,
  UV_REQ_TYPE_MAX
} uv_req_type;

struct uv_handle_s {
  void *data;
  uv_loop_t *loop;
  uv_handle_type type;
  uv_close_cb close_cb;
  bool closing;
  bool closed;
  struct uv_handle_s *handle_next;
};

struct uv_timer_s {
  void *data;
  uv_loop_t *loop;
  uv_handle_type type;
  uv_close_cb close_cb;
  bool closing;
  bool closed;
  struct uv_handle_s *handle_next;

  uv_timer_cb cb;
  uint64_t timeout;
  uint64_t repeat;
  uint64_t next_fire;
  bool active;
  struct uv_timer_s *timer_next;
};

struct uv_stream_s {
  void *data;
  uv_loop_t *loop;
  uv_handle_type type;
  uv_close_cb close_cb;
  bool closing;
  bool closed;
  struct uv_handle_s *handle_next;

  uv_alloc_cb alloc_cb;
  uv_read_cb read_cb;
  bool reading;
};

struct uv_tcp_s {
  void *data;
  uv_loop_t *loop;
  uv_handle_type type;
  uv_close_cb close_cb;
  bool closing;
  bool closed;
  struct uv_handle_s *handle_next;

  uv_alloc_cb alloc_cb;
  uv_read_cb read_cb;
  bool reading;

  bool bound;
  bool listening;
  int backlog;
  uv_connection_cb connection_cb;

  uint8_t *pending_read_data;
  size_t pending_read_len;
  ssize_t pending_read_error;
  bool pending_read_eof;

  uint8_t *sent_data;
  size_t sent_len;
  size_t sent_cap;

  struct pending_conn {
    uv_tcp_t *client;
    struct pending_conn *next;
  } *pending_conns;

  uv_tcp_t *tcp_next;
};

struct uv_write_s {
  void *data;
  uv_req_type type;
  uv_stream_t *handle;
  uv_write_cb cb;
};

struct uv_connect_s {
  void *data;
  uv_req_type type;
  uv_stream_t *handle;
  uv_connect_cb cb;
};

struct uv_async_s {
  void *data;
  uv_loop_t *loop;
  uv_handle_type type;
  uv_close_cb close_cb;
  bool closing;
  bool closed;
  struct uv_handle_s *handle_next;

  uv_async_cb async_cb;
  bool pending;
};

struct uv_loop_s {
  void *data;
  uint64_t time;
  bool running;
  bool stop_flag;

  uv_timer_t *timer_head;
  uv_tcp_t *tcp_head;
  uv_handle_t *handle_head;
  uv_async_t *async_head;
};

int uv_timer_init(uv_loop_t *loop, uv_timer_t *handle);
int uv_timer_start(uv_timer_t *handle, uv_timer_cb cb, uint64_t timeout, uint64_t repeat);
int uv_timer_stop(uv_timer_t *handle);

void uv_close(uv_handle_t *handle, uv_close_cb close_cb);
int uv_is_closing(const uv_handle_t *handle);
int uv_is_active(const uv_handle_t *handle);

uv_loop_t *uv_default_loop(void);
int uv_loop_init(uv_loop_t *loop);
int uv_loop_close(uv_loop_t *loop);
int uv_run(uv_loop_t *loop, int mode);
void uv_stop(uv_loop_t *loop);
uint64_t uv_now(const uv_loop_t *loop);
uint64_t uv_hrtime(void);
int uv_loop_alive(const uv_loop_t *loop);
void uv_walk(uv_loop_t *loop, uv_walk_cb walk_cb, void *arg);

int uv_tcp_init(uv_loop_t *loop, uv_tcp_t *handle);
int uv_tcp_bind(uv_tcp_t *handle, const struct sockaddr *addr, unsigned int flags);
int uv_listen(uv_stream_t *stream, int backlog, uv_connection_cb cb);
int uv_accept(uv_stream_t *server, uv_stream_t *client);
int uv_read_start(uv_stream_t *stream, uv_alloc_cb alloc_cb, uv_read_cb read_cb);
int uv_read_stop(uv_stream_t *stream);
int uv_write(uv_write_t *req, uv_stream_t *handle, const uv_buf_t bufs[],
             unsigned int nbufs, uv_write_cb cb);
int uv_tcp_connect(uv_connect_t *req, uv_tcp_t *handle,
                   const struct sockaddr *addr, uv_connect_cb cb);
int uv_tcp_nodelay(uv_tcp_t *handle, int enable);
int uv_tcp_getpeername(const uv_tcp_t *handle, struct sockaddr *name, int *namelen);
int uv_tcp_getsockname(const uv_tcp_t *handle, struct sockaddr *name, int *namelen);

int uv_async_init(uv_loop_t *loop, uv_async_t *async, uv_async_cb async_cb);
int uv_async_send(uv_async_t *async);

int uv_ip4_addr(const char *ip, int port, struct sockaddr_in *addr);
int uv_ip4_name(const struct sockaddr_in *src, char *dst, size_t size);
int uv_ip6_name(const struct sockaddr_in6 *src, char *dst, size_t size);
const char *uv_strerror(int err);
const char *uv_err_name(int err);

uv_buf_t uv_buf_init(char *base, unsigned int len);
