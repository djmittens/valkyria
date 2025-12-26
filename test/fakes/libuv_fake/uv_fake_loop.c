#include "uv_fake.h"
#include "uv_fake_control.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

static uv_loop_t g_default_loop;
static bool g_default_loop_initialized = false;
static uint64_t g_hrtime = 0;

uv_loop_t *uv_default_loop(void) {
  if (!g_default_loop_initialized) {
    uv_loop_init(&g_default_loop);
    g_default_loop_initialized = true;
  }
  return &g_default_loop;
}

int uv_loop_init(uv_loop_t *loop) {
  memset(loop, 0, sizeof(*loop));
  loop->data = NULL;
  loop->time = 0;
  loop->running = false;
  loop->stop_flag = false;
  loop->timer_head = NULL;
  loop->tcp_head = NULL;
  loop->handle_head = NULL;
  loop->async_head = NULL;
  return 0;
}

int uv_loop_close(uv_loop_t *loop) {
  (void)loop;
  return 0;
}

int uv_run(uv_loop_t *loop, int mode) {
  loop->running = true;
  loop->stop_flag = false;
  
  switch (mode) {
    case UV_RUN_NOWAIT:
      uv_fake_run_pending(loop);
      break;
    case UV_RUN_ONCE:
      uv_fake_run_pending(loop);
      break;
    case UV_RUN_DEFAULT:
      while (!loop->stop_flag && uv_loop_alive(loop)) {
        uv_fake_run_pending(loop);
      }
      break;
  }
  
  loop->running = false;
  return loop->stop_flag ? 0 : uv_loop_alive(loop);
}

void uv_stop(uv_loop_t *loop) {
  loop->stop_flag = true;
}

uint64_t uv_now(const uv_loop_t *loop) {
  return loop->time;
}

uint64_t uv_hrtime(void) {
  return g_hrtime;
}

int uv_loop_alive(const uv_loop_t *loop) {
  if (loop->timer_head) {
    for (uv_timer_t *t = loop->timer_head; t; t = t->timer_next) {
      if (t->active && !t->closing) return 1;
    }
  }
  
  if (loop->tcp_head) {
    for (uv_tcp_t *tcp = loop->tcp_head; tcp; tcp = tcp->tcp_next) {
      if (!tcp->closing) return 1;
    }
  }
  
  if (loop->async_head) {
    for (uv_async_t *a = loop->async_head; a; a = (uv_async_t *)a->handle_next) {
      if (!a->closing) return 1;
    }
  }
  
  return 0;
}

void uv_walk(uv_loop_t *loop, uv_walk_cb walk_cb, void *arg) {
  for (uv_handle_t *h = loop->handle_head; h; h = h->handle_next) {
    walk_cb(h, arg);
  }
}

void uv_close(uv_handle_t *handle, uv_close_cb close_cb) {
  handle->closing = true;
  handle->close_cb = close_cb;
  
  switch (handle->type) {
    case UV_TIMER: {
      uv_timer_t *timer = (uv_timer_t *)handle;
      timer->active = false;
      break;
    }
    default:
      break;
  }
  
  handle->closed = true;
  if (close_cb) close_cb(handle);
}

int uv_is_closing(const uv_handle_t *handle) {
  return handle->closing || handle->closed;
}

int uv_is_active(const uv_handle_t *handle) {
  if (handle->closing || handle->closed) return 0;
  
  switch (handle->type) {
    case UV_TIMER: {
      const uv_timer_t *timer = (const uv_timer_t *)handle;
      return timer->active ? 1 : 0;
    }
    case UV_TCP: {
      const uv_tcp_t *tcp = (const uv_tcp_t *)handle;
      return (tcp->listening || tcp->reading) ? 1 : 0;
    }
    default:
      return 0;
  }
}

void uv_fake_time_set(uv_loop_t *loop, uint64_t time_ms) {
  loop->time = time_ms;
  g_hrtime = time_ms * 1000000ULL;
}

void uv_fake_time_advance(uv_loop_t *loop, uint64_t delta_ms) {
  loop->time += delta_ms;
  g_hrtime += delta_ms * 1000000ULL;
  uv_fake_run_pending(loop);
}

uint64_t uv_fake_time_get(uv_loop_t *loop) {
  return loop->time;
}

int uv_fake_run_pending(uv_loop_t *loop) {
  int total_fired = 0;
  int fired_this_round;
  
  do {
    fired_this_round = 0;
    
    for (uv_timer_t *timer = loop->timer_head; timer; timer = timer->timer_next) {
      if (timer->active && !timer->closing && timer->next_fire <= loop->time) {
        if (timer->cb) {
          timer->cb(timer);
          fired_this_round++;
          total_fired++;
        }
        
        if (timer->repeat > 0) {
          timer->next_fire = timer->next_fire + timer->repeat;
        } else {
          timer->active = false;
        }
      }
    }
    
    for (uv_async_t *async = loop->async_head; async; async = (uv_async_t *)async->handle_next) {
      if (async->pending && !async->closing && async->async_cb) {
        async->pending = false;
        async->async_cb(async);
        fired_this_round++;
        total_fired++;
      }
    }
  } while (fired_this_round > 0);
  
  return total_fired;
}

size_t uv_fake_timer_count(uv_loop_t *loop) {
  size_t count = 0;
  for (uv_timer_t *t = loop->timer_head; t; t = t->timer_next) {
    if (t->active) count++;
  }
  return count;
}

size_t uv_fake_active_handles(uv_loop_t *loop) {
  size_t count = 0;
  for (uv_handle_t *h = loop->handle_head; h; h = h->handle_next) {
    if (!h->closing && !h->closed) count++;
  }
  return count;
}

void uv_fake_reset(uv_loop_t *loop) {
  loop->time = 0;
  loop->running = false;
  loop->stop_flag = false;
  
  loop->timer_head = NULL;
  loop->tcp_head = NULL;
  loop->handle_head = NULL;
  loop->async_head = NULL;
  
  g_hrtime = 0;
}

int uv_ip4_addr(const char *ip, int port, struct sockaddr_in *addr) {
  memset(addr, 0, sizeof(*addr));
  addr->sin_family = AF_INET;
  addr->sin_port = htons((uint16_t)port);
  
  if (strcmp(ip, "0.0.0.0") == 0) {
    addr->sin_addr.s_addr = INADDR_ANY;
  } else if (strcmp(ip, "127.0.0.1") == 0) {
    addr->sin_addr.s_addr = htonl(0x7f000001);
  } else {
    addr->sin_addr.s_addr = 0;
  }
  
  return 0;
}

int uv_ip4_name(const struct sockaddr_in *src, char *dst, size_t size) {
  uint32_t addr = ntohl(src->sin_addr.s_addr);
  snprintf(dst, size, "%u.%u.%u.%u",
           (addr >> 24) & 0xff,
           (addr >> 16) & 0xff,
           (addr >> 8) & 0xff,
           addr & 0xff);
  return 0;
}

int uv_ip6_name(const struct sockaddr_in6 *src, char *dst, size_t size) {
  (void)src;
  snprintf(dst, size, "::1");
  return 0;
}

static const char *g_error_strings[] = {
  [0] = "success",
  [-UV_EOF & 0xfff] = "end of file",
  [-UV_EAGAIN & 0xfff] = "resource temporarily unavailable",
  [-UV_ENOBUFS & 0xfff] = "no buffer space available",
  [-UV_ECANCELED & 0xfff] = "operation canceled",
};

const char *uv_strerror(int err) {
  if (err == 0) return "success";
  int idx = (-err) & 0xfff;
  if (idx < (int)(sizeof(g_error_strings) / sizeof(g_error_strings[0])) && g_error_strings[idx]) {
    return g_error_strings[idx];
  }
  return "unknown error";
}

const char *uv_err_name(int err) {
  if (err == 0) return "OK";
  if (err == UV_EOF) return "EOF";
  if (err == UV_EAGAIN) return "EAGAIN";
  if (err == UV_ENOBUFS) return "ENOBUFS";
  if (err == UV_ECANCELED) return "ECANCELED";
  return "UNKNOWN";
}

uv_buf_t uv_buf_init(char *base, unsigned int len) {
  uv_buf_t buf;
  buf.base = base;
  buf.len = len;
  return buf;
}

static void __register_handle(uv_loop_t *loop, uv_handle_t *handle) {
  handle->handle_next = loop->handle_head;
  loop->handle_head = handle;
}

int uv_async_init(uv_loop_t *loop, uv_async_t *async, uv_async_cb async_cb) {
  memset(async, 0, sizeof(*async));
  async->loop = loop;
  async->type = UV_ASYNC;
  async->async_cb = async_cb;
  async->pending = false;
  
  async->handle_next = (uv_handle_t *)loop->async_head;
  loop->async_head = async;
  
  __register_handle(loop, (uv_handle_t *)async);
  
  return 0;
}

int uv_async_send(uv_async_t *async) {
  async->pending = true;
  return 0;
}
