#include "uv_fake.h"
#include "uv_fake_control.h"
#include <stdlib.h>
#include <string.h>

int uv_tcp_init(uv_loop_t *loop, uv_tcp_t *handle) {
  memset(handle, 0, sizeof(*handle));
  handle->loop = loop;
  handle->type = UV_TCP;
  
  handle->tcp_next = loop->tcp_head;
  loop->tcp_head = handle;
  
  handle->handle_next = loop->handle_head;
  loop->handle_head = (uv_handle_t *)handle;
  
  return 0;
}

int uv_tcp_bind(uv_tcp_t *handle, const struct sockaddr *addr, unsigned int flags) {
  (void)addr;
  (void)flags;
  handle->bound = true;
  return 0;
}

int uv_listen(uv_stream_t *stream, int backlog, uv_connection_cb cb) {
  uv_tcp_t *tcp = (uv_tcp_t *)stream;
  tcp->listening = true;
  tcp->backlog = backlog;
  tcp->connection_cb = cb;
  return 0;
}

int uv_accept(uv_stream_t *server, uv_stream_t *client) {
  uv_tcp_t *srv = (uv_tcp_t *)server;
  uv_tcp_t *cli = (uv_tcp_t *)client;
  
  if (!srv->pending_conns) return UV_EAGAIN;
  
  struct pending_conn *pc = srv->pending_conns;
  srv->pending_conns = pc->next;
  
  uv_tcp_t *cli_src = pc->client;
  
  uv_tcp_init(srv->loop, cli);
  cli->pending_read_data = cli_src->pending_read_data;
  cli->pending_read_len = cli_src->pending_read_len;
  cli->pending_read_error = cli_src->pending_read_error;
  cli->pending_read_eof = cli_src->pending_read_eof;
  
  free(pc);
  return 0;
}

int uv_read_start(uv_stream_t *stream, uv_alloc_cb alloc_cb, uv_read_cb read_cb) {
  stream->alloc_cb = alloc_cb;
  stream->read_cb = read_cb;
  stream->reading = true;
  
  uv_tcp_t *tcp = (uv_tcp_t *)stream;
  if (tcp->pending_read_data && tcp->pending_read_len > 0) {
    uv_buf_t buf;
    alloc_cb((uv_handle_t *)stream, tcp->pending_read_len, &buf);
    
    size_t to_copy = tcp->pending_read_len < buf.len ? tcp->pending_read_len : buf.len;
    memcpy(buf.base, tcp->pending_read_data, to_copy);
    
    read_cb(stream, (ssize_t)to_copy, &buf);
    
    free(tcp->pending_read_data);
    tcp->pending_read_data = NULL;
    tcp->pending_read_len = 0;
  }
  
  if (tcp->pending_read_error != 0) {
    uv_buf_t buf = {0};
    read_cb(stream, tcp->pending_read_error, &buf);
    tcp->pending_read_error = 0;
  }
  
  if (tcp->pending_read_eof) {
    uv_buf_t buf = {0};
    read_cb(stream, UV_EOF, &buf);
    tcp->pending_read_eof = false;
  }
  
  return 0;
}

int uv_read_stop(uv_stream_t *stream) {
  stream->reading = false;
  stream->alloc_cb = NULL;
  stream->read_cb = NULL;
  return 0;
}

int uv_write(uv_write_t *req, uv_stream_t *handle, const uv_buf_t bufs[],
             unsigned int nbufs, uv_write_cb cb) {
  uv_tcp_t *tcp = (uv_tcp_t *)handle;
  
  size_t total = 0;
  for (unsigned int i = 0; i < nbufs; i++) {
    total += bufs[i].len;
  }
  
  if (tcp->sent_len + total > tcp->sent_cap) {
    size_t new_cap = tcp->sent_cap == 0 ? 4096 : tcp->sent_cap * 2;
    while (new_cap < tcp->sent_len + total) new_cap *= 2;
    uint8_t *new_buf = realloc(tcp->sent_data, new_cap);
    if (!new_buf) return UV_ENOBUFS;
    tcp->sent_data = new_buf;
    tcp->sent_cap = new_cap;
  }
  
  for (unsigned int i = 0; i < nbufs; i++) {
    memcpy(tcp->sent_data + tcp->sent_len, bufs[i].base, bufs[i].len);
    tcp->sent_len += bufs[i].len;
  }
  
  req->handle = handle;
  req->cb = cb;
  req->type = UV_WRITE;
  if (cb) cb(req, 0);
  
  return 0;
}

int uv_tcp_connect(uv_connect_t *req, uv_tcp_t *handle,
                   const struct sockaddr *addr, uv_connect_cb cb) {
  (void)addr;
  req->handle = (uv_stream_t *)handle;
  req->cb = cb;
  req->type = UV_CONNECT;
  if (cb) cb(req, 0);
  return 0;
}

int uv_tcp_nodelay(uv_tcp_t *handle, int enable) {
  (void)handle;
  (void)enable;
  return 0;
}

int uv_tcp_getpeername(const uv_tcp_t *handle, struct sockaddr *name, int *namelen) {
  (void)handle;
  struct sockaddr_in *addr = (struct sockaddr_in *)name;
  memset(addr, 0, sizeof(*addr));
  addr->sin_family = AF_INET;
  addr->sin_addr.s_addr = htonl(0x7f000001);
  addr->sin_port = htons(12345);
  *namelen = sizeof(struct sockaddr_in);
  return 0;
}

int uv_tcp_getsockname(const uv_tcp_t *handle, struct sockaddr *name, int *namelen) {
  (void)handle;
  struct sockaddr_in *addr = (struct sockaddr_in *)name;
  memset(addr, 0, sizeof(*addr));
  addr->sin_family = AF_INET;
  addr->sin_addr.s_addr = htonl(0x7f000001);
  addr->sin_port = htons(8080);
  *namelen = sizeof(struct sockaddr_in);
  return 0;
}

void uv_fake_inject_connection(uv_tcp_t *server, uv_tcp_t *client) {
  struct pending_conn *pc = malloc(sizeof(struct pending_conn));
  if (!pc) return;
  
  pc->client = client;
  pc->next = server->pending_conns;
  server->pending_conns = pc;
  
  if (server->connection_cb) {
    server->connection_cb((uv_stream_t *)server, 0);
  }
}

void uv_fake_inject_read_data(uv_tcp_t *tcp, const void *data, size_t len) {
  free(tcp->pending_read_data);
  tcp->pending_read_data = malloc(len);
  if (!tcp->pending_read_data) return;
  
  memcpy(tcp->pending_read_data, data, len);
  tcp->pending_read_len = len;
  
  if (tcp->reading && tcp->read_cb) {
    uv_buf_t buf;
    tcp->alloc_cb((uv_handle_t *)tcp, len, &buf);
    
    size_t to_copy = len < buf.len ? len : buf.len;
    memcpy(buf.base, data, to_copy);
    
    tcp->read_cb((uv_stream_t *)tcp, (ssize_t)to_copy, &buf);
    
    free(tcp->pending_read_data);
    tcp->pending_read_data = NULL;
    tcp->pending_read_len = 0;
  }
}

void uv_fake_inject_read_eof(uv_tcp_t *tcp) {
  if (tcp->reading && tcp->read_cb) {
    uv_buf_t buf = {0};
    tcp->read_cb((uv_stream_t *)tcp, UV_EOF, &buf);
  } else {
    tcp->pending_read_eof = true;
  }
}

void uv_fake_inject_read_error(uv_tcp_t *tcp, int error) {
  if (tcp->reading && tcp->read_cb) {
    uv_buf_t buf = {0};
    tcp->read_cb((uv_stream_t *)tcp, error, &buf);
  } else {
    tcp->pending_read_error = error;
  }
}

size_t uv_fake_get_written_data(uv_tcp_t *tcp, void *buf, size_t max_len) {
  size_t to_copy = tcp->sent_len < max_len ? tcp->sent_len : max_len;
  if (buf && to_copy > 0) {
    memcpy(buf, tcp->sent_data, to_copy);
  }
  return tcp->sent_len;
}

void uv_fake_clear_written_data(uv_tcp_t *tcp) {
  tcp->sent_len = 0;
}

void uv_fake_process_io(uv_loop_t *loop) {
  (void)loop;
}
