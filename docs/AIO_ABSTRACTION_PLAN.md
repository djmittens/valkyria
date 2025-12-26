# AIO Abstraction Plan: libuv and nghttp2

## Overview

This document outlines a phased approach to enabling testability of the AIO subsystem without runtime overhead. The key insight is that **production code should not pay for testability** - all abstraction costs should be paid only at test time via link-time substitution.

### Design Principles

1. **Zero-Cost Production** - No vtables, no pointer chasing, direct function calls
2. **Link-Time Substitution** - Test builds link against fake implementations of libuv/nghttp2
3. **Test Doubles over Mocks** - Use real implementations with controlled behavior
4. **Incremental Migration** - Each phase produces working, tested code

### Architecture Decision: Link-Time vs Runtime Abstraction

**Rejected Approach (Runtime vtables):**
```c
// Every call goes through vtable - pointer chase in production
sys->tcp_ops->write(tcp, data, len, cb);
```

**Chosen Approach (Link-time substitution):**
```c
// Production: direct call to libuv
uv_write(req, stream, bufs, nbufs, cb);

// Test build: same code, but links against libuv_fake.a instead of libuv.a
```

Benefits:
- Zero runtime overhead in production
- AIO code stays simple, calls `uv_*` and `nghttp2_*` directly
- Test doubles implement the exact same API
- No struct size mismatches between implementations

---

## Current State Analysis

### libuv Usage (~100 call sites)

| Category | Functions | Files | Complexity |
|----------|-----------|-------|------------|
| **Timer** | `uv_timer_init/start/stop/close` | 5 | Low |
| **TCP** | `uv_tcp_init/bind/listen/accept/connect/read/write/close` | 4 | High |
| **Loop** | `uv_run/stop/now/hrtime/walk/loop_alive` | 2 | Medium |
| **Async** | `uv_async_init/send` | 2 | Low |
| **Utilities** | `uv_is_closing/strerror/ip4_addr/ip4_name` | 6 | Low |

### nghttp2 Usage (~87 call sites)

| Category | Functions | Files | Complexity |
|----------|-----------|-------|------------|
| **Session** | `nghttp2_session_*_new/del/recv/send/want_*` | 3 | High |
| **Stream** | `nghttp2_session_get/set_stream_user_data` | 8 | Medium |
| **Submit** | `nghttp2_submit_response/request/rst_stream/goaway/settings` | 6 | Medium |
| **Callbacks** | `nghttp2_session_callbacks_*` | 2 | Medium |
| **Memory** | `nghttp2_mem` custom allocator | 1 | Low |

---

## Build System Changes

### Target Structure

```
src/
  aio/                    # AIO code - calls uv_*/nghttp2_* directly
    ...
    
test/
  fakes/
    libuv_fake/
      uv_fake.h           # Matches <uv.h> API
      uv_fake_loop.c      # Fake event loop
      uv_fake_tcp.c       # Fake TCP
      uv_fake_timer.c     # Fake timers
      uv_fake_control.h   # Test control API (inject data, advance time)
    nghttp2_fake/
      nghttp2_fake.h      # Matches <nghttp2/nghttp2.h> API
      nghttp2_fake.c      # Fake HTTP/2 session
      nghttp2_fake_control.h  # Test control API
```

### CMake Configuration

```cmake
# Production build
add_library(valk_aio ...)
target_link_libraries(valk_aio PRIVATE uv nghttp2)

# Test build - link against fakes instead
add_library(libuv_fake STATIC test/fakes/libuv_fake/*.c)
add_library(nghttp2_fake STATIC test/fakes/nghttp2_fake/*.c)

add_executable(test_aio_unit ...)
target_link_libraries(test_aio_unit PRIVATE 
  valk_aio_objects    # Same object files as production
  libuv_fake          # Fake libuv instead of real
  nghttp2_fake        # Fake nghttp2 instead of real
)
```

---

## Phase 1: libuv Fake - Timer Operations

**Goal**: Create fake timer implementation to test time-dependent code without real delays.

**Duration**: 2-3 days

### Deliverable 1.1: Fake Timer Types

Create `test/fakes/libuv_fake/uv_fake.h`:

```c
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

// Match libuv's type definitions exactly
typedef struct uv_loop_s uv_loop_t;
typedef struct uv_handle_s uv_handle_t;
typedef struct uv_timer_s uv_timer_t;
typedef struct uv_tcp_s uv_tcp_t;
typedef struct uv_stream_s uv_stream_t;
typedef struct uv_write_s uv_write_t;
typedef struct uv_connect_s uv_connect_t;
typedef struct uv_buf_s uv_buf_t;

typedef void (*uv_timer_cb)(uv_timer_t *handle);
typedef void (*uv_close_cb)(uv_handle_t *handle);
typedef void (*uv_alloc_cb)(uv_handle_t *handle, size_t suggested_size, uv_buf_t *buf);
typedef void (*uv_read_cb)(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf);
typedef void (*uv_write_cb)(uv_write_t *req, int status);
typedef void (*uv_connection_cb)(uv_stream_t *server, int status);
typedef void (*uv_connect_cb)(uv_connect_t *req, int status);

struct uv_buf_s {
  char *base;
  size_t len;
};

// Handle types - sized to match real libuv (or larger)
struct uv_handle_s {
  void *data;
  uv_loop_t *loop;
  int type;
  uv_close_cb close_cb;
  bool closing;
  bool closed;
};

struct uv_timer_s {
  uv_handle_t handle;  // Must be first for casting
  uv_timer_cb cb;
  uint64_t timeout;
  uint64_t repeat;
  uint64_t next_fire;
  bool active;
};

struct uv_loop_s {
  void *data;
  uint64_t time;           // Current fake time in ms
  bool running;
  bool stop_flag;
  
  // Linked list of active timers
  uv_timer_t *timer_head;
  
  // Linked list of active TCP handles
  uv_tcp_t *tcp_head;
};

// Timer API - matches libuv exactly
int uv_timer_init(uv_loop_t *loop, uv_timer_t *handle);
int uv_timer_start(uv_timer_t *handle, uv_timer_cb cb, uint64_t timeout, uint64_t repeat);
int uv_timer_stop(uv_timer_t *handle);
void uv_close(uv_handle_t *handle, uv_close_cb close_cb);
int uv_is_closing(const uv_handle_t *handle);

// Loop API
uv_loop_t *uv_default_loop(void);
int uv_loop_init(uv_loop_t *loop);
int uv_loop_close(uv_loop_t *loop);
int uv_run(uv_loop_t *loop, int mode);
void uv_stop(uv_loop_t *loop);
uint64_t uv_now(const uv_loop_t *loop);
uint64_t uv_hrtime(void);

// Run modes
#define UV_RUN_DEFAULT 0
#define UV_RUN_ONCE    1
#define UV_RUN_NOWAIT  2
```

### Deliverable 1.2: Test Control API

Create `test/fakes/libuv_fake/uv_fake_control.h`:

```c
#pragma once

#include "uv_fake.h"

// Time control
void uv_fake_time_set(uv_loop_t *loop, uint64_t time_ms);
void uv_fake_time_advance(uv_loop_t *loop, uint64_t delta_ms);
uint64_t uv_fake_time_get(uv_loop_t *loop);

// Process pending callbacks (timers that have fired)
int uv_fake_run_pending(uv_loop_t *loop);

// Introspection
size_t uv_fake_timer_count(uv_loop_t *loop);
size_t uv_fake_active_handles(uv_loop_t *loop);

// Reset all state (call between tests)
void uv_fake_reset(uv_loop_t *loop);
```

### Deliverable 1.3: Fake Timer Implementation

Create `test/fakes/libuv_fake/uv_fake_timer.c`:

```c
#include "uv_fake.h"
#include "uv_fake_control.h"
#include <stdlib.h>
#include <string.h>

static uint64_t g_hrtime = 0;

int uv_timer_init(uv_loop_t *loop, uv_timer_t *handle) {
  memset(handle, 0, sizeof(*handle));
  handle->handle.loop = loop;
  handle->handle.type = 1;  // UV_TIMER
  return 0;
}

int uv_timer_start(uv_timer_t *handle, uv_timer_cb cb, uint64_t timeout, uint64_t repeat) {
  handle->cb = cb;
  handle->timeout = timeout;
  handle->repeat = repeat;
  handle->next_fire = handle->handle.loop->time + timeout;
  handle->active = true;
  
  // Add to loop's timer list
  uv_loop_t *loop = handle->handle.loop;
  handle->handle.data = loop->timer_head;  // Reuse data as next pointer for simplicity
  loop->timer_head = handle;
  
  return 0;
}

int uv_timer_stop(uv_timer_t *handle) {
  handle->active = false;
  return 0;
}

void uv_close(uv_handle_t *handle, uv_close_cb close_cb) {
  handle->closing = true;
  handle->close_cb = close_cb;
  // In fake, close is synchronous
  handle->closed = true;
  if (close_cb) close_cb(handle);
}

int uv_is_closing(const uv_handle_t *handle) {
  return handle->closing || handle->closed;
}

uint64_t uv_now(const uv_loop_t *loop) {
  return loop->time;
}

uint64_t uv_hrtime(void) {
  return g_hrtime;
}

// Test control implementation
void uv_fake_time_set(uv_loop_t *loop, uint64_t time_ms) {
  loop->time = time_ms;
  g_hrtime = time_ms * 1000000ULL;  // Convert to nanoseconds
}

void uv_fake_time_advance(uv_loop_t *loop, uint64_t delta_ms) {
  loop->time += delta_ms;
  g_hrtime += delta_ms * 1000000ULL;
  
  // Fire any timers that are now due
  uv_fake_run_pending(loop);
}

int uv_fake_run_pending(uv_loop_t *loop) {
  int fired = 0;
  uv_timer_t *timer = loop->timer_head;
  
  while (timer) {
    if (timer->active && timer->next_fire <= loop->time) {
      timer->cb(timer);
      fired++;
      
      if (timer->repeat > 0) {
        timer->next_fire = loop->time + timer->repeat;
      } else {
        timer->active = false;
      }
    }
    timer = (uv_timer_t *)timer->handle.data;  // next in list
  }
  
  return fired;
}

size_t uv_fake_timer_count(uv_loop_t *loop) {
  size_t count = 0;
  uv_timer_t *timer = loop->timer_head;
  while (timer) {
    if (timer->active) count++;
    timer = (uv_timer_t *)timer->handle.data;
  }
  return count;
}

void uv_fake_reset(uv_loop_t *loop) {
  loop->time = 0;
  loop->timer_head = NULL;
  loop->tcp_head = NULL;
  loop->running = false;
  loop->stop_flag = false;
  g_hrtime = 0;
}
```

### Deliverable 1.4: Unit Tests Using Fakes

Create `test/unit/test_maintenance_timer.c`:

```c
#include "testing.h"
#include "uv_fake.h"
#include "uv_fake_control.h"
#include "aio/aio_maintenance.h"

static uv_loop_t test_loop;

static void setup(void) {
  uv_loop_init(&test_loop);
  uv_fake_reset(&test_loop);
}

static int callback_count = 0;

static void counting_cb(uv_timer_t *timer) {
  callback_count++;
}

VALK_TEST(timer_fires_at_timeout) {
  setup();
  callback_count = 0;
  
  uv_timer_t timer;
  uv_timer_init(&test_loop, &timer);
  uv_timer_start(&timer, counting_cb, 1000, 0);  // Fire once after 1s
  
  VALK_ASSERT_EQ(callback_count, 0);
  
  uv_fake_time_advance(&test_loop, 500);
  VALK_ASSERT_EQ(callback_count, 0);  // Not yet
  
  uv_fake_time_advance(&test_loop, 500);
  VALK_ASSERT_EQ(callback_count, 1);  // Now!
  
  uv_fake_time_advance(&test_loop, 1000);
  VALK_ASSERT_EQ(callback_count, 1);  // No repeat
}

VALK_TEST(timer_repeats) {
  setup();
  callback_count = 0;
  
  uv_timer_t timer;
  uv_timer_init(&test_loop, &timer);
  uv_timer_start(&timer, counting_cb, 100, 100);  // Fire every 100ms
  
  uv_fake_time_advance(&test_loop, 350);
  VALK_ASSERT_EQ(callback_count, 3);  // At 100, 200, 300
}

VALK_TEST(maintenance_timer_closes_idle_connections) {
  setup();
  
  valk_aio_system_config_t cfg = valk_aio_config_minimal();
  cfg.connection_idle_timeout_ms = 60000;
  cfg.maintenance_interval_ms = 1000;
  
  valk_aio_system_t sys = {0};
  sys.config = cfg;
  sys.eventloop = &test_loop;
  
  // Create connection with last_activity at time 0
  valk_aio_handle_t conn = {0};
  conn.kind = VALK_HNDL_HTTP_CONN;
  conn.http.state = VALK_CONN_ESTABLISHED;
  conn.http.last_activity_ms = 0;
  
  // Link into live handles
  valk_aio_link_handle(&sys, &conn);
  
  valk_maintenance_timer_init(&sys);
  valk_maintenance_timer_start(&sys);
  
  // Advance 30 seconds - should NOT timeout
  uv_fake_time_advance(&test_loop, 30000);
  VALK_ASSERT_EQ(conn.http.state, VALK_CONN_ESTABLISHED);
  
  // Advance to 61 seconds - SHOULD timeout
  uv_fake_time_advance(&test_loop, 31000);
  VALK_ASSERT_EQ(conn.http.state, VALK_CONN_CLOSING);
}
```

### Phase 1 Verification

- [ ] `make build` passes (production build unchanged)
- [ ] `make test-unit` passes with fake libuv
- [ ] Timer tests are deterministic (no flakiness)
- [ ] No changes to production AIO code

---

## Phase 2: libuv Fake - TCP Operations

**Goal**: Create fake TCP implementation to test connection handling without real network.

**Duration**: 3-4 days

**Depends on**: Phase 1

### Deliverable 2.1: Fake TCP Types

Add to `test/fakes/libuv_fake/uv_fake.h`:

```c
struct uv_stream_s {
  uv_handle_t handle;
  uv_alloc_cb alloc_cb;
  uv_read_cb read_cb;
  bool reading;
};

struct uv_tcp_s {
  uv_stream_t stream;  // Must be first for casting
  
  // Fake state
  bool bound;
  bool listening;
  int backlog;
  uv_connection_cb connection_cb;
  
  // Pending data to deliver on read
  uint8_t *pending_read_data;
  size_t pending_read_len;
  
  // Captured write data
  uint8_t *sent_data;
  size_t sent_len;
  size_t sent_cap;
  
  // Pending connections for accept
  struct pending_conn {
    uv_tcp_t *client;
    struct pending_conn *next;
  } *pending_conns;
  
  // Link for loop tracking
  uv_tcp_t *next;
};

struct uv_write_s {
  uv_stream_t *handle;
  uv_write_cb cb;
};

struct uv_connect_s {
  uv_stream_t *handle;
  uv_connect_cb cb;
};

// TCP API - matches libuv
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

// Address helpers
int uv_ip4_addr(const char *ip, int port, struct sockaddr_in *addr);
int uv_ip4_name(const struct sockaddr_in *src, char *dst, size_t size);
const char *uv_strerror(int err);
```

### Deliverable 2.2: TCP Test Control API

Add to `test/fakes/libuv_fake/uv_fake_control.h`:

```c
// Inject incoming connection to a listening server
void uv_fake_inject_connection(uv_tcp_t *server, uv_tcp_t *client);

// Inject data to be read from a TCP stream
void uv_fake_inject_read_data(uv_tcp_t *tcp, const void *data, size_t len);

// Inject read EOF
void uv_fake_inject_read_eof(uv_tcp_t *tcp);

// Inject read error
void uv_fake_inject_read_error(uv_tcp_t *tcp, int error);

// Get data written to a TCP stream
size_t uv_fake_get_written_data(uv_tcp_t *tcp, void *buf, size_t max_len);

// Clear written data buffer
void uv_fake_clear_written_data(uv_tcp_t *tcp);

// Process pending I/O (call after inject)
void uv_fake_process_io(uv_loop_t *loop);
```

### Deliverable 2.3: Fake TCP Implementation

Create `test/fakes/libuv_fake/uv_fake_tcp.c`:

```c
#include "uv_fake.h"
#include "uv_fake_control.h"
#include <stdlib.h>
#include <string.h>

int uv_tcp_init(uv_loop_t *loop, uv_tcp_t *handle) {
  memset(handle, 0, sizeof(*handle));
  handle->stream.handle.loop = loop;
  handle->stream.handle.type = 2;  // UV_TCP
  
  // Add to loop's TCP list
  handle->next = loop->tcp_head;
  loop->tcp_head = handle;
  
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
  if (!srv->pending_conns) return -1;  // UV_EAGAIN
  
  struct pending_conn *pc = srv->pending_conns;
  srv->pending_conns = pc->next;
  
  // Copy client state
  uv_tcp_t *cli_src = pc->client;
  uv_tcp_t *cli_dst = (uv_tcp_t *)client;
  
  uv_tcp_init(srv->stream.handle.loop, cli_dst);
  // Copy any pre-set state from the injected client
  cli_dst->pending_read_data = cli_src->pending_read_data;
  cli_dst->pending_read_len = cli_src->pending_read_len;
  
  free(pc);
  return 0;
}

int uv_read_start(uv_stream_t *stream, uv_alloc_cb alloc_cb, uv_read_cb read_cb) {
  stream->alloc_cb = alloc_cb;
  stream->read_cb = read_cb;
  stream->reading = true;
  
  // Deliver any pending data immediately
  uv_tcp_t *tcp = (uv_tcp_t *)stream;
  if (tcp->pending_read_data && tcp->pending_read_len > 0) {
    uv_buf_t buf;
    alloc_cb((uv_handle_t *)stream, tcp->pending_read_len, &buf);
    
    size_t to_copy = tcp->pending_read_len < buf.len ? tcp->pending_read_len : buf.len;
    memcpy(buf.base, tcp->pending_read_data, to_copy);
    
    read_cb(stream, (ssize_t)to_copy, &buf);
    
    // Clear pending data
    free(tcp->pending_read_data);
    tcp->pending_read_data = NULL;
    tcp->pending_read_len = 0;
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
  
  // Calculate total size
  size_t total = 0;
  for (unsigned int i = 0; i < nbufs; i++) {
    total += bufs[i].len;
  }
  
  // Grow buffer if needed
  if (tcp->sent_len + total > tcp->sent_cap) {
    size_t new_cap = tcp->sent_cap == 0 ? 4096 : tcp->sent_cap * 2;
    while (new_cap < tcp->sent_len + total) new_cap *= 2;
    tcp->sent_data = realloc(tcp->sent_data, new_cap);
    tcp->sent_cap = new_cap;
  }
  
  // Copy data
  for (unsigned int i = 0; i < nbufs; i++) {
    memcpy(tcp->sent_data + tcp->sent_len, bufs[i].base, bufs[i].len);
    tcp->sent_len += bufs[i].len;
  }
  
  // Complete write synchronously in fake
  req->handle = handle;
  req->cb = cb;
  if (cb) cb(req, 0);
  
  return 0;
}

// Test control
void uv_fake_inject_connection(uv_tcp_t *server, uv_tcp_t *client) {
  struct pending_conn *pc = malloc(sizeof(*pc));
  pc->client = client;
  pc->next = server->pending_conns;
  server->pending_conns = pc;
  
  // Trigger connection callback
  if (server->connection_cb) {
    server->connection_cb((uv_stream_t *)server, 0);
  }
}

void uv_fake_inject_read_data(uv_tcp_t *tcp, const void *data, size_t len) {
  tcp->pending_read_data = malloc(len);
  memcpy(tcp->pending_read_data, data, len);
  tcp->pending_read_len = len;
  
  // If already reading, deliver immediately
  if (tcp->stream.reading && tcp->stream.read_cb) {
    uv_buf_t buf;
    tcp->stream.alloc_cb((uv_handle_t *)tcp, len, &buf);
    
    size_t to_copy = len < buf.len ? len : buf.len;
    memcpy(buf.base, data, to_copy);
    
    tcp->stream.read_cb((uv_stream_t *)tcp, (ssize_t)to_copy, &buf);
    
    free(tcp->pending_read_data);
    tcp->pending_read_data = NULL;
    tcp->pending_read_len = 0;
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
```

### Phase 2 Verification

- [ ] Server accepts fake connections
- [ ] Read callbacks fire with injected data
- [ ] Write data is captured for assertions
- [ ] Connection lifecycle (accept/close) works

---

## Phase 3: nghttp2 Fake

**Goal**: Create fake nghttp2 implementation for HTTP/2 protocol testing without real frames.

**Duration**: 4-5 days

**Depends on**: Phase 2

### Deliverable 3.1: Fake nghttp2 Types

Create `test/fakes/nghttp2_fake/nghttp2_fake.h`:

```c
#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sys/types.h>

// Opaque types - match nghttp2's forward declarations
typedef struct nghttp2_session nghttp2_session;
typedef struct nghttp2_session_callbacks nghttp2_session_callbacks;
typedef struct nghttp2_option nghttp2_option;

// Error codes
#define NGHTTP2_ERR_WOULDBLOCK -504
#define NGHTTP2_ERR_CALLBACK_FAILURE -902

// Frame types
#define NGHTTP2_DATA 0
#define NGHTTP2_HEADERS 1
#define NGHTTP2_RST_STREAM 3
#define NGHTTP2_SETTINGS 4
#define NGHTTP2_GOAWAY 7

// Flags
#define NGHTTP2_FLAG_NONE 0
#define NGHTTP2_FLAG_END_STREAM 0x01
#define NGHTTP2_FLAG_END_HEADERS 0x04

// NV flags
#define NGHTTP2_NV_FLAG_NONE 0

typedef struct {
  uint8_t *name;
  uint8_t *value;
  size_t namelen;
  size_t valuelen;
  uint8_t flags;
} nghttp2_nv;

typedef struct {
  size_t length;
  int32_t stream_id;
  uint8_t type;
  uint8_t flags;
} nghttp2_frame_hd;

typedef struct {
  nghttp2_frame_hd hd;
} nghttp2_frame;

typedef struct {
  union {
    int fd;
    void *ptr;
  } source;
} nghttp2_data_source;

typedef ssize_t (*nghttp2_data_source_read_callback)(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data);

typedef struct {
  nghttp2_data_source source;
  nghttp2_data_source_read_callback read_callback;
} nghttp2_data_provider;

// Same for nghttp2_data_provider2
typedef ssize_t (*nghttp2_data_source_read_callback2)(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data);

typedef struct {
  nghttp2_data_source source;
  nghttp2_data_source_read_callback2 read_callback;
} nghttp2_data_provider2;

// Callbacks
typedef int (*nghttp2_on_begin_headers_callback)(
    nghttp2_session *session, const nghttp2_frame *frame, void *user_data);

typedef int (*nghttp2_on_header_callback)(
    nghttp2_session *session, const nghttp2_frame *frame,
    const uint8_t *name, size_t namelen,
    const uint8_t *value, size_t valuelen,
    uint8_t flags, void *user_data);

typedef int (*nghttp2_on_data_chunk_recv_callback)(
    nghttp2_session *session, uint8_t flags, int32_t stream_id,
    const uint8_t *data, size_t len, void *user_data);

typedef int (*nghttp2_on_stream_close_callback)(
    nghttp2_session *session, int32_t stream_id, uint32_t error_code,
    void *user_data);

typedef int (*nghttp2_on_frame_send_callback)(
    nghttp2_session *session, const nghttp2_frame *frame, void *user_data);

typedef int (*nghttp2_on_frame_recv_callback)(
    nghttp2_session *session, const nghttp2_frame *frame, void *user_data);

// Session callbacks API
int nghttp2_session_callbacks_new(nghttp2_session_callbacks **callbacks_ptr);
void nghttp2_session_callbacks_del(nghttp2_session_callbacks *callbacks);

void nghttp2_session_callbacks_set_on_begin_headers_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_begin_headers_callback cb);
void nghttp2_session_callbacks_set_on_header_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_header_callback cb);
void nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_data_chunk_recv_callback cb);
void nghttp2_session_callbacks_set_on_stream_close_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_stream_close_callback cb);
void nghttp2_session_callbacks_set_on_frame_send_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_frame_send_callback cb);
void nghttp2_session_callbacks_set_on_frame_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_frame_recv_callback cb);

// Session API
int nghttp2_session_server_new(nghttp2_session **session_ptr,
                                const nghttp2_session_callbacks *callbacks,
                                void *user_data);
int nghttp2_session_client_new(nghttp2_session **session_ptr,
                                const nghttp2_session_callbacks *callbacks,
                                void *user_data);
void nghttp2_session_del(nghttp2_session *session);

ssize_t nghttp2_session_mem_recv(nghttp2_session *session,
                                  const uint8_t *in, size_t inlen);
ssize_t nghttp2_session_mem_send(nghttp2_session *session,
                                  const uint8_t **data_ptr);
int nghttp2_session_want_write(nghttp2_session *session);
int nghttp2_session_want_read(nghttp2_session *session);

void *nghttp2_session_get_stream_user_data(nghttp2_session *session,
                                            int32_t stream_id);
int nghttp2_session_set_stream_user_data(nghttp2_session *session,
                                          int32_t stream_id, void *user_data);
int nghttp2_session_resume_data(nghttp2_session *session, int32_t stream_id);

// Submit API
typedef struct {
  int32_t settings_id;
  uint32_t value;
} nghttp2_settings_entry;

int nghttp2_submit_settings(nghttp2_session *session, uint8_t flags,
                            const nghttp2_settings_entry *iv, size_t niv);
int nghttp2_submit_response(nghttp2_session *session, int32_t stream_id,
                            const nghttp2_nv *nva, size_t nvlen,
                            const nghttp2_data_provider *data_prd);
int nghttp2_submit_response2(nghttp2_session *session, int32_t stream_id,
                             const nghttp2_nv *nva, size_t nvlen,
                             const nghttp2_data_provider2 *data_prd);
int32_t nghttp2_submit_request(nghttp2_session *session,
                                const void *pri_spec,
                                const nghttp2_nv *nva, size_t nvlen,
                                const nghttp2_data_provider *data_prd,
                                void *stream_user_data);
int32_t nghttp2_submit_request2(nghttp2_session *session,
                                 const void *pri_spec,
                                 const nghttp2_nv *nva, size_t nvlen,
                                 const nghttp2_data_provider2 *data_prd,
                                 void *stream_user_data);
int nghttp2_submit_rst_stream(nghttp2_session *session, uint8_t flags,
                               int32_t stream_id, uint32_t error_code);
int nghttp2_submit_goaway(nghttp2_session *session, uint8_t flags,
                           int32_t last_stream_id, uint32_t error_code,
                           const uint8_t *opaque_data, size_t opaque_data_len);

const char *nghttp2_strerror(int lib_error_code);
```

### Deliverable 3.2: nghttp2 Test Control API

Create `test/fakes/nghttp2_fake/nghttp2_fake_control.h`:

```c
#pragma once

#include "nghttp2_fake.h"

// Inject a complete request into a server session
// This triggers on_begin_headers, on_header (for each header), and optionally on_data
int32_t nghttp2_fake_inject_request(nghttp2_session *session,
                                     const char *method,
                                     const char *path,
                                     const nghttp2_nv *extra_headers,
                                     size_t nextra,
                                     const uint8_t *body,
                                     size_t body_len);

// Get response submitted for a stream
typedef struct {
  int status_code;
  nghttp2_nv *headers;
  size_t nheaders;
  uint8_t *body;
  size_t body_len;
  bool closed;
} nghttp2_fake_response_t;

bool nghttp2_fake_get_response(nghttp2_session *session, int32_t stream_id,
                                nghttp2_fake_response_t *response);

// Simulate frame send (process any pending submit_* calls)
int nghttp2_fake_process_pending(nghttp2_session *session);

// Introspection
size_t nghttp2_fake_stream_count(nghttp2_session *session);
bool nghttp2_fake_stream_exists(nghttp2_session *session, int32_t stream_id);

// Reset session state
void nghttp2_fake_reset(nghttp2_session *session);
```

### Deliverable 3.3: Fake nghttp2 Implementation

Create `test/fakes/nghttp2_fake/nghttp2_fake.c`:

```c
#include "nghttp2_fake.h"
#include "nghttp2_fake_control.h"
#include <stdlib.h>
#include <string.h>

typedef struct fake_stream {
  int32_t id;
  void *user_data;
  bool closed;
  
  // Response data (captured from submit_response)
  int status_code;
  nghttp2_nv *response_headers;
  size_t response_nheaders;
  uint8_t *response_body;
  size_t response_body_len;
  size_t response_body_cap;
  
  struct fake_stream *next;
} fake_stream_t;

struct nghttp2_session_callbacks {
  nghttp2_on_begin_headers_callback on_begin_headers;
  nghttp2_on_header_callback on_header;
  nghttp2_on_data_chunk_recv_callback on_data_chunk_recv;
  nghttp2_on_stream_close_callback on_stream_close;
  nghttp2_on_frame_send_callback on_frame_send;
  nghttp2_on_frame_recv_callback on_frame_recv;
};

struct nghttp2_session {
  nghttp2_session_callbacks cbs;
  void *user_data;
  bool is_server;
  int32_t next_stream_id;
  fake_stream_t *streams;
  bool want_write;
};

// Callbacks setup
int nghttp2_session_callbacks_new(nghttp2_session_callbacks **cbs_ptr) {
  *cbs_ptr = calloc(1, sizeof(nghttp2_session_callbacks));
  return *cbs_ptr ? 0 : -1;
}

void nghttp2_session_callbacks_del(nghttp2_session_callbacks *cbs) {
  free(cbs);
}

void nghttp2_session_callbacks_set_on_begin_headers_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_begin_headers_callback cb) {
  cbs->on_begin_headers = cb;
}

void nghttp2_session_callbacks_set_on_header_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_header_callback cb) {
  cbs->on_header = cb;
}

void nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_data_chunk_recv_callback cb) {
  cbs->on_data_chunk_recv = cb;
}

void nghttp2_session_callbacks_set_on_stream_close_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_stream_close_callback cb) {
  cbs->on_stream_close = cb;
}

void nghttp2_session_callbacks_set_on_frame_send_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_frame_send_callback cb) {
  cbs->on_frame_send = cb;
}

void nghttp2_session_callbacks_set_on_frame_recv_callback(
    nghttp2_session_callbacks *cbs, nghttp2_on_frame_recv_callback cb) {
  cbs->on_frame_recv = cb;
}

// Session lifecycle
int nghttp2_session_server_new(nghttp2_session **session_ptr,
                                const nghttp2_session_callbacks *callbacks,
                                void *user_data) {
  nghttp2_session *s = calloc(1, sizeof(nghttp2_session));
  if (!s) return -1;
  
  if (callbacks) s->cbs = *callbacks;
  s->user_data = user_data;
  s->is_server = true;
  s->next_stream_id = 1;
  
  *session_ptr = s;
  return 0;
}

int nghttp2_session_client_new(nghttp2_session **session_ptr,
                                const nghttp2_session_callbacks *callbacks,
                                void *user_data) {
  nghttp2_session *s = calloc(1, sizeof(nghttp2_session));
  if (!s) return -1;
  
  if (callbacks) s->cbs = *callbacks;
  s->user_data = user_data;
  s->is_server = false;
  s->next_stream_id = 1;
  
  *session_ptr = s;
  return 0;
}

void nghttp2_session_del(nghttp2_session *session) {
  if (!session) return;
  
  fake_stream_t *s = session->streams;
  while (s) {
    fake_stream_t *next = s->next;
    free(s->response_headers);
    free(s->response_body);
    free(s);
    s = next;
  }
  free(session);
}

// Stream helpers
static fake_stream_t *find_stream(nghttp2_session *session, int32_t stream_id) {
  fake_stream_t *s = session->streams;
  while (s) {
    if (s->id == stream_id) return s;
    s = s->next;
  }
  return NULL;
}

static fake_stream_t *create_stream(nghttp2_session *session, int32_t stream_id) {
  fake_stream_t *s = calloc(1, sizeof(fake_stream_t));
  if (!s) return NULL;
  s->id = stream_id;
  s->next = session->streams;
  session->streams = s;
  return s;
}

// Session API
ssize_t nghttp2_session_mem_recv(nghttp2_session *session,
                                  const uint8_t *in, size_t inlen) {
  (void)session;
  (void)in;
  return (ssize_t)inlen;  // Pretend we consumed it all
}

ssize_t nghttp2_session_mem_send(nghttp2_session *session,
                                  const uint8_t **data_ptr) {
  (void)session;
  *data_ptr = NULL;
  return 0;  // Nothing to send in fake
}

int nghttp2_session_want_write(nghttp2_session *session) {
  return session->want_write ? 1 : 0;
}

int nghttp2_session_want_read(nghttp2_session *session) {
  (void)session;
  return 1;  // Always ready to read in fake
}

void *nghttp2_session_get_stream_user_data(nghttp2_session *session, int32_t stream_id) {
  fake_stream_t *s = find_stream(session, stream_id);
  return s ? s->user_data : NULL;
}

int nghttp2_session_set_stream_user_data(nghttp2_session *session, int32_t stream_id,
                                          void *user_data) {
  fake_stream_t *s = find_stream(session, stream_id);
  if (!s) {
    s = create_stream(session, stream_id);
    if (!s) return -1;
  }
  s->user_data = user_data;
  return 0;
}

int nghttp2_session_resume_data(nghttp2_session *session, int32_t stream_id) {
  (void)session;
  (void)stream_id;
  return 0;
}

// Submit API
int nghttp2_submit_settings(nghttp2_session *session, uint8_t flags,
                            const nghttp2_settings_entry *iv, size_t niv) {
  (void)session;
  (void)flags;
  (void)iv;
  (void)niv;
  return 0;
}

int nghttp2_submit_response2(nghttp2_session *session, int32_t stream_id,
                             const nghttp2_nv *nva, size_t nvlen,
                             const nghttp2_data_provider2 *data_prd) {
  fake_stream_t *s = find_stream(session, stream_id);
  if (!s) {
    s = create_stream(session, stream_id);
    if (!s) return -1;
  }
  
  // Store headers
  s->response_headers = malloc(sizeof(nghttp2_nv) * nvlen);
  memcpy(s->response_headers, nva, sizeof(nghttp2_nv) * nvlen);
  s->response_nheaders = nvlen;
  
  // Parse status from :status header
  for (size_t i = 0; i < nvlen; i++) {
    if (nva[i].namelen == 7 && memcmp(nva[i].name, ":status", 7) == 0) {
      char buf[8] = {0};
      size_t len = nva[i].valuelen < 7 ? nva[i].valuelen : 7;
      memcpy(buf, nva[i].value, len);
      s->status_code = atoi(buf);
      break;
    }
  }
  
  // Read body via data provider
  if (data_prd && data_prd->read_callback) {
    uint8_t buf[4096];
    uint32_t flags = 0;
    ssize_t nread;
    
    while ((nread = data_prd->read_callback(session, stream_id, buf, sizeof(buf),
                                             &flags, (nghttp2_data_source *)&data_prd->source,
                                             session->user_data)) > 0) {
      size_t new_len = s->response_body_len + (size_t)nread;
      if (new_len > s->response_body_cap) {
        size_t new_cap = s->response_body_cap == 0 ? 4096 : s->response_body_cap * 2;
        while (new_cap < new_len) new_cap *= 2;
        s->response_body = realloc(s->response_body, new_cap);
        s->response_body_cap = new_cap;
      }
      memcpy(s->response_body + s->response_body_len, buf, (size_t)nread);
      s->response_body_len += (size_t)nread;
      
      if (flags & 0x01) break;  // EOF
    }
  }
  
  session->want_write = true;
  return 0;
}

int nghttp2_submit_response(nghttp2_session *session, int32_t stream_id,
                            const nghttp2_nv *nva, size_t nvlen,
                            const nghttp2_data_provider *data_prd) {
  // Convert to data_provider2 format
  nghttp2_data_provider2 dp2 = {0};
  if (data_prd) {
    dp2.source = data_prd->source;
    dp2.read_callback = (nghttp2_data_source_read_callback2)data_prd->read_callback;
  }
  return nghttp2_submit_response2(session, stream_id, nva, nvlen, 
                                   data_prd ? &dp2 : NULL);
}

int32_t nghttp2_submit_request2(nghttp2_session *session,
                                 const void *pri_spec,
                                 const nghttp2_nv *nva, size_t nvlen,
                                 const nghttp2_data_provider2 *data_prd,
                                 void *stream_user_data) {
  (void)pri_spec;
  (void)data_prd;
  
  int32_t stream_id = session->next_stream_id;
  session->next_stream_id += 2;
  
  fake_stream_t *s = create_stream(session, stream_id);
  if (!s) return -1;
  
  s->user_data = stream_user_data;
  s->response_headers = malloc(sizeof(nghttp2_nv) * nvlen);
  memcpy(s->response_headers, nva, sizeof(nghttp2_nv) * nvlen);
  s->response_nheaders = nvlen;
  
  return stream_id;
}

int32_t nghttp2_submit_request(nghttp2_session *session,
                                const void *pri_spec,
                                const nghttp2_nv *nva, size_t nvlen,
                                const nghttp2_data_provider *data_prd,
                                void *stream_user_data) {
  nghttp2_data_provider2 dp2 = {0};
  if (data_prd) {
    dp2.source = data_prd->source;
    dp2.read_callback = (nghttp2_data_source_read_callback2)data_prd->read_callback;
  }
  return nghttp2_submit_request2(session, pri_spec, nva, nvlen,
                                  data_prd ? &dp2 : NULL, stream_user_data);
}

int nghttp2_submit_rst_stream(nghttp2_session *session, uint8_t flags,
                               int32_t stream_id, uint32_t error_code) {
  (void)flags;
  (void)error_code;
  
  fake_stream_t *s = find_stream(session, stream_id);
  if (s) s->closed = true;
  return 0;
}

int nghttp2_submit_goaway(nghttp2_session *session, uint8_t flags,
                           int32_t last_stream_id, uint32_t error_code,
                           const uint8_t *opaque_data, size_t opaque_data_len) {
  (void)session;
  (void)flags;
  (void)last_stream_id;
  (void)error_code;
  (void)opaque_data;
  (void)opaque_data_len;
  return 0;
}

const char *nghttp2_strerror(int lib_error_code) {
  (void)lib_error_code;
  return "fake error";
}

// Test control implementation
int32_t nghttp2_fake_inject_request(nghttp2_session *session,
                                     const char *method,
                                     const char *path,
                                     const nghttp2_nv *extra_headers,
                                     size_t nextra,
                                     const uint8_t *body,
                                     size_t body_len) {
  int32_t stream_id = session->next_stream_id;
  session->next_stream_id += 2;
  
  // Create stream
  create_stream(session, stream_id);
  
  // Build frame header
  nghttp2_frame frame = {0};
  frame.hd.stream_id = stream_id;
  frame.hd.type = NGHTTP2_HEADERS;
  
  // Trigger on_begin_headers
  if (session->cbs.on_begin_headers) {
    session->cbs.on_begin_headers(session, &frame, session->user_data);
  }
  
  // Trigger on_header for pseudo-headers
  if (session->cbs.on_header) {
    session->cbs.on_header(session, &frame,
                           (uint8_t *)":method", 7,
                           (uint8_t *)method, strlen(method),
                           0, session->user_data);
    session->cbs.on_header(session, &frame,
                           (uint8_t *)":path", 5,
                           (uint8_t *)path, strlen(path),
                           0, session->user_data);
    session->cbs.on_header(session, &frame,
                           (uint8_t *)":scheme", 7,
                           (uint8_t *)"https", 5,
                           0, session->user_data);
    
    // Extra headers
    for (size_t i = 0; i < nextra; i++) {
      session->cbs.on_header(session, &frame,
                             extra_headers[i].name, extra_headers[i].namelen,
                             extra_headers[i].value, extra_headers[i].valuelen,
                             0, session->user_data);
    }
  }
  
  // Trigger on_data if body present
  if (body && body_len > 0 && session->cbs.on_data_chunk_recv) {
    session->cbs.on_data_chunk_recv(session, 0, stream_id, body, body_len,
                                     session->user_data);
  }
  
  // Trigger frame recv for END_HEADERS + END_STREAM
  if (session->cbs.on_frame_recv) {
    frame.hd.flags = NGHTTP2_FLAG_END_HEADERS;
    if (!body || body_len == 0) {
      frame.hd.flags |= NGHTTP2_FLAG_END_STREAM;
    }
    session->cbs.on_frame_recv(session, &frame, session->user_data);
    
    if (body && body_len > 0) {
      // Send DATA frame with END_STREAM
      frame.hd.type = NGHTTP2_DATA;
      frame.hd.flags = NGHTTP2_FLAG_END_STREAM;
      session->cbs.on_frame_recv(session, &frame, session->user_data);
    }
  }
  
  return stream_id;
}

bool nghttp2_fake_get_response(nghttp2_session *session, int32_t stream_id,
                                nghttp2_fake_response_t *response) {
  fake_stream_t *s = find_stream(session, stream_id);
  if (!s || s->status_code == 0) return false;
  
  response->status_code = s->status_code;
  response->headers = s->response_headers;
  response->nheaders = s->response_nheaders;
  response->body = s->response_body;
  response->body_len = s->response_body_len;
  response->closed = s->closed;
  
  return true;
}

size_t nghttp2_fake_stream_count(nghttp2_session *session) {
  size_t count = 0;
  fake_stream_t *s = session->streams;
  while (s) {
    count++;
    s = s->next;
  }
  return count;
}
```

### Phase 3 Verification

- [ ] Request injection triggers correct callbacks
- [ ] Response submission captures headers and body
- [ ] Stream user data works correctly
- [ ] RST_STREAM/GOAWAY handled

---

## Phase 4: Integration Tests

**Goal**: Write comprehensive tests using both fakes together.

**Duration**: 3-4 days

**Depends on**: Phase 3

### Deliverable 4.1: Full Request/Response Test

```c
VALK_TEST(full_http2_request_response) {
  // Setup
  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_fake_reset(&loop);
  
  valk_aio_system_t *sys = valk_aio_start(&loop, &valk_aio_config_minimal());
  
  // Start server
  valk_aio_http_server *srv;
  valk_aio_http_listen(sys, "127.0.0.1", 8080, test_handler, &srv);
  
  // Inject client connection
  uv_tcp_t fake_client;
  uv_tcp_init(&loop, &fake_client);
  uv_fake_inject_connection(&srv->listener, &fake_client);
  uv_fake_process_io(&loop);
  
  // Get the HTTP/2 session for this connection
  nghttp2_session *session = get_connection_session(srv);
  
  // Inject HTTP/2 request
  int32_t stream_id = nghttp2_fake_inject_request(
    session, "GET", "/test",
    NULL, 0,   // no extra headers
    NULL, 0    // no body
  );
  
  // Process
  uv_fake_time_advance(&loop, 0);
  
  // Verify response
  nghttp2_fake_response_t resp;
  VALK_ASSERT(nghttp2_fake_get_response(session, stream_id, &resp));
  VALK_ASSERT_EQ(resp.status_code, 200);
  
  valk_aio_stop(sys);
}
```

### Deliverable 4.2: Timeout Test

```c
VALK_TEST(connection_times_out) {
  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_fake_reset(&loop);
  
  valk_aio_system_config_t cfg = valk_aio_config_minimal();
  cfg.connection_idle_timeout_ms = 5000;
  
  valk_aio_system_t *sys = valk_aio_start(&loop, &cfg);
  valk_aio_http_server *srv;
  valk_aio_http_listen(sys, "127.0.0.1", 8080, test_handler, &srv);
  
  // Connect
  uv_tcp_t fake_client;
  uv_tcp_init(&loop, &fake_client);
  uv_fake_inject_connection(&srv->listener, &fake_client);
  uv_fake_process_io(&loop);
  
  VALK_ASSERT_EQ(srv->connection_count, 1);
  
  // Advance time past timeout
  uv_fake_time_advance(&loop, 6000);
  
  // Connection should be closed
  VALK_ASSERT_EQ(srv->connection_count, 0);
  
  valk_aio_stop(sys);
}
```

### Phase 4 Verification

- [ ] End-to-end request/response works
- [ ] Timeouts trigger correctly
- [ ] Multiple concurrent streams work
- [ ] Error handling (RST_STREAM, GOAWAY) works

---

## Phase 5: SSE Testing

**Goal**: Test SSE streams using the fake infrastructure.

**Duration**: 2-3 days

**Depends on**: Phase 4

### Deliverable 5.1: SSE Test Helpers

```c
// Get SSE events written to a stream
typedef struct {
  char *event;
  char *data;
  char *id;
} sse_event_t;

size_t nghttp2_fake_get_sse_events(nghttp2_session *session, 
                                    int32_t stream_id,
                                    sse_event_t *events, 
                                    size_t max_events);
```

### Deliverable 5.2: SSE Stream Tests

```c
VALK_TEST(sse_stream_sends_events) {
  // Setup...
  
  // Start SSE endpoint
  int32_t stream_id = nghttp2_fake_inject_request(
    session, "GET", "/events", NULL, 0, NULL, 0);
  
  uv_fake_time_advance(&loop, 0);
  
  // Trigger some events
  valk_sse_send(sse_stream, "update", "{\"count\": 1}");
  valk_sse_send(sse_stream, "update", "{\"count\": 2}");
  
  uv_fake_time_advance(&loop, 0);
  
  // Check SSE output
  sse_event_t events[10];
  size_t n = nghttp2_fake_get_sse_events(session, stream_id, events, 10);
  
  VALK_ASSERT_EQ(n, 2);
  VALK_ASSERT_STREQ(events[0].event, "update");
  VALK_ASSERT_STREQ(events[0].data, "{\"count\": 1}");
}
```

---

## Summary

| Phase | Deliverables | Duration | Dependencies |
|-------|--------------|----------|--------------|
| 1 | libuv fake timers | 2-3 days | None |
| 2 | libuv fake TCP | 3-4 days | Phase 1 |
| 3 | nghttp2 fake | 4-5 days | Phase 2 |
| 4 | Integration tests | 3-4 days | Phase 3 |
| 5 | SSE testing | 2-3 days | Phase 4 |

**Total**: 14-19 days

### Success Criteria

1. **Zero Production Overhead** - No changes to production code paths
2. **Testability** - 80%+ of AIO code paths testable without real I/O
3. **Determinism** - All tests are deterministic (no timing dependencies)
4. **Coverage** - AIO coverage increases from ~65% to ~85%

### Key Benefits of Link-Time Approach

| Aspect | Vtable Approach | Link-Time Approach |
|--------|-----------------|---------------------|
| Production overhead | Pointer chase per call | Zero |
| Struct sizes | Must match or use allocation | Independent |
| Code changes | Requires abstraction layer | None |
| Build complexity | Low | Medium (separate test build) |
| Test realism | Lower (different code paths) | Higher (same code paths) |

### Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| API drift | Fake headers generated from real headers where possible |
| Missing behavior | Document known limitations, add as needed |
| Build complexity | Clear CMake structure, CI validation |
| Incomplete fakes | Implement only what AIO actually uses |
