# Request Context Design: Finagle-Style Context Propagation

## Executive Summary

This document describes the design for Finagle-style request contexts in Valkyria. Request contexts carry deadline, tracing, and local storage through async operation graphs, enabling:

1. **Deadline propagation** - Child operations inherit remaining time budget
2. **Distributed tracing** - Trace/span IDs flow through service calls
3. **Request-scoped storage** - Arbitrary key-value data per request
4. **Automatic timeout** - Operations fail when deadline exceeded

---

## Table of Contents

1. [Motivation](#1-motivation)
2. [Design Overview](#2-design-overview)
3. [Data Structures](#3-data-structures)
4. [Propagation Semantics](#4-propagation-semantics)
5. [Lisp API](#5-lisp-api)
6. [HTTP Header Propagation](#6-http-header-propagation)
7. [Implementation Plan](#7-implementation-plan)
8. [Test Plan](#8-test-plan)

---

## 1. Motivation

### 1.1 Current State

Valkyria has foundational async infrastructure:

| Feature | Status | Notes |
|---------|--------|-------|
| Memory scoping | Done | Region propagates through async handles |
| Parent-child tracking | Done | Handle tree for combinators |
| Cancellation | Done | `cancel_requested` flag + callbacks |
| Environment propagation | Done | Lisp env flows through handles |
| Request metrics | Basic | `start_time_us`, bytes sent/recv |

### 1.2 Missing Capabilities

| Feature | Impact |
|---------|--------|
| **Deadlines** | Can't enforce end-to-end latency SLOs |
| **Tracing** | Can't debug distributed request flow |
| **Local storage** | Can't pass request-scoped data implicitly |
| **Timeout inheritance** | Child ops don't know remaining budget |

### 1.3 Finagle Inspiration

Twitter's Finagle library provides `Local` context that propagates through `Future` chains:

```scala
// Finagle (Scala)
Deadline.let(deadline) {
  // All nested operations inherit this deadline
  client.get("/api").flatMap { resp =>
    // Remaining deadline automatically applied
    db.query("SELECT ...")
  }
}
```

We want equivalent semantics in Valkyria:

```lisp
; Valkyria (Lisp)
(ctx/with-deadline 5000
  ; All nested operations inherit this deadline
  (aio/then (http/get "/api")
    (lambda (resp)
      ; Remaining deadline automatically applied
      (db/query "SELECT ..."))))
```

---

## 2. Design Overview

### 2.1 Architecture

```
                    valk_request_ctx_t
                   ┌─────────────────────────────────────┐
                   │ trace_id: u64                       │
                   │ span_id: u64                        │
                   │ parent_span_id: u64                 │
                   │ deadline_us: u64 (absolute)         │
                   │ locals: valk_lval_t* (alist)        │
                   │ allocator: valk_mem_allocator_t*    │
                   └─────────────────────────────────────┘
                              │
                              │ stored in
                              ▼
                    valk_async_handle_t
                   ┌─────────────────────────────────────┐
                   │ ...existing fields...               │
                   │ request_ctx: valk_request_ctx_t*    │◄── NEW
                   └─────────────────────────────────────┘
```

### 2.2 Key Principles

1. **Immutable context** - Context is copied on modification, never mutated
2. **Automatic propagation** - Child handles inherit parent context
3. **Zero-cost when unused** - `request_ctx` is NULL if no context set
4. **Region-allocated** - Context structs live in request region
5. **Deadline is absolute** - Stored as microseconds since epoch, not relative

### 2.3 Propagation Flow

```
HTTP request arrives
  │
  ├── Create request context:
  │     trace_id = extract from headers or generate
  │     span_id = generate new
  │     deadline_us = now_us + timeout_ms * 1000
  │     locals = nil
  │
  └── VALK_WITH_ALLOC(stream_region) {
        │
        ├── Handler calls (aio/then ...)
        │     └── Child handle created
        │           └── request_ctx = copy from parent
        │
        ├── Handler calls (ctx/with-deadline 1000 ...)
        │     └── New context with updated deadline
        │           └── deadline_us = min(parent.deadline, now + 1000ms)
        │
        └── Timer/HTTP ops check deadline before work
              └── If past deadline, fail with :timeout error
      }
```

---

## 3. Data Structures

### 3.1 Request Context Structure

```c
// src/aio/aio_request_ctx.h

typedef struct valk_request_ctx {
  u64 trace_id;
  u64 span_id;
  u64 parent_span_id;
  u64 deadline_us;                    // Absolute deadline (0 = no deadline)
  struct valk_lval_t *locals;         // Alist of (key . value) pairs
  valk_mem_allocator_t *allocator;    // For allocating copies
} valk_request_ctx_t;

// Special value: no deadline set
#define VALK_NO_DEADLINE 0

// Check if deadline has passed
static inline bool valk_request_ctx_deadline_exceeded(valk_request_ctx_t *ctx) {
  if (!ctx || ctx->deadline_us == VALK_NO_DEADLINE) return false;
  return valk_time_now_us() > ctx->deadline_us;
}

// Get remaining time in milliseconds (0 if no deadline or expired)
static inline u64 valk_request_ctx_remaining_ms(valk_request_ctx_t *ctx) {
  if (!ctx || ctx->deadline_us == VALK_NO_DEADLINE) return UINT64_MAX;
  u64 now = valk_time_now_us();
  if (now >= ctx->deadline_us) return 0;
  return (ctx->deadline_us - now) / 1000;
}
```

### 3.2 Async Handle Extension

```c
// In valk_async_handle_t (src/aio/aio.h)

struct valk_async_handle_t {
  // ...existing fields...

  // Request context (propagated from parent, may be NULL)
  valk_request_ctx_t *request_ctx;
};
```

### 3.3 Time Utilities

```c
// src/time.h (new file or extend existing)

// Get current time in microseconds since epoch
u64 valk_time_now_us(void);

// Get current time in milliseconds since epoch
u64 valk_time_now_ms(void);
```

---

## 4. Propagation Semantics

### 4.1 Context Inheritance Rules

| Scenario | Behavior |
|----------|----------|
| Child handle created | Inherits parent's `request_ctx` pointer (shared) |
| `ctx/with-deadline` | Creates new context with tighter deadline |
| `ctx/with-timeout` | Creates new context with deadline = now + timeout |
| `ctx/set` | Creates new context with updated locals |
| Combinator (`aio/all`, etc.) | All children inherit context |
| HTTP outbound request | Serializes trace IDs to headers |
| HTTP inbound request | Deserializes trace IDs from headers |

### 4.2 Deadline Inheritance

Deadlines can only get tighter, never looser:

```c
valk_request_ctx_t *valk_request_ctx_with_deadline(
    valk_request_ctx_t *parent,
    u64 deadline_us,
    valk_mem_allocator_t *allocator) {

  valk_request_ctx_t *ctx = valk_mem_allocator_alloc(allocator, sizeof(valk_request_ctx_t));
  if (parent) {
    *ctx = *parent;  // Copy all fields
  } else {
    memset(ctx, 0, sizeof(*ctx));
  }

  // Take the tighter deadline
  if (ctx->deadline_us == VALK_NO_DEADLINE || deadline_us < ctx->deadline_us) {
    ctx->deadline_us = deadline_us;
  }

  ctx->allocator = allocator;
  return ctx;
}
```

### 4.3 Span ID Generation

Each operation that creates a new "span" (HTTP request, significant async boundary) generates a new span_id:

```c
valk_request_ctx_t *valk_request_ctx_new_span(
    valk_request_ctx_t *parent,
    valk_mem_allocator_t *allocator) {

  valk_request_ctx_t *ctx = valk_mem_allocator_alloc(allocator, sizeof(valk_request_ctx_t));

  if (parent) {
    ctx->trace_id = parent->trace_id;
    ctx->parent_span_id = parent->span_id;
    ctx->deadline_us = parent->deadline_us;
    ctx->locals = parent->locals;
  } else {
    ctx->trace_id = valk_trace_id_generate();
    ctx->parent_span_id = 0;
    ctx->deadline_us = VALK_NO_DEADLINE;
    ctx->locals = nullptr;
  }

  ctx->span_id = valk_span_id_generate();
  ctx->allocator = allocator;
  return ctx;
}
```

### 4.4 Deadline Checking Integration Points

Deadline must be checked at key points:

| Location | Action on Deadline Exceeded |
|----------|----------------------------|
| `aio/delay` timer start | Fail immediately with `:deadline-exceeded` |
| HTTP client request start | Fail immediately with `:deadline-exceeded` |
| Combinator child creation | Fail immediately with `:deadline-exceeded` |
| Async handle completion | No-op (already succeeded) |

---

## 5. Lisp API

### 5.1 Deadline Builtins

```lisp
; Set absolute deadline (ms from now) for nested operations
; Returns result of body, or fails with :deadline-exceeded if timeout
(ctx/with-deadline timeout-ms body...)

; Equivalent but more explicit name
(ctx/with-timeout timeout-ms body...)

; Get remaining time until deadline (nil if no deadline)
(ctx/deadline) ; => milliseconds or nil

; Check if deadline exceeded
(ctx/deadline-exceeded?) ; => true/false
```

### 5.2 Local Storage Builtins

```lisp
; Get value from request-scoped locals (nil if not set)
(ctx/get key) ; => value or nil

; Set value in request-scoped locals (returns new context)
; Note: This creates a new context, doesn't mutate
(ctx/with key value body...)

; Get all locals as alist
(ctx/locals) ; => ((key1 . val1) (key2 . val2) ...)
```

### 5.3 Tracing Builtins

```lisp
; Get current trace ID (nil if no context)
(trace/id) ; => integer or nil

; Get current span ID (nil if no context)
(trace/span) ; => integer or nil

; Get parent span ID (nil if root span)
(trace/parent-span) ; => integer or nil

; Create new span (generates new span_id, keeps trace_id)
(trace/with-span name body...)
```

### 5.4 Usage Examples

```lisp
; HTTP handler with timeout enforcement
(defn handle-api-request (req k)
  (ctx/with-deadline 5000  ; 5 second deadline for entire request
    (aio/then (db/query "SELECT * FROM users")
      (lambda (users)
        (aio/then (cache/get "config")
          (lambda (config)
            ; Both db query and cache get share the 5s deadline
            (k {:status "200" :body (process users config)})))))))

; Passing request-scoped data
(defn handle-request (req k)
  (ctx/with :user-id (get-header req "X-User-ID")
    (ctx/with :request-id (uuid)
      (aio/then (do-work)
        (lambda (result)
          ; Inner code can access user-id and request-id
          (log "User" (ctx/get :user-id) "completed request" (ctx/get :request-id))
          (k result))))))

; Manual tracing
(defn call-downstream (req)
  (trace/with-span "downstream-call"
    (http/request
      {:url "https://api.example.com/data"
       :headers {"X-Trace-ID" (trace/id)
                 "X-Span-ID" (trace/span)
                 "X-Parent-Span-ID" (trace/parent-span)}})))
```

---

## 6. HTTP Header Propagation

### 6.1 Standard Headers

We follow the W3C Trace Context standard where practical:

| Header | Format | Description |
|--------|--------|-------------|
| `X-Trace-ID` | hex string (16 chars) | 64-bit trace identifier |
| `X-Span-ID` | hex string (16 chars) | 64-bit span identifier |
| `X-Parent-Span-ID` | hex string (16 chars) | Parent span (for nesting) |
| `X-Deadline-Ms` | decimal integer | Remaining deadline in ms |

### 6.2 Inbound Request Handling

```c
valk_request_ctx_t *valk_request_ctx_from_http_headers(
    valk_http2_server_request_t *req,
    u64 default_timeout_ms,
    valk_mem_allocator_t *allocator) {

  valk_request_ctx_t *ctx = valk_mem_allocator_alloc(allocator, sizeof(valk_request_ctx_t));
  memset(ctx, 0, sizeof(*ctx));

  // Extract trace ID from header or generate
  const char *trace_id_str = valk_http2_get_header(req, "X-Trace-ID");
  ctx->trace_id = trace_id_str ? valk_parse_hex_u64(trace_id_str) : valk_trace_id_generate();

  // Extract parent span ID (our span becomes child of this)
  const char *parent_span_str = valk_http2_get_header(req, "X-Span-ID");
  ctx->parent_span_id = parent_span_str ? valk_parse_hex_u64(parent_span_str) : 0;

  // Generate new span for this request
  ctx->span_id = valk_span_id_generate();

  // Calculate deadline from header or default
  const char *deadline_str = valk_http2_get_header(req, "X-Deadline-Ms");
  u64 remaining_ms = deadline_str ? valk_parse_u64(deadline_str) : default_timeout_ms;
  ctx->deadline_us = remaining_ms ? valk_time_now_us() + (remaining_ms * 1000) : VALK_NO_DEADLINE;

  ctx->locals = nullptr;
  ctx->allocator = allocator;
  return ctx;
}
```

### 6.3 Outbound Request Handling

```c
void valk_request_ctx_to_http_headers(
    valk_request_ctx_t *ctx,
    valk_http2_request_t *req) {

  if (!ctx) return;

  char buf[32];

  // Trace ID
  snprintf(buf, sizeof(buf), "%016llx", (unsigned long long)ctx->trace_id);
  valk_http2_add_header(req, "X-Trace-ID", buf);

  // Span ID (becomes parent for downstream)
  snprintf(buf, sizeof(buf), "%016llx", (unsigned long long)ctx->span_id);
  valk_http2_add_header(req, "X-Span-ID", buf);

  // Remaining deadline
  if (ctx->deadline_us != VALK_NO_DEADLINE) {
    u64 remaining_ms = valk_request_ctx_remaining_ms(ctx);
    snprintf(buf, sizeof(buf), "%llu", (unsigned long long)remaining_ms);
    valk_http2_add_header(req, "X-Deadline-Ms", buf);
  }
}
```

---

## 7. Implementation Plan

### Phase 1: Core Infrastructure

- [ ] **1.1** Create `src/aio/aio_request_ctx.h` with struct definition
- [ ] **1.2** Create `src/aio/aio_request_ctx.c` with allocation/copy functions
- [ ] **1.3** Add `valk_time_now_us()` utility function
- [ ] **1.4** Add `request_ctx` field to `valk_async_handle_t`
- [ ] **1.5** Update `valk_async_handle_new()` to initialize `request_ctx = NULL`

### Phase 2: Context Propagation

- [ ] **2.1** Update `valk_async_propagate_region()` to also propagate `request_ctx`
- [ ] **2.2** Update combinator context creation to inherit `request_ctx`
- [ ] **2.3** Update `aio/then` to propagate `request_ctx`
- [ ] **2.4** Add deadline check at async handle creation

### Phase 3: Lisp Builtins - Deadline

- [ ] **3.1** Implement `ctx/with-deadline` builtin
- [ ] **3.2** Implement `ctx/with-timeout` builtin (alias)
- [ ] **3.3** Implement `ctx/deadline` builtin
- [ ] **3.4** Implement `ctx/deadline-exceeded?` builtin
- [ ] **3.5** Add deadline check to `aio/delay` timer creation
- [ ] **3.6** Add deadline check to HTTP client request

### Phase 4: Lisp Builtins - Locals

- [ ] **4.1** Implement `ctx/get` builtin
- [ ] **4.2** Implement `ctx/with` builtin
- [ ] **4.3** Implement `ctx/locals` builtin

### Phase 5: Lisp Builtins - Tracing

- [ ] **5.1** Implement `trace/id` builtin
- [ ] **5.2** Implement `trace/span` builtin
- [ ] **5.3** Implement `trace/parent-span` builtin
- [ ] **5.4** Implement `trace/with-span` builtin
- [ ] **5.5** Add trace ID generation functions

### Phase 6: HTTP Integration

- [ ] **6.1** Extract trace context from inbound HTTP headers
- [ ] **6.2** Create request context for each HTTP request
- [ ] **6.3** Propagate trace context to outbound HTTP requests
- [ ] **6.4** Log trace/span IDs in request metrics

### Phase 7: Combinator Timeout Support

- [ ] **7.1** Add optional timeout parameter to `aio/all`
- [ ] **7.2** Add optional timeout parameter to `aio/race`
- [ ] **7.3** Add optional timeout parameter to `aio/any`

### Phase 8: Testing

- [ ] **8.1** Unit tests for context creation/propagation
- [ ] **8.2** Unit tests for deadline enforcement
- [ ] **8.3** Integration tests for HTTP header propagation
- [ ] **8.4** Stress tests for deadline under load

---

## 8. Test Plan

### 8.1 Unit Tests

| Test ID | Description | Validates |
|---------|-------------|-----------|
| CTX-01 | Create context with deadline, verify remaining_ms | Deadline tracking |
| CTX-02 | Context copy preserves all fields | Copy semantics |
| CTX-03 | Deadline inheritance takes tighter deadline | Deadline rules |
| CTX-04 | Span ID changes, trace ID preserved on new_span | Tracing |
| CTX-05 | Locals get/set work correctly | Local storage |
| CTX-06 | NULL context handling in all functions | Safety |

### 8.2 Async Integration Tests

| Test ID | Description | Validates |
|---------|-------------|-----------|
| ASYNC-01 | Child handle inherits parent context | Propagation |
| ASYNC-02 | `aio/then` chain propagates context | Combinator propagation |
| ASYNC-03 | `aio/all` children inherit context | Combinator propagation |
| ASYNC-04 | Deadline exceeded fails operation | Deadline enforcement |
| ASYNC-05 | Timer respects remaining deadline | Deadline enforcement |

### 8.3 HTTP Integration Tests

| Test ID | Description | Validates |
|---------|-------------|-----------|
| HTTP-01 | Inbound request extracts trace headers | Header parsing |
| HTTP-02 | Outbound request sends trace headers | Header serialization |
| HTTP-03 | Deadline header propagated to downstream | End-to-end deadline |
| HTTP-04 | Missing headers generate new trace ID | Fallback behavior |

### 8.4 Lisp API Tests

| Test ID | Description | Validates |
|---------|-------------|-----------|
| LISP-01 | `(ctx/with-deadline 100 ...)` sets deadline | Builtin |
| LISP-02 | `(ctx/deadline)` returns remaining ms | Builtin |
| LISP-03 | `(ctx/get :key)` returns stored value | Builtin |
| LISP-04 | `(trace/id)` returns trace ID | Builtin |
| LISP-05 | Nested `ctx/with-deadline` takes tighter | Nesting |

---

## Appendix A: Comparison with Finagle

| Feature | Finagle | Valkyria |
|---------|---------|----------|
| Context storage | `Local[T]` thread-local | `request_ctx` on async handle |
| Propagation | Implicit via `Future` | Explicit in handle creation |
| Deadline | `Deadline.current` | `ctx->deadline_us` |
| Trace ID | Zipkin integration | Simple u64, header propagation |
| Locals | `Contexts.local` | Alist in `ctx->locals` |
| Timeout API | `Future.within(duration)` | `ctx/with-deadline` |

---

## Appendix B: Thread Safety

Request context is designed for single-threaded access within the event loop:

1. **Creation** - Context created on event loop thread when request arrives
2. **Propagation** - Pointer copied when child handles created (same thread)
3. **Access** - Builtins read context on event loop thread
4. **Mutation** - Never mutated; new context created for modifications

No locking required because:
- HTTP requests are processed single-threaded per connection
- Async handles execute callbacks on the event loop that created them
- Context pointers are only copied, never shared mutably

---

## Appendix C: Memory Management

Context structs are region-allocated:

```c
// Context lives in request region
valk_request_ctx_t *ctx = valk_mem_alloc(sizeof(valk_request_ctx_t));

// When request completes, region is destroyed
// All contexts in region are freed together
```

Benefits:
- No individual frees needed
- No reference counting
- Automatic cleanup on request completion
- Efficient bulk deallocation
