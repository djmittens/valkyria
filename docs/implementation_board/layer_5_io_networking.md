# Layer 5: I/O & Networking

**Status**: libuv, HTTP/2 client complete; server partial

**Timeline**: ~1-2 months

---

## Current State

### Complete ✓
- [x] libuv integration (backend)
- [x] Event loop (`uv_run`)
- [x] Async callbacks (non-blocking)
- [x] TLS/SSL (OpenSSL)
- [x] Test certificates (in `build/`)
- [x] HTTP/2 Client (nghttp2)
- [x] Request/Response objects
- [x] High-level HTTP API (40+ functions)
- [x] HTTP/2 Server (C API works)

### Remaining Work
- [ ] Lisp Server API (S - 1-3 days) - **HIGH PRIORITY**
- [ ] HTTP Routing (M - 1-2 weeks)
- [ ] WebSocket support (M - 1-2 weeks)
- [ ] Streaming (M - 1-2 weeks)

---

## Feature 1: Lisp Server API (S - 1-3 days)

**Unlocks**: Write HTTP servers in Valk Lisp

**Status**: C API exists, needs Lisp bindings

### Tasks

- [ ] **5.1: Server Object** (2-3 hours)
  - Wrap C server handle in `LVAL_REF`
  - `(http-server-create port)` - create server
  - **File**: `src/modules/http.valk` or `src/parser.c` (builtin)
  - **Test**: Create server object

- [ ] **5.2: Request Handler** (3-4 hours)
  - `(http-server-on-request server handler-fn)`
  - Handler receives request object, returns response
  - Example:
    ```lisp
    (http-server-on-request srv
      (lambda (req)
        {:status 200
         :headers {"content-type" "text/plain"}
         :body "Hello!"}))
    ```
  - **Test**: Handler called on request

- [ ] **5.3: Server Start/Stop** (2 hours)
  - `(http-server-start server)` - start listening
  - `(http-server-stop server)` - graceful shutdown
  - **Test**: Start server, connect, stop server

- [ ] **5.4: Example Server** (1-2 hours)
  - Create `examples/hello_server.valk`
  - Simple HTTP server responding to requests
  - **Documentation**: Document API

---

## Feature 2: HTTP Routing (M - 1-2 weeks)

**Unlocks**: Build web applications with routes

### Tasks

- [ ] **5.5: Route Matching** (3-4 days)
  - Match URL patterns: `/users/:id`, `/posts/*path`
  - Extract path parameters
  - **Algorithm**: Trie-based router or regex
  - **Test**: Match routes, extract params

- [ ] **5.6: Method Routing** (1-2 days)
  - Route by HTTP method: GET, POST, PUT, DELETE
  - **Test**: Different handlers for GET vs POST

- [ ] **5.7: Middleware** (3-4 days)
  - Composable request/response processing
  - Example: logging, auth, CORS
  - **API**:
    ```lisp
    (use-middleware server logging-middleware)
    (use-middleware server auth-middleware)
    ```
  - **Test**: Middleware chain execution

- [ ] **5.8: Router Example** (1-2 days)
  - Create `examples/rest_api.valk`
  - RESTful API with routes
  - **Documentation**: Routing guide

---

## Feature 3: WebSocket Support (M - 1-2 weeks)

**Unlocks**: Real-time bidirectional communication

### Tasks

- [ ] **5.9: WebSocket Handshake** (3-4 days)
  - Upgrade HTTP connection to WebSocket
  - **Protocol**: RFC 6455
  - **Library**: libwebsockets or custom implementation
  - **Test**: Handshake succeeds

- [ ] **5.10: WebSocket Send/Receive** (2-3 days)
  - `(ws-send conn message)` - send message
  - `(ws-on-message conn handler)` - receive handler
  - **Test**: Bidirectional communication

- [ ] **5.11: WebSocket Close** (1-2 days)
  - Graceful close handshake
  - **Test**: Close connection

- [ ] **5.12: WebSocket Example** (1-2 days)
  - Chat server example
  - **Documentation**: WebSocket guide

---

## Feature 4: Streaming (M - 1-2 weeks)

**Unlocks**: Efficient handling of large data

### Tasks

- [ ] **5.13: Stream Abstraction** (2-3 days)
  - Readable/writable stream interface
  - Backpressure handling
  - **Test**: Create stream

- [ ] **5.14: HTTP Streaming** (3-4 days)
  - Chunked transfer encoding
  - Stream response bodies
  - **Test**: Stream large file

- [ ] **5.15: Transform Streams** (2-3 days)
  - Composable stream transformations
  - Example: gzip compression
  - **Test**: Pipe streams

- [ ] **5.16: Streaming Example** (1-2 days)
  - Video streaming server
  - **Documentation**: Streaming guide

---

## Resources

- libuv docs: https://docs.libuv.org/
- nghttp2 docs: https://nghttp2.org/documentation/
- WebSocket RFC 6455: https://tools.ietf.org/html/rfc6455
- HTTP/2 RFC 7540: https://tools.ietf.org/html/rfc7540
