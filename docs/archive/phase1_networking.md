# Phase 1: Complete Networking

**Duration**: 2 weeks
**Status**: Not started
**Goal**: Finish HTTP/2 server with Lisp handlers

## Prerequisites

- Phase 0 complete (continuations working)
- Async I/O using continuations
- No remaining ARCs

## Implementation Plan

### Week 7: HTTP/2 Server Handlers

**Files to modify**:
- `src/aio_uv.c`: Expose server handlers to Lisp
- `src/parser.c`: Add HTTP server builtins

**New builtins**:
```lisp
(http-listen port handler)
(http-respond conn status headers body)
(http-request-body request)
(http-request-headers request)
```

**Example server**:
```lisp
(http-listen 8080
  (lambda (req)
    (reset
      (let* ((body (await (http-request-body req)))
             (result (process body)))
        (http-respond req 200 {} result)))))
```

**Deliverable**: Working HTTP/2 server in Lisp

### Week 8: Validation Application

**Build real app**:
- REST API with routing
- Database integration
- WebSocket support
- Load testing

**Example**:
```lisp
(def {app} (router
  (GET "/" home-handler)
  (POST "/api/users" create-user)
  (GET "/ws" websocket-handler)))

(http-listen 8080 app)
```

**Performance targets**:
- 10K concurrent connections
- <10ms latency for simple requests
- Full HTTP/2 compliance

**Deliverable**: Production web service running

## Success Criteria

- [ ] HTTP/2 server fully functional
- [ ] WebSocket support working
- [ ] Streaming with backpressure
- [ ] Real app deployed and tested
- [ ] Performance targets met

## Next Phase

[Phase 2: Bytecode Compiler](phase2_bytecode.md)