# Networking Branch - Completion Tasks

## Current State

✅ **Working:**
- HTTP/2 client connecting to external servers (google.com test passes)
- HTTP/2 server listening and accepting TLS connections
- Async I/O with futures and await
- Basic error handling (connection failures, RST_STREAM)
- Server/client integration test passing
- Memory management with arenas

⚠️ **Incomplete:**
- Server cannot handle custom request handlers from Lisp
- No test framework primitives in Lisp
- No REPL crash safety mechanisms
- Several networking TODOs in codebase
- Missing higher-level HTTP conveniences
- No API documentation

## Tasks to Complete Networking Branch

### 1. Server Request Handler API ⭐ CRITICAL

**Problem**: Server accepts connections but cannot call Lisp functions to handle requests.

**Current state**: `valk_http2_demo_handler` is an empty struct, server just returns hardcoded response.

**What's needed**:
- [ ] Define Lisp callback signature for request handlers: `(fn (req) -> response)`
- [ ] Create request object in Lisp with methods: `(http2/request-method req)`, `(http2/request-path req)`, `(http2/request-headers req)`, `(http2/request-body req)`
- [ ] Create response builder: `(http2/response :status 200 :headers {...} :body "...")`
- [ ] Wire up the C handler callbacks to invoke Lisp functions
- [ ] Handle errors in Lisp handlers gracefully (return 500, don't crash)
- [ ] Update `http2/listen` to accept handler function: `(http2/listen aio interface port keyfile certfile handler-fn)`

**Test**:
```lisp
(def server (http2/listen aio "127.0.0.1" 8443
                          "server.key" "server.crt"
                          (fn (req)
                            (http2/response :status 200
                                           :body "Hello from Lisp!"))))
```

**Estimated effort**: 2-3 days

---

### 2. Test Framework in Lisp ⭐ CRITICAL

**Problem**: No way to write tests in Lisp itself.

**What's needed**:
- [ ] `(deftest name body)` macro/function to define tests
- [ ] `(assert condition message)` for assertions
- [ ] `(run-tests)` to execute all defined tests
- [ ] `(run-test name)` to run a specific test
- [ ] Test result tracking (pass/fail/skip counts)
- [ ] Pretty printing of test results
- [ ] Add to prelude or separate `test.valk` module

**Example**:
```lisp
(deftest "http-client-works"
  (let [resp (await (http/get "https://google.com"))]
    (assert (== (http2/response-status resp) "200")
            "Expected 200 status")))

(run-tests)  ; Runs all tests, prints summary
```

**Estimated effort**: 1-2 days

---

### 3. Basic REPL Safety ⭐ CRITICAL

**Problem**: REPL can crash from segfaults, infinite recursion, etc.

**What's needed**:
- [ ] Signal handlers for SIGSEGV, SIGABRT, SIGFPE (catch crashes)
- [ ] Stack depth limit in evaluator (prevent infinite recursion)
- [ ] Arena size limits with graceful failure
- [ ] NULL check all allocations
- [ ] Max evaluation time limit (watchdog timer)
- [ ] Graceful error messages instead of crashes

**Implementation locations**:
- `src/repl.c` - add signal handlers
- `src/vm.c` - add stack depth counter in `valk_lval_eval`
- `src/memory.c` - add size limits to arena allocator

**Test**: Try to crash REPL with:
- Infinite recursion: `(def {f} (\ {x} {f x}))`
- Division by zero: `(/ 1 0)`
- Memory exhaustion: infinite list building

**Estimated effort**: 2-3 days

---

### 4. Higher-Level HTTP Conveniences

**Problem**: Current API is low-level and verbose.

**What's needed**:
- [ ] `(http/get url)` - simple GET request
- [ ] `(http/post url :body data :headers {...})` - POST with body
- [ ] `(http/put url :body data)` - PUT request
- [ ] `(http/delete url)` - DELETE request
- [ ] JSON parsing/serialization helpers (future, but plan for it)
- [ ] Helper to extract common response parts: `(http/status response)`, `(http/body response)`

**Implementation**: Build these in Lisp (in prelude) on top of existing `http2/*` primitives.

**Example**:
```lisp
(fun {http/get url} {
  ; Parse URL to extract host, port, path
  ; Create request, send, await
  ; Return response
})
```

**Estimated effort**: 1 day (after handler API is done)

---

### 5. Resolve Networking TODOs

**Current TODOs** (from `make todo`):
- [ ] `CMakeLists.txt:68` - io_uring detection (low priority)
- [ ] `test/test_networking.c:96` - Connection closing cleanup
- [ ] `test/test_networking.c:109` - Refactor test structure
- [ ] `src/aio_ssl.c:207,228,283` - Proper SSL error strings
- [ ] `src/aio_uv.c` - Various buffer handling and lifetime issues

**Priority**: Fix critical error handling and buffer issues, defer io_uring work.

**Estimated effort**: 1-2 days

---

### 6. Error Handling Improvements

**Problem**: Some errors crash or have poor messages.

**What's needed**:
- [ ] All async operations return error futures (not crashes)
- [ ] Better error messages with context (e.g., "Connection failed to 127.0.0.1:8443: connection refused")
- [ ] Error codes/types in Lisp (`:error-connection`, `:error-timeout`, etc.)
- [ ] Document error conditions for each API function

**Implementation**: Review all error paths in `src/aio_uv.c`, `src/aio_ssl.c`.

**Estimated effort**: 1 day

---

### 7. Documentation

**What's needed**:
- [ ] Document all `http2/*` functions in Lisp
- [ ] API reference document (markdown)
- [ ] Tutorial: "Building your first HTTP server"
- [ ] Tutorial: "Making HTTP requests"
- [ ] Error handling guide

**Files to create**:
- `docs/API_REFERENCE.md` - Complete API docs
- `docs/HTTP_TUTORIAL.md` - Getting started guide

**Estimated effort**: 1 day

---

### 8. Enhanced Testing

**What's needed**:
- [ ] Stress test: Many concurrent requests
- [ ] Timeout test: Slow server/client
- [ ] Large body test: Multi-MB request/response
- [ ] Multiple parallel servers test
- [ ] Handler error test: What happens when Lisp handler crashes?

**Add tests**: Expand `test_networking_lisp.c` or create new test files.

**Estimated effort**: 1-2 days

---

## Completion Criteria

The networking branch is **complete** when:

1. ✅ HTTP/2 client works (already done)
2. ✅ HTTP/2 server works (already done)
3. ⬜ Server can call Lisp functions to handle requests
4. ⬜ Lisp test framework exists and is documented
5. ⬜ REPL has basic crash safety (signals, stack limits)
6. ⬜ All high-priority TODOs are resolved
7. ⬜ API is documented
8. ⬜ Example programs work: simple web server, HTTP client
9. ⬜ All tests pass including new stress tests

## Suggested Implementation Order

**Week 1** (Foundations):
1. Server request handler API (Task 1) - 2-3 days
2. Test framework (Task 2) - 1-2 days
3. REPL safety basics (Task 3) - 2-3 days

**Week 2** (Polish):
4. Error handling improvements (Task 6) - 1 day
5. Higher-level HTTP API (Task 4) - 1 day
6. Resolve critical TODOs (Task 5) - 1-2 days
7. Enhanced testing (Task 8) - 1-2 days

**Week 3** (Documentation & Cleanup):
8. Documentation (Task 7) - 1 day
9. Final testing and bug fixes - 2-3 days
10. Code review and cleanup - 1-2 days

## Example: Complete HTTP Server in Lisp

After completion, this should work:

```lisp
; Load prelude with test framework
(load "src/prelude.valk")

; Define request handler
(def {handle-request} (\ {req} {
  (let
    [(method (http2/request-method req))
     (path (http2/request-path req))]

    (select
      [(== path "/") (http2/response :status 200 :body "Hello, World!")]
      [(== path "/about") (http2/response :status 200 :body "Valkyria HTTP Server")]
      [otherwise (http2/response :status 404 :body "Not Found")]))
}))

; Start server
(def {server} (await (http2/listen aio "127.0.0.1" 8443
                                   "server.key" "server.crt"
                                   handle-request)))

(print "Server running on https://127.0.0.1:8443")

; Test it works
(deftest "server-responds-to-root"
  (let [(resp (await (http/get "https://127.0.0.1:8443/")))]
    (assert (== (http2/response-status resp) "200") "Expected 200")
    (assert (== (http2/response-body resp) "Hello, World!") "Expected greeting")))

(run-tests)
```

## Post-Branch: What Comes Next

After networking branch is complete, the **type system branch** can begin with:
- Stable networking API to test type system on
- Test framework to validate type checker
- Safe REPL to experiment with type inference
- Real-world examples (HTTP servers) to guide type design

---

**Last Updated**: 2025-11-09
**Status**: Planning
**Owner**: Solo developer
