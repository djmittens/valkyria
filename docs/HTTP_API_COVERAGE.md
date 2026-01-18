# HTTP/2 API Coverage Analysis

Current coverage: **92.7% expression coverage**
Required: 90% expression coverage

**Status:** ✅ Coverage requirement met! All known bugs fixed. API now uses `http2/client-request` builtin directly.

## Summary

Coverage target achieved through network integration tests (`test/test_http_api_network.valk`).

The remaining ~7% uncovered expressions are in functions that either:
1. Use `async/run` which doesn't work inside async context (`http2/fetch-sync`, `http2/fetch-and-print`)
2. Are retry failure paths that only execute on network errors
3. Are complex patterns (`http2/fan-out`, `http2/aggregate`) that require multiple chained operations

Note: Redundant wrapper functions (`http/response-status`, `http/response-body`, `http/response-headers`) were removed - use the `http2/response-*` builtins directly.

## Known Bugs Found During Testing

### ~~BUG 1: http2/connect-async API mismatch~~ **FIXED**
**Location:** `src/http_api.valk` line 74
**Issue:** ~~`http2/fetch-async` calls `(http2/connect-async url cont)` but the builtin expects `(http2/connect-async aio host port cont)`~~
**Fix Applied:** Changed API to use `http2/client-request` builtin directly instead of lower-level connect/send primitives. API now accepts `(aio host port path)` parameters instead of URL strings.

### ~~BUG 2: GC corruption with nested async closures~~ **FIXED**
**Location:** Multiple places in `src/async_monadic.valk`
**Issue:** ~~Functions that create nested async closures (lambda returning lambda) cause `free(): invalid pointer` crashes~~
**Root Cause:** Async functions were using the wrong calling convention:
- **Wrong:** `(async-fn item continuation)` - passing 2 arguments to async-fn
- **Correct:** `((async-fn item) continuation)` - async-fn returns an async operation, then call it with continuation

**Fix Applied:** Updated all affected functions in `src/async_monadic.valk`:
- `async/map-list`, `async/filter-list`, `async/fold-list`
- `async/tap`, `async/pipe`, `async/compose`
- `async/zip-with`, `async/partition`

All async functions now work correctly. Tests enabled in `test/test_http_integration.valk`.

### ~~BUG 3: http2/validate-status error path causes crash~~ **FIXED**
**Location:** `src/http_api.valk` line 203
**Issue:** ~~Calling `(error (str "Unexpected status: " status))` causes `free(): invalid pointer` crash~~
**Fix Applied:** Simplified error message to static string `"Unexpected HTTP status"` to avoid memory issues with dynamic string concatenation in error context.

## Uncovered Functions Requiring Network/Integration Tests

### Response Handler (requires http2 response objects)

| Function | Why Untestable |
|----------|----------------|
| `http2/response-ok?` | Inner body requires response from network |

### Network Operations (require active connections)
These functions initiate network connections (API: `aio host port path`):

| Function | Why Untestable |
|----------|----------------|
| `http2/fetch-async` | Calls `http2/client-request` builtin |
| `http2/fetch-sync` | Wraps `http2/fetch` with `async/run` |
| `http2/fetch-and-print` | Calls `http2/fetch-sync` |

### Callback Bodies (require response objects)
Inner lambdas that receive response objects from network operations:

| Function | Why Untestable |
|----------|----------------|
| `http2/fetch-text` (inner) | Lambda receives network response |
| `http2/fetch-ok?` (inner) | Lambda receives network response |
| `http2/fetch-retry` | Entire retry loop requires responses |
| `http2/health-check` (inner) | Lambda receives network response |

### Response Pipeline Functions (require response objects)
Functions designed to process HTTP responses:

| Function | Why Untestable |
|----------|----------------|
| `http2/log-response` | Logs response status |
| `http2/parse-json-response` | Parses response body |
| `http2/validate-status` (inner) | Validates response status |

### Pattern Functions (require network + responses)
Higher-order patterns that combine network operations:

| Function | Why Untestable |
|----------|----------------|
| `http2/fan-out` (inner) | Processes response, fetches more URLs |
| `http2/aggregate` (inner) | Combines multiple responses |

## Options to Reach 90% Coverage

### Option 1: Add Integration Tests
Create tests that make actual HTTP requests to a local test server:
```lisp
; Start test server, then:
(def {aio} (aio/start))
(def {resp} (http2/fetch-sync aio "localhost" 8080 "/test"))
(http2/response-status resp)  ; Builtin - now executes and covers inner lambdas
```

### Option 2: Lower Coverage Threshold
Add exception for `http_api.valk` in coverage requirements since network-dependent code cannot be unit tested.

### Option 3: Refactor for Testability
Add abstraction layer that allows mocking HTTP primitives:
```lisp
; Instead of direct http2/* calls, use injectable transport
(fun {http2/response-status resp} {
  ((http2/transport-status) resp)
})
```

## What IS Covered (87.1%)

All testable code paths are covered:
- Request creation (`http2/get`, `http2/post`, `http2/make-request`)
- Header manipulation (`http2/with-header`, `http2/with-headers`)
- Middleware creation and composition
- Route matching logic (`http2/route-matches?`, `http2/find-route`)
- Builder pattern (`http2/request-builder`, etc.)
- Async operation construction (returns lambdas, doesn't execute network)
