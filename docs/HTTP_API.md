# High-Level HTTP API Documentation

## Overview

This document describes the high-level HTTP API for Valkyria, built on top of the monadic async combinators and HTTP/2 primitives. The API provides a functional, composable interface for building HTTP clients and backend services.

## Architecture

```
┌─────────────────────────────────────────────────┐
│           High-Level HTTP API                   │
│  (Request builders, Middleware, Patterns)       │
├─────────────────────────────────────────────────┤
│         Monadic Async Combinators               │
│  (map, filter, fold, pipe, bind, etc.)          │
├─────────────────────────────────────────────────│
│       Continuation-Based Async/Await            │
│      (async-shift, async-reset, async-resume)   │
├─────────────────────────────────────────────────┤
│          HTTP/2 Primitive Builtins              │
│  (http2/request, http2/connect-async, etc.)     │
├─────────────────────────────────────────────────┤
│           C HTTP/2 Implementation               │
│      (nghttp2 + libuv + OpenSSL)                │
└─────────────────────────────────────────────────┘
```

## Quick Start

### Load the API

```lisp
(load "src/prelude.valk")
(load "src/http_api.valk")
```

### Make a Simple Request

```lisp
; Create a GET request
(def {req} (http-get "example.com"))

; Add custom headers
(def {req2} (with-header req "x-api-key" "secret"))

; Fetch URL (returns async operation)
(def {fetch-op} (fetch "example.com"))

; Execute async operation
(def {response} (run-async fetch-op))
```

## API Reference

### Part 1: Request Creation

#### `http-get url`
Creates a GET request for the specified URL.

**Example:**
```lisp
(def {req} (http-get "api.example.com"))
```

#### `http-post url body`
Creates a POST request with a body.

**Example:**
```lisp
(def {req} (http-post "api.example.com" "{\"name\":\"Alice\"}"))
```

#### `http-request method url`
Creates a request with a custom HTTP method.

**Example:**
```lisp
(def {req} (http-request "PUT" "api.example.com"))
(def {req2} (http-request "DELETE" "api.example.com"))
```

#### `with-header req name value`
Adds a header to a request. Returns the modified request (chainable).

**Example:**
```lisp
(def {req} (http-get "api.example.com"))
(def {req2} (with-header req "authorization" "Bearer token"))
(def {req3} (with-header req2 "content-type" "application/json"))
```

#### `with-headers req headers`
Adds multiple headers to a request.

**Example:**
```lisp
(def {headers} (list
  (list "authorization" "Bearer token")
  (list "content-type" "application/json")
  (list "x-request-id" "12345")))
(def {req} (with-headers (http-get "api.example.com") headers))
```

### Part 2: Response Handling

#### `response-status resp`
Extracts the HTTP status code from a response.

**Example:**
```lisp
(def {status} (response-status resp))
; status = 200
```

#### `response-body resp`
Extracts the response body as a string.

**Example:**
```lisp
(def {body} (response-body resp))
; body = "Hello World"
```

#### `response-headers resp`
Extracts the response headers.

**Example:**
```lisp
(def {headers} (response-headers resp))
```

#### `response-ok resp`
Checks if the response status is in the 2xx success range.

**Example:**
```lisp
(if (response-ok resp)
  {(print "Success!")}
  {(print "Failed")})
```

### Part 3: Client API

#### `fetch url`
Creates an async operation that fetches the specified URL with a GET request.

**Example:**
```lisp
(def {fetch-op} (fetch "example.com"))
(def {response} (run-async fetch-op))
```

#### `fetch-with-request url request`
Creates an async operation that fetches with a custom request.

**Example:**
```lisp
(def {req} (http-post "api.example.com" "data"))
(def {fetch-op} (fetch-with-request "api.example.com" req))
(def {response} (run-async fetch-op))
```

#### `fetch-text url`
Fetches a URL and returns just the response body.

**Example:**
```lisp
(def {text} (run-async (fetch-text "example.com")))
; text = "Hello World"
```

#### `fetch-ok url`
Fetches a URL and returns whether the request was successful.

**Example:**
```lisp
(def {success} (run-async (fetch-ok "example.com")))
; success = 1 (true) or 0 (false)
```

#### `fetch-sync url`
Synchronous-style fetch (wraps run-async for convenience).

**Example:**
```lisp
(def {response} (fetch-sync "example.com"))
```

#### `fetch-and-print url`
Fetches a URL and prints the status and body.

**Example:**
```lisp
(fetch-and-print "example.com")
; Output:
; Status: 200
; Body: Hello World
```

### Part 4: Batch Operations

#### `fetch-all urls`
Fetches multiple URLs sequentially and returns all responses.

**Example:**
```lisp
(def {urls} (list "example.com" "google.com" "github.com"))
(def {responses} (run-async (fetch-all urls)))
```

#### `fetch-all-text urls`
Fetches multiple URLs and returns just the response bodies.

**Example:**
```lisp
(def {urls} (list "api.example.com/user/1" "api.example.com/user/2"))
(def {bodies} (run-async (fetch-all-text urls)))
```

#### `health-check url`
Checks if a URL is healthy (returns 2xx status).

**Example:**
```lisp
(def {is-healthy} (run-async (health-check "api.example.com")))
```

#### `health-check-all urls`
Health-checks multiple URLs.

**Example:**
```lisp
(def {urls} (list "api1.example.com" "api2.example.com" "api3.example.com"))
(def {results} (run-async (health-check-all urls)))
; results = (1 1 0) - first two healthy, third down
```

### Part 5: Middleware

Middleware are functions that transform requests before they are sent.

#### `with-auth token`
Creates middleware that adds an authorization header.

**Example:**
```lisp
(def {auth-mw} (with-auth "Bearer my-secret-token"))
(def {req} (http-get "api.example.com"))
(def {authed-req} (auth-mw req))
```

#### `with-user-agent agent`
Creates middleware that sets the user agent.

**Example:**
```lisp
(def {ua-mw} (with-user-agent "MyApp/2.0"))
(def {req} (ua-mw (http-get "api.example.com")))
```

#### `with-logging req`
Middleware that logs the request (for debugging).

**Example:**
```lisp
(def {req} (with-logging (http-get "api.example.com")))
```

#### `compose-middleware middleware-list`
Composes multiple middleware functions into one.

**Example:**
```lisp
(def {combined} (compose-middleware (list
  (with-auth "Bearer token")
  (with-user-agent "MyApp/1.0")
)))

(def {req} (combined (http-get "api.example.com")))
; Request now has both auth and user-agent headers
```

### Part 6: Common Patterns

#### `parallel async-ops`
Executes multiple async operations and collects results (currently sequential).

**Example:**
```lisp
(def {ops} (list
  (fetch "api.example.com/users")
  (fetch "api.example.com/posts")
  (fetch "api.example.com/comments")))

(def {results} (run-async (parallel ops)))
```

#### `sequential async-ops`
Executes async operations in sequence, returns last result.

**Example:**
```lisp
(def {ops} (list
  (fetch "api.example.com/log")
  (fetch "api.example.com/process")
  (fetch "api.example.com/notify")))

(def {final} (run-async (sequential ops)))
```

#### `fan-out url extractors`
Fan-out pattern: fetch a resource and then fetch related resources.

**Example:**
```lisp
(def {extract-user-id} (\ {resp} {"api.example.com/users/123"}))
(def {extract-posts} (\ {resp} {"api.example.com/posts?user=123"}))

(def {results} (run-async
  (fan-out "api.example.com/dashboard" (list extract-user-id extract-posts))))
```

#### `aggregate urls combiner`
Aggregate pattern: fetch multiple URLs and combine results.

**Example:**
```lisp
(def {combine} (\ {responses} {
  (list
    (response-body (head responses))
    (response-body (head (tail responses))))
}))

(def {result} (run-async
  (aggregate (list "api1.example.com" "api2.example.com") combine)))
```

### Part 7: Error Handling

#### `async-try async-op error-handler`
Wraps an async operation with error handling.

**Example:**
```lisp
(def {safe-fetch} (async-try
  (fetch "might-fail.example.com")
  (\ {error} {(async-pure "default-value")})))

(def {result} (run-async safe-fetch))
```

#### `async-or-default async-op default-value`
Returns default value if async operation fails.

**Example:**
```lisp
(def {result} (run-async
  (async-or-default (fetch "might-fail.example.com") "default")))
```

### Part 8: Route Matching (Server-Side)

#### `route-matches pattern path`
Checks if a path matches a pattern (exact match for now).

**Example:**
```lisp
(route-matches "/api/users" "/api/users")  ; Returns 1 (true)
(route-matches "/api/users" "/api/posts")  ; Returns 0 (false)
```

#### `find-route routes method path`
Finds a matching route from a list of routes.

**Example:**
```lisp
(def {routes} (list
  (list "GET" "/api/users" handler-get-users)
  (list "POST" "/api/users" handler-create-user)
  (list "GET" "/api/posts" handler-get-posts)))

(def {route} (find-route routes "GET" "/api/users"))
; route = (list "GET" "/api/users" handler-get-users)
```

## Usage Examples

### Example 1: Simple GET Request

```lisp
(load "src/http_api.valk")

; Fetch a URL
(def {response} (fetch-sync "example.com"))

; Check if successful
(if (response-ok response)
  {(print "Success:" (response-body response))}
  {(print "Failed with status:" (response-status response))})
```

### Example 2: POST Request with Authentication

```lisp
; Create POST request
(def {req} (http-post "api.example.com/users" "{\"name\":\"Alice\"}"))

; Add authentication
(def {authed} (with-header req "authorization" "Bearer my-token"))

; Send request
(def {resp} (run-async (fetch-with-request "api.example.com" authed)))

(print "Created user:" (response-body resp))
```

### Example 3: Batch Requests

```lisp
; Fetch multiple user profiles
(def {user-urls} (list
  "api.example.com/users/1"
  "api.example.com/users/2"
  "api.example.com/users/3"))

; Fetch all in sequence
(def {users} (run-async (fetch-all-text user-urls)))

; Print results
(map (\ {user} {(print "User:" user)}) users)
```

### Example 4: Request Pipeline with Middleware

```lisp
; Define middleware
(def {auth} (with-auth "Bearer secret-token"))
(def {custom-ua} (with-user-agent "MyApp/1.0"))

; Compose middleware
(def {middleware} (compose-middleware (list auth custom-ua)))

; Create and transform request
(def {req} (middleware (http-get "api.example.com/data")))

; Send request
(def {resp} (run-async (fetch-with-request "api.example.com" req)))
```

### Example 5: Error Handling

```lisp
; Try to fetch with fallback
(def {result} (run-async
  (async-or-default
    (fetch-text "might-fail.example.com")
    "Service unavailable")))

(print "Result:" result)
```

### Example 6: Health Checks

```lisp
; Check multiple services
(def {services} (list
  "api1.example.com/health"
  "api2.example.com/health"
  "api3.example.com/health"))

(def {health-results} (run-async (health-check-all services)))

; Print results
(def {print-health} (\ {service result} {
  (if result
    {(print "✓" service "is healthy")}
    {(print "✗" service "is down")})
}))

; Would need zip functionality to combine services with results
```

### Example 7: Async Pipeline

```lisp
; Define async transformations
(def {fetch-user} (\ {id} {
  (fetch-text (join (list "api.example.com/users/" id) ""))
}))

(def {fetch-posts} (\ {user} {
  ; Extract user ID and fetch posts
  (fetch-text "api.example.com/posts?user=123")
}))

; Chain operations
(def {user-posts} (async-bind (fetch-user "123") fetch-posts))

(def {posts} (run-async user-posts))
(print "Posts:" posts)
```

## Integration with Async Monadic API

The HTTP API is built on top of the monadic async combinators. All HTTP operations return async operations that can be combined using:

- `async-bind` - Chain operations
- `async-pipe` - Transform through pipeline
- `async-map-list` - Map over collections
- `async-filter-list` - Filter collections
- `async-fold-list` - Reduce collections
- `async-collect` - Gather multiple operations
- And more (see ASYNC_MONADIC_API.md)

**Example:**
```lisp
; Map fetch over URLs
(def {urls} (list "example.com" "google.com" "github.com"))
(def {fetch-op} (async-map-list fetch urls))
(def {responses} (run-async fetch-op))

; Filter successful responses
(def {filter-op} (async-filter-list (\ {resp} {
  (async-pure (response-ok resp))
}) responses))
```

## Low-Level HTTP/2 Builtins

The HTTP API wraps these low-level builtins:

- `http2/request method scheme authority path` - Create request object
- `http2/request-add-header req name value` - Add header
- `http2/connect-async url continuation` - Connect to server
- `http2/send-async client request continuation` - Send request
- `http2/response-status resp` - Extract status
- `http2/response-body resp` - Extract body
- `http2/response-headers resp` - Extract headers

You can use these directly for more control:

```lisp
(def {req} (http2/request "GET" "https" "example.com" "/"))
(http2/request-add-header req ":method" "GET")

(http2/connect-async "example.com" (\ {client} {
  (http2/send-async client req (\ {response} {
    (print "Got response:" response)
  }))
}))
```

## Current Limitations

1. **No Server Implementation** - Only client API is implemented
2. **Sequential Execution** - `parallel` currently executes sequentially
3. **No Connection Pooling** - Each request creates a new connection
4. **No Keep-Alive** - Connections close after each request
5. **Basic Error Handling** - Error propagation needs improvement
6. **No Timeouts** - Requests can hang indefinitely
7. **No Cancellation** - Cannot cancel in-flight requests
8. **Exact Route Matching Only** - No pattern matching or path parameters
9. **No JSON Parsing** - Response bodies are strings only
10. **Memory Issues** - Complex test suites trigger memory errors

## Future Enhancements

### Short-Term
- Improve error handling and propagation
- Add timeout support
- Implement proper JSON parsing
- Fix memory issues in complex scenarios

### Medium-Term
- Server-side HTTP/2 support
- Connection pooling
- Keep-alive connections
- Pattern-based route matching
- Path parameter extraction
- Query string parsing
- Cookie support

### Long-Term
- True parallel request execution
- Request cancellation
- Streaming responses
- WebSocket support
- HTTP/3 support
- Middleware for response transformation
- Request/response logging and metrics

## Testing

Basic tests are in `test/test_http_minimal.valk`:

```bash
# Run HTTP API tests
build/valk test/test_http_minimal.valk

# Run all tests (includes HTTP API)
make test
```

More comprehensive tests are available but have memory issues:
- `test/test_http_basic.valk` - Basic functionality tests
- `test/test_http_simple.valk` - Focused feature tests
- `test/test_http_api.valk` - Complete test suite

## Related Documentation

- `ASYNC_MONADIC_API.md` - Monadic async combinators reference
- `ASYNC_IMPLEMENTATION_SUMMARY.md` - Async/await implementation details
- `CLAUDE.md` - Project overview and development guide

## Contributing

When adding new HTTP API features:

1. Follow the functional, composable pattern
2. Return async operations (functions that take continuations)
3. Use `run-async` wrapper for executing operations
4. Add tests to `test/test_http_minimal.valk`
5. Update this documentation
6. Ensure compatibility with monadic combinators

## Status

✅ **Implemented:**
- Request creation and manipulation
- Response handling
- Client API (fetch operations)
- Batch operations
- Middleware composition
- Common patterns
- Basic error handling
- Route matching (for future server support)

⏳ **Partial:**
- Error propagation (needs improvement)
- JSON support (manual parsing only)

🔧 **Future Work:**
- Server-side API
- True parallel execution
- Connection pooling
- Advanced routing
- Better error handling
- Timeout support
- Request cancellation

**Ready for Production:** Client-side basic usage ✅
**Ready for Complex Backends:** Partial - needs improvements ⏳
