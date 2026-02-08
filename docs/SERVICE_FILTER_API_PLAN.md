# Service & Filter API Plan

## Executive Summary

This document outlines a redesign of Valkyria's HTTP API to adopt a Finagle-inspired Service/Filter architecture. The goal is to enable compositional, testable, and reusable HTTP handling with proper context propagation for observability concerns (tracing, metrics, deadlines).

**Key Insight**: Both HTTP clients and servers are fundamentally the same thing—a function from request to response. By unifying them under a single `Service` abstraction and providing `Filter` for cross-cutting concerns, we enable powerful composition patterns.

---

## Table of Contents

1. [Problem Statement](#problem-statement)
2. [Design Goals](#design-goals)
3. [Core Abstractions](#core-abstractions)
4. [Detailed Requirements](#detailed-requirements)
5. [Implementation Plan](#implementation-plan)
6. [API Specification](#api-specification)
7. [Examples](#examples)
8. [Test Cases](#test-cases)
9. [Migration Strategy](#migration-strategy)
10. [Success Criteria](#success-criteria)

---

## Problem Statement

### Current Limitations

1. **No Unified Abstraction**: Handlers and clients have completely different signatures
   - Handler: `(\ {req} response)` with opaque C reference
   - Client: `(http2/client-request aio host port path callback)`

2. **No Middleware Composition**: Can only transform requests, not intercept responses or short-circuit

3. **No Context Propagation**: Cross-cutting concerns (tracing, auth, deadlines) require manual threading

4. **Opaque Requests**: Can't create synthetic requests for testing

5. **Ad-hoc Routing**: Manual pattern matching with no path parameters

6. **AIO System Threading Problem**: Async primitives like `aio/sleep` require explicit `sys` argument
   - Easy to forget (webserver_demo.valk has this bug on `/slow` endpoint)
   - Boilerplate: every async call needs `sys` threaded through
   - Breaks composition: can't easily pass async functions around
   - Example bug:
     ```lisp
     ; BROKEN - missing sys argument
     (aio/do {
       (<- _ (aio/sleep 2000))  ; Error: aio/sleep needs 2 args!
       {:status "200" :body "done"}})
     
     ; CORRECT - but verbose
     (aio/do {
       (<- _ (aio/sleep sys 2000))  ; Must pass sys everywhere
       {:status "200" :body "done"}})
     ```

### Impact

- **Testing**: Requires spinning up real servers to test handlers
- **Observability**: No standard way to add tracing/metrics
- **Reusability**: Auth, rate limiting, retries must be reimplemented per-handler
- **Maintainability**: Cross-cutting concerns scattered throughout codebase
- **Correctness**: Easy to write broken async code that fails at runtime

---

## Design Goals

| Goal | Description | Rationale |
|------|-------------|-----------|
| **G1: Unified Service Type** | Clients and servers share the same interface | Enables filter reuse, simplifies mental model |
| **G2: Composable Filters** | Filters can wrap services to add behavior | Standard pattern for cross-cutting concerns |
| **G3: Explicit Context** | Request context flows through call chain | Required for distributed tracing, deadlines |
| **G4: Data-Based Requests** | Requests/responses are plain data structures | Enables unit testing without network |
| **G5: Type Safety** | Clear contracts between components | Catches errors at definition time |
| **G6: Backward Compatibility** | Existing handlers continue to work | Gradual migration path |

---

## Core Abstractions

### 1. Service

A Service is a function that takes a request and context, returning an async handle to a response.

```
Service[Req, Res] = (Req, Context) -> Handle[Res]
```

**Why this signature?**
- `Req, Res`: Generic over request/response types (HTTP, Thrift, custom protocols)
- `Context`: Explicit context avoids global state, enables tracing
- `Handle[Res]`: Async by default—sync is just immediate completion

### 2. Filter

A Filter wraps a Service, transforming requests, responses, or both.

```
Filter[ReqIn, ResOut, ReqOut, ResIn] = (ReqIn, Context, Service[ReqOut, ResIn]) -> Handle[ResOut]
```

**Simplified for same-type transformation:**
```
SimpleFilter[Req, Res] = (Req, Context, Service[Req, Res]) -> Handle[Res]
```

**Why four type parameters?**
- Filters can change types (e.g., add auth info to request)
- Most filters use `SimpleFilter` (same types in/out)

### 3. Context

An immutable map carrying request-scoped data through the call chain.

```
Context = {:aio sys :trace-id "abc" :deadline 1234567890 :user-id "123" ...}
```

**Critical: Context carries the AIO system**

The Context **must** carry the AIO system reference (`:aio`). This solves the threading problem:

```lisp
; OLD (broken) - sys must be passed everywhere manually
(def {handler}
  (\ {req}
    (aio/sleep sys 1000)))  ; Where does sys come from?

; NEW - Context carries :aio, async primitives extract it
(def {handler}
  (svc/new (\ {req ctx}
    (aio/sleep ctx 1000))))  ; ctx contains :aio, aio/sleep extracts it

; OR - Use ctx-aware wrappers
(def {handler}
  (svc/new (\ {req ctx}
    (ctx/sleep ctx 1000))))  ; Convenience wrapper
```

**Why Context instead of dynamic/thread-local?**
- Valkyria runs on libuv's single-threaded event loop
- No thread-locals in traditional sense
- Explicit is better: you can see exactly what's available
- Testing: easy to mock by providing test context

**Why immutable?**
- Thread-safe for concurrent handlers
- Easy to reason about (no spooky action at a distance)
- Child calls get derived context, parent unaffected

### 4. ServiceFactory

Creates Services with lifecycle management (for connection pooling, etc.).

```
ServiceFactory[Req, Res] = () -> Handle[Service[Req, Res]]
```

**Why separate from Service?**
- Services may need setup (TCP connection, TLS handshake)
- Enables connection pooling, load balancing
- Deferred for Phase 2

### 5. Context-Aware Async Primitives

The current `aio/*` functions require explicit `sys` argument. We provide context-aware wrappers:

```lisp
; Current API (error-prone)
(aio/sleep sys 1000)
(aio/then handle (\ {x} ...))

; New context-aware API
(ctx/sleep ctx 1000)      ; Extracts :aio from ctx
(ctx/delay ctx 1000 fn)   ; ctx-aware delay
(ctx/timeout ctx 5000 h)  ; ctx-aware timeout

; aio/* still work but need explicit sys
; ctx/* are convenience wrappers
```

**Implementation approach:**
```lisp
(fun {ctx/sleep ctx ms}
  (aio/sleep (ctx/get ctx :aio) ms))

(fun {ctx/delay ctx ms fn}
  (aio/delay (ctx/get ctx :aio) ms fn))
```

**Why wrappers instead of modifying aio/*?**
- Backward compatibility: existing code still works
- Explicit: clear where the sys comes from
- Testable: can mock :aio in context for testing
- Gradual migration: adopt ctx/* as needed

---

## Detailed Requirements

### R1: Service Definition

#### R1.1: Basic Service Creation
```lisp
; Create a service from a function
(def {my-service}
  (svc/new (\ {req ctx}
    (aio/pure {:status 200 :body "Hello"}))))
```

**Acceptance Criteria:**
- [ ] `svc/new` accepts `(Req, Ctx) -> Handle[Res]` function
- [ ] Returns a callable service
- [ ] Service can be invoked with `(my-service req ctx)`

#### R1.2: Service Invocation
```lisp
; Invoke service
(= {response-handle} (my-service request context))

; With aio/then to process response
(aio/then (my-service req ctx) (\ {res} ...))
```

**Acceptance Criteria:**
- [ ] Services are directly callable
- [ ] Returns `Handle[Response]`
- [ ] Works with all aio combinators

#### R1.3: Service Composition
```lisp
; Chain services (output of one feeds input of next)
(def {composed} (svc/and-then svc1 svc2))

; Parallel services (both receive same request)
(def {parallel} (svc/zip svc1 svc2))
```

**Acceptance Criteria:**
- [ ] `svc/and-then` pipes response of svc1 as request to svc2
- [ ] `svc/zip` returns tuple of both responses
- [ ] Composition preserves async semantics

### R2: Filter Definition

#### R2.1: Basic Filter Creation
```lisp
; Create a filter
(def {logging-filter}
  (filter/new (\ {req ctx svc}
    (println "Request:" (req :path))
    (= {start} (time/now))
    (aio/then (svc req ctx)
      (\ {res}
        (println "Response:" (res :status) "in" (- (time/now) start) "ms")
        (aio/pure res))))))
```

**Acceptance Criteria:**
- [ ] `filter/new` accepts `(Req, Ctx, Service) -> Handle[Res]` function
- [ ] Filter receives the downstream service to call
- [ ] Filter can inspect/modify request before calling service
- [ ] Filter can inspect/modify response after service returns

#### R2.2: Filter Application
```lisp
; Apply filter to service
(def {logged-service} (filter/apply logging-filter my-service))

; Or use |> for readability
(def {logged-service}
  (|> my-service
      (filter/apply logging-filter)))
```

**Acceptance Criteria:**
- [ ] `filter/apply` returns a new Service
- [ ] Original service unchanged (immutable)
- [ ] Resulting service has filter's behavior

#### R2.3: Filter Composition
```lisp
; Compose multiple filters (applied right-to-left)
(def {combined} (filter/compose auth-filter logging-filter timing-filter))

; Apply composed filter
(def {final} (filter/apply combined base-service))

; Equivalent to:
(def {final}
  (|> base-service
      (filter/apply timing-filter)
      (filter/apply logging-filter)
      (filter/apply auth-filter)))
```

**Acceptance Criteria:**
- [ ] `filter/compose` combines multiple filters
- [ ] Outermost filter in list is applied first (sees request first)
- [ ] Order matches intuition: `[auth, logging]` means auth checks before logging

#### R2.4: Short-Circuit Filters
```lisp
; Filter that may not call downstream service
(def {auth-filter}
  (filter/new (\ {req ctx svc}
    (if (valid-token? (ctx :auth-token))
      {(svc req ctx)}  ; Proceed
      {(aio/pure {:status 401 :body "Unauthorized"})}))))  ; Short-circuit
```

**Acceptance Criteria:**
- [ ] Filters can return response without calling service
- [ ] Downstream service not invoked on short-circuit
- [ ] Response propagates correctly through outer filters

### R3: Context Management

#### R3.1: Context Creation
```lisp
; Empty context (NOTE: has no :aio - can't use ctx/sleep etc.)
(def {ctx} (ctx/empty))

; Context with AIO system (required for async operations)
(def {ctx} (ctx/with-aio sys))

; Context with initial values including AIO
(def {ctx} (ctx/new sys {:trace-id "abc-123" :deadline (+ (time/now) 5000)}))

; For testing: context without real AIO (sync-only operations)
(def {test-ctx} (ctx/new nil {:user-id "test-user"}))
```

**Acceptance Criteria:**
- [ ] `ctx/empty` returns empty context (no :aio)
- [ ] `ctx/with-aio` creates context with just :aio set
- [ ] `ctx/new` accepts sys and initial map, sets :aio automatically
- [ ] Context is immutable
- [ ] `ctx/aio` accessor returns the AIO system or nil

#### R3.2: Context Access
```lisp
; Get value (returns nil if missing)
(ctx/get ctx :trace-id)

; Get with default
(ctx/get-or ctx :timeout 5000)

; Check existence
(ctx/has? ctx :user-id)
```

**Acceptance Criteria:**
- [ ] `ctx/get` returns value or nil
- [ ] `ctx/get-or` returns default if missing
- [ ] `ctx/has?` returns boolean

#### R3.3: Context Derivation
```lisp
; Add/update value (returns new context)
(= {child-ctx} (ctx/set ctx :user-id "123"))

; Add multiple values
(= {child-ctx} (ctx/merge ctx {:user-id "123" :role "admin"}))

; Remove value
(= {child-ctx} (ctx/remove ctx :temp-data))
```

**Acceptance Criteria:**
- [ ] `ctx/set` returns new context with value
- [ ] Original context unchanged
- [ ] `ctx/merge` combines maps
- [ ] `ctx/remove` excludes key

#### R3.4: Standard Context Keys
```lisp
; Well-known keys with accessor functions
(ctx/aio ctx)           ; :aio (AIO system - CRITICAL for async)
(ctx/trace-id ctx)      ; :trace-id
(ctx/span-id ctx)       ; :span-id  
(ctx/deadline ctx)      ; :deadline (unix timestamp)
(ctx/timeout-ms ctx)    ; Computed from deadline
(ctx/user-id ctx)       ; :user-id
(ctx/request-id ctx)    ; :request-id
```

**Acceptance Criteria:**
- [ ] Standard accessors for common keys
- [ ] `ctx/aio` returns the AIO system or nil
- [ ] `ctx/timeout-ms` computes remaining time from deadline
- [ ] Returns nil if key not set

#### R3.5: Context-Aware Async Primitives
```lisp
; Sleep using context's AIO system
(ctx/sleep ctx 1000)  ; Equivalent to (aio/sleep (ctx/aio ctx) 1000)

; Delay with callback
(ctx/delay ctx 1000 (\ {} {:done true}))

; Timeout wrapper
(ctx/timeout ctx 5000 some-handle)

; Schedule callback
(ctx/schedule ctx 1000 (\ {} (println "fired!")))
```

**Acceptance Criteria:**
- [ ] `ctx/sleep` extracts :aio and calls aio/sleep
- [ ] `ctx/delay` extracts :aio and calls aio/delay  
- [ ] `ctx/timeout` wraps handle with timeout using :aio
- [ ] All ctx/* async functions fail gracefully if :aio is nil
- [ ] Error messages clearly indicate missing :aio

### R4: HTTP Request/Response as Data

#### R4.1: Request Structure
```lisp
; HTTP Request is a plain map
{:method "GET"
 :path "/users/123"
 :scheme "https"
 :authority "api.example.com"
 :headers {:content-type "application/json"
           :authorization "Bearer xyz"}
 :body nil}
```

**Acceptance Criteria:**
- [ ] Requests are plain Q-expressions (maps)
- [ ] All HTTP/2 pseudo-headers represented
- [ ] Headers are a nested map
- [ ] Body is string or nil

#### R4.2: Response Structure
```lisp
; HTTP Response is a plain map
{:status 200
 :headers {:content-type "application/json"
           :x-request-id "abc-123"}
 :body "{\"users\": []}"}
```

**Acceptance Criteria:**
- [ ] Responses are plain Q-expressions
- [ ] Status is integer
- [ ] Headers are nested map
- [ ] Body is string or nil

#### R4.3: Request/Response Helpers
```lisp
; Request construction
(http/request "GET" "/users")
(http/request "POST" "/users" {:body "{...}"})

; Response construction  
(http/response 200 {:body "OK"})
(http/response 404)

; Accessors
(http/status resp)
(http/body req-or-resp)
(http/header req-or-resp "content-type")
(http/headers req-or-resp)

; Predicates
(http/ok? resp)        ; 2xx
(http/redirect? resp)  ; 3xx
(http/client-error? resp)  ; 4xx
(http/server-error? resp)  ; 5xx
```

**Acceptance Criteria:**
- [ ] Helpers construct valid request/response maps
- [ ] Accessors work on both requests and responses
- [ ] Predicates return boolean

### R5: HTTP Client as Service

#### R5.1: Client Creation
```lisp
; Create HTTP client service
(def {client} (http/client aio "api.example.com" 443))

; Client is a Service[HttpRequest, HttpResponse]
(= {resp-handle} (client {:method "GET" :path "/users"} ctx))
```

**Acceptance Criteria:**
- [ ] `http/client` returns a Service
- [ ] Client handles connection management internally
- [ ] Request is plain data (not C reference)

#### R5.2: Client with Filters
```lisp
; Apply standard client filters
(def {client}
  (|> (http/client aio "api.example.com" 443)
      (filter/apply retry-filter)
      (filter/apply timeout-filter)
      (filter/apply tracing-filter)))
```

**Acceptance Criteria:**
- [ ] Same filters work on clients and servers
- [ ] Filters compose in expected order

### R6: HTTP Server Integration

#### R6.1: Service to Handler Adapter
```lisp
; Convert Service to legacy handler format
(def {handler} (http/service->handler my-service))

; Use with existing server
(http2/server-listen aio PORT handler)
```

**Acceptance Criteria:**
- [ ] Adapter bridges new Service to existing C runtime
- [ ] Converts C request reference to data map
- [ ] Converts response map back to C format

#### R6.2: Native Server (Future)
```lisp
; Future: Native server that takes Service directly
(http/serve aio PORT my-service)
```

**Acceptance Criteria:**
- [ ] Direct Service support (Phase 2)
- [ ] No adapter overhead

### R7: Standard Filters Library

#### R7.1: Timing Filter
```lisp
(def {timing-filter}
  (filter/timing
    {:on-complete (\ {req ctx duration-ms} 
      (metrics/record "http.latency" duration-ms {:path (req :path)}))}))
```

**Acceptance Criteria:**
- [ ] Records request duration
- [ ] Calls callback with timing info
- [ ] Works for both success and failure

#### R7.2: Logging Filter
```lisp
(def {logging-filter}
  (filter/logging {:level :info}))
```

**Acceptance Criteria:**
- [ ] Logs request method, path, status
- [ ] Includes trace-id from context if present
- [ ] Configurable log level

#### R7.3: Tracing Filter
```lisp
(def {tracing-filter}
  (filter/tracing {:service-name "my-api"}))
```

**Acceptance Criteria:**
- [ ] Generates trace-id if not in context
- [ ] Creates span for request
- [ ] Propagates trace headers to downstream
- [ ] Records span on completion

#### R7.4: Timeout Filter
```lisp
(def {timeout-filter}
  (filter/timeout 5000))  ; 5 second timeout
```

**Acceptance Criteria:**
- [ ] Fails request if service doesn't respond in time
- [ ] Respects existing deadline in context (uses shorter)
- [ ] Cancels underlying handle on timeout

#### R7.5: Retry Filter
```lisp
(def {retry-filter}
  (filter/retry {:max-attempts 3
                 :backoff :exponential
                 :retryable? (\ {res} (>= (res :status) 500))}))
```

**Acceptance Criteria:**
- [ ] Retries on configurable conditions
- [ ] Respects deadline from context
- [ ] Exponential backoff between retries

#### R7.6: Circuit Breaker Filter
```lisp
(def {circuit-breaker}
  (filter/circuit-breaker {:threshold 5
                           :reset-timeout 30000}))
```

**Acceptance Criteria:**
- [ ] Opens after N consecutive failures
- [ ] Fails fast when open
- [ ] Half-open state allows test requests
- [ ] Closes on successful test

#### R7.7: Rate Limiting Filter
```lisp
(def {rate-limiter}
  (filter/rate-limit {:requests-per-second 100}))
```

**Acceptance Criteria:**
- [ ] Rejects requests over limit with 429
- [ ] Token bucket or sliding window algorithm
- [ ] Configurable rejection response

#### R7.8: Authentication Filter
```lisp
(def {auth-filter}
  (filter/auth {:validator validate-token
                :context-key :user-id}))
```

**Acceptance Criteria:**
- [ ] Extracts token from Authorization header
- [ ] Calls validator function
- [ ] Adds user info to context on success
- [ ] Returns 401 on failure

### R8: Router as Service

#### R8.1: Route Definition
```lisp
(def {router}
  (router/new
    (router/get "/users" list-users-svc)
    (router/get "/users/:id" get-user-svc)
    (router/post "/users" create-user-svc)
    (router/delete "/users/:id" delete-user-svc)
    (router/any "/health" health-svc)))
```

**Acceptance Criteria:**
- [ ] Method-specific route helpers
- [ ] Path parameters with `:name` syntax
- [ ] `router/any` matches all methods
- [ ] Router is itself a Service

#### R8.2: Path Parameters
```lisp
; Path params added to context
(def {get-user-svc}
  (svc/new (\ {req ctx}
    (= {user-id} (ctx/get ctx :path-params :id))
    (aio/pure {:status 200 :body (get-user user-id)}))))
```

**Acceptance Criteria:**
- [ ] Path params extracted and added to context
- [ ] Available via `ctx/get ctx :path-params`
- [ ] Multiple params supported (`/users/:uid/posts/:pid`)

#### R8.3: Route Groups
```lisp
(def {api-router}
  (router/group "/api/v1"
    (router/get "/users" list-users)
    (router/get "/posts" list-posts)))

; Equivalent to /api/v1/users, /api/v1/posts
```

**Acceptance Criteria:**
- [ ] `router/group` prefixes all routes
- [ ] Groups can be nested
- [ ] Filters can be applied to groups

#### R8.4: 404 Handling
```lisp
(def {router}
  (router/new
    (router/get "/users" list-users)
    (router/not-found custom-404-svc)))  ; Optional custom 404
```

**Acceptance Criteria:**
- [ ] Default 404 response for unmatched routes
- [ ] Custom 404 handler optional
- [ ] 404 handler receives original request

---

## Implementation Plan

### Phase 1: Core Abstractions (2-3 weeks)

#### Week 1: Foundation
1. **Context implementation** (ctx.valk)
   - Immutable map wrapper with :aio support
   - `ctx/new`, `ctx/with-aio`, `ctx/empty`
   - Standard accessors including `ctx/aio`
   - Context-aware async wrappers: `ctx/sleep`, `ctx/delay`, `ctx/timeout`
   - Unit tests

2. **Service abstraction** (service.valk)
   - `svc/new` function
   - Service invocation protocol
   - Basic composition (`svc/and-then`, `svc/zip`)

#### Week 2: Filters
3. **Filter abstraction** (filter.valk)
   - `filter/new` function
   - `filter/apply` function
   - `filter/compose` function
   - Short-circuit behavior

4. **HTTP data types** (http_data.valk)
   - Request/response as maps
   - Helper constructors
   - Accessor functions

#### Week 3: Integration
5. **Adapter layer** (http_adapter.valk)
   - `http/service->handler` adapter
   - Request conversion (C ref → map)
   - Response conversion (map → C format)

6. **HTTP client as Service** (http_client_service.valk)
   - Wrap existing client in Service interface
   - Request/response conversion

### Phase 2: Standard Filters (2 weeks)

#### Week 4: Basic Filters
1. Timing filter
2. Logging filter
3. Timeout filter
4. Auth filter

#### Week 5: Advanced Filters
5. Retry filter
6. Circuit breaker filter
7. Rate limiting filter
8. Tracing filter (basic)

### Phase 3: Router (1 week)

#### Week 6: Routing
1. Route matching engine
2. Path parameter extraction
3. Route groups
4. Method matching

### Phase 4: Advanced Features (2+ weeks)

1. Full distributed tracing integration
2. Metrics collection
3. Connection pooling
4. Load balancing
5. Native server support (bypass adapter)

---

## API Specification

### Module: ctx

```lisp
; Context creation
(ctx/empty) -> Context                    ; Empty context (no :aio)
(ctx/with-aio sys) -> Context             ; Context with just :aio
(ctx/new sys map) -> Context              ; Context with :aio and initial values

; Context access
(ctx/get ctx key) -> Value | nil
(ctx/get-or ctx key default) -> Value
(ctx/has? ctx key) -> Bool

; Context derivation
(ctx/set ctx key value) -> Context
(ctx/merge ctx map) -> Context
(ctx/remove ctx key) -> Context

; Standard keys
(ctx/aio ctx) -> AioSystem | nil          ; CRITICAL: the AIO system
(ctx/trace-id ctx) -> String | nil
(ctx/span-id ctx) -> String | nil
(ctx/deadline ctx) -> Integer | nil
(ctx/timeout-ms ctx) -> Integer | nil
(ctx/user-id ctx) -> String | nil
(ctx/request-id ctx) -> String | nil
(ctx/path-params ctx) -> Map | nil

; Context-aware async primitives (extract :aio automatically)
(ctx/sleep ctx ms) -> Handle[nil]         ; Sleep for ms milliseconds
(ctx/delay ctx ms fn) -> Handle[Result]   ; Sleep then call fn
(ctx/timeout ctx ms handle) -> Handle[T]  ; Race handle against timeout
(ctx/schedule ctx ms fn) -> Handle[nil]   ; Schedule callback after ms
```

### Module: svc

```lisp
; Service creation
(svc/new fn) -> Service
; where fn = (\ {req ctx} -> Handle[Res])

; Service composition
(svc/and-then svc1 svc2) -> Service
(svc/zip svc1 svc2) -> Service
(svc/map svc fn) -> Service  ; transform response

; Service invocation (services are callable)
(my-service req ctx) -> Handle[Res]
```

### Module: filter

```lisp
; Filter creation
(filter/new fn) -> Filter
; where fn = (\ {req ctx svc} -> Handle[Res])

; Filter application
(filter/apply filter service) -> Service

; Filter composition  
(filter/compose filter1 filter2 ...) -> Filter

; Standard filters
(filter/timing opts) -> Filter
(filter/logging opts) -> Filter
(filter/tracing opts) -> Filter
(filter/timeout ms) -> Filter
(filter/retry opts) -> Filter
(filter/circuit-breaker opts) -> Filter
(filter/rate-limit opts) -> Filter
(filter/auth opts) -> Filter
```

### Module: http

```lisp
; Request construction
(http/request method path) -> Request
(http/request method path opts) -> Request

; Response construction
(http/response status) -> Response
(http/response status opts) -> Response

; Accessors
(http/method req) -> String
(http/path req) -> String
(http/status resp) -> Integer
(http/body req-or-resp) -> String | nil
(http/header req-or-resp name) -> String | nil
(http/headers req-or-resp) -> Map

; Predicates
(http/ok? resp) -> Bool
(http/redirect? resp) -> Bool
(http/client-error? resp) -> Bool
(http/server-error? resp) -> Bool

; Client
(http/client aio host port) -> Service

; Server adapter
(http/service->handler service) -> LegacyHandler
```

### Module: router

```lisp
; Route definition
(router/new route1 route2 ...) -> Service

; Method-specific routes
(router/get path service) -> Route
(router/post path service) -> Route
(router/put path service) -> Route
(router/delete path service) -> Route
(router/patch path service) -> Route
(router/any path service) -> Route

; Route groups
(router/group prefix route1 route2 ...) -> Route

; Error handling
(router/not-found service) -> Route
```

---

## Examples

### Example 1: Basic Service with Filters

```lisp
(load "src/service.valk")
(load "src/filter.valk")
(load "src/http.valk")

; Define a simple service
(def {hello-service}
  (svc/new (\ {req ctx}
    (aio/pure (http/response 200 {:body "Hello, World!"})))))

; Add logging and timing
(def {app}
  (|> hello-service
      (filter/apply (filter/logging {:level :info}))
      (filter/apply (filter/timing {:on-complete log-timing}))))

; Convert to handler and serve
(def {handler} (http/service->handler app))
(http2/server-listen aio 8080 handler)
```

### Example 2: Authentication Filter

```lisp
; Auth filter that validates JWT and adds user to context
(def {jwt-auth}
  (filter/new (\ {req ctx svc}
    (= {auth-header} (http/header req "authorization"))
    (if (nil? auth-header)
      {(aio/pure (http/response 401 {:body "Missing Authorization header"}))}
      {(= {token} (string/strip-prefix auth-header "Bearer "))
       (= {claims} (jwt/verify token SECRET))
       (if (error? claims)
         {(aio/pure (http/response 401 {:body "Invalid token"}))}
         {(svc req (ctx/merge ctx {:user-id (claims :sub)
                                   :user-role (claims :role)}))})}))))

; Apply to protected routes
(def {protected-api}
  (|> users-service
      (filter/apply jwt-auth)))
```

### Example 3: Retry with Circuit Breaker

```lisp
; Configure retry
(def {retry}
  (filter/retry {:max-attempts 3
                 :backoff-ms (list 100 500 2000)
                 :retryable? (\ {res} (>= (http/status res) 500))}))

; Configure circuit breaker
(def {breaker}
  (filter/circuit-breaker {:failure-threshold 5
                           :success-threshold 2
                           :timeout-ms 30000
                           :is-failure? (\ {res} (>= (http/status res) 500))}))

; Resilient client
(def {resilient-client}
  (|> (http/client aio "unreliable-api.com" 443)
      (filter/apply retry)
      (filter/apply breaker)
      (filter/apply (filter/timeout 5000))))
```

### Example 4: Distributed Tracing

```lisp
; Tracing filter that propagates trace context
(def {tracing}
  (filter/new (\ {req ctx svc}
    ; Get or create trace-id
    (= {trace-id} (or (ctx/trace-id ctx)
                      (http/header req "x-trace-id")
                      (uuid/v4)))
    ; Create new span
    (= {span-id} (uuid/v4))
    (= {parent-span} (or (ctx/span-id ctx)
                         (http/header req "x-span-id")))
    
    ; Update context
    (= {traced-ctx} (ctx/merge ctx {:trace-id trace-id
                                    :span-id span-id
                                    :parent-span-id parent-span}))
    
    ; Record span start
    (tracer/start-span trace-id span-id parent-span (http/path req))
    
    ; Call service and record completion
    (aio/finally
      (svc req traced-ctx)
      (\ {} (tracer/end-span trace-id span-id))))))

; Apply to all services
(def {traced-app}
  (|> my-router
      (filter/apply tracing)))
```

### Example 5: Router with Path Parameters

```lisp
; Define services
(def {list-users}
  (svc/new (\ {req ctx}
    (= {users} (db/query "SELECT * FROM users"))
    (aio/pure (http/response 200 {:body (json/encode users)})))))

(def {get-user}
  (svc/new (\ {req ctx}
    (= {id} (ctx/get ctx :path-params :id))
    (= {user} (db/query-one "SELECT * FROM users WHERE id = ?" id))
    (if (nil? user)
      {(aio/pure (http/response 404 {:body "User not found"}))}
      {(aio/pure (http/response 200 {:body (json/encode user)}))}))))

(def {create-user}
  (svc/new (\ {req ctx}
    (= {body} (json/decode (http/body req)))
    (= {id} (db/insert "users" body))
    (aio/pure (http/response 201 {:body (json/encode {:id id})})))))

; Build router
(def {api}
  (router/new
    (router/get "/users" list-users)
    (router/get "/users/:id" get-user)
    (router/post "/users" create-user)
    (router/not-found (svc/new (\ {req ctx}
      (aio/pure (http/response 404 {:body "Not Found"})))))))

; Apply global filters
(def {app}
  (|> api
      (filter/apply jwt-auth)
      (filter/apply (filter/logging {}))
      (filter/apply tracing)))
```

### Example 6: Unit Testing Services

```lisp
; Test without network!
(def {test-get-user}
  (\ {}
    ; Create test context (nil for :aio since we don't need async in this test)
    (= {ctx} (ctx/new nil {:path-params {:id "123"}}))
    
    ; Create test request (plain data)
    (= {req} (http/request "GET" "/users/123"))
    
    ; Mock database
    (with-mock db/query-one (\ {_ _} {:id "123" :name "Alice"})
      ; Call service directly
      (= {resp-handle} (get-user req ctx))
      
      ; Verify response
      (= {resp} (aio/await resp-handle))
      (assert-eq (http/status resp) 200)
      (assert-eq (json/decode (http/body resp)) {:id "123" :name "Alice"}))))
```

### Example 7: Async Handler with ctx/sleep (Fixing the webserver_demo bug)

```lisp
; WRONG - This is the bug in webserver_demo.valk:
; (aio/do {
;   (<- _ (aio/sleep 2000))  ; ERROR: aio/sleep needs sys!
;   {:status "200" :body "done"}})

; CORRECT - Using ctx/sleep with Service API:
(def {slow-handler}
  (svc/new (\ {req ctx}
    ; ctx/sleep extracts :aio from context automatically
    (aio/then (ctx/sleep ctx 2000)
      (\ {_} (aio/pure {:status "200" :body "slept 2s"}))))))

; Or using aio/do with explicit aio extraction:
(def {slow-handler-do}
  (svc/new (\ {req ctx}
    (= {sys} (ctx/aio ctx))
    (aio/do {
      (println "Starting sleep...")
      (<- _ (aio/sleep sys 2000))  ; sys explicitly passed
      (println "Done!")
      {:status "200" :body "slept 2s"}}))))

; Serving the handler:
(def {sys} (aio/start))
(def {handler} (http/service->handler slow-handler))
(http2/server-listen sys 8443 handler)
(aio/run sys)
```

---

## Test Cases

### TC1: Context Operations

```lisp
; TC1.1: Empty context
(def {ctx} (ctx/empty))
(assert (nil? (ctx/get ctx :foo)))
(assert (not (ctx/has? ctx :foo)))

; TC1.2: Context with AIO system
(def {sys} (aio/start))
(def {ctx} (ctx/with-aio sys))
(assert-eq (ctx/aio ctx) sys)
(assert (nil? (ctx/get ctx :foo)))

; TC1.3: Context with values and AIO
(def {ctx} (ctx/new sys {:a 1 :b 2}))
(assert-eq (ctx/aio ctx) sys)
(assert-eq (ctx/get ctx :a) 1)
(assert-eq (ctx/get ctx :b) 2)
(assert (ctx/has? ctx :a))

; TC1.4: Context derivation (immutability)
(def {ctx1} (ctx/new sys {:a 1}))
(def {ctx2} (ctx/set ctx1 :b 2))
(assert-eq (ctx/get ctx1 :a) 1)
(assert (nil? (ctx/get ctx1 :b)))  ; Original unchanged
(assert-eq (ctx/get ctx2 :a) 1)
(assert-eq (ctx/get ctx2 :b) 2)

; TC1.5: Default values
(def {ctx} (ctx/empty))
(assert-eq (ctx/get-or ctx :timeout 5000) 5000)

; TC1.6: Merge
(def {ctx1} (ctx/new sys {:a 1 :b 2}))
(def {ctx2} (ctx/merge ctx1 {:b 3 :c 4}))
(assert-eq (ctx/get ctx2 :a) 1)
(assert-eq (ctx/get ctx2 :b) 3)  ; Overwritten
(assert-eq (ctx/get ctx2 :c) 4)
(assert-eq (ctx/aio ctx2) sys)   ; AIO preserved through merge

; TC1.7: Context-aware sleep (ctx/sleep)
(def {ctx} (ctx/with-aio sys))
(= {start} (time/now))
(= {handle} (ctx/sleep ctx 100))
(aio/await handle)
(assert (>= (- (time/now) start) 100))

; TC1.8: ctx/sleep fails gracefully without :aio
(def {ctx} (ctx/empty))
(= {result} (ctx/sleep ctx 100))
(assert (error? result))
(assert (string/contains? (str result) ":aio"))

; TC1.9: Context-aware delay (ctx/delay)
(def {ctx} (ctx/with-aio sys))
(def {called} false)
(= {handle} (ctx/delay ctx 50 (\ {} (def {called} true) {:done true})))
(= {result} (aio/await handle))
(assert called)
(assert-eq (result :done) true)

; TC1.10: Context-aware timeout (ctx/timeout)
(def {ctx} (ctx/with-aio sys))
(= {fast-handle} (aio/pure "fast"))
(= {result} (aio/await (ctx/timeout ctx 1000 fast-handle)))
(assert-eq result "fast")

; TC1.11: ctx/timeout actually times out
(def {ctx} (ctx/with-aio sys))
(= {slow-handle} (ctx/sleep ctx 5000))
(= {result} (aio/await-catch (ctx/timeout ctx 50 slow-handle)))
(assert (error? result))
```

### TC2: Service Operations

```lisp
; TC2.1: Basic service creation and invocation
(def {echo-svc}
  (svc/new (\ {req ctx}
    (aio/pure {:echo req}))))

(= {result} (aio/await (echo-svc {:msg "hello"} (ctx/empty))))
(assert-eq (result :echo) {:msg "hello"})

; TC2.2: Async service using ctx/sleep
(def {delayed-svc}
  (svc/new (\ {req ctx}
    (aio/then (ctx/sleep ctx 100)
      (\ {_} (aio/pure {:delayed true}))))))

(def {sys} (aio/start))
(def {ctx} (ctx/with-aio sys))
(= {start} (time/now))
(= {result} (aio/await (delayed-svc {} ctx)))
(assert (>= (- (time/now) start) 100))
(assert-eq (result :delayed) true)

; TC2.3: Service composition with and-then
(def {svc1} (svc/new (\ {req ctx} (aio/pure (+ req 1)))))
(def {svc2} (svc/new (\ {req ctx} (aio/pure (* req 2)))))
(def {composed} (svc/and-then svc1 svc2))

(= {result} (aio/await (composed 5 (ctx/empty))))
(assert-eq result 12)  ; (5 + 1) * 2

; TC2.4: Service zip
(def {svc1} (svc/new (\ {req ctx} (aio/pure "a"))))
(def {svc2} (svc/new (\ {req ctx} (aio/pure "b"))))
(def {zipped} (svc/zip svc1 svc2))

(= {result} (aio/await (zipped {} (ctx/empty))))
(assert-eq result (list "a" "b"))
```

### TC3: Filter Operations

```lisp
; TC3.1: Basic filter
(def {prefix-filter}
  (filter/new (\ {req ctx svc}
    (aio/then (svc req ctx)
      (\ {res} (aio/pure (str "PREFIX:" res)))))))

(def {base-svc} (svc/new (\ {req ctx} (aio/pure "hello"))))
(def {filtered} (filter/apply prefix-filter base-svc))

(= {result} (aio/await (filtered {} (ctx/empty))))
(assert-eq result "PREFIX:hello")

; TC3.2: Filter that modifies request
(def {add-header-filter}
  (filter/new (\ {req ctx svc}
    (= {req'} (assoc req :x-added "value"))
    (svc req' ctx))))

(def {echo-svc} (svc/new (\ {req ctx} (aio/pure req))))
(def {filtered} (filter/apply add-header-filter echo-svc))

(= {result} (aio/await (filtered {:original true} (ctx/empty))))
(assert-eq (result :original) true)
(assert-eq (result :x-added) "value")

; TC3.3: Filter that modifies context
(def {add-ctx-filter}
  (filter/new (\ {req ctx svc}
    (svc req (ctx/set ctx :added "from-filter")))))

(def {ctx-svc} (svc/new (\ {req ctx} (aio/pure (ctx/get ctx :added)))))
(def {filtered} (filter/apply add-ctx-filter ctx-svc))

(= {result} (aio/await (filtered {} (ctx/empty))))
(assert-eq result "from-filter")

; TC3.4: Short-circuit filter
(def {short-circuit}
  (filter/new (\ {req ctx svc}
    (if (req :block)
      {(aio/pure {:blocked true})}
      {(svc req ctx)}))))

(def {base-svc} (svc/new (\ {req ctx} (aio/pure {:reached true}))))
(def {filtered} (filter/apply short-circuit base-svc))

; Should reach service
(= {result} (aio/await (filtered {:block false} (ctx/empty))))
(assert-eq (result :reached) true)

; Should short-circuit
(= {result} (aio/await (filtered {:block true} (ctx/empty))))
(assert-eq (result :blocked) true)

; TC3.5: Filter composition order
(def {outer} (filter/new (\ {req ctx svc}
  (aio/then (svc req ctx) (\ {res} (aio/pure (str "O(" res ")")))))))
  
(def {inner} (filter/new (\ {req ctx svc}
  (aio/then (svc req ctx) (\ {res} (aio/pure (str "I(" res ")")))))))

(def {base} (svc/new (\ {req ctx} (aio/pure "X"))))

; Compose: outer wraps inner wraps base
(def {composed} (filter/compose outer inner))
(def {filtered} (filter/apply composed base))

(= {result} (aio/await (filtered {} (ctx/empty))))
(assert-eq result "O(I(X))")
```

### TC4: HTTP Data Types

```lisp
; TC4.1: Request construction
(def {req} (http/request "GET" "/users"))
(assert-eq (http/method req) "GET")
(assert-eq (http/path req) "/users")

; TC4.2: Request with options
(def {req} (http/request "POST" "/users" 
  {:headers {:content-type "application/json"}
   :body "{\"name\": \"Alice\"}"}))
(assert-eq (http/header req "content-type") "application/json")
(assert-eq (http/body req) "{\"name\": \"Alice\"}")

; TC4.3: Response construction
(def {resp} (http/response 200 {:body "OK"}))
(assert-eq (http/status resp) 200)
(assert-eq (http/body resp) "OK")

; TC4.4: Response predicates
(assert (http/ok? (http/response 200)))
(assert (http/ok? (http/response 201)))
(assert (not (http/ok? (http/response 404))))
(assert (http/client-error? (http/response 404)))
(assert (http/server-error? (http/response 500)))
```

### TC5: Standard Filters

```lisp
; TC5.1: Timeout filter - success
(def {fast-svc} (svc/new (\ {req ctx}
  (aio/then (aio/sleep aio 50) (\ {_} (aio/pure {:ok true}))))))
(def {timed} (filter/apply (filter/timeout 1000) fast-svc))

(= {result} (aio/await (timed {} (ctx/empty))))
(assert-eq (result :ok) true)

; TC5.2: Timeout filter - timeout
(def {slow-svc} (svc/new (\ {req ctx}
  (aio/then (aio/sleep aio 5000) (\ {_} (aio/pure {:ok true}))))))
(def {timed} (filter/apply (filter/timeout 100) slow-svc))

(= {result} (aio/await-catch (timed {} (ctx/empty))))
(assert (error? result))
(assert (string/contains? (str result) "timeout"))

; TC5.3: Retry filter - eventual success
(def {attempts} 0)
(def {flaky-svc} (svc/new (\ {req ctx}
  (def {attempts} (+ attempts 1))
  (if (< attempts 3)
    {(aio/pure (http/response 500))}
    {(aio/pure (http/response 200))}))))

(def {retried} (filter/apply 
  (filter/retry {:max-attempts 5 :retryable? (\ {r} (>= (http/status r) 500))})
  flaky-svc))

(= {result} (aio/await (retried {} (ctx/empty))))
(assert-eq (http/status result) 200)
(assert-eq attempts 3)

; TC5.4: Auth filter - valid token
(def {auth} (filter/auth {:validator (\ {token} (if (== token "valid") {:user "alice"} nil))}))
(def {protected} (svc/new (\ {req ctx} (aio/pure {:user (ctx/get ctx :user)}))))
(def {app} (filter/apply auth protected))

(= {req} (http/request "GET" "/" {:headers {:authorization "Bearer valid"}}))
(= {result} (aio/await (app req (ctx/empty))))
(assert-eq (result :user) {:user "alice"})

; TC5.5: Auth filter - invalid token
(= {req} (http/request "GET" "/" {:headers {:authorization "Bearer invalid"}}))
(= {result} (aio/await (app req (ctx/empty))))
(assert-eq (http/status result) 401)
```

### TC6: Router

```lisp
; TC6.1: Basic routing
(def {svc-a} (svc/new (\ {req ctx} (aio/pure {:route "a"}))))
(def {svc-b} (svc/new (\ {req ctx} (aio/pure {:route "b"}))))

(def {router}
  (router/new
    (router/get "/a" svc-a)
    (router/get "/b" svc-b)))

(= {result} (aio/await (router (http/request "GET" "/a") (ctx/empty))))
(assert-eq (result :route) "a")

(= {result} (aio/await (router (http/request "GET" "/b") (ctx/empty))))
(assert-eq (result :route) "b")

; TC6.2: Path parameters
(def {user-svc} (svc/new (\ {req ctx}
  (aio/pure {:id (ctx/get ctx :path-params :id)}))))

(def {router}
  (router/new
    (router/get "/users/:id" user-svc)))

(= {result} (aio/await (router (http/request "GET" "/users/123") (ctx/empty))))
(assert-eq (result :id) "123")

; TC6.3: Method matching
(def {get-svc} (svc/new (\ {req ctx} (aio/pure {:method "get"}))))
(def {post-svc} (svc/new (\ {req ctx} (aio/pure {:method "post"}))))

(def {router}
  (router/new
    (router/get "/resource" get-svc)
    (router/post "/resource" post-svc)))

(= {result} (aio/await (router (http/request "GET" "/resource") (ctx/empty))))
(assert-eq (result :method) "get")

(= {result} (aio/await (router (http/request "POST" "/resource") (ctx/empty))))
(assert-eq (result :method) "post")

; TC6.4: 404 handling
(= {result} (aio/await (router (http/request "GET" "/nonexistent") (ctx/empty))))
(assert-eq (http/status result) 404)

; TC6.5: Route groups
(def {v1-svc} (svc/new (\ {req ctx} (aio/pure {:version 1}))))

(def {router}
  (router/new
    (router/group "/api/v1"
      (router/get "/users" v1-svc))))

(= {result} (aio/await (router (http/request "GET" "/api/v1/users") (ctx/empty))))
(assert-eq (result :version) 1)
```

### TC7: Integration Tests

```lisp
; TC7.1: Full stack - client calls server
(def {server-svc}
  (svc/new (\ {req ctx}
    (aio/pure (http/response 200 {:body "Hello from server"})))))

(def {handler} (http/service->handler server-svc))
(http2/server-listen aio 9999 handler)

(def {client} (http/client aio "127.0.0.1" 9999))
(= {resp} (aio/await (client (http/request "GET" "/") (ctx/empty))))
(assert-eq (http/status resp) 200)
(assert-eq (http/body resp) "Hello from server")

; TC7.2: Context propagation through filters
(def {trace-ids} (list))

(def {record-trace}
  (filter/new (\ {req ctx svc}
    (def {trace-ids} (cons (ctx/trace-id ctx) trace-ids))
    (svc req ctx))))

(def {set-trace}
  (filter/new (\ {req ctx svc}
    (svc req (ctx/set ctx :trace-id "trace-123")))))

(def {base} (svc/new (\ {req ctx} (aio/pure {:ok true}))))
(def {app} (|> base (filter/apply record-trace) (filter/apply set-trace)))

(aio/await (app {} (ctx/empty)))
(assert-eq (head trace-ids) "trace-123")

; TC7.3: Error propagation
(def {failing-svc}
  (svc/new (\ {req ctx}
    (aio/fail "Something went wrong"))))

(def {with-fallback}
  (filter/new (\ {req ctx svc}
    (aio/catch (svc req ctx)
      (\ {err} (aio/pure (http/response 500 {:body (str err)})))))))

(def {app} (filter/apply with-fallback failing-svc))
(= {resp} (aio/await (app {} (ctx/empty))))
(assert-eq (http/status resp) 500)
```

---

## Migration Strategy

### Step 1: Add New API Alongside Existing

The new Service/Filter API will be added as new modules without modifying existing code:
- `src/modules/service/ctx.valk`
- `src/modules/service/service.valk`
- `src/modules/service/filter.valk`
- `src/modules/service/http.valk`
- `src/modules/service/router.valk`

### Step 2: Create Adapter Layer

`http/service->handler` bridges new services to existing runtime:
```lisp
(fun {http/service->handler service}
  (\ {req}  ; Legacy handler receives C request ref
    ; Convert C ref to data map
    (= {req-map} {:method (req/method req)
                  :path (req/path req)
                  :headers (req/headers req)
                  :body (req/body req)})
    ; Create default context
    (= {ctx} (ctx/empty))
    ; Call service
    (= {resp-handle} (service req-map ctx))
    ; Return handle (runtime handles async)
    (aio/then resp-handle (\ {resp}
      ; Convert response map back to expected format
      {:status (str (resp :status))
       :body (resp :body)
       :headers (resp :headers)}))))
```

### Step 3: Migrate Incrementally

1. New endpoints use Service/Filter API
2. Existing handlers wrapped with `svc/from-legacy`:
   ```lisp
   (def {legacy-as-service}
     (svc/from-legacy old-handler))
   ```
3. Gradually rewrite handlers to native Service API

### Step 4: Deprecate Legacy API

After all handlers migrated:
1. Mark legacy functions as deprecated
2. Remove legacy code in future version

---

## Success Criteria

### Functional Criteria

| ID | Criterion | Validation |
|----|-----------|------------|
| F1 | Services can be composed with `and-then` and `zip` | TC2.3, TC2.4 |
| F2 | Filters can intercept and modify requests | TC3.2 |
| F3 | Filters can intercept and modify responses | TC3.1 |
| F4 | Filters can short-circuit (not call downstream) | TC3.4 |
| F5 | Context is immutable and propagates correctly | TC1.3, TC7.2 |
| F6 | Requests/responses are plain data structures | TC4.* |
| F7 | Router extracts path parameters | TC6.2 |
| F8 | Standard filters work correctly | TC5.* |
| F9 | Services can be unit tested without network | Example 6 |
| F10 | Adapter bridges to existing C runtime | TC7.1 |
| F11 | ctx/sleep works without explicit sys argument | TC1.7, TC1.9 |
| F12 | ctx/* fails gracefully when :aio is nil | TC1.8 |

### Performance Criteria

| ID | Criterion | Target | Validation |
|----|-----------|--------|------------|
| P1 | Filter overhead per request | < 100μs | Benchmark |
| P2 | Context creation/derivation | < 10μs | Benchmark |
| P3 | Router path matching | < 50μs for 100 routes | Benchmark |
| P4 | Memory per request | < 1KB overhead | Memory profiling |

### Quality Criteria

| ID | Criterion | Validation |
|----|-----------|------------|
| Q1 | Test coverage > 90% for new modules | Coverage report |
| Q2 | All existing tests pass | CI/CD |
| Q3 | No memory leaks | Valgrind/ASAN |
| Q4 | Documentation complete | Review |

### Usability Criteria

| ID | Criterion | Validation |
|----|-----------|------------|
| U1 | Existing handlers work unchanged | Integration tests |
| U2 | Migration path documented | Documentation review |
| U3 | Examples cover common patterns | Documentation review |
| U4 | Error messages are helpful | Manual testing |

---

## Appendix A: Comparison with Other Frameworks

### Finagle (Twitter/Scala)
- **Service**: `Req => Future[Rep]`
- **Filter**: `(Req, Service[Req, Rep]) => Future[Rep]`
- **Context**: `Local` (thread-local storage)

Our design follows Finagle closely but uses explicit context parameter instead of implicit thread-locals (which don't exist in single-threaded libuv).

### Ring (Clojure)
- **Handler**: `Request -> Response`
- **Middleware**: `Handler -> Handler`

Ring is simpler but less powerful—middleware can only wrap handlers, not compose bidirectionally. Our Filter is more expressive.

### Express (Node.js)
- **Handler**: `(req, res, next) => void`
- **Middleware**: Same signature

Express uses mutation (calling methods on `res`) and callbacks (`next()`). Our design is more functional with immutable data and explicit return values.

### Finatra (Twitter/Scala)
- Builds on Finagle with HTTP-specific conveniences
- Controller-based routing
- Dependency injection

We adopt Finagle's core but simplify routing to be more Lisp-idiomatic.

---

## Appendix B: Future Considerations

### Connection Pooling
```lisp
; Future: Factory that manages connection pool
(def {client-factory}
  (http/client-factory {:host "api.example.com"
                        :port 443
                        :pool-size 10}))

; Acquire connection from pool
(aio/bracket
  (client-factory)
  (\ {client} (client/close client))
  (\ {client} (client request ctx)))
```

### Load Balancing
```lisp
; Future: Load-balanced client
(def {lb-client}
  (http/load-balanced
    {:strategy :round-robin
     :endpoints (list "host1:443" "host2:443" "host3:443")}))
```

### Streaming
```lisp
; Future: Streaming request/response bodies
(def {streaming-svc}
  (svc/new (\ {req ctx}
    (= {body-stream} (http/body-stream req))
    (aio/then (stream/collect body-stream)
      (\ {body} (aio/pure (http/response 200 {:body body})))))))
```

### gRPC Support
```lisp
; Future: Same Service abstraction for gRPC
(def {grpc-svc}
  (svc/new (\ {req ctx}
    ; req is protobuf message
    (aio/pure (make-response ...)))))

(def {grpc-client} (grpc/client "service.example.com" 50051))
```

---

## Appendix C: Naming Alternatives Considered

| Chosen | Alternative | Reason for Choice |
|--------|-------------|-------------------|
| `svc/new` | `service/create`, `make-service` | Short, clear |
| `filter/apply` | `filter/wrap`, `filter/decorate` | "apply" matches Finagle |
| `ctx/set` | `ctx/with`, `ctx/assoc` | "set" is common in FP |
| `http/service->handler` | `http/adapt`, `http/to-handler` | Arrow notation is Clojure idiom |
| `router/get` | `route/GET`, `get-route` | Lowercase matches method strings |

---

## Appendix D: Open Questions

1. **Should `|>` be a builtin or macro?**
   - Currently not defined in prelude
   - Needed for ergonomic filter composition
   - Recommend: Add as macro

2. **How to handle backpressure?**
   - Current aio system doesn't have explicit backpressure
   - Filters like rate-limiter help but aren't complete solution
   - Recommend: Defer to Phase 2

3. **Should Context support deadline propagation?**
   - `ctx/timeout-ms` computes from deadline
   - But who sets the initial deadline?
   - Recommend: HTTP layer sets deadline from client timeout

4. **How to handle websockets?**
   - Service abstraction is request/response oriented
   - Websockets are bidirectional streams
   - Recommend: Separate abstraction, defer to future

5. **Should we support sync services?**
   - All services return `Handle[Res]`
   - Sync is just `aio/pure result`
   - Recommend: Keep unified async model

6. **Should aio/do and aio/let auto-inject sys from context?**
   - Currently they just chain expressions, don't know about context
   - Could add `aio/do-ctx` variant that receives ctx and makes sys available
   - Recommend: Use ctx/* wrappers instead of modifying macros
   - Rationale: Keep aio/* pure, add context-awareness at higher level

7. **Should we fix webserver_demo.valk?**
   - Currently has bug: `(aio/sleep 2000)` missing sys argument
   - Options:
     a. Fix to use `(aio/sleep sys 2000)` - requires passing sys to handler
     b. Wait for Service API and use `(ctx/sleep ctx 2000)`
     c. Define `sys` as global (hacky, not recommended)
   - Recommend: Option (a) as immediate fix, then migrate to Service API
