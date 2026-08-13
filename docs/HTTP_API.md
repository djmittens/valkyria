# HTTP/2 API

Valkyria speaks HTTP/2 only. Every function is prefixed `http2/`.

Two layers:

| Layer | Where | What |
|---|---|---|
| Primitives | C builtins (`src/builtins_server.c`) | Connections, requests, responses, servers |
| High-level | `stdlib/http/api.valk` | Fetch helpers, batching, middleware, routing |

The primitives are always available. The high-level layer must be loaded:

```lisp
(load "stdlib/http/api.valk")
```

Everything async requires an AIO system from `(aio/start)`.

---

## Quick Start

```lisp
(def {aio} (aio/await (aio/start)))

(aio/then (http2/client-request aio "example.com" 443 "/") (\ {resp} {
  (print (http2/response-status resp))
  (print (http2/response-body resp))
}))

(aio/run aio)
```

---

## Primitives (C builtins)

### Client

```lisp
(http2/client-request aio host port path)
; -> async handle resolving to a response

(http2/client-request-with-headers aio host port path headers)
(http2/connect aio host port)
```

`host` is a string, `port` a number, `path` a string.

### Response Accessors

```lisp
(http2/response-status resp)   ; status as a STRING, e.g. "200"
(http2/response-body resp)     ; body string
(http2/response-headers resp)  ; headers
```

Note that the status is a string, not a number. Compare with `(== status "200")`,
or convert via `str->num` before numeric comparison.

### Request Building

```lisp
(http2/request method scheme host path)
(http2/request-add-header req name value)
```

### Server

```lisp
(http2/server-listen aio port handler)          ; port 0 = pick a free port
(http2/server-listen aio port handler config)   ; config is a qexpr plist
(http2/server-port server)                      ; resolved port
(http2/server-handle server)
(http2/server-stop server)
```

A handler takes a request and returns a plist with `:status` and `:body`:

```lisp
(def {handler}
  (\ {req} {
    (= {path} (req/path req))
    (if (== path "/error")
      {`{:status "500" :body "Internal Server Error"}}
      {`{:status "200" :body "Hello"}})
  }))

(def {server} (http2/server-listen aio 0 handler))
(def {port} (http2/server-port server))
```

The optional config qexpr supports `:error-handler`, a function of one argument
(the status code) returning a string body used for 503 responses.

### Request Accessors

```lisp
(req/method req)     (req/path req)       (req/scheme req)
(req/authority req)  (req/body req)       (req/stream-id req)
(req/header req name)                     (req/headers req)
```

### Testing

```lisp
(http2/mock-response status body)
```

---

## High-Level API (`stdlib/http/api.valk`)

### Fetching

All fetch functions take `aio host port path` — there is no URL-parsing form.
They return async values, composed with `async/bind` or invoked via `aio/then`.

```lisp
(http2/fetch aio host port path)        ; -> Async Response
(http2/fetch-async aio host port path)  ; same, explicit continuation form
(http2/fetch-text aio host port path)   ; -> Async body string
(http2/fetch-ok? aio host port path)    ; -> Async bool (2xx)
(http2/fetch-retry aio host port path max-retries)
```

Example:

```lisp
(async/bind (http2/fetch aio "example.com" 443 "/") (\ {resp} {
  (async/pure (http2/response-status resp))
}))
```

### Request Construction

```lisp
(http2/get url)                      ; GET request object
(http2/post url body)                ; POST (body support is a TODO in stdlib)
(http2/make-request method url)
(http2/with-header req name value)   ; chainable
(http2/with-headers req headers)     ; headers = list of {name value} pairs
```

### Status Checking

```lisp
(http2/response-ok? resp)            ; true when 200 <= status < 300
(http2/validate-status expected)     ; -> (\ {resp} ...) errors on mismatch
```

### Batch Operations

`endpoints` is a list of `{host port path}` lists.

```lisp
(http2/fetch-all aio endpoints)       ; -> Async list of responses
(http2/fetch-all-text aio endpoints)  ; -> Async list of bodies
(http2/parallel async-ops)            ; async/collect
(http2/sequential async-ops)          ; async/sequence
```

```lisp
(http2/fetch-all aio (list
  (list "example.com" 443 "/a")
  (list "example.com" 443 "/b")))
```

### Composite Patterns

```lisp
(http2/fan-out aio host port path extractors)   ; extractors -> {host port path}
(http2/aggregate aio endpoints combiner)        ; fetch all, then combine
(http2/health-check aio host port path)         ; -> Async bool
(http2/health-check-all aio endpoints)          ; -> Async list of bools
```

### Middleware

Middleware is a plain function `Request -> Request`.

```lisp
(http2/with-auth token)         ; -> middleware adding "authorization"
(http2/with-user-agent agent)   ; -> middleware setting "user-agent"
(http2/with-logging req)        ; prints and returns req
(http2/log-response resp)       ; prints status and returns resp

(http2/apply-middleware req middleware)
(http2/compose-middleware middleware-list)
```

```lisp
(= {mw} (http2/compose-middleware (list
  (http2/with-auth "Bearer tok")
  (http2/with-user-agent "svc/1.0"))))

(= {req} (mw (http2/get "example.com")))
```

### Routing

Server-side routing is minimal — path matching is exact equality, not pattern
matching.

```lisp
(http2/route-matches? pattern path)         ; == comparison
(http2/find-route routes method path)       ; routes = list of {method path handler}
```

### Error Handling

There are no HTTP-specific error combinators. Use the async ones from
`stdlib/aio/monadic.valk`:

```lisp
(async/try op)               ; -> (list "ok" result) | (list "error" err)
(async/recover op fallback)  ; fall back on error
```

Check for errors directly with `error?`:

```lisp
(aio/then (http2/client-request aio host port "/") (\ {resp} {
  (if (error? resp) {(print "failed")} {(print (http2/response-body resp))})
}))
```

---

## Complete Example: Server + Client

```lisp
(load "stdlib/http/api.valk")

(def {aio} (aio/await (aio/start)))

(def {server}
  (http2/server-listen aio 0 (\ {req} {
    `{:status "200" :body "Hello"}
  })))

(def {port} (http2/server-port server))

(aio/then (http2/client-request aio "127.0.0.1" port "/") (\ {resp} {
  (print (http2/response-status resp))   ; "200"
  (http2/server-stop server)
}))

(aio/run aio)
```

---

## See Also

- [HTTP_API_QUICK_REFERENCE.md](HTTP_API_QUICK_REFERENCE.md) - Cheat sheet
- [ASYNC_IO.md](ASYNC_IO.md) - Async handles and combinators
- `stdlib/http/api.valk` - High-level API source
- `test/http/` - Working integration tests
