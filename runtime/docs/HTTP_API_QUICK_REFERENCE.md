# HTTP/2 Quick Reference

HTTP/2 only. All names are `http2/`-prefixed. See [HTTP_API.md](HTTP_API.md) for detail.

## Setup

```lisp
(load "stdlib/http/api.valk")            ; high-level layer (optional)
(def {aio} (aio/await (aio/start)))      ; required for all async work
```

## Primitives (always available)

| Call | Returns |
|---|---|
| `(http2/client-request aio host port path)` | async handle -> response |
| `(http2/client-request-with-headers aio host port path headers)` | async handle -> response |
| `(http2/connect aio host port)` | connection |
| `(http2/response-status resp)` | status **string**, e.g. `"200"` |
| `(http2/response-body resp)` | body string |
| `(http2/response-headers resp)` | headers |
| `(http2/request method scheme host path)` | request |
| `(http2/request-add-header req name value)` | — |
| `(http2/mock-response status body)` | response (testing) |

## Server

| Call | Returns |
|---|---|
| `(http2/server-listen aio port handler)` | server (`port` 0 = auto) |
| `(http2/server-listen aio port handler config)` | server; config qexpr, `:error-handler` |
| `(http2/server-port server)` | resolved port |
| `(http2/server-handle server)` | handle |
| `(http2/server-stop server)` | — |

Handler returns a plist:

```lisp
(\ {req} {`{:status "200" :body "Hello"}})
```

## Request Accessors

```
(req/method req)  (req/path req)    (req/scheme req)   (req/body req)
(req/authority req)  (req/stream-id req)  (req/headers req)  (req/header req name)
```

## Fetching (high-level)

Signature is always `aio host port path` — no URL parsing.

```lisp
(http2/fetch aio host port path)               ; Async Response
(http2/fetch-text aio host port path)          ; Async body
(http2/fetch-ok? aio host port path)           ; Async bool
(http2/fetch-retry aio host port path retries) ; Async Response
```

## Batching

`endpoints` = list of `{host port path}` lists.

```lisp
(http2/fetch-all aio endpoints)
(http2/fetch-all-text aio endpoints)
(http2/parallel async-ops)
(http2/sequential async-ops)
(http2/aggregate aio endpoints combiner)
(http2/fan-out aio host port path extractors)
(http2/health-check aio host port path)
(http2/health-check-all aio endpoints)
```

## Requests & Middleware

```lisp
(http2/get url)                    (http2/post url body)
(http2/make-request method url)
(http2/with-header req name value) (http2/with-headers req headers)

(http2/with-auth token)            (http2/with-user-agent agent)
(http2/with-logging req)           (http2/log-response resp)
(http2/apply-middleware req mw)    (http2/compose-middleware mw-list)
```

## Status

```lisp
(http2/response-ok? resp)          ; 200 <= status < 300
(http2/validate-status expected)   ; -> (\ {resp} ...), errors on mismatch
```

## Routing

```lisp
(http2/route-matches? pattern path)      ; exact == match only
(http2/find-route routes method path)
```

## Errors

```lisp
(error? resp)                  ; direct check
(async/try op)                 ; -> (list "ok" v) | (list "error" e)
(async/recover op fallback)
```

## Minimal Round Trip

```lisp
(def {aio} (aio/await (aio/start)))
(def {srv} (http2/server-listen aio 0 (\ {req} {`{:status "200" :body "hi"}})))

(aio/then (http2/client-request aio "127.0.0.1" (http2/server-port srv) "/") (\ {r} {
  (print (http2/response-status r))
  (http2/server-stop srv)
}))

(aio/run aio)
```
