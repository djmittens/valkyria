# HTTP API Quick Reference

## Loading the API

```lisp
(load "src/prelude.valk")
(load "src/http_api.valk")
```

## Basic Requests

```lisp
; GET request
(def {req} (http-get "example.com"))

; POST request
(def {req} (http-post "api.example.com" "body"))

; Custom method
(def {req} (http-request "PUT" "api.example.com"))
```

## Adding Headers

```lisp
; Single header
(def {req} (with-header req "x-api-key" "secret"))

; Multiple headers
(def {req} (with-headers req (list
  (list "authorization" "Bearer token")
  (list "content-type" "application/json"))))
```

## Fetching URLs

```lisp
; Simple fetch (async operation)
(def {fetch-op} (fetch "example.com"))
(def {response} (run-async fetch-op))

; Synchronous-style
(def {response} (fetch-sync "example.com"))

; Just get the body
(def {text} (run-async (fetch-text "example.com")))

; Check if successful
(def {ok} (run-async (fetch-ok "example.com")))
```

## Response Handling

```lisp
; Extract parts
(def {status} (response-status resp))
(def {body} (response-body resp))
(def {headers} (response-headers resp))

; Check success
(if (response-ok resp)
  {(print "Success!")}
  {(print "Failed")})
```

## Batch Operations

```lisp
; Fetch multiple URLs
(def {urls} (list "a.com" "b.com" "c.com"))
(def {responses} (run-async (fetch-all urls)))

; Just get bodies
(def {bodies} (run-async (fetch-all-text urls)))

; Health checks
(def {healthy} (run-async (health-check-all urls)))
```

## Middleware

```lisp
; Authentication
(def {auth} (with-auth "Bearer token"))
(def {req} (auth (http-get "api.example.com")))

; User agent
(def {ua} (with-user-agent "MyApp/1.0"))
(def {req} (ua (http-get "api.example.com")))

; Compose multiple
(def {mw} (compose-middleware (list
  (with-auth "Bearer token")
  (with-user-agent "MyApp/1.0"))))
(def {req} (mw (http-get "api.example.com")))
```

## Patterns

```lisp
; Parallel (currently sequential)
(def {results} (run-async (parallel (list
  (fetch "a.com")
  (fetch "b.com")
  (fetch "c.com")))))

; Sequential
(def {final} (run-async (sequential (list
  (fetch "log.com")
  (fetch "process.com")
  (fetch "notify.com")))))

; Aggregate
(def {result} (run-async (aggregate
  (list "api1.com" "api2.com")
  (\ {responses} {(list (response-body (head responses)))}))))
```

## Error Handling

```lisp
; With default value
(def {result} (run-async
  (async-or-default (fetch "might-fail.com") "default")))

; With error handler
(def {result} (run-async
  (async-try (fetch "risky.com")
    (\ {err} {(async-pure "fallback")}))))
```

## Chaining Operations

```lisp
; Using async-bind
(def {result} (run-async
  (async-bind (fetch "user.com") (\ {resp} {
    (def {body} (response-body resp))
    (fetch-text "posts.com")
  }))))

; Using async-pipe
(def {transform} (\ {resp} {(\ {k} {(k (response-body resp))})}))
(def {result} (run-async
  (async-pipe (fetch "data.com") (list transform))))
```

## Complete Example: Authenticated POST

```lisp
; 1. Create request
(def {req} (http-post "api.example.com/users" "{\"name\":\"Alice\"}"))

; 2. Add headers
(def {req} (with-header req "authorization" "Bearer my-token"))
(def {req} (with-header req "content-type" "application/json"))

; 3. Send request
(def {resp} (run-async (fetch-with-request "api.example.com" req)))

; 4. Handle response
(if (response-ok resp)
  {(print "Created:" (response-body resp))}
  {(print "Failed:" (response-status resp))})
```

## Complete Example: Batch Health Checks

```lisp
; Define services
(def {services} (list
  "api1.example.com/health"
  "api2.example.com/health"
  "api3.example.com/health"))

; Check all
(def {results} (run-async (health-check-all services)))

; Print results
(print "Service health:" results)
; Output: (1 1 0) - first two healthy, third down
```

## Complete Example: Middleware Pipeline

```lisp
; Define middleware
(def {with-logging} (\ {req} {
  (print "Sending request:" req)
  req
}))

(def {middleware} (compose-middleware (list
  (with-auth "Bearer secret")
  (with-user-agent "MyApp/2.0")
  with-logging)))

; Apply to request
(def {req} (middleware (http-get "api.example.com/data")))

; Send
(def {resp} (run-async (fetch-with-request "api.example.com" req)))
```

## API Cheat Sheet

| Function | Purpose | Returns |
|----------|---------|---------|
| `http-get url` | Create GET request | Request |
| `http-post url body` | Create POST request | Request |
| `with-header req name val` | Add header | Request |
| `fetch url` | Fetch URL | Async operation |
| `fetch-text url` | Fetch body only | Async operation |
| `fetch-sync url` | Sync-style fetch | Response |
| `response-status resp` | Get status code | Number |
| `response-body resp` | Get body | String |
| `response-ok resp` | Check 2xx status | Boolean |
| `fetch-all urls` | Batch fetch | Async operation |
| `health-check url` | Check if healthy | Async operation |
| `with-auth token` | Auth middleware | Function |
| `compose-middleware list` | Combine middleware | Function |
| `parallel ops` | Run in parallel* | Async operation |
| `async-or-default op val` | With fallback | Async operation |
| `run-async op` | Execute async op | Result |

\* Currently executes sequentially

## See Also

- `HTTP_API.md` - Complete documentation
- `ASYNC_MONADIC_API.md` - Async combinators
- `test/test_http_minimal.valk` - Working examples
