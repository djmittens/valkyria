# Valkyria Web Server Examples

This directory contains examples of HTTP/2 web servers built with Valkyria Lisp.

## Quick Start

### Basic HTTP/2 Server

```bash
./build/valk examples/hello_server.valk
```

Then test with:
```bash
curl -k https://localhost:8443
```

### REST API Demo

```bash
./build/valk examples/rest_api_demo.valk
```

## Available APIs

### `aio/start`
Creates an asynchronous I/O system backed by libuv.

```lisp
(def {aio} (aio/start))
```

**Returns**: AIO system reference

### `http2/server-listen`
Starts an HTTP/2 server on the specified port.

```lisp
(def {server} (http2/server-listen aio 8443))
```

**Parameters**:
- `aio` - AIO system from `aio/start`
- `port` - Port number (typically 8443 for HTTPS)

**Returns**: Server future reference

**Note**: The server uses self-signed certificates from `build/server.{key,crt}`

### `aio/run`
Runs the event loop (blocks until stopped with Ctrl+C).

```lisp
(aio/run aio)
```

**Parameters**:
- `aio` - AIO system to run

## Architecture

The web server implementation uses:

- **libuv** - Asynchronous I/O and event loop
- **nghttp2** - HTTP/2 protocol implementation
- **OpenSSL** - TLS/SSL encryption
- **Multi-threading** - Event loop runs in background thread

### Request Flow

1. Client connects via HTTPS
2. TLS handshake (using self-signed cert)
3. HTTP/2 protocol negotiation (ALPN)
4. Request received and processed
5. Demo handler returns static response
6. Connection closed after response

## Current Limitations

### Known Issues

⚠️ **Connection Stability**: The server has known stability issues after handling multiple sequential requests. This is due to a race condition in connection cleanup code. The C implementation (used in tests) is stable, but the Lisp bindings trigger intermittent crashes.

**Symptoms**:
- Server may crash after 1-5 requests
- Crashes are intermittent (race condition)
- Single requests always work correctly

**Workaround**: Best for single-request demonstrations and testing for now.

### Missing Features

- **No routing**: All requests return the same response
- **No request parsing**: Cannot read request method, path, headers, or body from Lisp
- **No custom responses**: Response is hardcoded in C (`VALK_HTTP_MOTD`)
- **No middleware**: Cannot intercept or modify requests/responses
- **No async/await**: Cannot await futures from Lisp yet

## Future Enhancements

To build a production-ready web framework, we need:

1. **Fix stability issues** - Resolve connection cleanup race conditions
2. **Request API** - Expose request details (method, path, headers, body) to Lisp
3. **Response API** - Allow customizing response (status, headers, body) from Lisp
4. **Routing** - Pattern matching on request paths
5. **Middleware** - Request/response transformation pipeline
6. **Async/await** - Properly handle futures in Lisp
7. **Session management** - Cookies, auth tokens, etc.
8. **Static file serving** - Serve files from filesystem
9. **WebSocket support** - Bidirectional communication

## Technical Details

### Demo Handler

The current implementation uses a C demo handler that:
- Accepts all connections
- Reads all headers and body (but ignores them)
- Returns static HTML response: `<h1>Valkyria, valhallas treasure</h1>`
- Properly closes connections

### Certificates

The server requires TLS certificates at:
- `build/server.key` - Private key
- `build/server.crt` - Self-signed certificate

These are generated automatically by the build system.

### Ports

- Default: `8443` (HTTPS)
- Can be changed by passing different port to `http2/server-listen`

## Examples

### Minimal Server

```lisp
(load "src/prelude.valk")

; Start AIO and server
(def {aio} (aio/start))
(def {server} (http2/server-listen aio 8443))

; Run event loop
(aio/run aio)
```

### With Logging

```lisp
(load "src/prelude.valk")

(print "Starting server...")
(def {aio} (aio/start))
(print "AIO system created")

(def {server} (http2/server-listen aio 8443))
(print "Server listening on https://localhost:8443")

(aio/run aio)
```

## Testing

### Single Request Test

```bash
# Start server
./build/valk examples/hello_server.valk &
sleep 2

# Make request
curl -k https://localhost:8443

# Cleanup
pkill valk
```

### Verbose Request

```bash
curl -k -v https://localhost:8443
```

This will show:
- TLS handshake
- HTTP/2 negotiation
- Request headers
- Response headers
- Response body

## Contributing

If you want to help improve the web server:

1. **Fix the stability issue** - See `src/aio_uv.c` connection cleanup code
2. **Add request parsing** - Expose request details to Lisp
3. **Add response API** - Allow customizing responses from Lisp
4. **Add routing** - Implement path matching and dispatch

See `CLAUDE.md` for development guidelines.
