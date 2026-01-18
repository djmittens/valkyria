# Valkyria Examples

This directory contains comprehensive demonstrations of Valkyria's key features.

## Available Demos

### 1. Garbage Collection & Memory Management (`gc_demo.valk`)

**Run**: `./build/valk examples/gc_demo.valk`

A detailed, narrative-driven demonstration of Valkyria's sophisticated memory management system. This demo showcases:

- **Scratch Arena** - Fast temporary allocation for short-lived values
  - Bump allocator with instant reclamation
  - No GC overhead for temporary values
  - 4MB capacity with overflow handling

- **GC Heap** - Permanent storage for long-lived values
  - Mark-and-sweep garbage collection
  - Slab allocator for fixed-size objects
  - Malloc fallback for large allocations

- **Checkpoints** - Automatic memory boundaries
  - Scratch arena reset between expressions
  - Value evacuation from scratch to heap
  - Safe GC triggering points

- **Real-time Metrics** - All numbers are measured live
  - Arena usage and high-water mark
  - Heap statistics and GC counts
  - Evacuation counts and bytes moved
  - Visual graphs of memory usage

The demo presents a story in four chapters:
1. **The Vanishing Act** - Watch temporary values disappear instantly
2. **When the Fast Path Overflows** - Arena overflow to heap with GC cleanup
3. **Making Things Permanent** - Value evacuation with `def`
4. **The Garbage Collector** - Triggering and observing GC in action

**Key Concepts Demonstrated:**
- Generational memory management
- Allocation strategies (arena vs heap)
- Garbage collection mechanics
- Memory checkpointing
- Closure preservation across GC

### 2. HTTP/2 Web Server (`webserver_demo.valk`)

**Run**: `./build/valk examples/webserver_demo.valk`
**Test**: `curl -k https://localhost:8443`

A comprehensive HTTP/2 web server built on modern async I/O foundations. This demo showcases:

- **Asynchronous I/O System** - Powered by libuv
  - Event loop in background thread
  - Non-blocking I/O operations
  - Signal handling (Ctrl+C for shutdown)

- **HTTP/2 Protocol Support** - Via nghttp2
  - Binary protocol with header compression
  - Stream multiplexing
  - Server push capability (foundation)

- **TLS/SSL Encryption** - OpenSSL integration
  - Self-signed certificates for development
  - ALPN negotiation for HTTP/2
  - Secure HTTPS connections

- **Lisp Request Handlers** - Custom business logic
  - Handler functions in pure Lisp
  - Request map with details (being finalized)
  - Response map with status and body
  - Clean error handling

**Architecture:**
```
┌─────────────┐
│   Client    │
└──────┬──────┘
       │ HTTPS (port 8443)
       ▼
┌─────────────┐
│  OpenSSL    │ ← TLS/SSL encryption
│   (ALPN)    │ ← HTTP/2 negotiation
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  nghttp2    │ ← HTTP/2 protocol
└──────┬──────┘
       │
       ▼
┌─────────────┐
│ Lisp Handler│ ← Your business logic
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  libuv loop │ ← Async I/O events
└─────────────┘
```

**Request Flow:**
1. Client connects via HTTPS
2. TLS handshake using self-signed certificate
3. ALPN negotiates HTTP/2
4. Request routed to Lisp handler
5. Handler returns `{:status "200" :body "..."}`
6. Response sent to client
7. Connection closed cleanly

**Current Features:**
- ✓ HTTP/2 over TLS
- ✓ Async I/O with libuv
- ✓ Lisp request handlers
- ✓ Multi-request stability
- ✓ Clean shutdown handling

**Coming Soon:**
- Request parsing (method, path, headers, body)
- Custom response headers
- Routing system
- Middleware composition
- WebSocket support

**Testing the Server:**
```bash
# Basic request
curl -k https://localhost:8443

# With verbose output (see headers)
curl -k -v https://localhost:8443

# Multiple requests (server handles them all)
for i in {1..10}; do curl -k -s https://localhost:8443; done
```

**Note:** The `-k` flag tells curl to accept self-signed certificates. In production, use certificates from a trusted CA.

## Running the Demos

### Prerequisites

1. Build Valkyria:
   ```bash
   make build
   ```

2. For the web server demo, ensure TLS certificates exist:
   ```bash
   ls build/server.{key,crt}
   ```
   These are generated automatically by the build system.

### Execution

Both demos are designed to be run interactively:

```bash
# GC Demo - Watch memory management in action
./build/valk examples/gc_demo.valk

# Web Server Demo - Start HTTPS server
./build/valk examples/webserver_demo.valk
# Then in another terminal:
curl -k https://localhost:8443
```

## Learning Path

**New to Valkyria?** Start with these demos in order:

1. **gc_demo.valk** - Understand the memory model
   - See how values are allocated
   - Watch garbage collection work
   - Learn about checkpoints and evacuation

2. **webserver_demo.valk** - Build networked applications
   - Create HTTP/2 servers
   - Handle requests with Lisp code
   - Work with async I/O

## Documentation

For more details:
- [Language Reference](../docs/LANGUAGE.md)
- [Architecture Guide](../docs/ARCHITECTURE.md)
- [Contributing](../docs/CONTRIBUTING.md)

## Feedback

Found an issue or have suggestions? Open an issue on GitHub or check `CLAUDE.md` for development guidelines.
