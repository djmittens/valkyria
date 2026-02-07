#pragma once

#include <stddef.h>
#include <stdint.h>
#include "../types.h"

// System configuration for AIO pools
typedef struct valk_aio_system_config {
  // PRIMARY TUNING PARAMETERS
  u32 max_connections;          // Default: 100
  u32 max_concurrent_streams;   // Default: 100 (per connection, sent via SETTINGS)

  // CAPACITY LIMITS
  u32 max_handles;              // Default: 2056
  u32 max_servers;              // Default: 8
  u32 max_clients;              // Default: 8
  u32 max_connections_per_client; // Default: 2 (connections per HTTP/2 client)
  u32 max_timers;               // Default: max_handles / 4

  // DERIVED SETTINGS (set to 0 for auto-calculation)
  u32 tcp_buffer_pool_size;     // Auto: 2 × total_connections
  u32 arena_pool_size;          // Auto: max_connections × 2
  u32 queue_capacity;           // Auto: max_connections × 2

  // MEMORY SIZING
  u64   arena_size;               // Default: 64MB per arena
  u64   max_request_body_size;    // Default: 8MB (required - requests are buffered)

  // THREAD ONBOARDING
  void (*thread_onboard_fn)(void);  // Function to call when event loop thread starts

  // BACKPRESSURE SETTINGS
  float    buffer_high_watermark;     // Default: 0.85 (85%) - start load shedding
  float    buffer_critical_watermark; // Default: 0.95 (95%) - reject all new conns
  u32 min_buffers_per_conn;      // Default: 4 (BUFFERS_PER_CONNECTION)

  // BACKPRESSURE TIMING
  u32 backpressure_list_max;     // Default: 1000
  u32 backpressure_timeout_ms;   // Default: 30000 (30s)

  // CONNECTION TIMEOUT SETTINGS
  u32 connection_idle_timeout_ms;  // Default: 60000 (60s) - close idle connections
  u32 maintenance_interval_ms;     // Default: 1000 (1s) - timer for timeout checks
} valk_aio_system_config_t;

// Default system configuration
static inline valk_aio_system_config_t valk_aio_system_config_default(void) {
  return (valk_aio_system_config_t){0};
}

// Server configuration for HTTP/2 server behavior
typedef struct valk_http_server_config {
  u64      max_response_body_size;  // Default: 64MB (Lisp API limit, not C runtime)
  const char* error_503_body;          // Pre-rendered overload response
  u64      error_503_body_len;

  // SSE CONFIGURATION
  u64      sse_buffer_size;         // Default: 64KB (pending write buffer per stream)
  u32    sse_queue_max;           // Default: 1000 (event queue depth)
} valk_http_server_config_t;

// Default server configuration
static inline valk_http_server_config_t valk_http_server_config_default(void) {
  return (valk_http_server_config_t){
    .max_response_body_size = 64 * 1024 * 1024,  // 64MB
    .error_503_body = nullptr,
    .error_503_body_len = 0,
    .sse_buffer_size = 64 * 1024,   // 64KB
    .sse_queue_max = 1000,
  };
}

// Client configuration for HTTP/2 client behavior
typedef struct valk_http_client_config {
  u32 max_concurrent_streams;     // Default: 100
  u64   max_response_body_size;     // Default: 64MB
  u32 connect_timeout_ms;         // Default: 30000 (30s)
  u32 request_timeout_ms;         // Default: 60000 (60s)

  // Connection pooling (future use)
  u32 max_idle_connections;       // Default: 0 (no pooling)
  u32 keepalive_ms;               // Default: 0 (close after use)
} valk_http_client_config_t;

// Default client configuration
static inline valk_http_client_config_t valk_http_client_config_default(void) {
  return (valk_http_client_config_t){
    .max_concurrent_streams = 100,
    .max_response_body_size = 64 * 1024 * 1024,  // 64MB
    .connect_timeout_ms = 30000,
    .request_timeout_ms = 60000,
    .max_idle_connections = 0,
    .keepalive_ms = 0,
  };
}

// ============================================================================
// Configuration Presets
// ============================================================================

// Demo profile: low resource usage, good for demos and development
// Ratios: arena_pool_size >= max_concurrent_streams * 3 (handles 3 full connections)
static inline valk_aio_system_config_t valk_aio_config_demo(void) {
  return (valk_aio_system_config_t){
    .max_connections = 8,
    .max_concurrent_streams = 8,        // 8 streams/conn × 8 conns = 64 max
    .max_handles = 128,
    .max_servers = 3,
    .max_clients = 3,
    .arena_size = 4 * 1024 * 1024,      // 4MB per arena
    .arena_pool_size = 24,              // 24 × 4MB = 96MB (3x a full connection)
    .max_request_body_size = 1 * 1024 * 1024,  // 1MB
    .backpressure_list_max = 50,
    .backpressure_timeout_ms = 30000,
  };
}

// Production profile: high capacity for production deployments
// Memory: 1000 arenas × 4MB = 4GB (reasonable for production server)
// Capacity: 100 conns × 100 streams = 10,000 max concurrent, 1000 arenas = 10 saturated conns
static inline valk_aio_system_config_t valk_aio_config_production(void) {
  return (valk_aio_system_config_t){
    .max_connections = 100,
    .max_concurrent_streams = 100,      // RFC 7540 minimum, good balance
    .max_handles = 4096,
    .max_servers = 8,
    .max_clients = 8,
    .arena_size = 4 * 1024 * 1024,      // 4MB (sufficient for most requests)
    .arena_pool_size = 1000,            // 4GB total, handles 10 saturated connections
    .max_request_body_size = 8 * 1024 * 1024,  // 8MB
    .backpressure_list_max = 5000,
    .backpressure_timeout_ms = 30000,
  };
}

// Minimal profile: embedded systems and testing
// Memory: 12 arenas × 1MB = 12MB total
// Capacity: 4 conns × 4 streams = 16 max concurrent, 12 arenas = 3 saturated conns
static inline valk_aio_system_config_t valk_aio_config_minimal(void) {
  return (valk_aio_system_config_t){
    .max_connections = 4,
    .max_concurrent_streams = 4,        // Low streams to match small arena pool
    .max_handles = 64,
    .max_servers = 1,
    .max_clients = 1,
    .arena_size = 1 * 1024 * 1024,      // 1MB
    .arena_pool_size = 12,              // 12MB total, handles 3 saturated connections
    .max_request_body_size = 256 * 1024,  // 256KB
    .backpressure_list_max = 16,
    .backpressure_timeout_ms = 10000,
  };
}

// Test profile: fast timeouts for deterministic test execution
// Identical to demo config but with short idle timeout to prevent test hangs
static inline valk_aio_system_config_t valk_aio_config_test(void) {
  return (valk_aio_system_config_t){
    .max_connections = 8,
    .max_concurrent_streams = 8,
    .max_handles = 128,
    .max_servers = 3,
    .max_clients = 3,
    .arena_size = 4 * 1024 * 1024,
    .arena_pool_size = 24,
    .max_request_body_size = 1 * 1024 * 1024,
    .backpressure_list_max = 50,
    .backpressure_timeout_ms = 5000,
    .connection_idle_timeout_ms = 500,      // 500ms for fast test cleanup
    .maintenance_interval_ms = 100,         // 100ms for quick timeout detection
  };
}

// High-throughput API profile: maximum requests per second, small payloads
// Memory: 2000 arenas × 1MB = 2GB total
// Capacity: 50 conns × 256 streams = 12,800 max concurrent
static inline valk_aio_system_config_t valk_aio_config_api(void) {
  return (valk_aio_system_config_t){
    .max_connections = 50,
    .max_concurrent_streams = 256,      // High multiplexing for APIs
    .max_handles = 2048,
    .max_servers = 4,
    .max_clients = 4,
    .arena_size = 1 * 1024 * 1024,      // 1MB (small API payloads)
    .arena_pool_size = 2000,            // 2GB total
    .max_request_body_size = 1 * 1024 * 1024,  // 1MB
    .backpressure_list_max = 2000,
    .backpressure_timeout_ms = 15000,   // Faster timeout for APIs
  };
}

// Large payload profile: file uploads and downloads
// Memory: 64 arenas × 64MB = 4GB total
// Capacity: 20 conns × 16 streams = 320 max concurrent (but large payloads)
static inline valk_aio_system_config_t valk_aio_config_large_payload(void) {
  return (valk_aio_system_config_t){
    .max_connections = 20,
    .max_concurrent_streams = 16,       // Fewer streams for large payloads
    .max_handles = 512,
    .max_servers = 4,
    .max_clients = 4,
    .arena_size = 64 * 1024 * 1024,     // 64MB for large files
    .arena_pool_size = 64,              // 4GB total
    .max_request_body_size = 128 * 1024 * 1024,  // 128MB uploads
    .backpressure_list_max = 100,
    .backpressure_timeout_ms = 60000,   // Longer timeout for large transfers
  };
}

// Demo server config: smaller buffers for demos
static inline valk_http_server_config_t valk_http_server_config_demo(void) {
  return (valk_http_server_config_t){
    .max_response_body_size = 8 * 1024 * 1024,  // 8MB
    .error_503_body = nullptr,
    .error_503_body_len = 0,
    .sse_buffer_size = 32 * 1024,   // 32KB
    .sse_queue_max = 100,
  };
}
