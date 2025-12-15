// src/aio_metrics.h - AIO metrics collection
#ifndef VALK_AIO_METRICS_H
#define VALK_AIO_METRICS_H

#ifdef VALK_METRICS_ENABLED

#include <stdatomic.h>
#include <stdint.h>
#include <stdbool.h>

// Forward declaration - full definition in memory.h
// This allows us to use valk_mem_allocator_t* without including memory.h
struct valk_mem_allocator_t;

// HTTP Server metrics using RED/USE methodology
// RED Method: Rate, Errors, Duration
// USE Method: Utilization, Saturation, Errors
typedef struct {
  // RED Method (Rate, Errors, Duration)
  _Atomic uint64_t requests_total;
  _Atomic uint64_t requests_active;
  _Atomic uint64_t requests_errors;
  _Atomic uint64_t request_bytes_sent;
  _Atomic uint64_t request_bytes_recv;
  _Atomic uint64_t request_duration_us_sum;  // For avg latency

  // USE Method (Utilization, Saturation, Errors)
  _Atomic uint64_t connections_total;
  _Atomic uint64_t connections_active;
  _Atomic uint64_t connections_failed;
  _Atomic uint64_t connections_rejected;       // Rejected at connection limit
  _Atomic uint64_t connections_rejected_load;  // Rejected due to buffer pressure
  _Atomic uint64_t connections_connecting;     // Connections being established
  _Atomic uint64_t connections_idle;           // Idle, awaiting reuse
  _Atomic uint64_t connections_closing;        // Graceful shutdown in progress
  _Atomic uint64_t streams_total;
  _Atomic uint64_t streams_active;

  // Resource usage
  _Atomic uint64_t bytes_sent_total;
  _Atomic uint64_t bytes_recv_total;

  uint64_t start_time_us;  // System boot time
} valk_aio_metrics_t;

// AIO System-level statistics (resources, pools, event loop)
typedef struct {
  // Resource counts
  _Atomic uint64_t servers_count;       // Number of HTTP servers
  _Atomic uint64_t clients_count;       // Number of HTTP clients
  _Atomic uint64_t handles_count;       // Total active handles

  // Memory pool utilization
  _Atomic uint64_t arenas_used;         // Stream arenas in use
  uint64_t arenas_total;                // Total stream arenas available
  _Atomic uint64_t tcp_buffers_used;    // TCP buffers in use
  uint64_t tcp_buffers_total;           // Total TCP buffers available

  // Event loop queue stats
  _Atomic uint64_t queue_depth;         // HTTP queue depth
  _Atomic uint64_t pending_requests;    // Pending HTTP requests
  _Atomic uint64_t pending_responses;   // Pending HTTP responses
  uint64_t queue_capacity;              // Queue capacity (set at init)

  // Overflow tracking (cumulative)
  _Atomic uint64_t arena_pool_overflow;     // Arena acquire failures
  _Atomic uint64_t tcp_buffer_overflow;      // TCP buffer acquire failures

  // Load shedding
  _Atomic uint64_t connections_rejected_load;  // Rejected due to buffer pressure

  // Pending stream backpressure metrics
  _Atomic uint64_t pending_streams_current;    // Currently queued streams waiting for arenas
  _Atomic uint64_t pending_streams_total;      // Total streams queued (cumulative)
  _Atomic uint64_t pending_streams_processed;  // Successfully processed from queue (cumulative)
  _Atomic uint64_t pending_streams_dropped;    // Dropped due to client disconnect (cumulative)
  _Atomic uint64_t pending_streams_wait_us;    // Total wait time in microseconds (for avg calc)
  uint64_t pending_streams_pool_size;          // Pool capacity (set at init)
} valk_aio_system_stats_t;

// Forward declaration for libuv loop
struct uv_loop_s;

// Event loop metrics (from libuv uv_metrics_t)
// See: https://docs.libuv.org/en/v1.x/metrics.html
typedef struct {
  uint64_t loop_count;         // Number of event loop iterations
  uint64_t events;             // Total events processed
  uint64_t events_waiting;     // Events currently waiting
  uint64_t idle_time_us;       // Time spent idle in kernel poll (epoll/kqueue)
} valk_event_loop_metrics_t;

// Get current event loop metrics from libuv
void valk_event_loop_metrics_get(struct uv_loop_s* loop, valk_event_loop_metrics_t* out);

// Forward declarations for GC heap
struct valk_gc_malloc_heap_t;

// Combined VM metrics (all subsystems in one structure)
typedef struct {
  // GC metrics
  uint64_t gc_cycles;
  uint64_t gc_pause_us_total;
  uint64_t gc_pause_us_max;
  uint64_t gc_reclaimed_bytes;
  size_t gc_heap_used;
  size_t gc_heap_total;

  // Interpreter metrics
  uint64_t eval_total;
  uint64_t function_calls;
  uint64_t builtin_calls;
  uint32_t stack_depth_max;
  uint64_t closures_created;
  uint64_t env_lookups;

  // Event loop metrics
  uint64_t loop_count;
  uint64_t events_processed;
  uint64_t idle_time_us;
} valk_vm_metrics_t;

// Collect all VM metrics into a single structure
void valk_vm_metrics_collect(valk_vm_metrics_t* out,
                              struct valk_gc_malloc_heap_t* heap,
                              struct uv_loop_s* loop);

// Export VM metrics as JSON string
char* valk_vm_metrics_to_json(const valk_vm_metrics_t* m,
                               struct valk_mem_allocator_t* alloc);

// Export VM metrics in Prometheus format
char* valk_vm_metrics_to_prometheus(const valk_vm_metrics_t* m,
                                     struct valk_mem_allocator_t* alloc);

// Initialize metrics structure
void valk_aio_metrics_init(valk_aio_metrics_t* m);

// Initialize system stats structure
void valk_aio_system_stats_init(valk_aio_system_stats_t* s,
                                 uint64_t arenas_total,
                                 uint64_t tcp_buffers_total,
                                 uint64_t queue_capacity);

// Instrumentation functions for HTTP metrics
void valk_aio_metrics_on_connection(valk_aio_metrics_t* m, bool success);
void valk_aio_metrics_on_close(valk_aio_metrics_t* m);
void valk_aio_metrics_on_stream_start(valk_aio_metrics_t* m);
void valk_aio_metrics_on_stream_end(valk_aio_metrics_t* m, bool error,
                                     uint64_t duration_us,
                                     uint64_t bytes_sent, uint64_t bytes_recv);

// Connection state tracking
void valk_aio_metrics_on_connecting(valk_aio_metrics_t* m);
void valk_aio_metrics_on_connected(valk_aio_metrics_t* m);  // connecting -> active
void valk_aio_metrics_on_idle(valk_aio_metrics_t* m);       // active -> idle
void valk_aio_metrics_on_reactivate(valk_aio_metrics_t* m); // idle -> active
void valk_aio_metrics_on_closing(valk_aio_metrics_t* m);    // any -> closing
void valk_aio_metrics_on_closed(valk_aio_metrics_t* m);     // closing -> removed

// Instrumentation functions for AIO system stats
void valk_aio_system_stats_on_server_start(valk_aio_system_stats_t* s);
void valk_aio_system_stats_on_server_stop(valk_aio_system_stats_t* s);
void valk_aio_system_stats_on_client_start(valk_aio_system_stats_t* s);
void valk_aio_system_stats_on_client_stop(valk_aio_system_stats_t* s);
void valk_aio_system_stats_on_handle_create(valk_aio_system_stats_t* s);
void valk_aio_system_stats_on_handle_close(valk_aio_system_stats_t* s);
void valk_aio_system_stats_on_arena_acquire(valk_aio_system_stats_t* s);
void valk_aio_system_stats_on_arena_release(valk_aio_system_stats_t* s);
void valk_aio_system_stats_update_queue(valk_aio_system_stats_t* s,
                                         uint64_t pending_requests,
                                         uint64_t pending_responses);

// Pending stream backpressure instrumentation
void valk_aio_system_stats_on_pending_enqueue(valk_aio_system_stats_t* s);
void valk_aio_system_stats_on_pending_dequeue(valk_aio_system_stats_t* s, uint64_t wait_us);
void valk_aio_system_stats_on_pending_drop(valk_aio_system_stats_t* s);
void valk_aio_system_stats_update_pending_current(valk_aio_system_stats_t* s, uint64_t count);

// Rendering
char* valk_aio_metrics_to_json(const valk_aio_metrics_t* m, struct valk_mem_allocator_t* alloc);
char* valk_aio_metrics_to_prometheus(const valk_aio_metrics_t* m, struct valk_mem_allocator_t* alloc);

// Combined JSON rendering (metrics + system stats)
char* valk_aio_combined_to_json(const valk_aio_metrics_t* m,
                                 const valk_aio_system_stats_t* s,
                                 struct valk_mem_allocator_t* alloc);

// Combined JSON rendering with system name (for multi-system support)
char* valk_aio_combined_to_json_named(const char* name,
                                       const valk_aio_metrics_t* m,
                                       const valk_aio_system_stats_t* s,
                                       struct valk_mem_allocator_t* alloc);

// Export AIO system stats in Prometheus format
char* valk_aio_system_stats_to_prometheus(const valk_aio_system_stats_t* s,
                                           struct valk_mem_allocator_t* alloc);

// ============================================================================
// HTTP Client Metrics (Phase 3)
// ============================================================================

// Maximum number of registered HTTP clients
#define VALK_MAX_HTTP_CLIENTS 32

// HTTP Client metrics (for outbound connections)
typedef struct {
  char name[64];           // e.g., "postgres-primary"
  char type[32];           // e.g., "Database", "Cache", "API"
  _Atomic uint64_t connections_active;
  _Atomic uint64_t pool_size;
  _Atomic uint64_t operations_total;
  _Atomic uint64_t errors_total;
  _Atomic uint64_t retries_total;
  // For cache clients
  _Atomic uint64_t cache_hits_total;
  _Atomic uint64_t cache_misses_total;
  // Latency tracking (simple sum + count for avg)
  _Atomic uint64_t latency_us_sum;
  _Atomic uint64_t latency_count;
} valk_http_client_metrics_t;

// HTTP Clients registry
typedef struct {
  valk_http_client_metrics_t clients[VALK_MAX_HTTP_CLIENTS];
  _Atomic uint32_t count;
} valk_http_clients_registry_t;

// Initialize a single client metrics entry
void valk_http_client_metrics_init(valk_http_client_metrics_t* c,
                                    const char* name, const char* type,
                                    uint64_t pool_size);

// Register a new HTTP client, returns index or -1 on failure
int valk_http_client_register(valk_http_clients_registry_t* reg,
                               const char* name, const char* type,
                               uint64_t pool_size);

// Record an operation on a client
void valk_http_client_on_operation(valk_http_client_metrics_t* c,
                                    uint64_t duration_us, bool error, bool retry);

// Record cache hit/miss (for cache clients)
void valk_http_client_on_cache(valk_http_client_metrics_t* c, bool hit);

// Export client metrics as Prometheus
char* valk_http_clients_to_prometheus(const valk_http_clients_registry_t* reg,
                                       struct valk_mem_allocator_t* alloc);

#endif // VALK_METRICS_ENABLED
#endif // VALK_AIO_METRICS_H
