// src/aio_metrics.h - AIO metrics collection
#ifndef VALK_AIO_METRICS_H
#define VALK_AIO_METRICS_H

#ifdef VALK_METRICS_ENABLED

#include <stdatomic.h>
#include "types.h"

// Include memory.h and gc.h for type definitions.
// These types are typedefs for anonymous structs, so we cannot forward declare them.
#include "memory.h"
#include "gc.h"

// HTTP Server metrics using RED/USE methodology
// RED Method: Rate, Errors, Duration
// USE Method: Utilization, Saturation, Errors
typedef struct {
  // RED Method (Rate, Errors, Duration)
  _Atomic u64 requests_total;
  _Atomic u64 requests_active;
  _Atomic u64 requests_errors;
  _Atomic u64 request_bytes_sent;
  _Atomic u64 request_bytes_recv;
  _Atomic u64 request_duration_us_sum;  // For avg latency

  // USE Method (Utilization, Saturation, Errors)
  _Atomic u64 connections_total;
  _Atomic u64 connections_active;
  _Atomic u64 connections_failed;
  _Atomic u64 connections_rejected;       // Rejected at connection limit
  _Atomic u64 connections_rejected_load;  // Rejected due to buffer pressure
  _Atomic u64 connections_connecting;     // Connections being established
  _Atomic u64 connections_idle;           // Idle, awaiting reuse
  _Atomic u64 connections_closing;        // Graceful shutdown in progress
  _Atomic u64 streams_total;
  _Atomic u64 streams_active;

  // Resource usage
  _Atomic u64 bytes_sent_total;
  _Atomic u64 bytes_recv_total;

  u64 start_time_us;  // System boot time
} valk_aio_metrics_t;

// AIO System-level statistics (resources, pools, event loop)
typedef struct {
  // Resource counts
  _Atomic u64 servers_count;       // Number of HTTP servers
  _Atomic u64 clients_count;       // Number of HTTP clients
  _Atomic u64 handles_count;       // Total active handles

  // Memory pool utilization
  _Atomic u64 arenas_used;         // Stream arenas in use
  u64 arenas_total;                // Total stream arenas available
  _Atomic u64 tcp_buffers_used;    // TCP buffers in use
  u64 tcp_buffers_total;           // Total TCP buffers available

  // Event loop queue stats
  _Atomic u64 queue_depth;         // HTTP queue depth
  _Atomic u64 pending_requests;    // Pending HTTP requests
  _Atomic u64 pending_responses;   // Pending HTTP responses
  u64 queue_capacity;              // Queue capacity (set at init)

  // Overflow tracking (cumulative)
  _Atomic u64 arena_pool_overflow;     // Arena acquire failures
  _Atomic u64 tcp_buffer_overflow;      // TCP buffer acquire failures

  // Load shedding
  _Atomic u64 connections_rejected_load;  // Rejected due to buffer pressure

  // Pending stream backpressure metrics
  _Atomic u64 pending_streams_current;    // Currently queued streams waiting for arenas
  _Atomic u64 pending_streams_total;      // Total streams queued (cumulative)
  _Atomic u64 pending_streams_processed;  // Successfully processed from queue (cumulative)
  _Atomic u64 pending_streams_dropped;    // Dropped due to client disconnect (cumulative)
  _Atomic u64 pending_streams_wait_us;    // Total wait time in microseconds (for avg calc)
  u64 pending_streams_pool_size;          // Pool capacity (set at init)
} valk_aio_system_stats_t;

// Forward declaration for libuv loop
struct uv_loop_s;

// Event loop metrics (from libuv uv_metrics_t)
// See: https://docs.libuv.org/en/v1.x/metrics.html
typedef struct {
  u64 loop_count;         // Number of event loop iterations
  u64 events;             // Total events processed
  u64 events_waiting;     // Events currently waiting
  u64 idle_time_us;       // Time spent idle in kernel poll (epoll/kqueue)
} valk_event_loop_metrics_t;

// Get current event loop metrics from libuv
void valk_event_loop_metrics_get(struct uv_loop_s* loop, valk_event_loop_metrics_t* out);

// Size class metrics (9 classes: 16, 32, 64, 128, 256, 512, 1024, 2048, 4096)
#define VALK_VM_SIZE_CLASSES 9

// Combined VM metrics (all subsystems in one structure)
typedef struct {
  // GC metrics
  u64 gc_cycles;
  u64 gc_pause_us_total;
  u64 gc_pause_us_max;
  u64 gc_reclaimed_bytes;
  u64 gc_allocated_bytes;
  u8 gc_efficiency_pct;
  u64 gc_heap_used;
  u64 gc_heap_total;
  u64 gc_large_object_bytes;

  // Size class breakdown (slots used/total per class)
  u64 size_class_used[VALK_VM_SIZE_CLASSES];
  u64 size_class_total[VALK_VM_SIZE_CLASSES];

  // GC pause histogram (buckets: 0-1ms, 1-5ms, 5-10ms, 10-16ms, 16ms+)
  u64 pause_0_1ms;
  u64 pause_1_5ms;
  u64 pause_5_10ms;
  u64 pause_10_16ms;
  u64 pause_16ms_plus;

  // Object survival histogram (generations survived)
  u64 survival_gen_0;
  u64 survival_gen_1_5;
  u64 survival_gen_6_20;
  u64 survival_gen_21_plus;

  // Interpreter metrics
  u64 eval_total;
  u64 function_calls;
  u64 builtin_calls;
  u32 stack_depth_max;
  u64 closures_created;
  u64 env_lookups;

  // Event loop metrics
  u64 loop_count;
  u64 events_processed;
  u64 idle_time_us;
} valk_vm_metrics_t;

// Collect all VM metrics into a single structure
void valk_vm_metrics_collect(valk_vm_metrics_t* out,
                              valk_gc_malloc_heap_t* heap,
                              struct uv_loop_s* loop);

// Export VM metrics as JSON string
char* valk_vm_metrics_to_json(const valk_vm_metrics_t* m,
                               valk_mem_allocator_t* alloc);

// Export VM metrics in Prometheus format
char* valk_vm_metrics_to_prometheus(const valk_vm_metrics_t* m,
                                     valk_mem_allocator_t* alloc);

// Initialize metrics structure
void valk_aio_metrics_init(valk_aio_metrics_t* m);

// Initialize system stats structure
void valk_aio_system_stats_init(valk_aio_system_stats_t* s,
                                 u64 arenas_total,
                                 u64 tcp_buffers_total,
                                 u64 queue_capacity);

// Instrumentation functions for HTTP metrics
void valk_aio_metrics_on_connection(valk_aio_metrics_t* m, bool success);
void valk_aio_metrics_on_close(valk_aio_metrics_t* m);
void valk_aio_metrics_on_stream_start(valk_aio_metrics_t* m);
void valk_aio_metrics_on_stream_end(valk_aio_metrics_t* m, bool error,
                                     u64 duration_us,
                                     u64 bytes_sent, u64 bytes_recv);

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
                                         u64 pending_requests,
                                         u64 pending_responses);

// Pending stream backpressure instrumentation
void valk_aio_system_stats_on_pending_enqueue(valk_aio_system_stats_t* s);
void valk_aio_system_stats_on_pending_dequeue(valk_aio_system_stats_t* s, u64 wait_us);
void valk_aio_system_stats_on_pending_drop(valk_aio_system_stats_t* s);
void valk_aio_system_stats_update_pending_current(valk_aio_system_stats_t* s, u64 count);

// Rendering
char* valk_aio_metrics_to_json(const valk_aio_metrics_t* m, valk_mem_allocator_t* alloc);
char* valk_aio_metrics_to_prometheus(const valk_aio_metrics_t* m, valk_mem_allocator_t* alloc);

// Combined JSON rendering (metrics + system stats)
char* valk_aio_combined_to_json(const valk_aio_metrics_t* m,
                                 const valk_aio_system_stats_t* s,
                                 valk_mem_allocator_t* alloc);

// Combined JSON rendering with system name (for multi-system support)
char* valk_aio_combined_to_json_named(const char* name,
                                       const valk_aio_metrics_t* m,
                                       const valk_aio_system_stats_t* s,
                                       valk_mem_allocator_t* alloc);

// Export AIO system stats in Prometheus format
char* valk_aio_system_stats_to_prometheus(const valk_aio_system_stats_t* s,
                                           valk_mem_allocator_t* alloc);

// ============================================================================
// HTTP Client Metrics (Phase 3)
// ============================================================================

// Maximum number of registered HTTP clients
#define VALK_MAX_HTTP_CLIENTS 32

// HTTP Client metrics (for outbound connections)
typedef struct {
  char name[64];           // e.g., "postgres-primary"
  char type[32];           // e.g., "Database", "Cache", "API"
  _Atomic u64 connections_active;
  _Atomic u64 pool_size;
  _Atomic u64 operations_total;
  _Atomic u64 errors_total;
  _Atomic u64 retries_total;
  // For cache clients
  _Atomic u64 cache_hits_total;
  _Atomic u64 cache_misses_total;
  // Latency tracking (simple sum + count for avg)
  _Atomic u64 latency_us_sum;
  _Atomic u64 latency_count;
} valk_http_client_metrics_t;

// HTTP Clients registry
typedef struct {
  valk_http_client_metrics_t clients[VALK_MAX_HTTP_CLIENTS];
  _Atomic u32 count;
} valk_http_clients_registry_t;

// Initialize a single client metrics entry
void valk_http_client_metrics_init(valk_http_client_metrics_t* c,
                                    const char* name, const char* type,
                                    u64 pool_size);

// Register a new HTTP client, returns index or -1 on failure
int valk_http_client_register(valk_http_clients_registry_t* reg,
                               const char* name, const char* type,
                               u64 pool_size);

// Record an operation on a client
void valk_http_client_on_operation(valk_http_client_metrics_t* c,
                                    u64 duration_us, bool error, bool retry);

// Record cache hit/miss (for cache clients)
void valk_http_client_on_cache(valk_http_client_metrics_t* c, bool hit);

// Export client metrics as Prometheus
char* valk_http_clients_to_prometheus(const valk_http_clients_registry_t* reg,
                                       valk_mem_allocator_t* alloc);

// ============================================================================
// Metrics State Container (Phase 4 - Externalized Metrics)
// ============================================================================

// Container for all AIO system metrics
// This allows metrics to be optional at runtime via pointer indirection
typedef struct valk_aio_metrics_state {
  valk_aio_metrics_t metrics;
  valk_aio_system_stats_t system_stats;
  valk_http_clients_registry_t http_clients;
  valk_gc_malloc_heap_t *gc_heap;
  valk_mem_arena_t *scratch_arena;
} valk_aio_metrics_state_t;

// Allocate and initialize metrics state
// Returns nullptr if allocation fails
valk_aio_metrics_state_t* valk_aio_metrics_state_new(
    u64 arenas_total,
    u64 tcp_buffers_total,
    u64 queue_capacity,
    const char* loop_name);

// Free metrics state
void valk_aio_metrics_state_free(valk_aio_metrics_state_t* state);

// Helper macros for null-safe metrics access
#define VALK_METRICS_IF(sys) if ((sys) && (sys)->metrics_state)
#define VALK_METRICS_GET(sys) ((sys)->metrics_state)
#define VALK_METRICS(sys) ((sys)->metrics_state->metrics)
#define VALK_SYSTEM_STATS(sys) ((sys)->metrics_state->system_stats)
#define VALK_HTTP_CLIENTS(sys) ((sys)->metrics_state->http_clients)
#define VALK_OWNER_REGISTRY(sys) ((sys)->metrics_state->owner_registry)
#define VALK_LOOP_METRICS(sys) ((sys)->metrics_state->loop_metrics)

#endif // VALK_METRICS_ENABLED
#endif // VALK_AIO_METRICS_H
