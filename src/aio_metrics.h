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

// Metrics structure using RED/USE methodology
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
  _Atomic uint64_t streams_total;
  _Atomic uint64_t streams_active;

  // Resource usage
  _Atomic uint64_t bytes_sent_total;
  _Atomic uint64_t bytes_recv_total;

  uint64_t start_time_us;  // System boot time
} valk_aio_metrics_t;

// Initialize metrics structure
void valk_aio_metrics_init(valk_aio_metrics_t* m);

// Instrumentation functions
void valk_aio_metrics_on_connection(valk_aio_metrics_t* m, bool success);
void valk_aio_metrics_on_close(valk_aio_metrics_t* m);
void valk_aio_metrics_on_stream_start(valk_aio_metrics_t* m);
void valk_aio_metrics_on_stream_end(valk_aio_metrics_t* m, bool error,
                                     uint64_t duration_us,
                                     uint64_t bytes_sent, uint64_t bytes_recv);

// Rendering
char* valk_aio_metrics_to_json(const valk_aio_metrics_t* m, struct valk_mem_allocator_t* alloc);
char* valk_aio_metrics_to_prometheus(const valk_aio_metrics_t* m, struct valk_mem_allocator_t* alloc);

#endif // VALK_METRICS_ENABLED
#endif // VALK_AIO_METRICS_H
