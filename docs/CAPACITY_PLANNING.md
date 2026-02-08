# Valkyria AIO Capacity Planning Guide

A comprehensive guide for tuning Valkyria's HTTP/2 server for maximum throughput and lowest latency, based on Site Reliability Engineering best practices and queuing theory.

## Table of Contents

1. [Core Principles](#core-principles)
2. [Understanding the Parameters](#understanding-the-parameters)
3. [Capacity Planning Formulas](#capacity-planning-formulas)
4. [Configuration Profiles](#configuration-profiles)
5. [Tuning for Specific Workloads](#tuning-for-specific-workloads)
6. [Monitoring and Validation](#monitoring-and-validation)
7. [Common Pitfalls](#common-pitfalls)

---

## Core Principles

### Little's Law: The Foundation of Capacity Planning

**L = λ × W**

Where:
- **L** = Average number of concurrent requests (concurrency)
- **λ** = Arrival rate (requests per second)
- **W** = Average response time (seconds)

**Example:** If you expect 1,000 req/s with 200ms average response time:
```
L = 1,000 × 0.2 = 200 concurrent requests
```

This tells you the minimum resources needed to avoid queueing.

### The Utilization-Latency Curve

```
Latency
   ^
   |                    /
   |                   /
   |                  /
   |                 /
   |               ./
   |          ...--
   |     .....
   |.....
   +-----------------------> Utilization
   0%    60%   80%  90% 100%
```

**Critical insight:** Latency remains low until ~60-70% utilization, then increases **exponentially**. This is why:
- **Target 60-70% steady-state utilization** (Google SRE recommendation)
- Running at 95% "efficiency" causes severe latency spikes
- You need headroom for traffic bursts

### The Queue Depth Problem

From queuing theory (M/M/1 model):
- **Average queue length = ρ/(1-ρ)** where ρ = utilization

| Utilization | Avg Queue Depth | P99 Impact |
|-------------|-----------------|------------|
| 50%         | 1               | Low        |
| 70%         | 2.3             | Moderate   |
| 80%         | 4               | High       |
| 90%         | 9               | Severe     |
| 95%         | 19              | Critical   |

**Takeaway:** Small increases in utilization cause large increases in queue depth and tail latency.

---

## Understanding the Parameters

### Resource Hierarchy

```
valk_aio_system_t
├── Connections (max_connections)
│   └── HTTP/2 Streams (max_concurrent_streams per connection)
│       └── Stream Arena (one per active stream)
│           └── Request/Response data
├── TCP Buffer Pool (tcp_buffer_pool_size)
│   └── Read/Write buffers for TLS/TCP
├── Pending Stream Pool (pending_stream_pool_size)
│   └── Backpressure queue when arenas exhausted
└── HTTP Queues (queue_capacity)
    └── Lisp handler request/response transfer
```

### Parameter Relationships

```
                    ┌─────────────────────┐
                    │   max_connections   │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              │               │               │
              ▼               ▼               ▼
    ┌─────────────────┐ ┌───────────┐ ┌─────────────────┐
    │ tcp_buffer_pool │ │arena_pool │ │  queue_capacity │
    │     _size       │ │   _size   │ │                 │
    └─────────────────┘ └───────────┘ └─────────────────┘
              │               │
              │               │
              ▼               ▼
    ┌─────────────────┐ ┌───────────────────────┐
    │max_concurrent   │ │                       │
    │    _streams     │─┼─► MUST BE CONSISTENT! │
    │                 │ │                       │
    └─────────────────┘ └───────────────────────┘
```

### The Critical Ratio

**arena_pool_size must accommodate max_concurrent_streams**

Each HTTP/2 stream needs one arena. If you have:
- 8 connections × 8 streams/connection = 64 potential concurrent streams
- arena_pool_size must be >= 64 to avoid immediate backpressure

**Recommended ratio:**
```
arena_pool_size >= max_concurrent_streams × num_saturated_connections
```

Where `num_saturated_connections` = expected number of connections at full stream capacity (typically 2-4).

---

## Capacity Planning Formulas

### Step 1: Determine Your Load Requirements

```
Required concurrency (L) = Peak RPS (λ) × Target P99 latency (W)

Example:
  Peak RPS: 10,000
  Target P99: 100ms
  L = 10,000 × 0.1 = 1,000 concurrent requests
```

### Step 2: Size Connections and Streams

**HTTP/2 best practice:** Don't exceed 100-256 streams per connection (RFC 7540 minimum is 100).

```
max_connections = L / max_concurrent_streams

Example:
  L = 1,000 concurrent requests
  max_concurrent_streams = 100
  max_connections = 1,000 / 100 = 10 connections minimum

  With 70% target utilization:
  max_connections = 10 / 0.7 = 15 connections
```

### Step 3: Size Arena Pool

```
arena_pool_size = max_connections × max_concurrent_streams × utilization_factor

Where utilization_factor accounts for:
  - Not all connections at max streams simultaneously
  - Headroom for bursts
  - Typical value: 0.25 to 0.5

Example:
  max_connections = 15
  max_concurrent_streams = 100
  utilization_factor = 0.3
  arena_pool_size = 15 × 100 × 0.3 = 450 arenas
```

**Memory impact:**
```
Total arena memory = arena_pool_size × arena_size

Example:
  450 arenas × 4MB = 1.8GB
  450 arenas × 64MB = 28.8GB (too much!)
```

### Step 4: Size TCP Buffer Pool

```
tcp_buffer_pool_size = max_connections × (2 + max_concurrent_streams / 8)

Rationale:
  - 2 base buffers per connection (read + write)
  - Additional buffers for stream multiplexing overhead
  - /8 factor because streams share connection's TCP buffers

Example:
  max_connections = 15
  max_concurrent_streams = 100
  tcp_buffer_pool_size = 15 × (2 + 100/8) = 15 × 14.5 = 218 buffers
```

**Memory impact:**
```
TCP buffer memory = tcp_buffer_pool_size × 32KB = 218 × 32KB = 7MB
```

### Step 5: Size Pending Stream Pool

```
pending_stream_pool_size = arena_pool_size × overflow_factor

Where overflow_factor = 0.1 to 0.25 (10-25% overflow capacity)

Example:
  arena_pool_size = 450
  overflow_factor = 0.15
  pending_stream_pool_size = 450 × 0.15 = 68 pending slots
```

### Step 6: Size HTTP Queue

```
queue_capacity = max_connections × 2

Rationale:
  - One pending request + one pending response per connection
  - Lisp handler processing is typically faster than network I/O
```

---

## Configuration Profiles

### Demo Profile (Development/Testing)

**Goal:** Low memory footprint, responsive for light traffic

```lisp
{:max-connections 8
 :max-concurrent-streams 8        ; 64 max concurrent requests
 :max-handles 128
 :max-servers 3
 :arena-size 4194304              ; 4MB per arena
 :arena-pool-size 24              ; 96MB total (3× full connection)
 :max-request-body-size 1048576   ; 1MB
 :backpressure-list-max 50
 :pending-stream-pool-size 24}
```

**Memory budget:** ~100MB for arenas + ~2MB for TCP buffers

**Capacity:**
- 64 concurrent streams theoretical max
- ~20-30 sustained with headroom

### Production Profile (High Traffic)

**Goal:** High throughput, low latency at scale

```lisp
{:max-connections 100
 :max-concurrent-streams 100      ; 10,000 max concurrent requests
 :max-handles 4096
 :max-servers 8
 :arena-size 4194304              ; 4MB per arena (NOT 64MB!)
 :arena-pool-size 1000            ; 4GB total
 :max-request-body-size 8388608   ; 8MB
 :backpressure-list-max 5000
 :pending-stream-pool-size 200}
```

**Memory budget:** ~4GB for arenas + ~50MB for TCP buffers

**Capacity:**
- 10,000 concurrent streams theoretical max
- ~3,000-5,000 sustained at 70% utilization

### High-Throughput API Profile

**Goal:** Maximum requests per second, small payloads

```lisp
{:max-connections 50
 :max-concurrent-streams 256      ; Browser-like multiplexing
 :max-handles 2048
 :max-servers 4
 :arena-size 1048576              ; 1MB per arena (small payloads)
 :arena-pool-size 2000            ; 2GB total
 :max-request-body-size 1048576   ; 1MB
 :backpressure-list-max 2000
 :pending-stream-pool-size 500}
```

**Memory budget:** ~2GB for arenas

**Capacity:**
- Optimized for many small requests
- 12,800 theoretical max streams
- Target: 50,000+ req/s

### Large Payload Profile (File Upload/Download)

**Goal:** Handle large requests/responses efficiently

```lisp
{:max-connections 20
 :max-concurrent-streams 16       ; Fewer streams, larger payloads
 :max-handles 512
 :max-servers 4
 :arena-size 67108864             ; 64MB per arena
 :arena-pool-size 64              ; 4GB total
 :max-request-body-size 134217728 ; 128MB
 :backpressure-list-max 100
 :pending-stream-pool-size 32}
```

**Memory budget:** ~4GB for arenas

**Capacity:**
- 320 concurrent streams max
- Optimized for throughput, not request count

---

## Tuning for Specific Workloads

### Latency-Sensitive Workloads (APIs, Real-time)

**Goal:** Minimize P99 latency

1. **Over-provision arena pool** (target 50% utilization max)
   ```
   arena_pool_size = expected_concurrency × 2
   ```

2. **Use smaller arenas** (faster allocation)
   ```
   arena_size = 1MB to 4MB
   ```

3. **Aggressive backpressure** (fail fast)
   ```
   backpressure_list_max = arena_pool_size × 0.1
   backpressure_timeout_ms = 5000  ; 5 seconds
   ```

4. **Lower watermarks** (earlier load shedding)
   ```
   buffer_high_watermark = 0.6
   buffer_critical_watermark = 0.8
   ```

### Throughput-Sensitive Workloads (Batch, ETL)

**Goal:** Maximize requests per second

1. **Higher stream counts**
   ```
   max_concurrent_streams = 256
   ```

2. **Larger arena pools** (absorb bursts)
   ```
   arena_pool_size = max_connections × max_concurrent_streams × 0.5
   ```

3. **Longer backpressure timeouts** (queue rather than reject)
   ```
   backpressure_timeout_ms = 60000  ; 60 seconds
   pending_stream_pool_size = arena_pool_size × 0.5
   ```

### Memory-Constrained Environments

**Goal:** Minimize memory footprint

1. **Reduce arena size aggressively**
   ```
   arena_size = 1MB  ; Minimum practical
   ```

2. **Limit concurrency**
   ```
   max_connections = 4
   max_concurrent_streams = 8
   arena_pool_size = 16  ; 16MB total
   ```

3. **Aggressive timeouts** (free resources quickly)
   ```
   backpressure_timeout_ms = 10000
   ```

---

## Monitoring and Validation

### Key Metrics to Track

| Metric | Target | Action if Exceeded |
|--------|--------|-------------------|
| Arena pool utilization | < 70% | Increase arena_pool_size |
| TCP buffer utilization | < 85% | Increase tcp_buffer_pool_size |
| Pending stream queue depth | < 50% | Increase arena_pool_size |
| P99 latency | < 2× P50 | Reduce utilization targets |
| 503 responses | < 0.1% | Increase capacity or add nodes |

### Validation Checklist

Before deploying a configuration:

- [ ] **Little's Law check:** `arena_pool_size >= peak_rps × p99_latency`
- [ ] **Stream ratio check:** `arena_pool_size >= max_concurrent_streams × 3`
- [ ] **Memory budget check:** `arena_pool_size × arena_size < available_ram × 0.7`
- [ ] **Buffer check:** `tcp_buffer_pool_size >= max_connections`
- [ ] **Queue check:** `pending_stream_pool_size >= arena_pool_size × 0.1`

### Load Testing Protocol

1. **Baseline test:** Single connection, sequential requests
   - Measure single-request latency
   - This is your theoretical minimum

2. **Concurrency ramp:** Increase connections gradually
   - Plot latency vs concurrency
   - Find the "knee" where latency starts increasing

3. **Saturation test:** Push to 90% arena utilization
   - Verify backpressure works correctly
   - Measure 503 rate and recovery time

4. **Burst test:** Send 10× normal traffic for 10 seconds
   - Verify pending stream queue absorbs burst
   - Measure recovery time

---

## Common Pitfalls

### 1. Arena Pool Too Small for Streams

**Symptom:** Immediate 503s even at low traffic

**Problem:**
```
max_concurrent_streams = 32
arena_pool_size = 16  ; WRONG! One connection saturates pool
```

**Fix:**
```
arena_pool_size >= max_concurrent_streams × 3
```

### 2. Arena Size Too Large

**Symptom:** High memory usage, OOM under load

**Problem:**
```
arena_size = 64MB
arena_pool_size = 1000
Total = 64GB!  ; Way too much
```

**Fix:**
```
arena_size = 4MB   ; Sufficient for most requests
arena_pool_size = 1000
Total = 4GB  ; Reasonable
```

### 3. Pending Pool Too Small

**Symptom:** Requests dropped during traffic spikes

**Problem:**
```
arena_pool_size = 100
pending_stream_pool_size = 10  ; Only 10% overflow
```

**Fix:**
```
pending_stream_pool_size = arena_pool_size × 0.25  ; 25% overflow
```

### 4. Ignoring HTTP/2 Multiplexing

**Symptom:** Configuration assumes HTTP/1.1 (one request per connection)

**Problem:**
```
max_connections = 1000
max_concurrent_streams = 1  ; HTTP/1.1 mode
arena_pool_size = 1000      ; 1:1 ratio
```

**Fix:**
```
max_connections = 100
max_concurrent_streams = 100  ; HTTP/2 multiplexing
arena_pool_size = 1000        ; Handles 10 saturated connections
```

### 5. Running at High Utilization

**Symptom:** Good average latency, terrible P99

**Problem:** Targeting 90%+ utilization

**Fix:** Target 60-70% utilization, scale horizontally instead

---

## Quick Reference Card

### Minimum Viable Configuration

```
arena_pool_size >= max_concurrent_streams × 3
tcp_buffer_pool_size >= max_connections × 2
pending_stream_pool_size >= arena_pool_size × 0.1
queue_capacity >= max_connections × 2
```

### Memory Estimation

```
Total Memory ≈ (arena_pool_size × arena_size)
             + (tcp_buffer_pool_size × 32KB)
             + (pending_stream_pool_size × 1KB)
             + 50MB overhead
```

### Capacity Estimation

```
Max Sustainable RPS ≈ arena_pool_size / (avg_response_time × 0.7)

Example:
  arena_pool_size = 500
  avg_response_time = 50ms = 0.05s
  Max RPS ≈ 500 / (0.05 × 0.7) = 14,285 req/s
```

---

## References

- [Google SRE Book - Handling Overload](https://sre.google/sre-book/handling-overload/)
- [RFC 7540 - HTTP/2](https://tools.ietf.org/html/rfc7540)
- [Little's Law and Capacity Planning](https://sre.google/sre-book/service-best-practices/)
- [Queuing Theory for Web Services](https://www.nginx.com/blog/performance-tuning-tips-tricks/)
- [Envoy Buffer Management](https://www.envoyproxy.io/docs/envoy/latest/configuration/operations/overload_manager/overload_manager)
