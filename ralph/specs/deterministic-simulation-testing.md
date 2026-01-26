# Deterministic Simulation Testing (DST)

## Status: Future / Planning

## Overview

Make async code testable by controlling all non-determinism. Instead of real threads and real I/O, tests run single-threaded with a simulated event loop that can be seeded for reproducibility.

## Why

Current async testing problems:
- Timeouts don't tell you WHY something hangs
- Race conditions are non-deterministic
- rr recordings help but require human debugging
- Ralph can't effectively debug async issues

With DST:
- Any failure reproduces with the same seed
- Can inject faults deterministically (network errors, delays)
- Single-threaded = no real races, just simulated ones
- Failures include full execution trace

## Prior Art

- **FoundationDB**: Pioneered DST for distributed systems
- **TigerBeetle**: DST for storage engine
- **Jepsen**: Fault injection for distributed systems testing
- **Antithesis**: Commercial DST platform

## Architecture

### 1. Abstract Time

```c
// Instead of:
uint64_t now = uv_now(loop);

// Use:
uint64_t now = valk_sim_now(sim);  // Returns simulated time
valk_sim_advance(sim, 100);        // Advance 100ms
```

### 2. Abstract I/O Scheduling

```c
// Simulated event loop
typedef struct {
  uint64_t time;
  uint32_t seed;
  priority_queue_t *pending_events;
} valk_sim_t;

// Events are processed in deterministic order based on seed
void valk_sim_run_until(valk_sim_t *sim, uint64_t target_time);
```

### 3. Abstract Network

```c
// Instead of real TCP:
valk_sim_socket_t *sock = valk_sim_connect(sim, "host", port);

// Fault injection:
valk_sim_inject_latency(sim, sock, 50, 200);  // 50-200ms latency
valk_sim_inject_drop(sim, sock, 0.01);        // 1% packet loss
valk_sim_inject_disconnect(sim, sock, 5000);  // Disconnect at t=5000
```

### 4. Seeded Randomness

```c
// All "random" decisions use the simulation's PRNG
uint32_t r = valk_sim_random(sim);

// Reproducing a failure:
valk_sim_t *sim = valk_sim_new(failing_seed);
```

## Implementation Phases

### Phase 1: Time Abstraction
- Create `valk_time_source_t` interface
- Real implementation uses `uv_now()`
- Simulated implementation uses counter
- Thread through aio system

### Phase 2: Event Loop Abstraction  
- Create `valk_event_loop_t` interface
- Real implementation wraps libuv
- Simulated implementation uses priority queue
- Deterministic event ordering based on seed

### Phase 3: Network Abstraction
- Create `valk_network_t` interface
- Real implementation uses libuv TCP/UDP
- Simulated implementation uses in-memory queues
- Fault injection API

### Phase 4: Integration
- Test harness that runs tests with simulated infrastructure
- Seed discovery (run with many seeds to find failures)
- Failure minimization (find smallest seed that triggers bug)

## Acceptance Criteria

- [ ] Async tests run deterministically with a seed
- [ ] `SEED=12345 make test-sim` reproduces exact same execution
- [ ] Fault injection available (latency, drops, disconnects)
- [ ] Failing test prints seed for reproduction
- [ ] At least one real bug found via DST that wasn't found by regular tests

## References

- https://www.youtube.com/watch?v=4fFDFbi3toc (FoundationDB Testing)
- https://notes.eatonphil.com/2024-08-20-deterministic-simulation-testing.html
- https://tigerbeetle.com/blog/2023-07-26-a-]]-]eterministic-simulation-testing/
- https://antithesis.com/
