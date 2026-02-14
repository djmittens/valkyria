# Layer 4: Concurrency

**Status**: Futures, promises, work queue, ARC boxes complete

**Timeline**: ~2-4 months

---

## Current State

### Complete ✓
- [x] Threads (pthreads)
- [x] Work queue (job dispatch)
- [x] Worker pool (4 workers)
- [x] Futures (async result)
- [x] Promises (completion)
- [x] Await/Timeout (`valk_future_await_timeout`)
- [x] ARC Boxes (atomic refcount, `arc_retain`/`arc_release`)

### Remaining Work
- [ ] Work stealing scheduler (M - 1-2 weeks)
- [ ] Channels (M - 1-2 weeks)
- [ ] Actor model (L - 2-4 weeks)
- [ ] Software Transactional Memory (XL - 4-8 weeks)

---

## Feature 1: Work Stealing Scheduler (M - 1-2 weeks)

**Unlocks**: Better load balancing, reduced idle time

**Current**: Static work queue, can have idle workers while others are busy.

**Work stealing**: Each worker has local queue. Idle workers steal from busy workers.

### Tasks

- [ ] **4.1: Per-Worker Queues** (2-3 days)
  - Replace global queue with per-worker queues
  - Lock-free deque (double-ended queue) for each worker
  - Worker pushes/pops from own queue (LIFO for locality)
  - **Test**: Submit jobs, verify distributed across workers

- [ ] **4.2: Steal Algorithm** (2-3 days)
  - Idle worker attempts to steal from random victim
  - Steal from opposite end (FIFO to reduce contention)
  - Exponential backoff if steal fails
  - **Algorithm**: Chase-Lev work-stealing deque
  - **Test**: Workload imbalance, verify stealing

- [ ] **4.3: Benchmarking** (2-3 days)
  - Compare old queue vs work stealing
  - Metrics: throughput, latency, idle time
  - **Test cases**: Unbalanced workloads, fine-grained tasks
  - **Document**: Performance results

---

## Feature 2: Channels (M - 1-2 weeks)

**Unlocks**: CSP-style concurrency (like Go, Clojure core.async)

### Tasks

- [ ] **4.4: Channel Type** (1-2 days)
  - Buffered and unbuffered channels
  - `(chan capacity)` - create channel
  - **Test**: Create channel

- [ ] **4.5: Send/Receive** (3-4 days)
  - `(send ch value)` - blocking send
  - `(recv ch)` - blocking receive
  - Unbuffered: rendezvous (sender waits for receiver)
  - **Synchronization**: Condition variables
  - **Test**: Send/receive between threads

- [ ] **4.6: Select** (3-4 days)
  - `(select (ch1 => handler1) (ch2 => handler2) ...)`
  - Wait on multiple channels, handle first available
  - Like Go's `select` or Unix `select(2)`
  - **Test**: Select from multiple channels

- [ ] **4.7: Close Channel** (1-2 days)
  - `(close ch)` - no more sends
  - Receivers get EOF marker
  - **Test**: Close channel, receivers notified

---

## Feature 3: Actor Model (L - 2-4 weeks)

**Unlocks**: Erlang-style concurrency, isolated processes

### Tasks

- [ ] **4.8: Actor Type** (2-3 days)
  - Actor = isolated process + mailbox + behavior
  - `(spawn behavior)` - create actor
  - **Test**: Spawn actor

- [ ] **4.9: Mailbox** (2-3 days)
  - Each actor has message queue
  - `(send actor-id message)` - async send
  - `(receive)` - blocking receive (inside actor)
  - **Test**: Send message to actor

- [ ] **4.10: Actor Behavior** (3-4 days)
  - Behavior function: `(message state) => new-state`
  - Actor loops: receive message, update state, loop
  - **Test**: Stateful actor (counter)

- [ ] **4.11: Actor Supervision** (3-4 days)
  - Supervisor monitors actor health
  - If actor crashes: restart or kill
  - Supervision strategies: one-for-one, one-for-all
  - **Test**: Actor crashes, supervisor restarts it

- [ ] **4.12: Actor Registry** (2-3 days)
  - Name actors: `(register 'name actor-id)`
  - Send to named actor: `(send 'name message)`
  - **Test**: Named actors

---

## Feature 4: Software Transactional Memory (XL - 4-8 weeks)

**Unlocks**: Lock-free shared memory, composable transactions

**Warning**: Complex, may defer to future

### Tasks

- [ ] **4.13: STM Design** (1 week)
  - Research: Clojure STM, Haskell STM
  - MVCC (Multi-Version Concurrency Control)
  - Transaction log, commit protocol
  - **Document**: Design doc

- [ ] **4.14: TVar Type** (3-4 days)
  - Transactional variable
  - `(tvar value)` - create TVar
  - **Test**: Create TVar

- [ ] **4.15: Read/Write** (1 week)
  - `(tvar-read tv)` - read in transaction
  - `(tvar-write tv value)` - write in transaction
  - Track reads/writes in transaction log
  - **Test**: Read/write in transaction

- [ ] **4.16: Transaction Execution** (2 weeks)
  - `(atomically body)` - run transaction
  - On commit: validate no conflicts, commit all writes
  - On conflict: retry from start
  - **Algorithm**: Optimistic concurrency control
  - **Test**: Concurrent transactions, conflicts

- [ ] **4.17: STM Tests** (1 week)
  - Test: Bank account transfers (no lost updates)
  - Test: Composable transactions
  - Test: High contention workloads
  - **Benchmark**: Compare to locks

---

## Resources

- Chase-Lev work stealing: https://www.dre.vanderbilt.edu/~schmidt/PDF/work-stealing-dequeue.pdf
- Go channels: https://go.dev/ref/spec#Channel_types
- Erlang actors: https://www.erlang.org/doc/reference_manual/processes.html
- Clojure STM: https://clojure.org/reference/refs
- "The Art of Multiprocessor Programming" (Herlihy & Shavit)
