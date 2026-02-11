---------------------- MODULE Backpressure -------------------------
(*
 * TCP buffer slab backpressure model.
 *
 * System: HTTP/2 server+client sharing a fixed pool of TCP buffers.
 * Each connection side (server, client) needs buffers to read/write.
 * When the pool is exhausted, connections enter backpressure (reads
 * paused). A periodic maintenance timer kills connections that stay
 * in backpressure past a timeout, freeing their buffers.
 *
 * Models: slab.c, aio_overload_backpressure.c, aio_http2_conn.c,
 *         aio_maintenance.c, aio_http2_client.c, aio_http2_server.c
 *
 * Tests scenario: NumRequests concurrent requests, SlabSize buffers.
 *
 * Property: Every request eventually settles (success or error).
 * This is what aio/all-settled depends on.
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  NumRequests,     \* concurrent client requests (test: 4)
  SlabSize,        \* total TCP buffer items (test: 6)
  BufsPerSide,     \* buffers needed per connection side (1 read + 1 write = 2)
  TimeoutTicks,    \* maintenance ticks before BP kill (test: 10 = 1000ms/100ms)
  MaxTicks,        \* bound on total ticks (for finite model checking)
  NULL

Requests == 1..NumRequests

(*
 * Request lifecycle (maps to client_request_with_headers_impl):
 *   init -> connecting -> established -> request_sent -> settled
 *
 * A request settles via:
 *   - Normal response (happy path)
 *   - Connect failure (slab exhausted during handshake)
 *   - Load shedding (server rejects at accept)
 *   - Connection kill (BP timeout or peer close)
 *)

VARIABLES
  slab_free,           \* Nat: available buffer items in slab

  \* Per-request state
  req_settled,         \* [Requests -> BOOLEAN]

  \* Server-side of each connection
  srv_state,           \* [Requests -> {"none","active","bp","closed"}]
  srv_bufs,            \* [Requests -> 0..BufsPerSide] held buffers
  srv_bp_age,          \* [Requests -> 0..MaxTicks] ticks in BP

  \* Client-side of each connection
  cli_state,           \* [Requests -> {"none","active","bp","closed"}]
  cli_bufs,            \* [Requests -> 0..BufsPerSide] held buffers
  cli_bp_age,          \* [Requests -> 0..MaxTicks] ticks in BP

  \* Progress flags
  response_ready,      \* [Requests -> BOOLEAN] server generated response

  tick                 \* Nat: global tick counter (bounded)

vars == <<slab_free, req_settled,
          srv_state, srv_bufs, srv_bp_age,
          cli_state, cli_bufs, cli_bp_age,
          response_ready, tick>>

------------------------------------------------------------------------
Init ==
  /\ slab_free = SlabSize
  /\ req_settled = [r \in Requests |-> FALSE]
  /\ srv_state = [r \in Requests |-> "none"]
  /\ srv_bufs = [r \in Requests |-> 0]
  /\ srv_bp_age = [r \in Requests |-> 0]
  /\ cli_state = [r \in Requests |-> "none"]
  /\ cli_bufs = [r \in Requests |-> 0]
  /\ cli_bp_age = [r \in Requests |-> 0]
  /\ response_ready = [r \in Requests |-> FALSE]
  /\ tick = 0

------------------------------------------------------------------------
(* === CONNECTION SETUP === *)

(*
 * Establish connection: both sides acquire buffers.
 * Models: server accept + alloc_cb + write_buf_acquire,
 *         client connect + alloc_cb + write_buf_acquire.
 * Both sides need BufsPerSide each = 2*BufsPerSide total.
 *)
Establish(r) ==
  /\ ~req_settled[r]
  /\ srv_state[r] = "none"
  /\ cli_state[r] = "none"
  /\ slab_free >= 2 * BufsPerSide
  /\ slab_free' = slab_free - 2 * BufsPerSide
  /\ srv_state' = [srv_state EXCEPT ![r] = "active"]
  /\ srv_bufs' = [srv_bufs EXCEPT ![r] = BufsPerSide]
  /\ cli_state' = [cli_state EXCEPT ![r] = "active"]
  /\ cli_bufs' = [cli_bufs EXCEPT ![r] = BufsPerSide]
  /\ UNCHANGED <<req_settled, srv_bp_age, cli_bp_age, response_ready, tick>>

(*
 * Connection fails at setup: not enough buffers.
 * Models: __http2_connect_impl write_buf_acquire failure,
 *         or server __accept_should_reject (load shedding).
 * Request settles immediately with error.
 *)
EstablishFail(r) ==
  /\ ~req_settled[r]
  /\ srv_state[r] = "none"
  /\ cli_state[r] = "none"
  /\ slab_free < 2 * BufsPerSide
  /\ req_settled' = [req_settled EXCEPT ![r] = TRUE]
  /\ srv_state' = [srv_state EXCEPT ![r] = "closed"]
  /\ cli_state' = [cli_state EXCEPT ![r] = "closed"]
  /\ UNCHANGED <<slab_free, srv_bufs, srv_bp_age,
                 cli_bufs, cli_bp_age, response_ready, tick>>

------------------------------------------------------------------------
(* === NORMAL REQUEST FLOW === *)

(*
 * Server processes request, generates response.
 * Only possible when server is active (not in BP).
 *)
ServerProcess(r) ==
  /\ ~req_settled[r]
  /\ srv_state[r] = "active"
  /\ ~response_ready[r]
  /\ response_ready' = [response_ready EXCEPT ![r] = TRUE]
  /\ UNCHANGED <<slab_free, req_settled,
                 srv_state, srv_bufs, srv_bp_age,
                 cli_state, cli_bufs, cli_bp_age, tick>>

(*
 * Client receives response -> request settles successfully.
 * Both sides must be active (not in BP).
 *)
ClientReceive(r) ==
  /\ ~req_settled[r]
  /\ response_ready[r]
  /\ cli_state[r] = "active"
  /\ srv_state[r] = "active"
  /\ req_settled' = [req_settled EXCEPT ![r] = TRUE]
  /\ UNCHANGED <<slab_free,
                 srv_state, srv_bufs, srv_bp_age,
                 cli_state, cli_bufs, cli_bp_age,
                 response_ready, tick>>

------------------------------------------------------------------------
(* === BUFFER DYNAMICS === *)

(*
 * A connection side releases a buffer (models write flush completion
 * returning the write buffer to slab, or read buffer release).
 * This is what enables backpressure entry on the NEXT read cycle.
 *)
SrvReleaseBuf(r) ==
  /\ srv_state[r] = "active"
  /\ srv_bufs[r] > 0
  /\ srv_bufs' = [srv_bufs EXCEPT ![r] = srv_bufs[r] - 1]
  /\ slab_free' = slab_free + 1
  /\ UNCHANGED <<req_settled, srv_state, srv_bp_age,
                 cli_state, cli_bufs, cli_bp_age,
                 response_ready, tick>>

CliReleaseBuf(r) ==
  /\ cli_state[r] = "active"
  /\ cli_bufs[r] > 0
  /\ cli_bufs' = [cli_bufs EXCEPT ![r] = cli_bufs[r] - 1]
  /\ slab_free' = slab_free + 1
  /\ UNCHANGED <<req_settled, srv_state, srv_bufs, srv_bp_age,
                 cli_state, cli_bp_age,
                 response_ready, tick>>

(*
 * Re-acquire a buffer (models alloc_cb or write_buf_acquire succeeding).
 *)
SrvAcquireBuf(r) ==
  /\ srv_state[r] = "active"
  /\ srv_bufs[r] < BufsPerSide
  /\ slab_free >= 1
  /\ srv_bufs' = [srv_bufs EXCEPT ![r] = srv_bufs[r] + 1]
  /\ slab_free' = slab_free - 1
  /\ UNCHANGED <<req_settled, srv_state, srv_bp_age,
                 cli_state, cli_bufs, cli_bp_age,
                 response_ready, tick>>

CliAcquireBuf(r) ==
  /\ cli_state[r] = "active"
  /\ cli_bufs[r] < BufsPerSide
  /\ slab_free >= 1
  /\ cli_bufs' = [cli_bufs EXCEPT ![r] = cli_bufs[r] + 1]
  /\ slab_free' = slab_free - 1
  /\ UNCHANGED <<req_settled, srv_state, srv_bufs, srv_bp_age,
                 cli_state, cli_bp_age,
                 response_ready, tick>>

------------------------------------------------------------------------
(* === BACKPRESSURE ENTRY === *)

(*
 * Enter backpressure: connection needs a buffer but slab is empty.
 * Models: alloc_cb returns NULL -> __tcp_read_handle_null_buffer
 *         or tcp_read_impl -> write_buf_acquire fails
 * Connection reads are stopped, added to BP list.
 *)
SrvEnterBP(r) ==
  /\ srv_state[r] = "active"
  /\ srv_bufs[r] < BufsPerSide    \* needs a buffer
  /\ slab_free = 0                 \* none available
  /\ srv_state' = [srv_state EXCEPT ![r] = "bp"]
  /\ srv_bp_age' = [srv_bp_age EXCEPT ![r] = 0]
  /\ UNCHANGED <<slab_free, req_settled,
                 srv_bufs,
                 cli_state, cli_bufs, cli_bp_age,
                 response_ready, tick>>

CliEnterBP(r) ==
  /\ cli_state[r] = "active"
  /\ cli_bufs[r] < BufsPerSide
  /\ slab_free = 0
  /\ cli_state' = [cli_state EXCEPT ![r] = "bp"]
  /\ cli_bp_age' = [cli_bp_age EXCEPT ![r] = 0]
  /\ UNCHANGED <<slab_free, req_settled,
                 srv_state, srv_bufs, srv_bp_age,
                 cli_bufs,
                 response_ready, tick>>

------------------------------------------------------------------------
(* === BACKPRESSURE RESUME === *)

(*
 * Resume from backpressure: try_resume_one is called when a write
 * flush completes. If enough buffers available (>= ResumeThreshold),
 * pop one connection from BP list, re-acquire buffer, restart reads.
 *
 * Models: valk_http2_backpressure_try_resume_one called from
 *         __http2_flush_complete.
 *
 * IMPORTANT: Resume is ONLY triggered by flush completion (or
 * maintenance timeout in the fix version). If all connections are
 * in BP, no flushes happen -> no resumes. This is the key design
 * issue the model captures.
 *)
SrvResumeBP(r) ==
  /\ srv_state[r] = "bp"
  /\ slab_free >= 1
  \* Resume is triggered by SOME other connection flushing.
  \* At least one connection must be active (not in BP or closed).
  /\ \E q \in Requests :
       q # r /\ (srv_state[q] = "active" \/ cli_state[q] = "active")
  /\ srv_state' = [srv_state EXCEPT ![r] = "active"]
  /\ srv_bp_age' = [srv_bp_age EXCEPT ![r] = 0]
  /\ srv_bufs' = [srv_bufs EXCEPT ![r] = srv_bufs[r] + 1]
  /\ slab_free' = slab_free - 1
  /\ UNCHANGED <<req_settled,
                 cli_state, cli_bufs, cli_bp_age,
                 response_ready, tick>>

CliResumeBP(r) ==
  /\ cli_state[r] = "bp"
  /\ slab_free >= 1
  /\ \E q \in Requests :
       q # r /\ (srv_state[q] = "active" \/ cli_state[q] = "active")
  /\ cli_state' = [cli_state EXCEPT ![r] = "active"]
  /\ cli_bp_age' = [cli_bp_age EXCEPT ![r] = 0]
  /\ cli_bufs' = [cli_bufs EXCEPT ![r] = cli_bufs[r] + 1]
  /\ slab_free' = slab_free - 1
  /\ UNCHANGED <<req_settled,
                 srv_state, srv_bufs, srv_bp_age,
                 response_ready, tick>>

------------------------------------------------------------------------
(* === MAINTENANCE TIMER === *)

(*
 * Maintenance tick: ages all BP connections.
 * Maps to: __maintenance_timer_cb (fires every maintenance_interval_ms).
 *)
MaintenanceTick ==
  /\ tick < MaxTicks
  /\ tick' = tick + 1
  /\ srv_bp_age' = [r \in Requests |->
       IF srv_state[r] = "bp" THEN srv_bp_age[r] + 1
       ELSE srv_bp_age[r]]
  /\ cli_bp_age' = [r \in Requests |->
       IF cli_state[r] = "bp" THEN cli_bp_age[r] + 1
       ELSE cli_bp_age[r]]
  /\ UNCHANGED <<slab_free, req_settled,
                 srv_state, srv_bufs,
                 cli_state, cli_bufs,
                 response_ready>>

(*
 * BP timeout: kill connection, release all held buffers.
 * Maps to: valk_maintenance_check_backpressure_timeouts
 *          -> VALK_CONN_EVT_TIMEOUT -> close -> handle_closed_cb
 *          -> conn_io_free (releases buffers to slab)
 *)
SrvBPTimeout(r) ==
  /\ srv_state[r] = "bp"
  /\ srv_bp_age[r] >= TimeoutTicks
  /\ srv_state' = [srv_state EXCEPT ![r] = "closed"]
  /\ srv_bp_age' = [srv_bp_age EXCEPT ![r] = 0]
  /\ slab_free' = slab_free + srv_bufs[r]
  /\ srv_bufs' = [srv_bufs EXCEPT ![r] = 0]
  /\ UNCHANGED <<req_settled,
                 cli_state, cli_bufs, cli_bp_age,
                 response_ready, tick>>

CliBPTimeout(r) ==
  /\ cli_state[r] = "bp"
  /\ cli_bp_age[r] >= TimeoutTicks
  /\ cli_state' = [cli_state EXCEPT ![r] = "closed"]
  /\ cli_bp_age' = [cli_bp_age EXCEPT ![r] = 0]
  /\ slab_free' = slab_free + cli_bufs[r]
  /\ cli_bufs' = [cli_bufs EXCEPT ![r] = 0]
  \* Disconnect handler fails the request
  /\ IF ~req_settled[r]
     THEN req_settled' = [req_settled EXCEPT ![r] = TRUE]
     ELSE UNCHANGED req_settled
  /\ UNCHANGED <<srv_state, srv_bufs, srv_bp_age,
                 response_ready, tick>>

------------------------------------------------------------------------
(* === PEER CLOSE PROPAGATION === *)

(*
 * Server closes -> TCP FIN sent to client.
 * Client can only see this if NOT in backpressure (reads active).
 *
 * When client reads EOF: close -> disconnect -> settle.
 *
 * KEY: If client is in BP (reads stopped), it CANNOT see the FIN.
 * It must wait for its own BP timeout.
 *)
SrvCloseNotifiesClient(r) ==
  /\ srv_state[r] = "closed"
  /\ cli_state[r] = "active"      \* client is reading -> sees EOF
  /\ cli_state' = [cli_state EXCEPT ![r] = "closed"]
  /\ slab_free' = slab_free + cli_bufs[r]
  /\ cli_bufs' = [cli_bufs EXCEPT ![r] = 0]
  /\ IF ~req_settled[r]
     THEN req_settled' = [req_settled EXCEPT ![r] = TRUE]
     ELSE UNCHANGED req_settled
  /\ UNCHANGED <<srv_state, srv_bufs, srv_bp_age,
                 cli_bp_age,
                 response_ready, tick>>

(*
 * Client closes -> server sees EOF (symmetric).
 *)
CliCloseNotifiesServer(r) ==
  /\ cli_state[r] = "closed"
  /\ srv_state[r] = "active"
  /\ srv_state' = [srv_state EXCEPT ![r] = "closed"]
  /\ slab_free' = slab_free + srv_bufs[r]
  /\ srv_bufs' = [srv_bufs EXCEPT ![r] = 0]
  /\ UNCHANGED <<req_settled,
                 cli_state, cli_bufs, cli_bp_age,
                 srv_bp_age,
                 response_ready, tick>>

------------------------------------------------------------------------
(* === GRACEFUL CLOSE === *)

(*
 * After request settles normally, close connections.
 *)
GracefulClose(r) ==
  /\ req_settled[r]
  /\ \/ (srv_state[r] = "active" /\ srv_state' = [srv_state EXCEPT ![r] = "closed"]
         /\ slab_free' = slab_free + srv_bufs[r]
         /\ srv_bufs' = [srv_bufs EXCEPT ![r] = 0]
         /\ UNCHANGED <<cli_state, cli_bufs>>)
     \/ (cli_state[r] = "active" /\ cli_state' = [cli_state EXCEPT ![r] = "closed"]
         /\ slab_free' = slab_free + cli_bufs[r]
         /\ cli_bufs' = [cli_bufs EXCEPT ![r] = 0]
         /\ UNCHANGED <<srv_state, srv_bufs>>)
  /\ UNCHANGED <<req_settled, srv_bp_age, cli_bp_age, response_ready, tick>>

------------------------------------------------------------------------
Next ==
  \/ \E r \in Requests :
       \/ Establish(r)
       \/ EstablishFail(r)
       \/ ServerProcess(r)
       \/ ClientReceive(r)
       \/ SrvReleaseBuf(r)
       \/ CliReleaseBuf(r)
       \/ SrvAcquireBuf(r)
       \/ CliAcquireBuf(r)
       \/ SrvEnterBP(r)
       \/ CliEnterBP(r)
       \/ SrvResumeBP(r)
       \/ CliResumeBP(r)
       \/ SrvBPTimeout(r)
       \/ CliBPTimeout(r)
       \/ SrvCloseNotifiesClient(r)
       \/ CliCloseNotifiesServer(r)
       \/ GracefulClose(r)
  \/ MaintenanceTick

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------
(* === INVARIANTS === *)

TypeOK ==
  /\ slab_free \in 0..SlabSize
  /\ \A r \in Requests :
       /\ req_settled[r] \in BOOLEAN
       /\ srv_state[r] \in {"none","active","bp","closed"}
       /\ srv_bufs[r] \in 0..BufsPerSide
       /\ srv_bp_age[r] \in 0..(MaxTicks + 1)
       /\ cli_state[r] \in {"none","active","bp","closed"}
       /\ cli_bufs[r] \in 0..BufsPerSide
       /\ cli_bp_age[r] \in 0..(MaxTicks + 1)
       /\ response_ready[r] \in BOOLEAN

SlabNonNegative == slab_free >= 0

(*
 * Buffer conservation: free + held = total
 *)
BufferConservation ==
  LET TotalHeld == LET f[S \in SUBSET Requests] ==
                         IF S = {} THEN 0
                         ELSE LET r == CHOOSE r \in S : TRUE
                              IN srv_bufs[r] + cli_bufs[r] + f[S \ {r}]
                   IN f[Requests]
  IN slab_free + TotalHeld = SlabSize

(*
 * Closed connections hold no buffers.
 *)
ClosedHoldsNoBuffers ==
  \A r \in Requests :
    /\ (srv_state[r] = "closed" => srv_bufs[r] = 0)
    /\ (cli_state[r] = "closed" => cli_bufs[r] = 0)
    /\ (srv_state[r] = "none" => srv_bufs[r] = 0)
    /\ (cli_state[r] = "none" => cli_bufs[r] = 0)

(*
 * A non-settled request always has a path to settlement:
 *   1. Normal: both sides active, can progress
 *   2. Connect fail: caught by EstablishFail
 *   3. BP timeout: connection in BP will be killed
 *   4. Peer close: server closed and client is active (can read EOF)
 *   5. Not started yet
 *
 * The DANGEROUS state: server closed, client in BP.
 * Client can't read EOF. Must wait for client BP timeout.
 * This is FINE as long as the maintenance timer keeps ticking.
 *)
UnsettledHasPath ==
  \A r \in Requests :
    ~req_settled[r] =>
      \/ srv_state[r] = "none"        \* not started
      \/ cli_state[r] = "active"      \* client can make progress
      \/ srv_state[r] = "active"      \* server can make progress
      \/ cli_state[r] = "bp"          \* client BP -> will timeout
      \/ srv_state[r] = "bp"          \* server BP -> will timeout + notify client

(*
 * No request can be unsettled when both sides are closed.
 * If this fires, the settlement chain is broken.
 *)
NoOrphanedRequest ==
  \A r \in Requests :
    (srv_state[r] = "closed" /\ cli_state[r] = "closed") => req_settled[r]

(*
 * DEADLOCK detection: the system is stuck if no request can
 * make progress AND some request is unsettled. TLC's built-in
 * deadlock detection catches this (CHECK_DEADLOCK TRUE).
 *
 * This will find scenarios where:
 * - All connections are in BP
 * - No flush is happening (so try_resume_one never runs)
 * - Maintenance timer has ticked MaxTicks times (bounded)
 * - No timeout fires (all bp_age < TimeoutTicks)
 *
 * With proper timeout config, this shouldn't happen.
 *)

------------------------------------------------------------------------
(* === LIVENESS (Temporal Property) === *)

(*
 * Under fairness assumptions:
 *   - MaintenanceTick fires infinitely often (WF)
 *   - BP timeouts are acted on when enabled (WF)
 *   - Peer close notifications are delivered (WF)
 *
 * Every request eventually settles.
 *)

Fairness ==
  /\ WF_vars(MaintenanceTick)
  /\ \A r \in Requests :
       /\ WF_vars(SrvBPTimeout(r))
       /\ WF_vars(CliBPTimeout(r))
       /\ WF_vars(SrvCloseNotifiesClient(r))
       /\ WF_vars(CliCloseNotifiesServer(r))
       /\ WF_vars(EstablishFail(r))

LiveSpec == Spec /\ Fairness

AllRequestsSettle == <>(\A r \in Requests : req_settled[r])

========================================================================
