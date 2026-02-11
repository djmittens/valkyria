--------------------- MODULE BackpressureBuggy -------------------------
(*
 * Buggy version of Backpressure model.
 *
 * Bug: Resume from backpressure is ONLY possible when another active
 * connection flushes (calls try_resume_one from __http2_flush_complete).
 * When maintenance timeout kills a BP connection and frees buffers,
 * it does NOT call try_resume_one. So freed buffers sit unused until
 * some other connection happens to flush.
 *
 * In the degenerate case: ALL connections are in BP. Server BP timeouts
 * free buffers. But no active connections exist to trigger try_resume_one.
 * Client connections in BP can only be freed by their own BP timeout.
 *
 * This version makes resume STRICTER: requires an active connection
 * on the SAME side (server or client) to trigger the resume. If all
 * server connections are in BP, no server resume can happen even if
 * buffers are available.
 *
 * Additionally, this version models a scenario where the maintenance
 * timer ONLY kills server connections (since server BP timeout fires
 * first). The freed buffers should let client resume, but without
 * try_resume_one being called, they don't.
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  NumRequests,
  SlabSize,
  BufsPerSide,
  TimeoutTicks,
  MaxTicks,
  NULL

Requests == 1..NumRequests

VARIABLES
  slab_free,
  req_settled,
  srv_state,
  srv_bufs,
  srv_bp_age,
  cli_state,
  cli_bufs,
  cli_bp_age,
  response_ready,
  tick

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
ServerProcess(r) ==
  /\ ~req_settled[r]
  /\ srv_state[r] = "active"
  /\ ~response_ready[r]
  /\ response_ready' = [response_ready EXCEPT ![r] = TRUE]
  /\ UNCHANGED <<slab_free, req_settled,
                 srv_state, srv_bufs, srv_bp_age,
                 cli_state, cli_bufs, cli_bp_age, tick>>

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
SrvEnterBP(r) ==
  /\ srv_state[r] = "active"
  /\ srv_bufs[r] < BufsPerSide
  /\ slab_free = 0
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
(*
 * BUG: Resume DISABLED entirely.
 *
 * In the real code, try_resume_one is only called from
 * __http2_flush_complete. If no connection is actively writing
 * and flushing, try_resume_one is never called. When maintenance
 * timeout frees buffers, it does NOT call try_resume_one.
 *
 * We model this by removing the Resume actions entirely.
 * The only way out of BP is the timeout kill.
 *
 * This means the system relies ENTIRELY on the maintenance timer
 * to clear BP connections, and freed buffers sit idle until then.
 *)

\* SrvResumeBP and CliResumeBP intentionally OMITTED.

------------------------------------------------------------------------
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
  /\ IF ~req_settled[r]
     THEN req_settled' = [req_settled EXCEPT ![r] = TRUE]
     ELSE UNCHANGED req_settled
  /\ UNCHANGED <<srv_state, srv_bufs, srv_bp_age,
                 response_ready, tick>>

------------------------------------------------------------------------
SrvCloseNotifiesClient(r) ==
  /\ srv_state[r] = "closed"
  /\ cli_state[r] = "active"
  /\ cli_state' = [cli_state EXCEPT ![r] = "closed"]
  /\ slab_free' = slab_free + cli_bufs[r]
  /\ cli_bufs' = [cli_bufs EXCEPT ![r] = 0]
  /\ IF ~req_settled[r]
     THEN req_settled' = [req_settled EXCEPT ![r] = TRUE]
     ELSE UNCHANGED req_settled
  /\ UNCHANGED <<srv_state, srv_bufs, srv_bp_age,
                 cli_bp_age,
                 response_ready, tick>>

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
       \* NO Resume actions - this is the bug
       \/ SrvBPTimeout(r)
       \/ CliBPTimeout(r)
       \/ SrvCloseNotifiesClient(r)
       \/ CliCloseNotifiesServer(r)
       \/ GracefulClose(r)
  \/ MaintenanceTick

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------
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

BufferConservation ==
  LET TotalHeld == LET f[S \in SUBSET Requests] ==
                         IF S = {} THEN 0
                         ELSE LET r == CHOOSE r \in S : TRUE
                              IN srv_bufs[r] + cli_bufs[r] + f[S \ {r}]
                   IN f[Requests]
  IN slab_free + TotalHeld = SlabSize

(*
 * This invariant will be VIOLATED in the buggy model.
 *
 * Scenario: Server closed, client in BP. Client can't read EOF.
 * With no resume mechanism, client must wait for BP timeout.
 * But BP timeout DOES settle the request. So the invariant holds
 * as long as maintenance timer keeps ticking.
 *
 * The REAL bug this exposes: without resume, the only recovery
 * from BP is timeout. This means worst-case latency is always
 * backpressure_timeout_ms, even if buffers became available
 * immediately. In the test: even though the server connection
 * is killed at ~1100ms (1000ms timeout + 100ms granularity),
 * freeing 2 buffers, the client can't resume until its own
 * timeout at ~2200ms. Total: ~2.2s for the slowest request.
 *
 * With the test's 5s timeout, this SHOULD be fine. The real
 * issue must be something else — possibly the parallel test
 * runner consuming slab buffers from other tests running on
 * the same port space.
 *)
UnsettledHasPath ==
  \A r \in Requests :
    ~req_settled[r] =>
      \/ srv_state[r] = "none"
      \/ cli_state[r] = "active"
      \/ srv_state[r] = "active"
      \/ cli_state[r] = "bp"
      \/ srv_state[r] = "bp"

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
