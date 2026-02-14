----------------------------- MODULE ValkSchedAsync ------------------------------
(*
 * Composition: Scheduler Shutdown + Async Handle Completion
 *
 * Focused model verifying that the scheduler's shutdown ordering guarantees
 * preserve async handle notification delivery. Scenario:
 *
 *   race_p (ev1) — race combinator, parent
 *   ├── child1 (ev1)  — same pool leaf
 *   └── child2 (blk1) — cross-pool leaf
 *
 * Workers: w_ev on ev1, w_blk on blk1
 *
 * The critical path: child2 completes on blk1, enqueues cross-pool
 * notification. Shutdown fires. EV worker must deliver the notification
 * and resolve race_p before stopping.
 *
 * Shutdown ordering rules (from ValkScheduler):
 *   - EV workers don't stop while blocking workers are busy
 *   - EV workers don't stop while notifications target their pool
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  Handles, Workers, Pools, NULL

CONSTANTS
  HandlePool, WorkerPool, HandleParent, HandleCombType

ASSUME \A h \in Handles : HandlePool[h] \in Pools
ASSUME \A w \in Workers : WorkerPool[w] \in Pools

HandlePoolDef     == "race_p" :> "ev1" @@ "child1" :> "ev1" @@ "child2" :> "blk1"
WorkerPoolDef     == "w_ev" :> "ev1" @@ "w_blk" :> "blk1"
HandleParentDef   == "race_p" :> "null" @@ "child1" :> "race_p" @@ "child2" :> "race_p"
HandleCombTypeDef == "race_p" :> "race" @@ "child1" :> "leaf" @@ "child2" :> "leaf"

(* =========================================================================
   States
   ========================================================================= *)

Running   == "RUNNING"
Completed == "COMPLETED"
Failed    == "FAILED"
Cancelled == "CANCELLED"
Terminal  == {Completed, Failed, Cancelled}

WkIdle    == "IDLE"
WkStopped == "STOPPED"

(* =========================================================================
   Variables
   ========================================================================= *)

VARIABLES
  h_status,
  h_notified,       \* Ghost: parent notified count
  h_cleaned,        \* Ghost: cleanup count
  notify_queue,     \* Handles with pending cross-pool notification
  wk_state,
  blk_busy,         \* TRUE if blocking worker is mid-operation
  shutdown,
  drained,
  done

vars == <<h_status, h_notified, h_cleaned, notify_queue,
          wk_state, blk_busy, shutdown, drained, done>>

(* =========================================================================
   Helpers
   ========================================================================= *)

IsTerminal(s) == s \in Terminal
SamePool(h1, h2) == HandlePool[h1] = HandlePool[h2]
WorkerOnPool(w, p) == WorkerPool[w] = p
Children(h) == {c \in Handles : HandleParent[c] = h}

NotificationsToPool(p) ==
  {h \in notify_queue : HandleParent[h] # NULL /\ HandlePool[HandleParent[h]] = p}

(* =========================================================================
   Leaf Handle Completion (atomic — complete + enqueue notification)
   ========================================================================= *)

CompleteLeaf(w, h) ==
  /\ HandleCombType[h] = "leaf"
  /\ ~IsTerminal(h_status[h])
  /\ WorkerOnPool(w, HandlePool[h])
  /\ wk_state[w] = WkIdle
  /\ h_status' = [h_status EXCEPT ![h] = Completed]
  /\ h_notified' = [h_notified EXCEPT ![h] = @ + 1]
  /\ h_cleaned' = [h_cleaned EXCEPT ![h] = @ + 1]
  /\ IF HandleParent[h] # NULL /\ ~SamePool(h, HandleParent[h])
     THEN notify_queue' = notify_queue \union {h}
     ELSE UNCHANGED notify_queue
  \* Mark blocking worker as busy during completion
  /\ IF WorkerPool[w] # "ev1"
     THEN blk_busy' = TRUE
     ELSE UNCHANGED blk_busy
  /\ UNCHANGED <<wk_state, shutdown, drained, done>>

FailLeaf(w, h) ==
  /\ HandleCombType[h] = "leaf"
  /\ ~IsTerminal(h_status[h])
  /\ WorkerOnPool(w, HandlePool[h])
  /\ wk_state[w] = WkIdle
  /\ h_status' = [h_status EXCEPT ![h] = Failed]
  /\ h_notified' = [h_notified EXCEPT ![h] = @ + 1]
  /\ h_cleaned' = [h_cleaned EXCEPT ![h] = @ + 1]
  /\ IF HandleParent[h] # NULL /\ ~SamePool(h, HandleParent[h])
     THEN notify_queue' = notify_queue \union {h}
     ELSE UNCHANGED notify_queue
  /\ IF WorkerPool[w] # "ev1"
     THEN blk_busy' = TRUE
     ELSE UNCHANGED blk_busy
  /\ UNCHANGED <<wk_state, shutdown, drained, done>>

(* Blocking worker finishes its operation *)
BlkFinish ==
  /\ blk_busy
  /\ blk_busy' = FALSE
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, notify_queue,
                  wk_state, shutdown, drained, done>>

(* =========================================================================
   Cross-Pool Notification Delivery + Race Resolution
   ========================================================================= *)

DeliverAndResolve(w, child) ==
  /\ child \in notify_queue
  /\ HandleParent[child] # NULL
  /\ LET p == HandleParent[child]
     IN /\ HandleCombType[p] = "race"
        /\ h_status[p] = Running
        /\ WorkerOnPool(w, HandlePool[p])
        /\ wk_state[w] = WkIdle
        /\ LET new_s == IF h_status[child] = Completed THEN Completed ELSE Failed
           IN h_status' = [h_status EXCEPT ![p] = new_s]
        /\ h_notified' = [h_notified EXCEPT ![p] = @ + 1]
        /\ h_cleaned' = [h_cleaned EXCEPT ![p] = @ + 1]
        /\ notify_queue' = notify_queue \ {c \in Children(p) : c \in notify_queue}
  /\ UNCHANGED <<wk_state, blk_busy, shutdown, drained, done>>

(* Discard orphaned notification — parent already terminal *)
DiscardNotification(w, child) ==
  /\ child \in notify_queue
  /\ HandleParent[child] # NULL
  /\ LET p == HandleParent[child]
     IN /\ IsTerminal(h_status[p])          \* Parent already resolved
        /\ WorkerOnPool(w, HandlePool[p])
        /\ wk_state[w] = WkIdle
  /\ notify_queue' = notify_queue \ {child}
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, wk_state,
                  blk_busy, shutdown, drained, done>>

(* Same-pool child resolves race directly *)
SamePoolResolve(w, child) ==
  /\ IsTerminal(h_status[child])
  /\ HandleParent[child] # NULL
  /\ SamePool(child, HandleParent[child])
  /\ LET p == HandleParent[child]
     IN /\ HandleCombType[p] = "race"
        /\ h_status[p] = Running
        /\ WorkerOnPool(w, HandlePool[p])
        /\ wk_state[w] = WkIdle
        /\ LET new_s == IF h_status[child] = Completed THEN Completed ELSE Failed
           IN h_status' = [h_status EXCEPT ![p] = new_s]
        /\ h_notified' = [h_notified EXCEPT ![p] = @ + 1]
        /\ h_cleaned' = [h_cleaned EXCEPT ![p] = @ + 1]
        /\ notify_queue' = notify_queue \ {c \in Children(p) : c \in notify_queue}
  /\ UNCHANGED <<wk_state, blk_busy, shutdown, drained, done>>

(* =========================================================================
   Shutdown Protocol
   ========================================================================= *)

InitiateShutdown ==
  /\ ~shutdown
  /\ shutdown' = TRUE
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, notify_queue,
                  wk_state, blk_busy, drained, done>>

(* Handles whose completion could produce a notification to pool p.
   Covers: non-terminal handles on OTHER pools whose parent is on pool p. *)
PotentialNotificationsToPool(p) ==
  {h \in Handles : ~IsTerminal(h_status[h]) /\ HandleParent[h] # NULL
                   /\ HandlePool[HandleParent[h]] = p /\ HandlePool[h] # p}

(* EV worker stops — must wait for:
   1. No busy blocking workers
   2. No pending notifications to this pool
   3. No non-terminal handles on this pool
   4. No cross-pool handles that could produce future notifications here *)
EvWorkerStop(w) ==
  /\ wk_state[w] = WkIdle
  /\ WorkerOnPool(w, "ev1")
  /\ shutdown
  /\ ~blk_busy                              \* No busy blocking workers
  /\ NotificationsToPool("ev1") = {}        \* No pending notifications
  /\ \A h \in Handles :                     \* All handles on this pool are terminal
       HandlePool[h] = "ev1" => IsTerminal(h_status[h])
  /\ PotentialNotificationsToPool("ev1") = {} \* No future cross-pool notifications
  /\ wk_state' = [wk_state EXCEPT ![w] = WkStopped]
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, notify_queue,
                  blk_busy, shutdown, drained, done>>

(* Blocking worker stops — needs shutdown + idle + no non-terminal handles *)
BlkWorkerStop(w) ==
  /\ wk_state[w] = WkIdle
  /\ WorkerOnPool(w, "blk1")
  /\ shutdown
  /\ ~blk_busy
  /\ \A h \in Handles :                     \* All handles on this pool are terminal
       HandlePool[h] = "blk1" => IsTerminal(h_status[h])
  /\ wk_state' = [wk_state EXCEPT ![w] = WkStopped]
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, notify_queue,
                  blk_busy, shutdown, drained, done>>

MarkDrained ==
  /\ shutdown
  /\ ~drained
  /\ \A w \in Workers : wk_state[w] = WkStopped
  /\ notify_queue = {}
  /\ drained' = TRUE
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, notify_queue,
                  wk_state, blk_busy, shutdown, done>>

(* =========================================================================
   Specification
   ========================================================================= *)

Init ==
  /\ h_status = [h \in Handles |->
       IF HandleCombType[h] = "race" THEN Running ELSE Running]
  /\ h_notified = [h \in Handles |-> 0]
  /\ h_cleaned = [h \in Handles |-> 0]
  /\ notify_queue = {}
  /\ wk_state = [w \in Workers |-> WkIdle]
  /\ blk_busy = FALSE
  /\ shutdown = FALSE
  /\ drained = FALSE
  /\ done = FALSE

MarkAllDone ==
  /\ \A h \in Handles : IsTerminal(h_status[h])
  /\ notify_queue = {}
  /\ ~done
  /\ done' = TRUE
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, notify_queue,
                  wk_state, blk_busy, shutdown, drained>>

Stutter ==
  /\ (done \/ drained)
  /\ UNCHANGED vars

Next ==
  \/ \E w \in Workers, h \in Handles :
       \/ CompleteLeaf(w, h)
       \/ FailLeaf(w, h)
       \/ DeliverAndResolve(w, h)
       \/ DiscardNotification(w, h)
       \/ SamePoolResolve(w, h)
  \/ BlkFinish
  \/ \E w \in Workers :
       \/ EvWorkerStop(w)
       \/ BlkWorkerStop(w)
  \/ InitiateShutdown
  \/ MarkDrained
  \/ MarkAllDone
  \/ Stutter

Fairness ==
  /\ WF_vars(Next)
  /\ \A w \in Workers :
       SF_vars(\E h \in Handles :
         \/ CompleteLeaf(w, h)
         \/ FailLeaf(w, h)
         \/ DeliverAndResolve(w, h)
         \/ DiscardNotification(w, h)
         \/ SamePoolResolve(w, h))
  /\ WF_vars(BlkFinish)
  /\ \A w \in Workers :
       /\ WF_vars(EvWorkerStop(w))
       /\ WF_vars(BlkWorkerStop(w))
  /\ WF_vars(MarkDrained)
  /\ WF_vars(MarkAllDone)

Spec == Init /\ [][Next]_vars /\ Fairness

(* =========================================================================
   Safety
   ========================================================================= *)

TypeOK ==
  /\ \A h \in Handles :
       /\ h_status[h] \in {Running, Completed, Failed, Cancelled}
       /\ h_notified[h] \in 0..1
       /\ h_cleaned[h] \in 0..1
  /\ notify_queue \subseteq Handles
  /\ \A w \in Workers : wk_state[w] \in {WkIdle, WkStopped}
  /\ blk_busy \in BOOLEAN
  /\ shutdown \in BOOLEAN
  /\ drained \in BOOLEAN

NoLostNotification ==
  drained => notify_queue = {}

ShutdownSafety ==
  drained =>
    \A h \in Handles :
      HandleCombType[h] = "race" => IsTerminal(h_status[h])

HandleConsistency ==
  \A h \in Handles :
    IsTerminal(h_status[h]) =>
      /\ h_notified[h] = 1
      /\ h_cleaned[h] = 1

NoDoubleFire ==
  \A h \in Handles :
    /\ h_notified[h] <= 1
    /\ h_cleaned[h] <= 1

(* =========================================================================
   Liveness
   ========================================================================= *)

AllHandlesComplete ==
  \A h \in Handles : <>(IsTerminal(h_status[h]))

ShutdownCompletes ==
  shutdown ~> drained

================================================================================
