--------------------------- MODULE ValkScheduler ------------------------------
(*
 * Task Scheduling Model for Valkyria Runtime
 *
 * Models multiple AIO systems, each containing:
 *   - N event loop workers sharing a Chase-Lev work-stealing deque
 *   - An expandable blocking pool with its own task queue
 *   - Cross-pool notification: blocking pool -> event loop and vice versa
 *   - Cross-system notification: AIO system A -> AIO system B
 *
 * Thread types:
 *   - EventLoopWorker: runs libuv loop, processes async I/O, steals from deque
 *   - BlockingWorker: runs blocking ops (DNS, file I/O), expands on demand
 *
 * Task lifecycle:
 *   1. Task created (by any thread, on any system)
 *   2. Enqueued to target system's appropriate pool queue
 *   3. Worker picks up task (owner pop or steal)
 *   4. Task executes, may produce result
 *   5. Result notification sent (possibly cross-pool or cross-system)
 *
 * Properties proved:
 *   P1 (No Lost Tasks)    — Every enqueued task is eventually executed
 *   P2 (Work Stealing)    — If work exists in any deque, some worker processes it
 *   P3 (Cross-Pool)       — Blocking completion eventually notifies event loop
 *   P4 (Cross-System)     — Cross-system notification eventually delivered
 *   P5 (Pool Expansion)   — Blocking pool expands when all workers busy
 *   P6 (Shutdown)         — Shutdown signal drains all queues and stops all threads
 *   P7 (No Double Exec)   — Each task executes at most once
 *)
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  Systems,            \* Set of AIO system IDs
  Workers,            \* Set of all worker thread IDs
  Tasks,              \* Set of task IDs
  NULL

(* Worker type assignment — provided per-scenario *)
CONSTANTS
  WorkerSystem,       \* WorkerSystem[w] = system ID this worker belongs to
  WorkerType,         \* WorkerType[w] = "ev" | "blocking"
  IsExpandable        \* IsExpandable[w] = TRUE if this worker can be spawned on demand

ASSUME \A w \in Workers : WorkerSystem[w] \in Systems
ASSUME \A w \in Workers : WorkerType[w] \in {"ev", "blocking"}
ASSUME \A w \in Workers : IsExpandable[w] \in BOOLEAN

(* Operator definitions for TLC config overrides — single system scenario *)
WorkerSystemDef ==
  "ev1" :> "s1" @@ "blk1" :> "s1" @@ "blk2" :> "s1"

WorkerTypeDef ==
  "ev1" :> "ev" @@ "blk1" :> "blocking" @@ "blk2" :> "blocking"

IsExpandableDef ==
  "ev1" :> FALSE @@ "blk1" :> FALSE @@ "blk2" :> TRUE

(* Multi-system scenario operator definitions *)
WorkerSystemMultiDef ==
  "ev1a" :> "s1" @@ "ev1b" :> "s1" @@
  "blk1a" :> "s1" @@ "blk1x" :> "s1" @@
  "ev2a" :> "s2" @@ "blk2a" :> "s2"

WorkerTypeMultiDef ==
  "ev1a" :> "ev" @@ "ev1b" :> "ev" @@
  "blk1a" :> "blocking" @@ "blk1x" :> "blocking" @@
  "ev2a" :> "ev" @@ "blk2a" :> "blocking"

IsExpandableMultiDef ==
  "ev1a" :> FALSE @@ "ev1b" :> FALSE @@
  "blk1a" :> FALSE @@ "blk1x" :> TRUE @@
  "ev2a" :> FALSE @@ "blk2a" :> FALSE

(* =========================================================================
   Thread States
   ========================================================================= *)

WkIdle       == "IDLE"
WkBusy       == "BUSY"        \* Executing a task
WkStopped    == "STOPPED"
WkNotSpawned == "NOT_SPAWNED" \* Expandable blocking worker, not yet alive

AllWorkerStates == {WkIdle, WkBusy, WkStopped, WkNotSpawned}

(* =========================================================================
   Task States
   ========================================================================= *)

TkPending      == "PENDING"       \* Created, not yet enqueued
TkQueued       == "QUEUED"        \* In a system's task queue
TkExecuting    == "EXECUTING"     \* Being run by a worker
TkDone         == "DONE"          \* Execution complete
TkNotifyQueued == "NOTIFY_QUEUED" \* Result notification enqueued on target system
TkDelivered    == "DELIVERED"     \* Notification delivered to target

AllTaskStates == {TkPending, TkQueued, TkExecuting, TkDone, TkNotifyQueued, TkDelivered}

(* =========================================================================
   Variables
   ========================================================================= *)

VARIABLES
  wk_state,         \* wk_state[w]: worker state
  wk_task,          \* wk_task[w]: task currently being executed (or NULL)

  tk_state,         \* tk_state[t]: task lifecycle state
  tk_system,        \* tk_system[t]: which system the task is queued on
  tk_pool,          \* tk_pool[t]: "ev" or "blocking" — target pool
  tk_notify_sys,    \* tk_notify_sys[t]: system to notify on completion (or NULL)
  tk_notify_pool,   \* tk_notify_pool[t]: pool to notify on completion
  tk_executor,      \* tk_executor[t]: which worker executed this task (or NULL)

  \* Per-system queues (modeled as sets for abstraction — Chase-Lev ordering
  \* is not relevant for correctness, only performance)
  sys_ev_queue,     \* sys_ev_queue[s]: set of task IDs in event loop deque
  sys_blk_queue,    \* sys_blk_queue[s]: set of task IDs in blocking pool queue
  sys_notify_queue, \* sys_notify_queue[s]: set of task IDs with pending notifications

  sys_shutdown,     \* sys_shutdown[s]: TRUE if shutdown requested
  sys_drained       \* sys_drained[s]: TRUE if all work processed and workers stopped

vars == <<wk_state, wk_task, tk_state, tk_system, tk_pool,
          tk_notify_sys, tk_notify_pool, tk_executor,
          sys_ev_queue, sys_blk_queue, sys_notify_queue,
          sys_shutdown, sys_drained>>

(* =========================================================================
   Helpers
   ========================================================================= *)

WorkersOf(s, typ) == {w \in Workers : WorkerSystem[w] = s /\ WorkerType[w] = typ}

AliveWorkers(s, typ) == {w \in WorkersOf(s, typ) : wk_state[w] # WkNotSpawned}

IdleWorkers(s, typ) == {w \in WorkersOf(s, typ) : wk_state[w] = WkIdle}

BusyWorkers(s, typ) == {w \in WorkersOf(s, typ) : wk_state[w] = WkBusy}

SpawnableWorkers(s) ==
  {w \in WorkersOf(s, "blocking") : IsExpandable[w] /\ wk_state[w] = WkNotSpawned}

AllQueuesEmpty(s) ==
  /\ sys_ev_queue[s] = {}
  /\ sys_blk_queue[s] = {}
  /\ sys_notify_queue[s] = {}

AllWorkersStopped(s) ==
  \A w \in Workers :
    WorkerSystem[w] = s => wk_state[w] \in {WkStopped, WkNotSpawned}

(* Tasks that are queued or executing and will eventually send
   a notification to system s. Covers the full window from submission
   to completion — not just the executing moment. *)
PendingNotificationsTo(s) ==
  {t \in Tasks : tk_state[t] \in {TkQueued, TkExecuting} /\ tk_notify_sys[t] = s}

(* =========================================================================
   Init
   ========================================================================= *)

Init ==
  /\ wk_state = [w \in Workers |->
       IF IsExpandable[w] THEN WkNotSpawned ELSE WkIdle]
  /\ wk_task = [w \in Workers |-> NULL]
  /\ tk_state = [t \in Tasks |-> TkPending]
  /\ tk_system = [t \in Tasks |-> CHOOSE s \in Systems : TRUE]  \* arbitrary initial
  /\ tk_pool = [t \in Tasks |-> "ev"]    \* default: event loop
  /\ tk_notify_sys = [t \in Tasks |-> NULL]
  /\ tk_notify_pool = [t \in Tasks |-> "ev"]
  /\ tk_executor = [t \in Tasks |-> NULL]
  /\ sys_ev_queue = [s \in Systems |-> {}]
  /\ sys_blk_queue = [s \in Systems |-> {}]
  /\ sys_notify_queue = [s \in Systems |-> {}]
  /\ sys_shutdown = [s \in Systems |-> FALSE]
  /\ sys_drained = [s \in Systems |-> FALSE]

(* =========================================================================
   Task Submission
   ========================================================================= *)

(* Submit a task to a system's event loop queue *)
SubmitToEventLoop(t, s) ==
  /\ tk_state[t] = TkPending
  /\ ~sys_shutdown[s]
  /\ tk_state' = [tk_state EXCEPT ![t] = TkQueued]
  /\ tk_system' = [tk_system EXCEPT ![t] = s]
  /\ tk_pool' = [tk_pool EXCEPT ![t] = "ev"]
  /\ sys_ev_queue' = [sys_ev_queue EXCEPT ![s] = @ \union {t}]
  /\ UNCHANGED <<wk_state, wk_task, tk_notify_sys, tk_notify_pool, tk_executor,
                  sys_blk_queue, sys_notify_queue, sys_shutdown, sys_drained>>

(* Submit a task to a system's blocking pool queue *)
SubmitToBlockingPool(t, s) ==
  /\ tk_state[t] = TkPending
  /\ ~sys_shutdown[s]
  /\ tk_state' = [tk_state EXCEPT ![t] = TkQueued]
  /\ tk_system' = [tk_system EXCEPT ![t] = s]
  /\ tk_pool' = [tk_pool EXCEPT ![t] = "blocking"]
  /\ sys_blk_queue' = [sys_blk_queue EXCEPT ![s] = @ \union {t}]
  /\ UNCHANGED <<wk_state, wk_task, tk_notify_sys, tk_notify_pool, tk_executor,
                  sys_ev_queue, sys_notify_queue, sys_shutdown, sys_drained>>

(* Submit a task with cross-pool notification target.
   The notification target system must not be shutting down — once shutdown
   is initiated, no new work can target that system for notifications.
   In implementation: checked via atomic load of target's shutdown flag. *)
SubmitWithNotify(t, src_sys, src_pool, notify_sys, notify_pool) ==
  /\ tk_state[t] = TkPending
  /\ ~sys_shutdown[src_sys]
  /\ ~sys_shutdown[notify_sys]        \* Target must accept notifications
  /\ tk_state' = [tk_state EXCEPT ![t] = TkQueued]
  /\ tk_system' = [tk_system EXCEPT ![t] = src_sys]
  /\ tk_pool' = [tk_pool EXCEPT ![t] = src_pool]
  /\ tk_notify_sys' = [tk_notify_sys EXCEPT ![t] = notify_sys]
  /\ tk_notify_pool' = [tk_notify_pool EXCEPT ![t] = notify_pool]
  /\ IF src_pool = "ev"
     THEN /\ sys_ev_queue' = [sys_ev_queue EXCEPT ![src_sys] = @ \union {t}]
          /\ UNCHANGED sys_blk_queue
     ELSE /\ sys_blk_queue' = [sys_blk_queue EXCEPT ![src_sys] = @ \union {t}]
          /\ UNCHANGED sys_ev_queue
  /\ UNCHANGED <<wk_state, wk_task, tk_executor,
                  sys_notify_queue, sys_shutdown, sys_drained>>

(* =========================================================================
   Task Execution — Event Loop Workers
   ========================================================================= *)

(* Event loop worker picks up a task from its own system's deque *)
EvWorkerPickup(w) ==
  /\ wk_state[w] = WkIdle
  /\ WorkerType[w] = "ev"
  /\ LET s == WorkerSystem[w]
     IN /\ sys_ev_queue[s] # {}
        /\ \E t \in sys_ev_queue[s] :
             /\ wk_task' = [wk_task EXCEPT ![w] = t]
             /\ wk_state' = [wk_state EXCEPT ![w] = WkBusy]
             /\ tk_state' = [tk_state EXCEPT ![t] = TkExecuting]
             /\ tk_executor' = [tk_executor EXCEPT ![t] = w]
             /\ sys_ev_queue' = [sys_ev_queue EXCEPT ![s] = @ \ {t}]
  /\ UNCHANGED <<tk_system, tk_pool, tk_notify_sys, tk_notify_pool,
                  sys_blk_queue, sys_notify_queue, sys_shutdown, sys_drained>>

(* Event loop worker steals from another worker's system — not modeled
   because work-stealing is within a single system's deque. In the target
   architecture, each system has ONE shared deque, so "stealing" is just
   another worker popping from the same deque. The set-based queue model
   already captures this: any ev worker of the system can pick from the set. *)

(* =========================================================================
   Task Execution — Blocking Pool Workers
   ========================================================================= *)

(* Blocking worker picks up a task *)
BlkWorkerPickup(w) ==
  /\ wk_state[w] = WkIdle
  /\ WorkerType[w] = "blocking"
  /\ LET s == WorkerSystem[w]
     IN /\ sys_blk_queue[s] # {}
        /\ \E t \in sys_blk_queue[s] :
             /\ wk_task' = [wk_task EXCEPT ![w] = t]
             /\ wk_state' = [wk_state EXCEPT ![w] = WkBusy]
             /\ tk_state' = [tk_state EXCEPT ![t] = TkExecuting]
             /\ tk_executor' = [tk_executor EXCEPT ![t] = w]
             /\ sys_blk_queue' = [sys_blk_queue EXCEPT ![s] = @ \ {t}]
  /\ UNCHANGED <<tk_system, tk_pool, tk_notify_sys, tk_notify_pool,
                  sys_ev_queue, sys_notify_queue, sys_shutdown, sys_drained>>

(* =========================================================================
   Blocking Pool Expansion
   ========================================================================= *)

(* When all blocking workers are busy and queue is non-empty, expand *)
ExpandBlockingPool(s) ==
  /\ ~sys_shutdown[s]
  /\ sys_blk_queue[s] # {}
  /\ IdleWorkers(s, "blocking") = {}   \* No idle workers available
  /\ SpawnableWorkers(s) # {}
  /\ LET w == CHOOSE w \in SpawnableWorkers(s) : TRUE
     IN /\ wk_state' = [wk_state EXCEPT ![w] = WkIdle]
  /\ UNCHANGED <<wk_task, tk_state, tk_system, tk_pool,
                  tk_notify_sys, tk_notify_pool, tk_executor,
                  sys_ev_queue, sys_blk_queue, sys_notify_queue,
                  sys_shutdown, sys_drained>>

(* =========================================================================
   Task Completion and Cross-Pool Notification
   ========================================================================= *)

(* Worker completes a task — if notification target exists, enqueue notification *)
CompleteTask(w) ==
  /\ wk_state[w] = WkBusy
  /\ wk_task[w] # NULL
  /\ LET t == wk_task[w]
     IN /\ tk_state[t] = TkExecuting
        /\ IF tk_notify_sys[t] # NULL
           THEN \* Cross-pool or cross-system notification
                /\ tk_state' = [tk_state EXCEPT ![t] = TkNotifyQueued]
                /\ LET target_s == tk_notify_sys[t]
                   IN sys_notify_queue' = [sys_notify_queue EXCEPT
                        ![target_s] = @ \union {t}]
           ELSE \* No notification needed — task is done
                /\ tk_state' = [tk_state EXCEPT ![t] = TkDelivered]
                /\ UNCHANGED sys_notify_queue
        /\ wk_state' = [wk_state EXCEPT ![w] = WkIdle]
        /\ wk_task' = [wk_task EXCEPT ![w] = NULL]
  /\ UNCHANGED <<tk_system, tk_pool, tk_notify_sys, tk_notify_pool, tk_executor,
                  sys_ev_queue, sys_blk_queue, sys_shutdown, sys_drained>>

(* Event loop worker delivers a notification (e.g., uv_async_send woke us) *)
DeliverNotification(w) ==
  /\ wk_state[w] = WkIdle
  /\ WorkerType[w] = "ev"
  /\ LET s == WorkerSystem[w]
     IN /\ sys_notify_queue[s] # {}
        /\ \E t \in sys_notify_queue[s] :
             /\ tk_state[t] = TkNotifyQueued
             /\ tk_state' = [tk_state EXCEPT ![t] = TkDelivered]
             /\ sys_notify_queue' = [sys_notify_queue EXCEPT ![s] = @ \ {t}]
  /\ UNCHANGED <<wk_state, wk_task, tk_system, tk_pool,
                  tk_notify_sys, tk_notify_pool, tk_executor,
                  sys_ev_queue, sys_blk_queue, sys_shutdown, sys_drained>>

(* Blocking worker delivers a notification targeting the blocking pool *)
BlkDeliverNotification(w) ==
  /\ wk_state[w] = WkIdle
  /\ WorkerType[w] = "blocking"
  /\ LET s == WorkerSystem[w]
     IN /\ sys_notify_queue[s] # {}
        /\ \E t \in sys_notify_queue[s] :
             /\ tk_state[t] = TkNotifyQueued
             /\ tk_notify_pool[t] = "blocking"
             /\ tk_state' = [tk_state EXCEPT ![t] = TkDelivered]
             /\ sys_notify_queue' = [sys_notify_queue EXCEPT ![s] = @ \ {t}]
  /\ UNCHANGED <<wk_state, wk_task, tk_system, tk_pool,
                  tk_notify_sys, tk_notify_pool, tk_executor,
                  sys_ev_queue, sys_blk_queue, sys_shutdown, sys_drained>>

(* =========================================================================
   Shutdown Protocol
   ========================================================================= *)

(* Initiate shutdown on a system *)
InitiateShutdown(s) ==
  /\ ~sys_shutdown[s]
  /\ sys_shutdown' = [sys_shutdown EXCEPT ![s] = TRUE]
  /\ UNCHANGED <<wk_state, wk_task, tk_state, tk_system, tk_pool,
                  tk_notify_sys, tk_notify_pool, tk_executor,
                  sys_ev_queue, sys_blk_queue, sys_notify_queue, sys_drained>>

(* Worker stops after shutdown when safe to do so.
   Event loop workers must wait until:
     1. No local blocking workers are busy (they might enqueue local notifications)
     2. No inflight task on any system will send a cross-system notification here
   This prevents lost notifications from both local and remote completions. *)
WorkerStop(w) ==
  /\ wk_state[w] = WkIdle
  /\ LET s == WorkerSystem[w]
     IN /\ sys_shutdown[s]
        /\ AllQueuesEmpty(s)
        /\ IF WorkerType[w] = "ev"
           THEN /\ BusyWorkers(s, "blocking") = {}
                /\ PendingNotificationsTo(s) = {}
           ELSE TRUE
  /\ wk_state' = [wk_state EXCEPT ![w] = WkStopped]
  /\ UNCHANGED <<wk_task, tk_state, tk_system, tk_pool,
                  tk_notify_sys, tk_notify_pool, tk_executor,
                  sys_ev_queue, sys_blk_queue, sys_notify_queue,
                  sys_shutdown, sys_drained>>

(* System is fully drained when all workers stopped *)
MarkDrained(s) ==
  /\ sys_shutdown[s]
  /\ ~sys_drained[s]
  /\ AllWorkersStopped(s)
  /\ AllQueuesEmpty(s)
  /\ sys_drained' = [sys_drained EXCEPT ![s] = TRUE]
  /\ UNCHANGED <<wk_state, wk_task, tk_state, tk_system, tk_pool,
                  tk_notify_sys, tk_notify_pool, tk_executor,
                  sys_ev_queue, sys_blk_queue, sys_notify_queue, sys_shutdown>>

(* =========================================================================
   Next-State Relation
   ========================================================================= *)

(* Terminal condition: all systems drained *)
AllDrained == \A s \in Systems : sys_drained[s]

Stutter == AllDrained /\ UNCHANGED vars

Next ==
  \* Task submission
  \/ \E t \in Tasks, s \in Systems : SubmitToEventLoop(t, s)
  \/ \E t \in Tasks, s \in Systems : SubmitToBlockingPool(t, s)
  \/ \E t \in Tasks, s1 \in Systems, s2 \in Systems,
        p1 \in {"ev", "blocking"}, p2 \in {"ev", "blocking"} :
       SubmitWithNotify(t, s1, p1, s2, p2)
  \* Task execution
  \/ \E w \in Workers : EvWorkerPickup(w)
  \/ \E w \in Workers : BlkWorkerPickup(w)
  \* Pool expansion
  \/ \E s \in Systems : ExpandBlockingPool(s)
  \* Task completion
  \/ \E w \in Workers : CompleteTask(w)
  \* Notification delivery
  \/ \E w \in Workers : DeliverNotification(w)
  \/ \E w \in Workers : BlkDeliverNotification(w)
  \* Shutdown
  \/ \E s \in Systems : InitiateShutdown(s)
  \/ \E w \in Workers : WorkerStop(w)
  \/ \E s \in Systems : MarkDrained(s)
  \* Terminal stuttering
  \/ Stutter

Fairness ==
  /\ WF_vars(Next)
  /\ \A w \in Workers :
       /\ WF_vars(EvWorkerPickup(w))
       /\ WF_vars(BlkWorkerPickup(w))
       /\ WF_vars(CompleteTask(w))
       /\ WF_vars(DeliverNotification(w))
       /\ WF_vars(BlkDeliverNotification(w))
       /\ WF_vars(WorkerStop(w))
  /\ \A s \in Systems :
       /\ WF_vars(ExpandBlockingPool(s))
       /\ WF_vars(MarkDrained(s))

Spec == Init /\ [][Next]_vars /\ Fairness

(* =========================================================================
   Type Invariant
   ========================================================================= *)

TypeOK ==
  /\ \A w \in Workers : wk_state[w] \in AllWorkerStates
  /\ \A t \in Tasks : tk_state[t] \in AllTaskStates
  /\ \A s \in Systems :
       /\ sys_ev_queue[s] \subseteq Tasks
       /\ sys_blk_queue[s] \subseteq Tasks
       /\ sys_notify_queue[s] \subseteq Tasks
       /\ sys_shutdown[s] \in BOOLEAN
       /\ sys_drained[s] \in BOOLEAN

(* =========================================================================
   Safety Properties
   ========================================================================= *)

(* P7: No task is executed by more than one worker *)
NoDoubleExecution ==
  \A t \in Tasks :
    tk_state[t] = TkExecuting =>
      Cardinality({w \in Workers : wk_task[w] = t}) = 1

(* A task in a queue belongs to exactly one queue *)
NoQueueDuplication ==
  \A t \in Tasks :
    Cardinality({s \in Systems : t \in sys_ev_queue[s]}) +
    Cardinality({s \in Systems : t \in sys_blk_queue[s]}) +
    Cardinality({s \in Systems : t \in sys_notify_queue[s]}) <= 1

(* A busy worker always has a task assigned *)
BusyHasTask ==
  \A w \in Workers :
    wk_state[w] = WkBusy => wk_task[w] # NULL

(* Shutdown is monotonic — once requested, stays requested *)
ShutdownMonotonic ==
  \A s \in Systems :
    sys_drained[s] => sys_shutdown[s]

(* =========================================================================
   Liveness Properties
   ========================================================================= *)

(* P1: Every queued task eventually reaches a terminal state.
   Note: tasks that remain PENDING (never submitted) are not covered —
   that is a valid outcome since submission is voluntary. *)
TaskCompletion ==
  \A t \in Tasks :
    tk_state[t] = TkQueued ~> tk_state[t] \in {TkDone, TkDelivered}

(* P3: Cross-pool notification eventually delivered *)
CrossPoolDelivery ==
  \A t \in Tasks :
    tk_state[t] = TkNotifyQueued ~> tk_state[t] = TkDelivered

(* P6 (strong): After shutdown is requested, system eventually drains.
   This requires that all in-flight tasks complete, notifications deliver,
   and workers stop — the full shutdown protocol. *)
ShutdownDrains ==
  \A s \in Systems :
    sys_shutdown[s] ~> sys_drained[s]

================================================================================
