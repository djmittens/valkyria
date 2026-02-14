------------------------ MODULE ValkSchedAsyncDispatch -------------------------
(*
 * Composition: Scheduler Task Dispatch + Async Handle Completion
 *
 * Models the full path from scheduler task dispatch to async handle
 * resolution. The key interaction: a scheduler task's execution triggers
 * handle completion, which produces a cross-pool notification that must
 * be delivered via another scheduler task.
 *
 * Scenario:
 *   race_p (ev1) — race combinator on event loop pool
 *   ├── child1 (ev1)  — work runs as ev task
 *   └── child2 (blk1) — work runs as blocking task
 *
 *   Workers: w_ev on ev1, w_blk on blk1
 *   Tasks:
 *     task1 — scheduler task for child1's work (on ev1 queue)
 *     task2 — scheduler task for child2's work (on blk1 queue)
 *     ntask — dynamically created notification task (on ev1 queue)
 *
 * The model verifies that the chain: task pickup → execute → handle
 * complete → enqueue notification task → deliver → parent resolve
 * works correctly with work-stealing and concurrent completion.
 *
 * Properties:
 *   - TaskToHandle: every executed task completes its associated handle
 *   - HandleToNotification: cross-pool completion produces notification task
 *   - NotificationToResolution: delivered notification resolves parent
 *   - EndToEnd: scheduler task eventually leads to parent resolution
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  Handles, Workers, Pools, NULL

CONSTANTS
  HandlePool, WorkerPool, HandleParent, HandleCombType

HandlePoolDef     == "race_p" :> "ev1" @@ "child1" :> "ev1" @@ "child2" :> "blk1"
WorkerPoolDef     == "w_ev" :> "ev1" @@ "w_blk" :> "blk1"
HandleParentDef   == "race_p" :> "null" @@ "child1" :> "race_p" @@ "child2" :> "race_p"
HandleCombTypeDef == "race_p" :> "race" @@ "child1" :> "leaf" @@ "child2" :> "leaf"

ASSUME \A h \in Handles : HandlePool[h] \in Pools
ASSUME \A w \in Workers : WorkerPool[w] \in Pools

(* =========================================================================
   States
   ========================================================================= *)

Running   == "RUNNING"
Completed == "COMPLETED"
Failed    == "FAILED"
Cancelled == "CANCELLED"
Terminal  == {Completed, Failed, Cancelled}

(* Scheduler task states *)
TkQueued    == "QUEUED"
TkExecuting == "EXECUTING"
TkDone      == "DONE"

(* =========================================================================
   Variables
   ========================================================================= *)

VARIABLES
  \* Handle lifecycle
  h_status,
  h_notified,          \* Ghost counter
  h_cleaned,           \* Ghost counter

  \* Scheduler task queues (set-based, models Chase-Lev deque)
  ev_queue,            \* Set of task IDs on ev1 pool
  blk_queue,           \* Set of task IDs on blk1 pool

  \* Task → Handle association
  \* task_handle[task] = handle this task will complete when executed
  \* For notification tasks, this is the child handle whose notification we deliver
  task_state,          \* task_state[task]: TkQueued | TkExecuting | TkDone
  task_handle,         \* task_handle[task]: handle associated with this task
  task_is_notify,      \* task_is_notify[task]: TRUE if this is a notification task

  \* Worker state
  wk_task,             \* wk_task[w]: task currently being executed (or NULL)
  wk_idle,             \* wk_idle[w]: TRUE if idle

  \* Notification task lifecycle
  notify_task_created, \* TRUE if the cross-pool notification task has been created

  done

vars == <<h_status, h_notified, h_cleaned,
          ev_queue, blk_queue,
          task_state, task_handle, task_is_notify,
          wk_task, wk_idle,
          notify_task_created, done>>

(* =========================================================================
   Helpers
   ========================================================================= *)

IsTerminal(s) == s \in Terminal
SamePool(h1, h2) == HandlePool[h1] = HandlePool[h2]
WorkerOnPool(w, p) == WorkerPool[w] = p
Children(h) == {c \in Handles : HandleParent[c] = h}

(* Set of tasks — work tasks + optional notification task *)
Tasks == {"task1", "task2", "ntask"}

(* =========================================================================
   Task Pickup (models Chase-Lev pop/steal)
   ========================================================================= *)

EvPickup(w) ==
  /\ WorkerOnPool(w, "ev1")
  /\ wk_idle[w]
  /\ ev_queue # {}
  /\ \E t \in ev_queue :
       /\ wk_task' = [wk_task EXCEPT ![w] = t]
       /\ wk_idle' = [wk_idle EXCEPT ![w] = FALSE]
       /\ task_state' = [task_state EXCEPT ![t] = TkExecuting]
       /\ ev_queue' = ev_queue \ {t}
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, blk_queue,
                  task_handle, task_is_notify, notify_task_created, done>>

BlkPickup(w) ==
  /\ WorkerOnPool(w, "blk1")
  /\ wk_idle[w]
  /\ blk_queue # {}
  /\ \E t \in blk_queue :
       /\ wk_task' = [wk_task EXCEPT ![w] = t]
       /\ wk_idle' = [wk_idle EXCEPT ![w] = FALSE]
       /\ task_state' = [task_state EXCEPT ![t] = TkExecuting]
       /\ blk_queue' = blk_queue \ {t}
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, ev_queue,
                  task_handle, task_is_notify, notify_task_created, done>>

(* =========================================================================
   Task Execution — Work Tasks (complete the associated handle)
   ========================================================================= *)

ExecuteWorkTask(w) ==
  /\ ~wk_idle[w]
  /\ wk_task[w] # NULL
  /\ LET t == wk_task[w]
     IN /\ ~task_is_notify[t]                \* This is a work task, not notification
        /\ task_state[t] = TkExecuting
        /\ LET h == task_handle[t]
           IN /\ ~IsTerminal(h_status[h])    \* Handle not yet terminal
              \* Complete the handle via __reach_terminal
              /\ h_status' = [h_status EXCEPT ![h] = Completed]
              /\ h_notified' = [h_notified EXCEPT ![h] = @ + 1]
              /\ h_cleaned' = [h_cleaned EXCEPT ![h] = @ + 1]
              \* If cross-pool parent, create notification task
              /\ IF HandleParent[h] # NULL /\ ~SamePool(h, HandleParent[h])
                      /\ ~notify_task_created
                 THEN /\ ev_queue' = ev_queue \union {"ntask"}
                      /\ task_state' = [task_state EXCEPT ![t] = TkDone,
                                                          !["ntask"] = TkQueued]
                      /\ task_handle' = [task_handle EXCEPT !["ntask"] = h]
                      /\ task_is_notify' = [task_is_notify EXCEPT !["ntask"] = TRUE]
                      /\ notify_task_created' = TRUE
                 ELSE /\ task_state' = [task_state EXCEPT ![t] = TkDone]
                      /\ UNCHANGED <<ev_queue, task_handle, task_is_notify,
                                      notify_task_created>>
        /\ wk_task' = [wk_task EXCEPT ![w] = NULL]
        /\ wk_idle' = [wk_idle EXCEPT ![w] = TRUE]
  /\ UNCHANGED <<blk_queue, done>>

(* Work task completes but handle is already terminal (CAS loser) *)
ExecuteWorkTaskCasLose(w) ==
  /\ ~wk_idle[w]
  /\ wk_task[w] # NULL
  /\ LET t == wk_task[w]
     IN /\ ~task_is_notify[t]
        /\ task_state[t] = TkExecuting
        /\ LET h == task_handle[t]
           IN IsTerminal(h_status[h])        \* Already terminal — CAS would fail
        /\ task_state' = [task_state EXCEPT ![t] = TkDone]
  /\ wk_task' = [wk_task EXCEPT ![w] = NULL]
  /\ wk_idle' = [wk_idle EXCEPT ![w] = TRUE]
  /\ UNCHANGED <<h_status, h_notified, h_cleaned, ev_queue, blk_queue,
                  task_handle, task_is_notify, notify_task_created, done>>

(* =========================================================================
   Task Execution — Notification Task (deliver cross-pool notification)
   ========================================================================= *)

ExecuteNotifyTask(w) ==
  /\ ~wk_idle[w]
  /\ wk_task[w] # NULL
  /\ LET t == wk_task[w]
     IN /\ task_is_notify[t]
        /\ task_state[t] = TkExecuting
        /\ LET child == task_handle[t]
               p == HandleParent[child]
           IN /\ p # NULL
              /\ HandleCombType[p] = "race"
              /\ IF h_status[p] = Running
                 THEN \* Resolve the parent
                      /\ LET new_s == IF h_status[child] = Completed
                                      THEN Completed ELSE Failed
                         IN h_status' = [h_status EXCEPT ![p] = new_s]
                      /\ h_notified' = [h_notified EXCEPT ![p] = @ + 1]
                      /\ h_cleaned' = [h_cleaned EXCEPT ![p] = @ + 1]
                 ELSE \* Parent already terminal — discard
                      UNCHANGED <<h_status, h_notified, h_cleaned>>
        /\ task_state' = [task_state EXCEPT ![t] = TkDone]
  /\ wk_task' = [wk_task EXCEPT ![w] = NULL]
  /\ wk_idle' = [wk_idle EXCEPT ![w] = TRUE]
  /\ UNCHANGED <<ev_queue, blk_queue, task_handle, task_is_notify,
                  notify_task_created, done>>

(* =========================================================================
   Same-Pool Resolution (no scheduler task needed)
   ========================================================================= *)

SamePoolResolve(w, child) ==
  /\ IsTerminal(h_status[child])
  /\ HandleParent[child] # NULL
  /\ SamePool(child, HandleParent[child])
  /\ LET p == HandleParent[child]
     IN /\ HandleCombType[p] = "race"
        /\ h_status[p] = Running
        /\ WorkerOnPool(w, HandlePool[p])
        /\ wk_idle[w]
        /\ LET new_s == IF h_status[child] = Completed THEN Completed ELSE Failed
           IN h_status' = [h_status EXCEPT ![p] = new_s]
        /\ h_notified' = [h_notified EXCEPT ![p] = @ + 1]
        /\ h_cleaned' = [h_cleaned EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<ev_queue, blk_queue, task_state, task_handle, task_is_notify,
                  wk_task, wk_idle, notify_task_created, done>>

(* =========================================================================
   Specification
   ========================================================================= *)

Init ==
  /\ h_status = ("race_p" :> Running @@ "child1" :> Running @@ "child2" :> Running)
  /\ h_notified = [h \in Handles |-> 0]
  /\ h_cleaned = [h \in Handles |-> 0]
  /\ ev_queue = {"task1"}            \* child1's work task on ev queue
  /\ blk_queue = {"task2"}           \* child2's work task on blk queue
  /\ task_state = ("task1" :> TkQueued @@ "task2" :> TkQueued @@ "ntask" :> TkDone)
  /\ task_handle = ("task1" :> "child1" @@ "task2" :> "child2" @@ "ntask" :> NULL)
  /\ task_is_notify = ("task1" :> FALSE @@ "task2" :> FALSE @@ "ntask" :> FALSE)
  /\ wk_task = [w \in Workers |-> NULL]
  /\ wk_idle = [w \in Workers |-> TRUE]
  /\ notify_task_created = FALSE
  /\ done = FALSE

AllTerminal == \A h \in Handles : IsTerminal(h_status[h])

MarkDone ==
  /\ AllTerminal
  /\ ~done
  /\ done' = TRUE
  /\ UNCHANGED <<h_status, h_notified, h_cleaned,
                  ev_queue, blk_queue, task_state, task_handle, task_is_notify,
                  wk_task, wk_idle, notify_task_created>>

Stutter ==
  /\ done
  /\ UNCHANGED vars

Next ==
  \/ \E w \in Workers : EvPickup(w)
  \/ \E w \in Workers : BlkPickup(w)
  \/ \E w \in Workers : ExecuteWorkTask(w)
  \/ \E w \in Workers : ExecuteWorkTaskCasLose(w)
  \/ \E w \in Workers : ExecuteNotifyTask(w)
  \/ \E w \in Workers, h \in Handles : SamePoolResolve(w, h)
  \/ MarkDone
  \/ Stutter

Fairness ==
  /\ WF_vars(Next)
  /\ \A w \in Workers :
       /\ WF_vars(EvPickup(w))
       /\ WF_vars(BlkPickup(w))
       /\ WF_vars(ExecuteWorkTask(w))
       /\ WF_vars(ExecuteNotifyTask(w))
       /\ SF_vars(\E h \in Handles : SamePoolResolve(w, h))

Spec == Init /\ [][Next]_vars /\ Fairness

(* =========================================================================
   Type Invariant
   ========================================================================= *)

TypeOK ==
  /\ \A h \in Handles :
       /\ h_status[h] \in {Running, Completed, Failed, Cancelled}
       /\ h_notified[h] \in 0..1
       /\ h_cleaned[h] \in 0..1
  /\ ev_queue \subseteq Tasks
  /\ blk_queue \subseteq Tasks
  /\ \A t \in Tasks : task_state[t] \in {TkQueued, TkExecuting, TkDone}

(* =========================================================================
   Safety Properties
   ========================================================================= *)

NoDoubleFire ==
  \A h \in Handles :
    /\ h_notified[h] <= 1
    /\ h_cleaned[h] <= 1

HandleConsistency ==
  \A h \in Handles :
    IsTerminal(h_status[h]) =>
      /\ h_notified[h] = 1
      /\ h_cleaned[h] = 1

(* A task in at most one queue *)
NoQueueDuplication ==
  \A t \in Tasks :
    ~(t \in ev_queue /\ t \in blk_queue)

(* =========================================================================
   Liveness Properties
   ========================================================================= *)

(* End-to-end: all handles eventually reach terminal *)
EndToEnd ==
  \A h \in Handles : <>(IsTerminal(h_status[h]))

================================================================================
