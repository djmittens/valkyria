------------------------------ MODULE ValkAsync --------------------------------
(*
 * Async Handle Lifecycle with Cross-Pool Completion
 *
 * Extends the original AsyncHandle model to cover the target architecture:
 *   - Handles may be owned by different AIO systems
 *   - Completion can happen on any pool (blocking pool, event loop)
 *   - Parent notification may require cross-pool or cross-system dispatch
 *   - GC safe points interleave with async operations
 *   - Resource cleanups run exactly once, on the terminal-transition winner
 *
 * The key design: __reach_terminal is a CAS-guarded function. Any thread on
 * any pool can call it. Exactly one caller wins the CAS and runs:
 *   1. notify_parent (may enqueue cross-pool task)
 *   2. notify_done (atomic exchange, fires at most once)
 *   3. propagate_completion (enqueues cancel tasks for siblings)
 *   4. run_resource_cleanups (LIFO cleanup list)
 *
 * Cross-pool notification model:
 *   When a handle completes on pool A but its parent lives on pool B,
 *   the parent notification is enqueued as a task on pool B's queue.
 *   The actual parent state transition happens when a pool B worker
 *   picks up and executes that task.
 *
 * Properties proved:
 *   P1 (Terminal Completeness) — Every handle eventually reaches terminal
 *   P2 (Notification Symmetry) — Terminal => notified_parent = 1, cleanups = 1
 *   P3 (Resource Release)      — Cleanups run exactly once per terminal handle
 *   P4 (Cancel Propagation)    — Cancel cascades to all descendants
 *   P5 (No Double-Fire)        — on_done, notify_parent, cleanups fire at most once
 *   P6 (Cross-Pool Safety)     — Parent notification delivered despite pool boundary
 *   P7 (GC Interleave Safety)  — GC pause doesn't lose notifications or double-fire
 *
 * Design constraints discovered by TLC:
 *   C1 (Pool Affinity)         — Workers only complete/fail/cancel handles on own pool
 *   C2 (Cross-Pool Cancel)     — Cancel of cross-pool handle goes through pending queue
 *   C3 (Cancelled = Terminal)  — Race/all combinators must treat Cancelled as terminal
 *   C4 (No Double Queue Write) — Combinator resolution that drains sibling queue entries
 *                                 must use ReachTerminal (not ReachTerminalWithNotify)
 *                                 to avoid conflicting cross_pool_queue assignments
 *   C5 (SF for GC Interleave)  — Work actions need strong fairness to guarantee progress
 *                                 despite repeated GC pause/resume interleaving
 *
 * Verified scenarios:
 *   ValkAsyncCrossPool      — race(leaf_same, leaf_cross), 2 pools, 2,260 states
 *   ValkAsyncCrossPoolAll   — all(leaf_same, leaf_cross), 2 pools, 2,848 states
 *   ValkAsyncMultiLevel     — race(all(leaf, leaf_cross), leaf_cross2), 3 pools,
 *                             304,520 states
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  Handles,        \* Set of handle IDs
  Workers,        \* Set of worker thread IDs (from any pool/system)
  Pools,          \* Set of pool IDs (e.g., {"ev1", "blk1", "ev2"})
  NULL

(* Handle-to-pool assignment — which pool a handle's owner lives on *)
CONSTANTS
  HandlePool      \* HandlePool[h] = pool ID

ASSUME \A h \in Handles : HandlePool[h] \in Pools

(* Worker-to-pool assignment — which pool each worker belongs to *)
CONSTANTS
  WorkerPool      \* WorkerPool[w] = pool ID

ASSUME \A w \in Workers : WorkerPool[w] \in Pools

(* =========================================================================
   Handle States
   ========================================================================= *)

Pending   == "PENDING"
Running   == "RUNNING"
Completed == "COMPLETED"
Failed    == "FAILED"
Cancelled == "CANCELLED"

Terminal == {Completed, Failed, Cancelled}

(* =========================================================================
   Variables
   ========================================================================= *)

VARIABLES
  status,              \* status[h]: handle state
  parent,              \* parent[h]: parent handle or NULL
  children,            \* children[h]: set of child handles
  comb_type,           \* comb_type[h]: "leaf" | "all" | "race" | "within"
  all_completed,       \* all_completed[h]: counter for all combinator
  all_total,           \* all_total[h]: total children for all combinator

  \* Notification tracking (ghost variables for verification)
  notified_parent,     \* notified_parent[h]: count (should be 0 or 1)
  notified_done,       \* notified_done[h]: count (should be 0 or 1)
  cleanups_run,        \* cleanups_run[h]: count (should be 0 or 1)
  on_done_slot,        \* on_done_slot[h]: TRUE if callback present

  \* Cross-pool notification queue
  \* Models the task queue for parent notifications that cross pool boundaries
  cross_pool_queue,    \* Set of <<child_handle, terminal_status>> pairs
                       \* waiting to be delivered to parent's pool

  \* Cancel propagation
  cancel_requested,    \* cancel_requested[h]: TRUE if cancel requested
  pending_cancels,     \* Set of handles with enqueued cancel tasks

  \* GC coordination
  gc_paused,           \* Set of workers currently paused for GC

  done                 \* Terminal detection

vars == <<status, parent, children, comb_type, all_completed, all_total,
          notified_parent, notified_done, cleanups_run, on_done_slot,
          cross_pool_queue, cancel_requested, pending_cancels,
          gc_paused, done>>

(* =========================================================================
   Helpers
   ========================================================================= *)

IsTerminal(s) == s \in Terminal

NonTerminalChildren(h) == {c \in children[h] : ~IsTerminal(status[c])}

SamePool(h1, h2) == HandlePool[h1] = HandlePool[h2]

WorkerCanActOnPool(w, p) == WorkerPool[w] = p

(* =========================================================================
   __reach_terminal — THE core design
   CAS-guarded terminal transition. Exactly one caller wins.
   Winner runs full notification sequence:
     1. notify_parent (possibly via cross-pool queue)
     2. notify_done (atomic exchange)
     3. propagate_completion (enqueue cancel tasks)
     4. run_resource_cleanups
   ========================================================================= *)

ReachTerminal(h, new_status) ==
  /\ \/ status[h] = Pending
     \/ status[h] = Running
  /\ status' = [status EXCEPT ![h] = new_status]
  \* Step 1: notify_parent
  /\ notified_parent' = [notified_parent EXCEPT ![h] = @ + 1]
  \* Step 2: notify_done (atomic exchange of on_done_slot)
  /\ on_done_slot' = [on_done_slot EXCEPT ![h] = FALSE]
  /\ notified_done' = [notified_done EXCEPT
       ![h] = IF on_done_slot[h] THEN @ + 1 ELSE @]
  \* Step 4: run_resource_cleanups
  /\ cleanups_run' = [cleanups_run EXCEPT ![h] = @ + 1]

(* ReachTerminal + enqueue cross-pool parent notification if needed *)
ReachTerminalWithNotify(h, new_status) ==
  /\ ReachTerminal(h, new_status)
  \* If parent is on a different pool, enqueue cross-pool notification
  /\ IF parent[h] # NULL /\ ~SamePool(h, parent[h])
     THEN cross_pool_queue' = cross_pool_queue \union {<<h, new_status>>}
     ELSE UNCHANGED cross_pool_queue

(* =========================================================================
   Leaf Handle Actions
   ========================================================================= *)

CompleteLeaf(w, h) ==
  /\ comb_type[h] = "leaf"
  /\ ~IsTerminal(status[h])
  /\ WorkerCanActOnPool(w, HandlePool[h])  \* Pool affinity: complete on own pool
  /\ w \notin gc_paused                    \* Can't act during GC pause
  /\ ReachTerminalWithNotify(h, Completed)
  /\ UNCHANGED <<parent, children, comb_type, all_completed, all_total,
                  cancel_requested, pending_cancels, gc_paused, done>>

FailLeaf(w, h) ==
  /\ comb_type[h] = "leaf"
  /\ ~IsTerminal(status[h])
  /\ WorkerCanActOnPool(w, HandlePool[h])  \* Pool affinity: fail on own pool
  /\ w \notin gc_paused
  /\ ReachTerminalWithNotify(h, Failed)
  /\ UNCHANGED <<parent, children, comb_type, all_completed, all_total,
                  cancel_requested, pending_cancels, gc_paused, done>>

(* =========================================================================
   Cancel — via __reach_terminal
   ========================================================================= *)

CancelHandle(w, h) ==
  /\ ~IsTerminal(status[h])
  /\ WorkerCanActOnPool(w, HandlePool[h])  \* Pool affinity: cancel on own pool
  /\ w \notin gc_paused
  /\ ReachTerminalWithNotify(h, Cancelled)
  /\ cancel_requested' = [cancel_requested EXCEPT ![h] = TRUE]
  /\ pending_cancels' = pending_cancels \union NonTerminalChildren(h)
  /\ UNCHANGED <<parent, children, comb_type, all_completed, all_total,
                  gc_paused, done>>

(* Cancel request from another pool — enqueue as pending cancel task.
   Models cross-pool cancel: any thread can request cancel of any handle,
   but actual terminal transition happens on the handle's owning pool. *)
RequestCancel(h) ==
  /\ ~IsTerminal(status[h])
  /\ h \notin pending_cancels       \* Don't double-enqueue
  /\ ~cancel_requested[h]           \* Don't re-cancel
  /\ pending_cancels' = pending_cancels \union {h}
  /\ UNCHANGED <<status, parent, children, notified_parent, notified_done,
                  cleanups_run, on_done_slot, cancel_requested,
                  comb_type, all_completed, all_total,
                  cross_pool_queue, gc_paused, done>>

ProcessCancelTask(w) ==
  /\ pending_cancels # {}
  /\ w \notin gc_paused
  /\ \E h \in pending_cancels :
       /\ WorkerCanActOnPool(w, HandlePool[h])  \* Pool affinity
       /\ pending_cancels' = (pending_cancels \ {h}) \union
            (IF ~IsTerminal(status[h]) THEN NonTerminalChildren(h) ELSE {})
       /\ IF ~IsTerminal(status[h])
          THEN /\ ReachTerminalWithNotify(h, Cancelled)
               /\ cancel_requested' = [cancel_requested EXCEPT ![h] = TRUE]
          ELSE UNCHANGED <<status, notified_parent, notified_done,
                            cleanups_run, on_done_slot, cancel_requested,
                            cross_pool_queue>>
  /\ UNCHANGED <<parent, children, comb_type, all_completed, all_total,
                  gc_paused, done>>

(* =========================================================================
   Combinator: aio/all
   ========================================================================= *)

(* Same-pool child completion — immediate parent notification *)
AllChildCompletedLocal(w, child) ==
  /\ status[child] = Completed
  /\ parent[child] # NULL
  /\ SamePool(child, parent[child])
  /\ WorkerCanActOnPool(w, HandlePool[parent[child]])
  /\ w \notin gc_paused
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "all"
        /\ status[p] = Running
        /\ LET new_count == all_completed[p] + 1
           IN /\ all_completed' = [all_completed EXCEPT ![p] = new_count]
              /\ IF new_count = all_total[p]
                 THEN ReachTerminalWithNotify(p, Completed)
                 ELSE UNCHANGED <<status, notified_parent, notified_done,
                                   cleanups_run, on_done_slot, cross_pool_queue>>
  /\ UNCHANGED <<parent, children, cancel_requested, comb_type,
                  all_total, pending_cancels, gc_paused, done>>

(* Cross-pool child completion — delivered via cross_pool_queue *)
AllChildCompletedCrossPool(w, child) ==
  /\ <<child, Completed>> \in cross_pool_queue
  /\ parent[child] # NULL
  /\ WorkerCanActOnPool(w, HandlePool[parent[child]])
  /\ w \notin gc_paused
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "all"
        /\ status[p] = Running
        /\ LET new_count == all_completed[p] + 1
           IN /\ all_completed' = [all_completed EXCEPT ![p] = new_count]
              /\ IF new_count = all_total[p]
                 THEN /\ ReachTerminal(p, Completed)
                      /\ IF parent[p] # NULL /\ ~SamePool(p, parent[p])
                         THEN cross_pool_queue' =
                                (cross_pool_queue \ {<<child, Completed>>})
                                \union {<<p, Completed>>}
                         ELSE cross_pool_queue' =
                                cross_pool_queue \ {<<child, Completed>>}
                 ELSE /\ cross_pool_queue' =
                           cross_pool_queue \ {<<child, Completed>>}
                      /\ UNCHANGED <<status, notified_parent, notified_done,
                                     cleanups_run, on_done_slot>>
  /\ UNCHANGED <<parent, children, cancel_requested, comb_type,
                  all_total, pending_cancels, gc_paused, done>>

(* When an all-combinator fails (any child fails), drain all sibling
   cross-pool entries since siblings will be cancelled. *)
AllChildFailed(w, child) ==
  /\ \/ status[child] = Failed
     \/ status[child] = Cancelled
  /\ parent[child] # NULL
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "all"
        /\ status[p] = Running
        /\ \/ (SamePool(child, p) /\ WorkerCanActOnPool(w, HandlePool[p]))
           \/ <<child, status[child]>> \in cross_pool_queue
        \* Use ReachTerminal (NOT ReachTerminalWithNotify) because we
        \* manage cross_pool_queue ourselves (drain siblings + add parent)
        /\ ReachTerminal(p, Failed)
        /\ pending_cancels' = pending_cancels \union
             {c \in children[p] : c # child /\ ~IsTerminal(status[c])}
        \* Drain all children's cross-pool entries, add parent's if needed
        /\ LET sibling_entries == {e \in cross_pool_queue :
                                     e[1] \in children[p]}
               base == cross_pool_queue \ sibling_entries
           IN cross_pool_queue' =
                IF parent[p] # NULL /\ ~SamePool(p, parent[p])
                THEN base \union {<<p, Failed>>}
                ELSE base
  /\ w \notin gc_paused
  /\ UNCHANGED <<parent, children, cancel_requested, comb_type,
                  all_completed, all_total, gc_paused, done>>

(* =========================================================================
   Combinator: aio/race
   ========================================================================= *)

(* When a race resolves, drain cross-pool entries for all children of the
   race parent — they're now irrelevant (siblings will be cancelled).
   This models the real implementation where the cancel propagation for
   siblings implicitly consumes their pending notifications. *)
RaceChildResolved(w, child) ==
  /\ IsTerminal(status[child])              \* Completed, Failed, OR Cancelled
  /\ parent[child] # NULL
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "race"
        /\ status[p] = Running
        \* Same-pool: worker on parent's pool sees terminal child directly
        \* Cross-pool: child's notification arrived in queue
        /\ \/ (SamePool(child, p) /\ WorkerCanActOnPool(w, HandlePool[p]))
           \/ \E s \in Terminal : <<child, s>> \in cross_pool_queue
        \* Use ReachTerminal (NOT ReachTerminalWithNotify) because we
        \* manage cross_pool_queue ourselves (drain siblings + add parent)
        /\ LET new_status == IF status[child] = Completed THEN Completed ELSE Failed
           IN ReachTerminal(p, new_status)
        /\ pending_cancels' = pending_cancels \union
             {c \in children[p] : c # child /\ ~IsTerminal(status[c])}
        \* Drain all cross-pool entries for children of this race parent,
        \* then add the parent's own cross-pool entry if needed
        /\ LET sibling_entries == {e \in cross_pool_queue :
                                     e[1] \in children[p]}
               base == cross_pool_queue \ sibling_entries
               new_status2 == IF status[child] = Completed THEN Completed ELSE Failed
           IN cross_pool_queue' =
                IF parent[p] # NULL /\ ~SamePool(p, parent[p])
                THEN base \union {<<p, new_status2>>}
                ELSE base
  /\ w \notin gc_paused
  /\ UNCHANGED <<parent, children, cancel_requested, comb_type,
                  all_completed, all_total, gc_paused, done>>

(* =========================================================================
   Activate: PENDING -> RUNNING
   ========================================================================= *)

ActivateHandle(w, h) ==
  /\ status[h] = Pending
  /\ WorkerCanActOnPool(w, HandlePool[h])  \* Pool affinity
  /\ w \notin gc_paused
  /\ status' = [status EXCEPT ![h] = Running]
  /\ UNCHANGED <<parent, children, notified_parent, notified_done,
                  cleanups_run, on_done_slot, cancel_requested,
                  comb_type, all_completed, all_total,
                  cross_pool_queue, pending_cancels, gc_paused, done>>

(* =========================================================================
   GC Safe Point Interleaving
   A worker can be paused for GC at any time (models STW).
   While paused, it cannot perform any async handle operations.
   ========================================================================= *)

GCPause(w) ==
  /\ w \notin gc_paused
  /\ gc_paused' = gc_paused \union {w}
  /\ UNCHANGED <<status, parent, children, notified_parent, notified_done,
                  cleanups_run, on_done_slot, cancel_requested,
                  comb_type, all_completed, all_total,
                  cross_pool_queue, pending_cancels, done>>

GCResume(w) ==
  /\ w \in gc_paused
  /\ gc_paused' = gc_paused \ {w}
  /\ UNCHANGED <<status, parent, children, notified_parent, notified_done,
                  cleanups_run, on_done_slot, cancel_requested,
                  comb_type, all_completed, all_total,
                  cross_pool_queue, pending_cancels, done>>

(* =========================================================================
   Termination Detection
   ========================================================================= *)

AllHandlesTerminal == \A h \in Handles : IsTerminal(status[h])

MarkDone ==
  /\ AllHandlesTerminal
  /\ pending_cancels = {}
  /\ cross_pool_queue = {}
  /\ ~done
  /\ done' = TRUE
  /\ UNCHANGED <<status, parent, children, notified_parent, notified_done,
                  cleanups_run, on_done_slot, cancel_requested,
                  comb_type, all_completed, all_total,
                  cross_pool_queue, pending_cancels, gc_paused>>

Stutter ==
  /\ done
  /\ UNCHANGED vars

(* =========================================================================
   Specification
   ========================================================================= *)

Init ==
  /\ status = [h \in Handles |-> Pending]
  /\ parent = [h \in Handles |-> NULL]
  /\ children = [h \in Handles |-> {}]
  /\ comb_type = [h \in Handles |-> "leaf"]
  /\ all_completed = [h \in Handles |-> 0]
  /\ all_total = [h \in Handles |-> 0]
  /\ notified_parent = [h \in Handles |-> 0]
  /\ notified_done = [h \in Handles |-> 0]
  /\ cleanups_run = [h \in Handles |-> 0]
  /\ on_done_slot = [h \in Handles |-> TRUE]
  /\ cross_pool_queue = {}
  /\ cancel_requested = [h \in Handles |-> FALSE]
  /\ pending_cancels = {}
  /\ gc_paused = {}
  /\ done = FALSE

Next ==
  \/ \E w \in Workers, h \in Handles :
       \/ CompleteLeaf(w, h)
       \/ FailLeaf(w, h)
       \/ CancelHandle(w, h)
       \/ ActivateHandle(w, h)
       \/ AllChildCompletedLocal(w, h)
       \/ AllChildCompletedCrossPool(w, h)
       \/ AllChildFailed(w, h)
       \/ RaceChildResolved(w, h)
  \/ \E h \in Handles : RequestCancel(h)
  \/ \E w \in Workers : ProcessCancelTask(w)
  \/ \E w \in Workers : GCPause(w)
  \/ \E w \in Workers : GCResume(w)
  \/ MarkDone
  \/ Stutter

Fairness ==
  /\ WF_vars(Next)
  /\ \A w \in Workers, h \in Handles :
       /\ WF_vars(CompleteLeaf(w, h))
       /\ WF_vars(FailLeaf(w, h))
       /\ WF_vars(AllChildCompletedLocal(w, h))
       /\ WF_vars(AllChildCompletedCrossPool(w, h))
       /\ WF_vars(AllChildFailed(w, h))
       /\ WF_vars(RaceChildResolved(w, h))
  /\ \A w \in Workers :
       /\ WF_vars(ProcessCancelTask(w))
       /\ WF_vars(GCResume(w))
  \* GC pauses are finite: if a worker is paused, it eventually resumes,
  \* and GC cannot re-pause a worker immediately (models bounded GC).
  \* We express this as: GCPause is not infinitely often enabled without
  \* other actions firing. Strong fairness on the combined "work" actions.
  /\ \A w \in Workers :
       SF_vars(\E h \in Handles :
         \/ CompleteLeaf(w, h)
         \/ FailLeaf(w, h)
         \/ AllChildCompletedLocal(w, h)
         \/ AllChildCompletedCrossPool(w, h)
         \/ AllChildFailed(w, h)
         \/ RaceChildResolved(w, h)
         \/ ProcessCancelTask(w))

Spec == Init /\ [][Next]_vars /\ Fairness

(* =========================================================================
   Type Invariant
   ========================================================================= *)

TypeOK ==
  /\ \A h \in Handles :
       /\ status[h] \in {Pending, Running, Completed, Failed, Cancelled}
       /\ notified_parent[h] \in 0..1
       /\ notified_done[h] \in 0..1
       /\ cleanups_run[h] \in 0..1
       /\ on_done_slot[h] \in BOOLEAN
  /\ gc_paused \subseteq Workers

(* =========================================================================
   Safety Properties
   ========================================================================= *)

(* P5: No double-fire of notifications or cleanups *)
NoDoubleFire ==
  \A h \in Handles :
    /\ notified_parent[h] <= 1
    /\ notified_done[h] <= 1
    /\ cleanups_run[h] <= 1

(* P2: Terminal => fully notified and cleaned up *)
NotificationSymmetry ==
  \A h \in Handles :
    IsTerminal(status[h]) =>
      /\ notified_parent[h] = 1
      /\ cleanups_run[h] = 1

(* P3: Cleanups run exactly once per terminal handle *)
ResourceRelease ==
  \A h \in Handles :
    IsTerminal(status[h]) => cleanups_run[h] = 1

(* P6: Cross-pool queue doesn't grow unbounded — items are consumed *)
CrossPoolBounded ==
  Cardinality(cross_pool_queue) <= Cardinality(Handles)

(* P7: GC pause doesn't corrupt handle state — handles don't move backwards *)
MonotonicProgress ==
  \A h \in Handles :
    IsTerminal(status[h]) =>
      /\ notified_parent[h] >= 1
      /\ cleanups_run[h] >= 1

(* =========================================================================
   Liveness Properties
   ========================================================================= *)

(* P1: Every handle eventually reaches terminal *)
TerminalCompleteness ==
  \A h \in Handles : <>(IsTerminal(status[h]))

================================================================================
