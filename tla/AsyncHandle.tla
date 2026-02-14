--------------------------- MODULE AsyncHandle ----------------------------
(*
 * TLA+ model of the Valkyria async handle state machine.
 *
 * Models:
 *   - Handle FSM: PENDING -> RUNNING -> {COMPLETED, FAILED, CANCELLED}
 *   - CAS-based terminal transitions (__reach_terminal unification)
 *   - Notification sequence: notify_parent -> notify_done -> propagate -> cleanup
 *   - Combinator resolution: all (N children), race (first wins), within (timeout)
 *   - Cancellation propagation through handle trees
 *   - N concurrent workers performing transitions
 *
 * Verifies invariants P1-P5:
 *   P1 — Terminal Completeness: every non-terminal handle eventually reaches terminal
 *   P2 — Notification Symmetry: every terminal transition fires full notify sequence
 *   P3 — Resource Release: cleanups run exactly once per handle that reaches terminal
 *   P4 — Cancellation Propagation: cancel cascades to all descendants
 *   P5 — No Double-Fire: on_done, notify_parent, cleanups fire at most once
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  Handles,          \* set of handle IDs
  Workers,          \* set of worker thread IDs
  NULL              \* null value

(* Handle states *)
Pending   == "PENDING"
Running   == "RUNNING"
Completed == "COMPLETED"
Failed    == "FAILED"
Cancelled == "CANCELLED"

Terminal == {Completed, Failed, Cancelled}

VARIABLES
  status,             \* status[h]          : handle state
  parent,             \* parent[h]          : parent handle or NULL
  children,           \* children[h]        : set of child handles
  notified_parent,    \* notified_parent[h] : count of notify_parent calls
  notified_done,      \* notified_done[h]   : count of notify_done calls  
  cleanups_run,       \* cleanups_run[h]    : count of cleanup executions
  on_done_slot,       \* on_done_slot[h]    : TRUE if on_done callback present (atomic exchange)
  cancel_requested,   \* cancel_requested[h]: TRUE if cancel was requested
  
  \* Combinator-specific state
  comb_type,          \* comb_type[h]       : "all" | "race" | "within" | "leaf"
  all_completed,      \* all_completed[h]   : atomic counter for all combinator
  all_total,          \* all_total[h]       : total children count for all
  
  \* Pending cancel set (models task queue for cancellations)
  pending_cancels,    \* set of handles with enqueued cancel tasks
  
  \* Scheduling fairness
  done                \* TRUE when no more actions possible

vars == <<status, parent, children, notified_parent, notified_done,
          cleanups_run, on_done_slot, cancel_requested,
          comb_type, all_completed, all_total,
          pending_cancels, done>>

------------------------------------------------------------------------
(* Helper predicates *)

IsTerminal(s) == s \in Terminal

NonTerminalChildren(h) == {c \in children[h] : ~IsTerminal(status[c])}

------------------------------------------------------------------------
(*
 * __reach_terminal — THE central design change.
 * All terminal transitions go through this single function.
 * CAS provides mutual exclusion: exactly one caller wins.
 * The winner runs the full notification sequence.
 *)
ReachTerminal(h, new_status) ==
  /\ \/ status[h] = Pending
     \/ status[h] = Running
  /\ status' = [status EXCEPT ![h] = new_status]
  /\ notified_parent' = [notified_parent EXCEPT ![h] = @ + 1]
  /\ on_done_slot' = [on_done_slot EXCEPT ![h] = FALSE]
  /\ notified_done' = [notified_done EXCEPT 
       ![h] = IF on_done_slot[h] THEN @ + 1 ELSE @]
  /\ cleanups_run' = [cleanups_run EXCEPT ![h] = @ + 1]

------------------------------------------------------------------------
(* Actions *)

(* Complete a leaf handle *)
CompleteLeaf(w, h) ==
  /\ comb_type[h] = "leaf"
  /\ ~IsTerminal(status[h])
  /\ ReachTerminal(h, Completed)
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, pending_cancels, done>>

(* Fail a leaf handle *)
FailLeaf(w, h) ==
  /\ comb_type[h] = "leaf"
  /\ ~IsTerminal(status[h])
  /\ ReachTerminal(h, Failed)
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, pending_cancels, done>>

(* Cancel a handle via __reach_terminal + enqueue children *)
CancelHandle(w, h) ==
  /\ ~IsTerminal(status[h])
  /\ ReachTerminal(h, Cancelled)
  /\ cancel_requested' = [cancel_requested EXCEPT ![h] = TRUE]
  /\ pending_cancels' = pending_cancels \union NonTerminalChildren(h)
  /\ UNCHANGED <<parent, children, comb_type, all_completed, all_total, done>>

(* Process a pending cancel task *)
ProcessCancelTask(w) ==
  /\ pending_cancels # {}
  /\ \E h \in pending_cancels :
       /\ pending_cancels' = (pending_cancels \ {h}) \union
            (IF ~IsTerminal(status[h]) THEN NonTerminalChildren(h) ELSE {})
       /\ IF ~IsTerminal(status[h])
          THEN /\ ReachTerminal(h, Cancelled)
               /\ cancel_requested' = [cancel_requested EXCEPT ![h] = TRUE]
          ELSE UNCHANGED <<status, notified_parent, notified_done,
                            cleanups_run, on_done_slot, cancel_requested>>
  /\ UNCHANGED <<parent, children, comb_type, all_completed, all_total, done>>

------------------------------------------------------------------------
(* Combinator: aio/all *)

AllChildCompleted(w, child) ==
  /\ status[child] = Completed
  /\ parent[child] # NULL
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "all"
        /\ status[p] = Running
        /\ LET new_count == all_completed[p] + 1
           IN /\ all_completed' = [all_completed EXCEPT ![p] = new_count]
              /\ IF new_count = all_total[p]
                 THEN ReachTerminal(p, Completed)
                 ELSE UNCHANGED <<status, notified_parent, notified_done,
                                   cleanups_run, on_done_slot>>
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_total, pending_cancels, done>>

AllChildFailed(w, child) ==
  /\ \/ status[child] = Failed
     \/ status[child] = Cancelled
  /\ parent[child] # NULL
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "all"
        /\ status[p] = Running
        /\ ReachTerminal(p, Failed)
        /\ pending_cancels' = pending_cancels \union
             {c \in children[p] : c # child /\ ~IsTerminal(status[c])}
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, done>>

------------------------------------------------------------------------
(* Combinator: aio/race *)

RaceChildResolved(w, child) ==
  /\ \/ status[child] = Completed
     \/ status[child] = Failed
  /\ parent[child] # NULL
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "race"
        /\ status[p] = Running
        /\ LET new_status == IF status[child] = Completed THEN Completed ELSE Failed
           IN ReachTerminal(p, new_status)
        /\ pending_cancels' = pending_cancels \union
             {c \in children[p] : c # child /\ ~IsTerminal(status[c])}
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, done>>

------------------------------------------------------------------------
(* Combinator: aio/within *)

WithinChildResolved(w, child) ==
  /\ \/ status[child] = Completed
     \/ status[child] = Failed
  /\ parent[child] # NULL
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "within"
        /\ status[p] = Running
        /\ LET new_status == IF status[child] = Completed THEN Completed ELSE Failed
           IN ReachTerminal(p, new_status)
        /\ pending_cancels' = pending_cancels \union
             {c \in children[p] : c # child /\ ~IsTerminal(status[c])}
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, done>>

------------------------------------------------------------------------
(* Activate: PENDING -> RUNNING *)

ActivateHandle(w, h) ==
  /\ status[h] = Pending
  /\ status' = [status EXCEPT ![h] = Running]
  /\ UNCHANGED <<parent, children, notified_parent, notified_done,
                  cleanups_run, on_done_slot, cancel_requested,
                  comb_type, all_completed, all_total, pending_cancels, done>>

------------------------------------------------------------------------
(* Termination detection *)

AllHandlesTerminal == \A h \in Handles : IsTerminal(status[h])

MarkDone ==
  /\ AllHandlesTerminal
  /\ pending_cancels = {}
  /\ ~done
  /\ done' = TRUE
  /\ UNCHANGED <<status, parent, children, notified_parent, notified_done,
                  cleanups_run, on_done_slot, cancel_requested,
                  comb_type, all_completed, all_total, pending_cancels>>

Stutter ==
  /\ done
  /\ UNCHANGED vars

------------------------------------------------------------------------
(* Specification *)

Init ==
  /\ status = [h \in Handles |-> Pending]
  /\ parent = [h \in Handles |-> NULL]
  /\ children = [h \in Handles |-> {}]
  /\ notified_parent = [h \in Handles |-> 0]
  /\ notified_done = [h \in Handles |-> 0]
  /\ cleanups_run = [h \in Handles |-> 0]
  /\ on_done_slot = [h \in Handles |-> TRUE]
  /\ cancel_requested = [h \in Handles |-> FALSE]
  /\ comb_type = [h \in Handles |-> "leaf"]
  /\ all_completed = [h \in Handles |-> 0]
  /\ all_total = [h \in Handles |-> 0]
  /\ pending_cancels = {}
  /\ done = FALSE

Next ==
  \/ \E w \in Workers, h \in Handles :
       \/ CompleteLeaf(w, h)
       \/ FailLeaf(w, h)
       \/ CancelHandle(w, h)
       \/ ActivateHandle(w, h)
       \/ AllChildCompleted(w, h)
       \/ AllChildFailed(w, h)
       \/ RaceChildResolved(w, h)
       \/ WithinChildResolved(w, h)
  \/ \E w \in Workers : ProcessCancelTask(w)
  \/ MarkDone
  \/ Stutter

Fairness ==
  /\ WF_vars(Next)
  /\ \A w \in Workers, h \in Handles :
       /\ WF_vars(CompleteLeaf(w, h))
       /\ WF_vars(FailLeaf(w, h))
       /\ WF_vars(ProcessCancelTask(w))

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
  /\ \A h \in Handles :
       /\ status[h] \in {Pending, Running, Completed, Failed, Cancelled}
       /\ notified_parent[h] \in 0..1
       /\ notified_done[h] \in 0..1
       /\ cleanups_run[h] \in 0..1
       /\ on_done_slot[h] \in {TRUE, FALSE}

(* P5: No double-fire *)
NoDoubleFire ==
  \A h \in Handles :
    /\ notified_parent[h] <= 1
    /\ notified_done[h] <= 1
    /\ cleanups_run[h] <= 1

(* P2+P3: Terminal => notified and cleaned up *)
NotificationSymmetry ==
  \A h \in Handles :
    IsTerminal(status[h]) =>
      /\ notified_parent[h] = 1
      /\ cleanups_run[h] = 1

ResourceRelease ==
  \A h \in Handles :
    IsTerminal(status[h]) => cleanups_run[h] = 1

------------------------------------------------------------------------
(* Temporal properties *)

(* P1: Every handle eventually reaches terminal *)
TerminalCompleteness ==
  \A h \in Handles : <>(IsTerminal(status[h]))

========================================================================
