------------------------- MODULE AsyncHandleBuggy -------------------------
(*
 * BUGGY variant: models the CURRENT system where cancel skips notifications.
 * This should FAIL P2 (NotificationSymmetry) and P3 (ResourceRelease).
 *
 * Differences from AsyncHandle:
 *   - CancelHandle does NOT call notify_parent/notify_done/cleanup
 *   - ProcessCancelTask does NOT call notify_parent/notify_done/cleanup
 *   - is_closed path in complete/fail transitions to CANCELLED without notifications
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  Handles,
  Workers,
  NULL

Pending   == "PENDING"
Running   == "RUNNING"
Completed == "COMPLETED"
Failed    == "FAILED"
Cancelled == "CANCELLED"

Terminal == {Completed, Failed, Cancelled}

VARIABLES
  status,
  parent,
  children,
  notified_parent,
  notified_done,
  cleanups_run,
  on_done_slot,
  cancel_requested,
  comb_type,
  all_completed,
  all_total,
  pending_cancels,
  done

vars == <<status, parent, children, notified_parent, notified_done,
          cleanups_run, on_done_slot, cancel_requested,
          comb_type, all_completed, all_total,
          pending_cancels, done>>

IsTerminal(s) == s \in Terminal

NonTerminalChildren(h) == {c \in children[h] : ~IsTerminal(status[c])}

(* ReachTerminal WITH notifications — used by complete/fail *)
ReachTerminalNotify(h, new_status) ==
  /\ \/ status[h] = Pending
     \/ status[h] = Running
  /\ status' = [status EXCEPT ![h] = new_status]
  /\ notified_parent' = [notified_parent EXCEPT ![h] = @ + 1]
  /\ on_done_slot' = [on_done_slot EXCEPT ![h] = FALSE]
  /\ notified_done' = [notified_done EXCEPT 
       ![h] = IF on_done_slot[h] THEN @ + 1 ELSE @]
  /\ cleanups_run' = [cleanups_run EXCEPT ![h] = @ + 1]

(* ReachTerminal WITHOUT notifications — the BUG: cancel's path *)
ReachTerminalSilent(h, new_status) ==
  /\ \/ status[h] = Pending
     \/ status[h] = Running
  /\ status' = [status EXCEPT ![h] = new_status]
  /\ UNCHANGED <<notified_parent, notified_done, cleanups_run, on_done_slot>>

------------------------------------------------------------------------
(* Actions *)

CompleteLeaf(w, h) ==
  /\ comb_type[h] = "leaf"
  /\ ~IsTerminal(status[h])
  /\ ReachTerminalNotify(h, Completed)
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, pending_cancels, done>>

FailLeaf(w, h) ==
  /\ comb_type[h] = "leaf"
  /\ ~IsTerminal(status[h])
  /\ ReachTerminalNotify(h, Failed)
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, pending_cancels, done>>

(* BUG: Cancel transitions to CANCELLED but skips all notifications *)
CancelHandle(w, h) ==
  /\ ~IsTerminal(status[h])
  /\ ReachTerminalSilent(h, Cancelled)
  /\ cancel_requested' = [cancel_requested EXCEPT ![h] = TRUE]
  /\ pending_cancels' = pending_cancels \union NonTerminalChildren(h)
  /\ UNCHANGED <<parent, children, comb_type, all_completed, all_total, done>>

ProcessCancelTask(w) ==
  /\ pending_cancels # {}
  /\ \E h \in pending_cancels :
       /\ pending_cancels' = (pending_cancels \ {h}) \union
            (IF ~IsTerminal(status[h]) THEN NonTerminalChildren(h) ELSE {})
       /\ IF ~IsTerminal(status[h])
          THEN /\ ReachTerminalSilent(h, Cancelled)
               /\ cancel_requested' = [cancel_requested EXCEPT ![h] = TRUE]
          ELSE UNCHANGED <<status, notified_parent, notified_done,
                            cleanups_run, on_done_slot, cancel_requested>>
  /\ UNCHANGED <<parent, children, comb_type, all_completed, all_total, done>>

------------------------------------------------------------------------
(* Combinators — same as fixed version, they use ReachTerminalNotify *)

AllChildCompleted(w, child) ==
  /\ status[child] = Completed
  /\ parent[child] # NULL
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "all"
        /\ status[p] = Running
        /\ LET new_count == all_completed[p] + 1
           IN /\ all_completed' = [all_completed EXCEPT ![p] = new_count]
              /\ IF new_count = all_total[p]
                 THEN ReachTerminalNotify(p, Completed)
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
        /\ ReachTerminalNotify(p, Failed)
        /\ pending_cancels' = pending_cancels \union
             {c \in children[p] : c # child /\ ~IsTerminal(status[c])}
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, done>>

RaceChildResolved(w, child) ==
  /\ \/ status[child] = Completed
     \/ status[child] = Failed
  /\ parent[child] # NULL
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "race"
        /\ status[p] = Running
        /\ LET new_status == IF status[child] = Completed THEN Completed ELSE Failed
           IN ReachTerminalNotify(p, new_status)
        /\ pending_cancels' = pending_cancels \union
             {c \in children[p] : c # child /\ ~IsTerminal(status[c])}
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, done>>

WithinChildResolved(w, child) ==
  /\ \/ status[child] = Completed
     \/ status[child] = Failed
  /\ parent[child] # NULL
  /\ LET p == parent[child]
     IN /\ comb_type[p] = "within"
        /\ status[p] = Running
        /\ LET new_status == IF status[child] = Completed THEN Completed ELSE Failed
           IN ReachTerminalNotify(p, new_status)
        /\ pending_cancels' = pending_cancels \union
             {c \in children[p] : c # child /\ ~IsTerminal(status[c])}
  /\ UNCHANGED <<parent, children, cancel_requested,
                  comb_type, all_completed, all_total, done>>

------------------------------------------------------------------------

ActivateHandle(w, h) ==
  /\ status[h] = Pending
  /\ status' = [status EXCEPT ![h] = Running]
  /\ UNCHANGED <<parent, children, notified_parent, notified_done,
                  cleanups_run, on_done_slot, cancel_requested,
                  comb_type, all_completed, all_total, pending_cancels, done>>

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
(* Invariants — same as fixed version *)

TypeOK ==
  /\ \A h \in Handles :
       /\ status[h] \in {Pending, Running, Completed, Failed, Cancelled}
       /\ notified_parent[h] \in 0..1
       /\ notified_done[h] \in 0..1
       /\ cleanups_run[h] \in 0..1
       /\ on_done_slot[h] \in {TRUE, FALSE}

NoDoubleFire ==
  \A h \in Handles :
    /\ notified_parent[h] <= 1
    /\ notified_done[h] <= 1
    /\ cleanups_run[h] <= 1

(* This SHOULD FAIL: cancelled handles have no notifications *)
NotificationSymmetry ==
  \A h \in Handles :
    IsTerminal(status[h]) =>
      /\ notified_parent[h] = 1
      /\ cleanups_run[h] = 1

(* This SHOULD FAIL: cancelled handles have no cleanup *)
ResourceRelease ==
  \A h \in Handles :
    IsTerminal(status[h]) => cleanups_run[h] = 1

TerminalCompleteness ==
  \A h \in Handles : <>(IsTerminal(status[h]))

========================================================================
