---------------------- MODULE AsyncHandleBuggyLeaf -----------------------
(*
 * Simplest buggy scenario: 2 independent leaf handles, 1 worker.
 * Worker can cancel a handle. This should violate NotificationSymmetry
 * because the current code's cancel path skips notifications.
 *)
EXTENDS AsyncHandleBuggy

ASSUME Handles = {"h1", "h2"}

ScenarioInit ==
  /\ status = [h \in Handles |-> Running]
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

ScenarioSpec == ScenarioInit /\ [][Next]_vars /\ Fairness

========================================================================
