----------------------- MODULE AsyncHandleCancelTree ----------------------
(*
 * Scenario: Cancel propagation through a 3-level tree.
 * h1 (race) -> h2 (all) -> {h4, h5}
 *           -> h3 (leaf)
 * 
 * If h3 wins the race, h2 gets cancelled, which must cascade to h4, h5.
 * Tests P4 (cancellation propagation) deeply.
 *)
EXTENDS AsyncHandle

ASSUME Handles = {"h1", "h2", "h3", "h4", "h5"}

ScenarioInit ==
  /\ status = [h \in Handles |-> Running]
  /\ parent = [h \in Handles |->
       CASE h = "h2" -> "h1"
         [] h = "h3" -> "h1"
         [] h = "h4" -> "h2"
         [] h = "h5" -> "h2"
         [] OTHER    -> NULL]
  /\ children = [h \in Handles |->
       CASE h = "h1" -> {"h2", "h3"}
         [] h = "h2" -> {"h4", "h5"}
         [] OTHER    -> {}]
  /\ notified_parent = [h \in Handles |-> 0]
  /\ notified_done = [h \in Handles |-> 0]
  /\ cleanups_run = [h \in Handles |-> 0]
  /\ on_done_slot = [h \in Handles |-> TRUE]
  /\ cancel_requested = [h \in Handles |-> FALSE]
  /\ comb_type = [h \in Handles |->
       CASE h = "h1" -> "race"
         [] h = "h2" -> "all"
         [] OTHER    -> "leaf"]
  /\ all_completed = [h \in Handles |-> 0]
  /\ all_total = [h \in Handles |-> IF h = "h2" THEN 2 ELSE 0]
  /\ pending_cancels = {}
  /\ done = FALSE

ScenarioSpec == ScenarioInit /\ [][Next]_vars /\ Fairness

========================================================================
