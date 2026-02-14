-------------------------- MODULE AsyncHandleRace -------------------------
(*
 * Scenario: aio/race combinator with 2 leaf children and 2 workers.
 * Parent h1 is a "race" combinator. Children h2, h3 are leaves.
 * First child to reach terminal wins. Loser gets cancelled.
 *)
EXTENDS AsyncHandle

ASSUME Handles = {"h1", "h2", "h3"}

ScenarioInit ==
  /\ status = [h \in Handles |-> Running]
  /\ parent = [h \in Handles |-> IF h \in {"h2", "h3"} THEN "h1" ELSE NULL]
  /\ children = [h \in Handles |-> 
       IF h = "h1" THEN {"h2", "h3"} ELSE {}]
  /\ notified_parent = [h \in Handles |-> 0]
  /\ notified_done = [h \in Handles |-> 0]
  /\ cleanups_run = [h \in Handles |-> 0]
  /\ on_done_slot = [h \in Handles |-> TRUE]
  /\ cancel_requested = [h \in Handles |-> FALSE]
  /\ comb_type = [h \in Handles |-> 
       IF h = "h1" THEN "race" ELSE "leaf"]
  /\ all_completed = [h \in Handles |-> 0]
  /\ all_total = [h \in Handles |-> 0]
  /\ pending_cancels = {}
  /\ done = FALSE

ScenarioSpec == ScenarioInit /\ [][Next]_vars /\ Fairness

========================================================================
