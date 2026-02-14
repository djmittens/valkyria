------------------------- MODULE ValkAsyncCrossPool ---------------------------
(*
 * Scenario: Cross-pool aio/race
 *   - Parent "race" handle on pool "ev1"
 *   - Child "c1" on pool "ev1" (same pool as parent)
 *   - Child "c2" on pool "blk1" (different pool — blocking)
 *   - Workers: w1 on ev1, w2 on blk1
 *   - Tests: cross-pool notification, concurrent completion, GC interleaving
 *)
EXTENDS ValkAsync

CrossPoolInit ==
  /\ status = [h \in Handles |-> IF h = "race" THEN Running ELSE Pending]
  /\ parent = ("c1" :> "race" @@ "c2" :> "race" @@ "race" :> NULL)
  /\ children = ("race" :> {"c1", "c2"} @@ "c1" :> {} @@ "c2" :> {})
  /\ comb_type = ("race" :> "race" @@ "c1" :> "leaf" @@ "c2" :> "leaf")
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

CrossPoolSpec == CrossPoolInit /\ [][Next]_vars /\ Fairness

HandlePoolDef == "race" :> "ev1" @@ "c1" :> "ev1" @@ "c2" :> "blk1"
WorkerPoolDef == "w1" :> "ev1" @@ "w2" :> "blk1"

================================================================================
