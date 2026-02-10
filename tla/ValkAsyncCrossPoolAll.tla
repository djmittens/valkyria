------------------------ MODULE ValkAsyncCrossPoolAll -------------------------
(*
 * Scenario: Cross-pool aio/all
 *   - Parent "all_p" handle on pool "ev1" (all combinator, 2 children)
 *   - Child "c1" on pool "ev1" (same pool as parent)
 *   - Child "c2" on pool "blk1" (different pool — blocking)
 *   - Workers: w1 on ev1, w2 on blk1
 *   - Tests:
 *     - Both children complete → all completes via cross-pool notification
 *     - One child fails → all fails + cancel propagation across pools
 *     - GC interleaving doesn't lose notifications
 *)
EXTENDS ValkAsync

CrossPoolAllInit ==
  /\ status = [h \in Handles |-> IF h = "all_p" THEN Running ELSE Pending]
  /\ parent = ("c1" :> "all_p" @@ "c2" :> "all_p" @@ "all_p" :> NULL)
  /\ children = ("all_p" :> {"c1", "c2"} @@ "c1" :> {} @@ "c2" :> {})
  /\ comb_type = ("all_p" :> "all" @@ "c1" :> "leaf" @@ "c2" :> "leaf")
  /\ all_completed = [h \in Handles |-> 0]
  /\ all_total = ("all_p" :> 2 @@ "c1" :> 0 @@ "c2" :> 0)
  /\ notified_parent = [h \in Handles |-> 0]
  /\ notified_done = [h \in Handles |-> 0]
  /\ cleanups_run = [h \in Handles |-> 0]
  /\ on_done_slot = [h \in Handles |-> TRUE]
  /\ cross_pool_queue = {}
  /\ cancel_requested = [h \in Handles |-> FALSE]
  /\ pending_cancels = {}
  /\ gc_paused = {}
  /\ done = FALSE

CrossPoolAllSpec == CrossPoolAllInit /\ [][Next]_vars /\ Fairness

HandlePoolDef == "all_p" :> "ev1" @@ "c1" :> "ev1" @@ "c2" :> "blk1"
WorkerPoolDef == "w1" :> "ev1" @@ "w2" :> "blk1"

================================================================================
