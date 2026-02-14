------------------------- MODULE ValkAsyncMultiLevel --------------------------
(*
 * Scenario: Multi-level cross-pool tree
 *
 *   race (ev1)
 *   ├── all_p (ev1)
 *   │   ├── leaf1 (ev1)   — same pool as all_p
 *   │   └── leaf2 (blk1)  — cross-pool
 *   └── leaf3 (blk2)      — cross-pool from race
 *
 *   Workers: w1 on ev1, w2 on blk1, w3 on blk2
 *
 *   Tests:
 *   - leaf3 completes first → race resolves, cancel propagates to all_p
 *     → all_p cancels → cancel propagates to leaf1 (same pool) and leaf2
 *       (cross-pool to blk1)
 *   - leaf1+leaf2 complete → all_p completes → race resolves (same pool)
 *     → cancel propagates to leaf3 (cross-pool to blk2)
 *   - leaf2 fails → all_p fails → race fails (same pool)
 *   - Cross-pool notifications bubble up two levels
 *   - GC interleaving at any point
 *)
EXTENDS ValkAsync

MultiLevelInit ==
  /\ status = ("race" :> Running @@ "all_p" :> Running
               @@ "leaf1" :> Pending @@ "leaf2" :> Pending @@ "leaf3" :> Pending)
  /\ parent = ("race" :> NULL @@ "all_p" :> "race"
               @@ "leaf1" :> "all_p" @@ "leaf2" :> "all_p" @@ "leaf3" :> "race")
  /\ children = ("race" :> {"all_p", "leaf3"} @@ "all_p" :> {"leaf1", "leaf2"}
                 @@ "leaf1" :> {} @@ "leaf2" :> {} @@ "leaf3" :> {})
  /\ comb_type = ("race" :> "race" @@ "all_p" :> "all"
                  @@ "leaf1" :> "leaf" @@ "leaf2" :> "leaf" @@ "leaf3" :> "leaf")
  /\ all_completed = [h \in Handles |-> 0]
  /\ all_total = ("race" :> 0 @@ "all_p" :> 2
                  @@ "leaf1" :> 0 @@ "leaf2" :> 0 @@ "leaf3" :> 0)
  /\ notified_parent = [h \in Handles |-> 0]
  /\ notified_done = [h \in Handles |-> 0]
  /\ cleanups_run = [h \in Handles |-> 0]
  /\ on_done_slot = [h \in Handles |-> TRUE]
  /\ cross_pool_queue = {}
  /\ cancel_requested = [h \in Handles |-> FALSE]
  /\ pending_cancels = {}
  /\ gc_paused = {}
  /\ done = FALSE

MultiLevelSpec == MultiLevelInit /\ [][Next]_vars /\ Fairness

HandlePoolDef == "race" :> "ev1" @@ "all_p" :> "ev1"
                 @@ "leaf1" :> "ev1" @@ "leaf2" :> "blk1" @@ "leaf3" :> "blk2"
WorkerPoolDef == "w1" :> "ev1" @@ "w2" :> "blk1" @@ "w3" :> "blk2"

================================================================================
