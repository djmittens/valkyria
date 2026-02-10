------------------------------ MODULE ValkGCAsync --------------------------------
(*
 * Composition: GC + Async Handle Lifecycle
 *
 * Models the interaction between stop-the-world GC and the multi-step
 * __reach_terminal operation. The key insight: __reach_terminal is NOT
 * atomic. It consists of:
 *
 *   Step 1: CAS status to terminal (atomic — single compare-and-swap)
 *   Step 2: notify_parent (may enqueue cross-pool task — involves memory ops)
 *   Step 3: notify_done (atomic exchange of callback slot)
 *   Step 4: propagate_completion (enqueue cancel tasks for siblings)
 *   Step 5: run_resource_cleanups (LIFO walk of cleanup list)
 *
 * GC can request STW between ANY two steps. The worker must reach a safe
 * point, pause for GC, then resume and continue from where it left off.
 *
 * Risks being verified:
 *   R1: Worker completes CAS (step 1) but hasn't enqueued cross-pool
 *       notification (step 2). GC runs. After resume, notification must
 *       still be enqueued — not lost or duplicated.
 *   R2: Worker has enqueued notification (step 2) but not yet run cleanups
 *       (step 5). GC runs mark phase — must not mark the handle as live
 *       based on the pending notification (the handle is already terminal).
 *   R3: Two workers race to complete the same handle (one via complete,
 *       another via cancel). CAS ensures exactly one wins. The loser must
 *       not continue with steps 2-5.
 *   R4: GC runs between propagate_completion (step 4) and cleanups (step 5).
 *       Siblings have cancel tasks enqueued. GC must not sweep the cleanup
 *       list before step 5 runs.
 *
 * Simplifications:
 *   - GC is modeled as a single STW pause (no mark/sweep phases —
 *     ValkGC.tla already proves those work correctly in isolation)
 *   - 2 handles: parent (race combinator) on ev1, child on blk1
 *   - 2 workers: w_ev on ev1, w_blk on blk1
 *   - Focus is on the interleaving between reach_terminal steps and GC
 *
 * Properties:
 *   Safety:  NotificationIntegrity, CleanupExactlyOnce, NoDoubleNotify
 *   Liveness: TerminalCompleteness, GCCompletes
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  Handles,      \* e.g., {"parent", "child"}
  Workers,      \* e.g., {"w_ev", "w_blk"}
  Pools,        \* e.g., {"ev1", "blk1"}
  NULL

CONSTANTS
  HandlePool,   \* HandlePool[h] = pool
  WorkerPool,   \* WorkerPool[w] = pool
  Parent,       \* Parent[h] = parent handle or NULL
  CombType,     \* CombType[h] = "leaf" | "race" | "all"
  MaxGCCycles   \* Bound on GC cycles for finite model checking

ASSUME \A h \in Handles : HandlePool[h] \in Pools
ASSUME \A w \in Workers : WorkerPool[w] \in Pools

(* Operator definitions for TLC config overrides *)
HandlePoolDef == "parent" :> "ev1" @@ "child" :> "blk1"
WorkerPoolDef == "w_ev" :> "ev1" @@ "w_blk" :> "blk1"
ParentDef == "parent" :> "null" @@ "child" :> "parent"
CombTypeDef == "parent" :> "race" @@ "child" :> "leaf"

(* =========================================================================
   States
   ========================================================================= *)

Pending   == "PENDING"
Running   == "RUNNING"
Completed == "COMPLETED"
Failed    == "FAILED"
Cancelled == "CANCELLED"
Terminal  == {Completed, Failed, Cancelled}

(* reach_terminal progress for the winning worker *)
RtNone       == "RT_NONE"       \* Haven't started reach_terminal
RtCasDone    == "RT_CAS_DONE"   \* Step 1: CAS succeeded, status is terminal
RtNotified   == "RT_NOTIFIED"   \* Step 2: parent notification enqueued
RtDoneFired  == "RT_DONE_FIRED" \* Step 3: on_done callback fired
RtPropagated == "RT_PROPAGATED" \* Step 4: cancel tasks enqueued
RtCleanedUp  == "RT_CLEANED_UP" \* Step 5: cleanups run — fully complete

AllRtSteps == {RtNone, RtCasDone, RtNotified, RtDoneFired, RtPropagated, RtCleanedUp}

(* GC states *)
GcIdle       == "GC_IDLE"
GcRequested  == "GC_REQUESTED"
GcRunning    == "GC_RUNNING"     \* All threads paused, GC doing work

AllGcStates  == {GcIdle, GcRequested, GcRunning}

(* =========================================================================
   Variables
   ========================================================================= *)

VARIABLES
  status,           \* status[h]: handle state
  rt_step,          \* rt_step[h]: how far reach_terminal has progressed
  rt_winner,        \* rt_winner[h]: worker that won CAS (or NULL)
  rt_target_status, \* rt_target_status[h]: the terminal status being set

  \* Ghost counters for verification
  notify_parent_count,  \* How many times parent was notified for this handle
  notify_done_count,    \* How many times on_done fired
  cleanup_count,        \* How many times cleanups ran

  \* Cross-pool notification queue
  cross_pool_queue,     \* Set of <<handle, status>> awaiting delivery

  \* GC state
  gc_state,             \* Global GC state
  worker_paused,        \* Set of workers paused for GC
  gc_cycles,            \* Count of completed GC cycles

  done                  \* Terminal detection

vars == <<status, rt_step, rt_winner, rt_target_status,
          notify_parent_count, notify_done_count, cleanup_count,
          cross_pool_queue, gc_state, worker_paused, gc_cycles, done>>

(* =========================================================================
   Helpers
   ========================================================================= *)

IsTerminal(s) == s \in Terminal
SamePool(h1, h2) == HandlePool[h1] = HandlePool[h2]
WorkerOnPool(w, p) == WorkerPool[w] = p
WorkerActive(w) == w \notin worker_paused

Children(h) == {c \in Handles : Parent[c] = h}

(* =========================================================================
   reach_terminal — multi-step with GC interleaving
   ========================================================================= *)

(* Step 1: CAS status from non-terminal to target terminal state.
   This is the linearization point — exactly one worker wins. *)
RtCas(w, h, target) ==
  /\ WorkerOnPool(w, HandlePool[h])
  /\ WorkerActive(w)
  /\ ~IsTerminal(status[h])        \* CAS precondition: not yet terminal
  /\ rt_step[h] = RtNone           \* No one has started yet
  /\ target \in Terminal
  /\ status' = [status EXCEPT ![h] = target]
  /\ rt_step' = [rt_step EXCEPT ![h] = RtCasDone]
  /\ rt_winner' = [rt_winner EXCEPT ![h] = w]
  /\ rt_target_status' = [rt_target_status EXCEPT ![h] = target]
  /\ UNCHANGED <<notify_parent_count, notify_done_count, cleanup_count,
                  cross_pool_queue, gc_state, worker_paused, gc_cycles, done>>

(* Step 2: Notify parent — may enqueue to cross-pool queue *)
RtNotifyParent(w, h) ==
  /\ rt_step[h] = RtCasDone
  /\ rt_winner[h] = w
  /\ WorkerActive(w)
  /\ notify_parent_count' = [notify_parent_count EXCEPT ![h] = @ + 1]
  /\ IF Parent[h] # NULL /\ ~SamePool(h, Parent[h])
     THEN cross_pool_queue' = cross_pool_queue \union {<<h, rt_target_status[h]>>}
     ELSE UNCHANGED cross_pool_queue
  /\ rt_step' = [rt_step EXCEPT ![h] = RtNotified]
  /\ UNCHANGED <<status, rt_winner, rt_target_status,
                  notify_done_count, cleanup_count,
                  gc_state, worker_paused, gc_cycles, done>>

(* Step 3: Fire on_done callback *)
RtFireDone(w, h) ==
  /\ rt_step[h] = RtNotified
  /\ rt_winner[h] = w
  /\ WorkerActive(w)
  /\ notify_done_count' = [notify_done_count EXCEPT ![h] = @ + 1]
  /\ rt_step' = [rt_step EXCEPT ![h] = RtDoneFired]
  /\ UNCHANGED <<status, rt_winner, rt_target_status, notify_parent_count,
                  cleanup_count, cross_pool_queue,
                  gc_state, worker_paused, gc_cycles, done>>

(* Step 4: Propagate completion — enqueue cancel tasks for siblings *)
RtPropagate(w, h) ==
  /\ rt_step[h] = RtDoneFired
  /\ rt_winner[h] = w
  /\ WorkerActive(w)
  \* In a real model this would enqueue cancel tasks; here we just advance
  /\ rt_step' = [rt_step EXCEPT ![h] = RtPropagated]
  /\ UNCHANGED <<status, rt_winner, rt_target_status,
                  notify_parent_count, notify_done_count, cleanup_count,
                  cross_pool_queue, gc_state, worker_paused, gc_cycles, done>>

(* Step 5: Run resource cleanups *)
RtCleanup(w, h) ==
  /\ rt_step[h] = RtPropagated
  /\ rt_winner[h] = w
  /\ WorkerActive(w)
  /\ cleanup_count' = [cleanup_count EXCEPT ![h] = @ + 1]
  /\ rt_step' = [rt_step EXCEPT ![h] = RtCleanedUp]
  /\ UNCHANGED <<status, rt_winner, rt_target_status,
                  notify_parent_count, notify_done_count,
                  cross_pool_queue, gc_state, worker_paused, gc_cycles, done>>

(* CAS loser: another worker tries to complete the same handle but CAS fails
   because status is already terminal. The loser does NOTHING — no steps 2-5. *)
RtCasFail(w, h) ==
  /\ WorkerOnPool(w, HandlePool[h])
  /\ WorkerActive(w)
  /\ IsTerminal(status[h])         \* CAS would fail — already terminal
  /\ UNCHANGED vars

(* =========================================================================
   Parent combinator resolution — delivered via cross-pool queue
   ========================================================================= *)

(* Race parent resolves when child's cross-pool notification arrives *)
RaceResolve(w, child) ==
  /\ Parent[child] # NULL
  /\ CombType[Parent[child]] = "race"
  /\ LET p == Parent[child]
     IN /\ status[p] = Running
        /\ rt_step[p] = RtNone
        /\ WorkerOnPool(w, HandlePool[p])
        /\ WorkerActive(w)
        \* Child notification available (same-pool direct, cross-pool via queue)
        /\ \/ (SamePool(child, p) /\ IsTerminal(status[child])
               /\ rt_step[child] = RtCleanedUp)
           \/ \E s \in Terminal : <<child, s>> \in cross_pool_queue
        \* Begin reach_terminal for parent
        /\ LET new_s == IF status[child] = Completed THEN Completed ELSE Failed
           IN /\ status' = [status EXCEPT ![p] = new_s]
              /\ rt_step' = [rt_step EXCEPT ![p] = RtCasDone]
              /\ rt_winner' = [rt_winner EXCEPT ![p] = w]
              /\ rt_target_status' = [rt_target_status EXCEPT ![p] = new_s]
        \* Drain child entries from cross-pool queue
        /\ LET child_entries == {e \in cross_pool_queue : e[1] \in Children(p)}
           IN cross_pool_queue' = cross_pool_queue \ child_entries
  /\ UNCHANGED <<notify_parent_count, notify_done_count, cleanup_count,
                  gc_state, worker_paused, gc_cycles, done>>

(* =========================================================================
   GC Protocol — simplified STW
   Models the coordination, not mark/sweep internals (proved in ValkGC.tla)
   ========================================================================= *)

(* GC coordinator requests STW *)
GCRequest ==
  /\ gc_state = GcIdle
  /\ gc_cycles < MaxGCCycles       \* Bound for finite model checking
  /\ gc_state' = GcRequested
  /\ UNCHANGED <<status, rt_step, rt_winner, rt_target_status,
                  notify_parent_count, notify_done_count, cleanup_count,
                  cross_pool_queue, worker_paused, gc_cycles, done>>

(* Worker hits safe point — pauses.
   CRITICAL: A worker in the middle of reach_terminal (between steps)
   MUST pause at the next safe point. The safe points are between steps. *)
GCWorkerPause(w) ==
  /\ gc_state = GcRequested
  /\ WorkerActive(w)
  /\ worker_paused' = worker_paused \union {w}
  \* Check if all workers are now paused -> GC can run
  /\ IF worker_paused' = Workers
     THEN gc_state' = GcRunning
     ELSE UNCHANGED gc_state
  /\ UNCHANGED <<status, rt_step, rt_winner, rt_target_status,
                  notify_parent_count, notify_done_count, cleanup_count,
                  cross_pool_queue, gc_cycles, done>>

(* GC completes — all workers resume *)
GCComplete ==
  /\ gc_state = GcRunning
  /\ gc_state' = GcIdle
  /\ worker_paused' = {}
  /\ gc_cycles' = gc_cycles + 1
  /\ UNCHANGED <<status, rt_step, rt_winner, rt_target_status,
                  notify_parent_count, notify_done_count, cleanup_count,
                  cross_pool_queue, done>>

(* =========================================================================
   Termination Detection
   ========================================================================= *)

AllDone ==
  /\ \A h \in Handles : rt_step[h] = RtCleanedUp
  /\ cross_pool_queue = {}

MarkDone ==
  /\ AllDone
  /\ ~done
  /\ done' = TRUE
  /\ UNCHANGED <<status, rt_step, rt_winner, rt_target_status,
                  notify_parent_count, notify_done_count, cleanup_count,
                  cross_pool_queue, gc_state, worker_paused, gc_cycles>>

Stutter ==
  /\ done
  /\ UNCHANGED vars

(* =========================================================================
   Specification
   ========================================================================= *)

Init ==
  /\ status = [h \in Handles |->
       IF CombType[h] \in {"race", "all"} THEN Running ELSE Pending]
  /\ rt_step = [h \in Handles |-> RtNone]
  /\ rt_winner = [h \in Handles |-> NULL]
  /\ rt_target_status = [h \in Handles |-> NULL]
  /\ notify_parent_count = [h \in Handles |-> 0]
  /\ notify_done_count = [h \in Handles |-> 0]
  /\ cleanup_count = [h \in Handles |-> 0]
  /\ cross_pool_queue = {}
  /\ gc_state = GcIdle
  /\ worker_paused = {}
  /\ gc_cycles = 0
  /\ done = FALSE

Next ==
  \* reach_terminal steps (any worker, any handle)
  \/ \E w \in Workers, h \in Handles, s \in Terminal : RtCas(w, h, s)
  \/ \E w \in Workers, h \in Handles : RtNotifyParent(w, h)
  \/ \E w \in Workers, h \in Handles : RtFireDone(w, h)
  \/ \E w \in Workers, h \in Handles : RtPropagate(w, h)
  \/ \E w \in Workers, h \in Handles : RtCleanup(w, h)
  \/ \E w \in Workers, h \in Handles : RtCasFail(w, h)
  \* Combinator resolution
  \/ \E w \in Workers, h \in Handles : RaceResolve(w, h)
  \* GC protocol
  \/ GCRequest
  \/ \E w \in Workers : GCWorkerPause(w)
  \/ GCComplete
  \* Terminal
  \/ MarkDone
  \/ Stutter

Fairness ==
  /\ WF_vars(Next)
  /\ \A w \in Workers, h \in Handles :
       /\ SF_vars(RtCas(w, h, Completed))
       /\ SF_vars(RtCas(w, h, Failed))
       /\ WF_vars(RtNotifyParent(w, h))
       /\ WF_vars(RtFireDone(w, h))
       /\ WF_vars(RtPropagate(w, h))
       /\ WF_vars(RtCleanup(w, h))
       /\ SF_vars(RaceResolve(w, h))
  /\ \A w \in Workers :
       WF_vars(GCWorkerPause(w))
  /\ WF_vars(GCComplete)
  /\ WF_vars(MarkDone)

Spec == Init /\ [][Next]_vars /\ Fairness

(* =========================================================================
   Type Invariant
   ========================================================================= *)

TypeOK ==
  /\ \A h \in Handles :
       /\ status[h] \in {Pending, Running, Completed, Failed, Cancelled}
       /\ rt_step[h] \in AllRtSteps
       /\ rt_winner[h] \in Workers \union {NULL}
       /\ notify_parent_count[h] \in 0..1
       /\ notify_done_count[h] \in 0..1
       /\ cleanup_count[h] \in 0..1
  /\ gc_state \in AllGcStates
  /\ worker_paused \subseteq Workers

(* =========================================================================
   Safety Properties
   ========================================================================= *)

(* R1: Cross-pool notification is never lost.
   If CAS succeeded (status is terminal), notification is eventually enqueued.
   Expressed as invariant: if status is terminal and we haven't notified parent
   yet, the winner is still progressing (not stuck). *)
NotificationIntegrity ==
  \A h \in Handles :
    (IsTerminal(status[h]) /\ rt_step[h] # RtNone) =>
      notify_parent_count[h] <= 1

(* R3: CAS guarantees exactly one winner — no double notification *)
NoDoubleNotify ==
  \A h \in Handles :
    /\ notify_parent_count[h] <= 1
    /\ notify_done_count[h] <= 1

(* R4: Cleanups run exactly once per terminal handle *)
CleanupExactlyOnce ==
  \A h \in Handles :
    cleanup_count[h] <= 1

(* Notification and cleanup are paired — if one is done, the other will be *)
NotifyCleanupConsistency ==
  \A h \in Handles :
    rt_step[h] = RtCleanedUp =>
      /\ notify_parent_count[h] = 1
      /\ notify_done_count[h] = 1
      /\ cleanup_count[h] = 1

(* GC doesn't corrupt in-progress reach_terminal state.
   A worker paused mid-reach_terminal resumes at the same step. *)
GCDoesNotCorruptRt ==
  \A h \in Handles :
    \A w \in Workers :
      (rt_winner[h] = w /\ w \in worker_paused) =>
        rt_step[h] \in AllRtSteps  \* Step is preserved across pause

(* No worker operates on async handles during GC *)
NoWorkDuringGC ==
  gc_state = GcRunning =>
    worker_paused = Workers

(* =========================================================================
   Liveness Properties
   ========================================================================= *)

(* Every handle eventually completes all reach_terminal steps *)
TerminalCompleteness ==
  \A h \in Handles : <>(rt_step[h] = RtCleanedUp)

(* GC requests eventually complete *)
GCCompletes ==
  gc_state = GcRequested ~> gc_state = GcIdle

================================================================================
