--------------------------- MODULE GCBarrier ----------------------------------
(*
 * GC Barrier Coordination Protocol for Valkyria Runtime
 *
 * Models the two-phase STW request pattern that prevents the barrier reset
 * race discovered in test_gc_soft_limit_multithread.
 *
 * THE BUG (without PREPARING phase):
 *   Leader: CAS IDLE -> STW_REQUESTED   (immediately visible to workers)
 *           barrier_reset()             (zeroes waiting counter)
 *
 *   Worker: sees STW_REQUESTED
 *           barrier_wait()              (increments waiting to 1)
 *
 *   If the worker enters barrier_wait BETWEEN the CAS and barrier_reset,
 *   the reset zeroes the waiting counter, losing the worker's arrival.
 *   Both threads then wait forever in the barrier.
 *
 * THE FIX (two-phase pattern):
 *   Leader: CAS IDLE -> STW_PREPARING   (workers ignore this phase)
 *           barrier_reset()             (safe - no one can be in the barrier)
 *           store STW_REQUESTED         (now workers enter the barrier)
 *
 * This model verifies:
 *   - BarrierSafety: no arrival is ever lost by a concurrent reset
 *   - Liveness: every STW request eventually reaches the rendezvous
 *   - Deadlock freedom: the system never gets stuck
 *
 * Set UsePreparing = TRUE for the fixed protocol, FALSE for the buggy one.
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  Workers,          \* Set of worker thread IDs (e.g., {"w1", "w2"})
  Leader,           \* The GC initiator thread ID (e.g., "leader")
  UsePreparing      \* TRUE = fixed protocol, FALSE = buggy protocol

ASSUME Leader \notin Workers
ASSUME Workers # {}

Threads == Workers \union {Leader}

(* =========================================================================
   Phase values (mirrors valk_gc_phase_e, relevant subset)
   ========================================================================= *)

PhaseIdle       == "IDLE"
PhasePreparing  == "STW_PREPARING"
PhaseRequested  == "STW_REQUESTED"
PhaseDone       == "DONE"

AllPhases == {PhaseIdle, PhasePreparing, PhaseRequested, PhaseDone}

(* =========================================================================
   Leader sub-steps within request_stw
   ========================================================================= *)

LeaderIdle       == "idle"            \* Not requesting STW
LeaderCasDone    == "cas_done"        \* CAS succeeded, haven't reset barrier yet
LeaderResetDone  == "reset_done"      \* Barrier reset, haven't published REQUESTED yet
LeaderPublished  == "published"       \* Published STW_REQUESTED, about to enter barrier
LeaderInBarrier  == "in_barrier"      \* Entered barrier_wait
LeaderComplete   == "complete"        \* Passed barrier, STW achieved

AllLeaderSteps == {LeaderIdle, LeaderCasDone, LeaderResetDone,
                   LeaderPublished, LeaderInBarrier, LeaderComplete}

(* =========================================================================
   Worker states
   ========================================================================= *)

WorkerRunning    == "running"         \* Executing application code
WorkerSawPhase   == "saw_phase"       \* Read phase != IDLE, about to check which
WorkerInBarrier  == "in_barrier"      \* Entered barrier_wait
WorkerComplete   == "complete"        \* Passed barrier

AllWorkerStates == {WorkerRunning, WorkerSawPhase, WorkerInBarrier, WorkerComplete}

(* =========================================================================
   Variables
   ========================================================================= *)

VARIABLES
  phase,              \* Global GC phase (atomic variable)
  leader_step,        \* Where the leader is in request_stw
  worker_state,       \* worker_state[w]: worker's current state
  worker_read_phase,  \* worker_read_phase[w]: phase value the worker read
  barrier_count,      \* Expected number of threads at barrier
  barrier_waiting,    \* Current number of threads waiting in barrier
  barrier_released,   \* TRUE when barrier has been satisfied and released
  barrier_ever_reset_after_arrive  \* Safety tracking: TRUE if reset happened after someone arrived

vars == <<phase, leader_step, worker_state, worker_read_phase,
          barrier_count, barrier_waiting, barrier_released,
          barrier_ever_reset_after_arrive>>

NumThreads == Cardinality(Workers) + 1

(* =========================================================================
   Init
   ========================================================================= *)

Init ==
  /\ phase = PhaseIdle
  /\ leader_step = LeaderIdle
  /\ worker_state = [w \in Workers |-> WorkerRunning]
  /\ worker_read_phase = [w \in Workers |-> PhaseIdle]
  /\ barrier_count = 0
  /\ barrier_waiting = 0
  /\ barrier_released = FALSE
  /\ barrier_ever_reset_after_arrive = FALSE

(* =========================================================================
   Leader Actions
   ========================================================================= *)

(* Step 1: CAS IDLE -> PREPARING or REQUESTED depending on UsePreparing *)
LeaderCAS ==
  /\ leader_step = LeaderIdle
  /\ phase = PhaseIdle
  /\ leader_step' = LeaderCasDone
  /\ phase' = IF UsePreparing THEN PhasePreparing ELSE PhaseRequested
  /\ UNCHANGED <<worker_state, worker_read_phase, barrier_count,
                  barrier_waiting, barrier_released, barrier_ever_reset_after_arrive>>

(* Step 2: Reset barrier (set count = N, waiting = 0) *)
LeaderBarrierReset ==
  /\ leader_step = LeaderCasDone
  /\ leader_step' = LeaderResetDone
  /\ barrier_count' = NumThreads
  /\ barrier_ever_reset_after_arrive' =
       IF barrier_waiting > 0 THEN TRUE
       ELSE barrier_ever_reset_after_arrive
  /\ barrier_waiting' = 0
  /\ barrier_released' = FALSE
  /\ UNCHANGED <<phase, worker_state, worker_read_phase>>

(* Step 3: Publish STW_REQUESTED (only needed in two-phase; in buggy path,
   phase is already REQUESTED, so this is a no-op structurally, but we
   model it as the point where we enter the barrier) *)
LeaderPublish ==
  /\ leader_step = LeaderResetDone
  /\ leader_step' = LeaderPublished
  /\ phase' = PhaseRequested
  /\ UNCHANGED <<worker_state, worker_read_phase, barrier_count,
                  barrier_waiting, barrier_released, barrier_ever_reset_after_arrive>>

(* Step 4: Leader enters barrier_wait *)
LeaderEnterBarrier ==
  /\ leader_step = LeaderPublished
  /\ leader_step' = LeaderInBarrier
  /\ barrier_waiting' = barrier_waiting + 1
  /\ barrier_released' = IF barrier_waiting + 1 = barrier_count
                          THEN TRUE ELSE barrier_released
  /\ UNCHANGED <<phase, worker_state, worker_read_phase, barrier_count,
                  barrier_ever_reset_after_arrive>>

(* Step 5: Leader leaves barrier after release *)
LeaderExitBarrier ==
  /\ leader_step = LeaderInBarrier
  /\ barrier_released
  /\ leader_step' = LeaderComplete
  /\ phase' = PhaseDone
  /\ UNCHANGED <<worker_state, worker_read_phase, barrier_count,
                  barrier_waiting, barrier_released, barrier_ever_reset_after_arrive>>

(* =========================================================================
   Worker Actions

   Models the VALK_GC_SAFE_POINT macro + safe_point_slow():
     1. Worker reads phase (atomic load)
     2. If phase != IDLE, enter safe_point_slow
     3. safe_point_slow reads phase again and checks for STW_REQUESTED
     4. If STW_REQUESTED, enter barrier_wait
   ========================================================================= *)

(* Worker reads phase != IDLE *)
WorkerReadPhase(w) ==
  /\ worker_state[w] = WorkerRunning
  /\ phase # PhaseIdle
  /\ worker_state' = [worker_state EXCEPT ![w] = WorkerSawPhase]
  /\ worker_read_phase' = [worker_read_phase EXCEPT ![w] = phase]
  /\ UNCHANGED <<phase, leader_step, barrier_count, barrier_waiting,
                  barrier_released, barrier_ever_reset_after_arrive>>

(* Worker enters barrier if it saw STW_REQUESTED.
   If it saw STW_PREPARING, it returns without entering the barrier
   (will re-check on next safe point). *)
WorkerEnterBarrier(w) ==
  /\ worker_state[w] = WorkerSawPhase
  /\ worker_read_phase[w] = PhaseRequested
  /\ worker_state' = [worker_state EXCEPT ![w] = WorkerInBarrier]
  /\ barrier_waiting' = barrier_waiting + 1
  /\ barrier_released' = IF barrier_waiting + 1 = barrier_count
                          THEN TRUE ELSE barrier_released
  /\ UNCHANGED <<phase, leader_step, worker_read_phase, barrier_count,
                  barrier_ever_reset_after_arrive>>

(* Worker saw PREPARING (or other non-REQUESTED phase), returns to running.
   This models the safe_point_slow() fall-through. *)
WorkerIgnorePhase(w) ==
  /\ worker_state[w] = WorkerSawPhase
  /\ worker_read_phase[w] # PhaseRequested
  /\ worker_state' = [worker_state EXCEPT ![w] = WorkerRunning]
  /\ UNCHANGED <<phase, leader_step, worker_read_phase, barrier_count,
                  barrier_waiting, barrier_released, barrier_ever_reset_after_arrive>>

(* Worker leaves barrier after release *)
WorkerExitBarrier(w) ==
  /\ worker_state[w] = WorkerInBarrier
  /\ barrier_released
  /\ worker_state' = [worker_state EXCEPT ![w] = WorkerComplete]
  /\ UNCHANGED <<phase, leader_step, worker_read_phase, barrier_count,
                  barrier_waiting, barrier_released, barrier_ever_reset_after_arrive>>

(* =========================================================================
   Next-State Relation
   ========================================================================= *)

Terminated ==
  /\ leader_step = LeaderComplete
  /\ \A w \in Workers : worker_state[w] = WorkerComplete

Done ==
  /\ Terminated
  /\ UNCHANGED vars

Next ==
  \/ LeaderCAS
  \/ LeaderBarrierReset
  \/ LeaderPublish
  \/ LeaderEnterBarrier
  \/ LeaderExitBarrier
  \/ \E w \in Workers : WorkerReadPhase(w)
  \/ \E w \in Workers : WorkerEnterBarrier(w)
  \/ \E w \in Workers : WorkerIgnorePhase(w)
  \/ \E w \in Workers : WorkerExitBarrier(w)
  \/ Done

Fairness ==
  /\ WF_vars(LeaderCAS)
  /\ WF_vars(LeaderBarrierReset)
  /\ WF_vars(LeaderPublish)
  /\ WF_vars(LeaderEnterBarrier)
  /\ WF_vars(LeaderExitBarrier)
  /\ \A w \in Workers :
       /\ WF_vars(WorkerReadPhase(w))
       /\ WF_vars(WorkerEnterBarrier(w))
       /\ WF_vars(WorkerIgnorePhase(w))
       /\ WF_vars(WorkerExitBarrier(w))

Spec == Init /\ [][Next]_vars /\ Fairness

(* =========================================================================
   Type Invariant
   ========================================================================= *)

TypeOK ==
  /\ phase \in AllPhases
  /\ leader_step \in AllLeaderSteps
  /\ \A w \in Workers : worker_state[w] \in AllWorkerStates
  /\ \A w \in Workers : worker_read_phase[w] \in AllPhases
  /\ barrier_count \in 0..NumThreads
  /\ barrier_waiting \in 0..NumThreads
  /\ barrier_released \in BOOLEAN
  /\ barrier_ever_reset_after_arrive \in BOOLEAN

(* =========================================================================
   Safety Properties
   ========================================================================= *)

(* Core safety: barrier_reset never happens while someone is already waiting.
   This is the exact bug we found — if this is violated, an arrival is lost. *)
BarrierResetSafety ==
  ~barrier_ever_reset_after_arrive

(* No thread is stuck in the barrier with waiting < count after the leader
   has finished the request sequence. This catches the deadlock symptom. *)
NoLostArrivals ==
  (leader_step = LeaderInBarrier /\ \A w \in Workers : worker_state[w] = WorkerInBarrier) =>
    barrier_waiting = NumThreads

(* =========================================================================
   Liveness Properties
   ========================================================================= *)

(* The STW request eventually completes *)
STWLiveness ==
  (leader_step = LeaderCasDone) ~> (leader_step = LeaderComplete)

(* Every worker eventually passes the barrier *)
WorkerLiveness ==
  \A w \in Workers :
    (worker_state[w] = WorkerInBarrier) ~> (worker_state[w] = WorkerComplete)

================================================================================
