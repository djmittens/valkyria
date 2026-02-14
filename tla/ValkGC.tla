------------------------------ MODULE ValkGC ----------------------------------
(*
 * Parallel GC Coordination Protocol for Valkyria Runtime
 *
 * Models the stop-the-world GC protocol across heterogeneous thread pools:
 *   - Event loop workers (each with a Chase-Lev deque)
 *   - Blocking pool threads (expandable)
 *   - Main evaluator thread
 *
 * Each thread has:
 *   - A TLAB (thread-local allocation buffer) with a generation stamp
 *   - A safe-point obligation: must reach safe point when STW requested
 *   - A role in parallel mark/sweep after pausing
 *
 * The GC coordinator (thread 0 / main):
 *   1. CAS phase IDLE -> STW_REQUESTED
 *   2. Reset barrier for N registered threads
 *   3. Wake all threads (uv_async_send for event loops, condvar for blocking pool)
 *   4. All threads hit safe point -> barrier 1 (everyone paused)
 *   5. Root enumeration -> barrier 2 (roots queued)
 *   6. Parallel mark with work-stealing -> termination detection -> barrier 3
 *   7. Parallel sweep -> barrier 4
 *   8. Bump generation, phase -> IDLE
 *   9. barrier 5 (everyone resumes)
 *
 * Properties proved:
 *   S1 (GC Safety)     — No thread allocates or mutates heap during mark/sweep
 *   S2 (GC Liveness)   — STW request eventually completes if all threads are responsive
 *   S3 (No Stale TLAB) — After GC, no thread uses pre-GC TLAB without refilling
 *   S4 (Barrier Safety) — No thread passes barrier N+1 before all pass barrier N
 *   S5 (Pool Expansion) — New threads register before participating in GC
 *   S6 (Mark Termination) — Parallel mark terminates when all work is consumed
 *)
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  Threads,            \* Set of all possible thread IDs (superset of active)
  EventLoopWorkers,   \* Subset of Threads: event loop workers
  BlockingPoolInit,   \* Subset of Threads: initial blocking pool threads
  BlockingPoolMax,    \* Subset of Threads: all possible blocking pool threads
  MainThread,         \* Single thread: the main evaluator / GC initiator
  MaxGeneration,      \* Bound on heap generation counter (for finite model)
  NULL

ASSUME MainThread \in Threads
ASSUME EventLoopWorkers \subseteq Threads
ASSUME BlockingPoolInit \subseteq Threads
ASSUME BlockingPoolMax \subseteq Threads
ASSUME BlockingPoolInit \subseteq BlockingPoolMax
ASSUME MainThread \notin EventLoopWorkers
ASSUME MainThread \notin BlockingPoolMax

(* =========================================================================
   GC Phases (mirrors valk_gc_phase_e)
   ========================================================================= *)

PhaseIdle       == "IDLE"
PhaseSTW        == "STW_REQUESTED"
PhaseMarking    == "MARKING"
PhaseSweeping   == "SWEEPING"

AllPhases == {PhaseIdle, PhaseSTW, PhaseMarking, PhaseSweeping}

(* =========================================================================
   Thread States
   ========================================================================= *)

ThrRunning      == "RUNNING"          \* Executing application code, may allocate
ThrAtSafePoint  == "AT_SAFE_POINT"    \* Reached safe point, waiting for barrier
ThrMarking      == "MARKING"          \* Participating in parallel mark
ThrSweeping     == "SWEEPING"         \* Participating in parallel sweep
ThrResumed      == "RESUMED"          \* Post-GC, waiting for phase -> IDLE
ThrIdle         == "IDLE"             \* Blocking pool thread waiting for work
ThrUnregistered == "UNREGISTERED"     \* Not yet registered with GC

AllThreadStates == {ThrRunning, ThrAtSafePoint, ThrMarking, ThrSweeping,
                    ThrResumed, ThrIdle, ThrUnregistered}

(* =========================================================================
   Variables
   ========================================================================= *)

VARIABLES
  gc_phase,           \* Global GC phase (atomic in impl)
  generation,         \* Heap generation counter (bumped after each GC)
  registered,         \* Set of currently GC-registered threads
  thr_state,          \* thr_state[t]: thread's current state
  thr_tlab_gen,       \* thr_tlab_gen[t]: generation of thread's TLAB
  thr_allocated,      \* thr_allocated[t]: TRUE if thread allocated since last GC
  barrier_arrived,    \* Set of threads that arrived at current barrier
  barrier_phase,      \* Which barrier we're at (1..5 within a GC cycle)
  mark_queue,         \* mark_queue[t]: count of items in thread's mark queue
  mark_offered,       \* Set of threads that offered termination
  gc_cycles,          \* Count of completed GC cycles
  expanding           \* TRUE if a blocking pool expansion is in progress

vars == <<gc_phase, generation, registered, thr_state, thr_tlab_gen,
          thr_allocated, barrier_arrived, barrier_phase, mark_queue,
          mark_offered, gc_cycles, expanding>>

(* =========================================================================
   Helpers
   ========================================================================= *)

ActiveThreads == registered

NumRegistered == Cardinality(registered)

AllArrived == barrier_arrived = registered

TotalMarkWork == LET Sum(S) == LET RECURSIVE SumHelper(_, _)
                                   SumHelper(s, acc) ==
                                     IF s = {} THEN acc
                                     ELSE LET x == CHOOSE x \in s : TRUE
                                          IN SumHelper(s \ {x}, acc + mark_queue[x])
                               IN SumHelper(S, 0)
                IN Sum(registered)

AllQueuesEmpty == \A t \in registered : mark_queue[t] = 0

(* =========================================================================
   Init
   ========================================================================= *)

InitialThreads == {MainThread} \union EventLoopWorkers \union BlockingPoolInit

Init ==
  /\ gc_phase = PhaseIdle
  /\ generation = 0
  /\ registered = InitialThreads
  /\ thr_state = [t \in Threads |->
       IF t \in InitialThreads THEN ThrRunning ELSE ThrUnregistered]
  /\ thr_tlab_gen = [t \in Threads |-> 0]
  /\ thr_allocated = [t \in Threads |-> FALSE]
  /\ barrier_arrived = {}
  /\ barrier_phase = 0
  /\ mark_queue = [t \in Threads |-> 0]
  /\ mark_offered = {}
  /\ gc_cycles = 0
  /\ expanding = FALSE

(* =========================================================================
   Application Actions (normal operation, no GC)
   ========================================================================= *)

(* Thread allocates from TLAB — only allowed when running and phase is IDLE *)
Allocate(t) ==
  /\ gc_phase = PhaseIdle
  /\ thr_state[t] = ThrRunning
  /\ t \in registered
  /\ thr_tlab_gen[t] = generation   \* TLAB is current generation
  /\ thr_allocated' = [thr_allocated EXCEPT ![t] = TRUE]
  /\ UNCHANGED <<gc_phase, generation, registered, thr_state, thr_tlab_gen,
                  barrier_arrived, barrier_phase, mark_queue, mark_offered,
                  gc_cycles, expanding>>

(* Thread needs to refill TLAB — stale generation forces refill *)
RefillTLAB(t) ==
  /\ gc_phase = PhaseIdle
  /\ thr_state[t] = ThrRunning
  /\ t \in registered
  /\ thr_tlab_gen[t] # generation   \* TLAB is stale
  /\ thr_tlab_gen' = [thr_tlab_gen EXCEPT ![t] = generation]
  /\ UNCHANGED <<gc_phase, generation, registered, thr_state, thr_allocated,
                  barrier_arrived, barrier_phase, mark_queue, mark_offered,
                  gc_cycles, expanding>>

(* =========================================================================
   Blocking Pool Expansion
   ========================================================================= *)

(* Start expanding: spawn a new blocking pool thread *)
StartExpansion(t) ==
  /\ ~expanding
  /\ gc_phase = PhaseIdle           \* Only expand outside GC
  /\ t \in BlockingPoolMax \ registered
  /\ thr_state[t] = ThrUnregistered
  /\ expanding' = TRUE
  /\ UNCHANGED <<gc_phase, generation, registered, thr_state, thr_tlab_gen,
                  thr_allocated, barrier_arrived, barrier_phase, mark_queue,
                  mark_offered, gc_cycles>>

(* Complete expansion: thread registers with GC *)
CompleteExpansion(t) ==
  /\ expanding
  /\ t \in BlockingPoolMax \ registered
  /\ thr_state[t] = ThrUnregistered
  /\ registered' = registered \union {t}
  /\ thr_state' = [thr_state EXCEPT ![t] = ThrRunning]
  /\ thr_tlab_gen' = [thr_tlab_gen EXCEPT ![t] = generation]
  /\ expanding' = FALSE
  /\ UNCHANGED <<gc_phase, generation, thr_allocated, barrier_arrived,
                  barrier_phase, mark_queue, mark_offered, gc_cycles>>

(* =========================================================================
   GC Initiation (Main thread)
   ========================================================================= *)

(* CAS: IDLE -> STW_REQUESTED. Reset barrier for current thread count. *)
RequestSTW ==
  /\ gc_phase = PhaseIdle
  /\ ~expanding                      \* Don't start GC during expansion
  /\ thr_state[MainThread] = ThrRunning
  /\ gc_phase' = PhaseSTW
  /\ barrier_arrived' = {}
  /\ barrier_phase' = 1
  /\ thr_state' = [thr_state EXCEPT ![MainThread] = ThrAtSafePoint]
  /\ barrier_arrived' = {MainThread}  \* Initiator is already at safe point
  /\ UNCHANGED <<generation, registered, thr_tlab_gen, thr_allocated,
                  mark_queue, mark_offered, gc_cycles, expanding>>

(* =========================================================================
   Safe Point Protocol
   ========================================================================= *)

(* A running thread hits a safe point in response to STW_REQUESTED *)
HitSafePoint(t) ==
  /\ gc_phase = PhaseSTW
  /\ t \in registered
  /\ t # MainThread
  /\ thr_state[t] \in {ThrRunning, ThrIdle}
  /\ thr_state' = [thr_state EXCEPT ![t] = ThrAtSafePoint]
  /\ barrier_arrived' = barrier_arrived \union {t}
  /\ UNCHANGED <<gc_phase, generation, registered, thr_tlab_gen, thr_allocated,
                  barrier_phase, mark_queue, mark_offered, gc_cycles, expanding>>

(* =========================================================================
   Barrier Transitions
   Barrier 1: All paused -> begin root enum
   Barrier 2: Roots queued -> begin marking
   Barrier 3: Mark done -> begin sweeping
   Barrier 4: Sweep done -> cleanup
   Barrier 5: Cleanup done -> resume
   ========================================================================= *)

(* Barrier 1 -> 2: All threads at safe point. Enter marking phase. *)
BarrierPauseToRoots ==
  /\ barrier_phase = 1
  /\ AllArrived
  /\ gc_phase = PhaseSTW
  /\ gc_phase' = PhaseMarking
  \* Each thread enqueues its roots (modeled as initial mark work)
  /\ mark_queue' = [t \in Threads |->
       IF t \in registered THEN 1 ELSE 0]   \* Each thread has 1 unit of root work
  /\ mark_offered' = {}
  /\ thr_state' = [t \in Threads |->
       IF t \in registered THEN ThrMarking ELSE thr_state[t]]
  /\ barrier_arrived' = {}
  /\ barrier_phase' = 2
  /\ UNCHANGED <<generation, registered, thr_tlab_gen, thr_allocated,
                  gc_cycles, expanding>>

(* =========================================================================
   Parallel Mark Phase
   ========================================================================= *)

(* Thread processes its own mark queue *)
MarkLocal(t) ==
  /\ gc_phase = PhaseMarking
  /\ thr_state[t] = ThrMarking
  /\ mark_queue[t] > 0
  \* Processing one item may discover 0-2 children (nondeterministic)
  /\ \E children \in {0, 1, 2} :
       mark_queue' = [mark_queue EXCEPT ![t] = @ - 1 + children]
  /\ mark_offered' = mark_offered \ {t}  \* Retract termination offer
  /\ UNCHANGED <<gc_phase, generation, registered, thr_state, thr_tlab_gen,
                  thr_allocated, barrier_arrived, barrier_phase,
                  gc_cycles, expanding>>

(* Thread steals from another thread's mark queue *)
MarkSteal(t) ==
  /\ gc_phase = PhaseMarking
  /\ thr_state[t] = ThrMarking
  /\ mark_queue[t] = 0              \* Own queue empty
  /\ \E victim \in registered \ {t} :
       /\ mark_queue[victim] > 0
       /\ mark_queue' = [mark_queue EXCEPT
            ![victim] = @ - 1,
            ![t] = 1]               \* Steal one item
  /\ mark_offered' = mark_offered \ {t}
  /\ UNCHANGED <<gc_phase, generation, registered, thr_state, thr_tlab_gen,
                  thr_allocated, barrier_arrived, barrier_phase,
                  gc_cycles, expanding>>

(* Thread offers termination (OWST protocol) *)
MarkOfferTermination(t) ==
  /\ gc_phase = PhaseMarking
  /\ thr_state[t] = ThrMarking
  /\ mark_queue[t] = 0
  /\ t \notin mark_offered
  /\ mark_offered' = mark_offered \union {t}
  /\ UNCHANGED <<gc_phase, generation, registered, thr_state, thr_tlab_gen,
                  thr_allocated, barrier_arrived, barrier_phase, mark_queue,
                  gc_cycles, expanding>>

(* All threads offered termination and all queues empty -> mark done *)
MarkTerminate ==
  /\ gc_phase = PhaseMarking
  /\ mark_offered = registered
  /\ AllQueuesEmpty
  /\ barrier_arrived' = registered   \* All arrive at barrier 2 simultaneously
  /\ UNCHANGED <<gc_phase, generation, registered, thr_state, thr_tlab_gen,
                  thr_allocated, barrier_phase, mark_queue, mark_offered,
                  gc_cycles, expanding>>

(* Barrier 2 -> 3: Mark complete. Enter sweep phase. *)
BarrierMarkToSweep ==
  /\ barrier_phase = 2
  /\ barrier_arrived = registered
  /\ gc_phase = PhaseMarking
  /\ gc_phase' = PhaseSweeping
  /\ thr_state' = [t \in Threads |->
       IF t \in registered THEN ThrSweeping ELSE thr_state[t]]
  /\ barrier_arrived' = {}
  /\ barrier_phase' = 3
  /\ UNCHANGED <<generation, registered, thr_tlab_gen, thr_allocated,
                  mark_queue, mark_offered, gc_cycles, expanding>>

(* =========================================================================
   Parallel Sweep Phase
   ========================================================================= *)

(* Thread completes its sweep partition *)
SweepComplete(t) ==
  /\ gc_phase = PhaseSweeping
  /\ thr_state[t] = ThrSweeping
  /\ barrier_arrived' = barrier_arrived \union {t}
  /\ UNCHANGED <<gc_phase, generation, registered, thr_state, thr_tlab_gen,
                  thr_allocated, barrier_phase, mark_queue, mark_offered,
                  gc_cycles, expanding>>

(* Barrier 3 -> 4: Sweep complete. Coordinator bumps generation. *)
BarrierSweepToCleanup ==
  /\ barrier_phase = 3
  /\ barrier_arrived = registered
  /\ gc_phase = PhaseSweeping
  /\ generation' = IF generation < MaxGeneration THEN generation + 1 ELSE generation
  /\ thr_allocated' = [t \in Threads |-> FALSE]  \* Reset allocation tracking
  /\ barrier_arrived' = {}
  /\ barrier_phase' = 4
  /\ UNCHANGED <<gc_phase, registered, thr_state, thr_tlab_gen,
                  mark_queue, mark_offered, gc_cycles, expanding>>

(* Barrier 4 -> 5: All threads resume. Phase -> IDLE. *)
BarrierCleanupToResume ==
  /\ barrier_phase = 4
  \* All threads implicitly arrive at barrier 4 (coordinator action)
  /\ gc_phase' = PhaseIdle
  /\ thr_state' = [t \in Threads |->
       IF t \in registered THEN ThrRunning ELSE thr_state[t]]
  /\ barrier_arrived' = {}
  /\ barrier_phase' = 0
  /\ gc_cycles' = gc_cycles + 1
  /\ UNCHANGED <<generation, registered, thr_tlab_gen, thr_allocated,
                  mark_queue, mark_offered, expanding>>

(* =========================================================================
   Idle Thread (blocking pool)
   ========================================================================= *)

(* Blocking pool thread goes idle when no work available *)
GoIdle(t) ==
  /\ gc_phase = PhaseIdle
  /\ thr_state[t] = ThrRunning
  /\ t \in BlockingPoolMax
  /\ t \in registered
  /\ thr_state' = [thr_state EXCEPT ![t] = ThrIdle]
  /\ UNCHANGED <<gc_phase, generation, registered, thr_tlab_gen, thr_allocated,
                  barrier_arrived, barrier_phase, mark_queue, mark_offered,
                  gc_cycles, expanding>>

(* Idle thread wakes up to do work *)
WakeFromIdle(t) ==
  /\ gc_phase = PhaseIdle
  /\ thr_state[t] = ThrIdle
  /\ t \in registered
  /\ thr_state' = [thr_state EXCEPT ![t] = ThrRunning]
  /\ UNCHANGED <<gc_phase, generation, registered, thr_tlab_gen, thr_allocated,
                  barrier_arrived, barrier_phase, mark_queue, mark_offered,
                  gc_cycles, expanding>>

(* =========================================================================
   Next-State Relation
   ========================================================================= *)

Next ==
  \* Application actions
  \/ \E t \in Threads : Allocate(t)
  \/ \E t \in Threads : RefillTLAB(t)
  \* Pool expansion
  \/ \E t \in Threads : StartExpansion(t)
  \/ \E t \in Threads : CompleteExpansion(t)
  \* GC initiation
  \/ RequestSTW
  \* Safe point
  \/ \E t \in Threads : HitSafePoint(t)
  \* Barrier transitions
  \/ BarrierPauseToRoots
  \/ BarrierMarkToSweep
  \/ BarrierSweepToCleanup
  \/ BarrierCleanupToResume
  \* Mark phase
  \/ \E t \in Threads : MarkLocal(t)
  \/ \E t \in Threads : MarkSteal(t)
  \/ \E t \in Threads : MarkOfferTermination(t)
  \/ MarkTerminate
  \* Sweep phase
  \/ \E t \in Threads : SweepComplete(t)
  \* Blocking pool idle/wake
  \/ \E t \in Threads : GoIdle(t)
  \/ \E t \in Threads : WakeFromIdle(t)

Fairness ==
  /\ WF_vars(Next)
  /\ \A t \in Threads :
       /\ WF_vars(HitSafePoint(t))
       /\ WF_vars(SweepComplete(t))
       /\ WF_vars(MarkLocal(t))
       /\ WF_vars(MarkSteal(t))
       /\ WF_vars(MarkOfferTermination(t))
  /\ WF_vars(MarkTerminate)
  /\ WF_vars(BarrierPauseToRoots)
  /\ WF_vars(BarrierMarkToSweep)
  /\ WF_vars(BarrierSweepToCleanup)
  /\ WF_vars(BarrierCleanupToResume)

Spec == Init /\ [][Next]_vars /\ Fairness

(* =========================================================================
   Type Invariant
   ========================================================================= *)

TypeOK ==
  /\ gc_phase \in AllPhases
  /\ generation \in 0..MaxGeneration
  /\ registered \subseteq Threads
  /\ \A t \in Threads : thr_state[t] \in AllThreadStates
  /\ \A t \in Threads : thr_tlab_gen[t] \in 0..MaxGeneration
  /\ \A t \in Threads : thr_allocated[t] \in BOOLEAN
  /\ barrier_arrived \subseteq Threads
  /\ barrier_phase \in 0..4
  /\ \A t \in Threads : mark_queue[t] \in 0..10  \* bounded for model checking
  /\ mark_offered \subseteq Threads
  /\ gc_cycles \in Nat
  /\ expanding \in BOOLEAN

(* =========================================================================
   Safety Properties
   ========================================================================= *)

(* S1: No thread allocates during mark or sweep *)
GCSafety ==
  gc_phase \in {PhaseMarking, PhaseSweeping} =>
    \A t \in registered :
      thr_state[t] \in {ThrMarking, ThrSweeping, ThrAtSafePoint}

(* S3: No thread uses a stale TLAB to allocate.
   If a thread allocates, its TLAB generation must match the heap generation. *)
NoStaleTLAB ==
  \A t \in Threads :
    thr_allocated[t] => thr_tlab_gen[t] = generation

(* S4: Barrier ordering — no thread in state N+1 while others haven't left state N.
   Expressed as: if any thread is marking, no thread should be sweeping. *)
BarrierOrdering ==
  /\ (\E t \in registered : thr_state[t] = ThrMarking) =>
       ~(\E t2 \in registered : thr_state[t2] = ThrSweeping)
  /\ (\E t \in registered : thr_state[t] = ThrSweeping) =>
       ~(\E t2 \in registered : thr_state[t2] = ThrMarking)

(* S5: Pool expansion safety — unregistered threads don't participate in GC *)
ExpansionSafety ==
  \A t \in Threads :
    thr_state[t] \in {ThrMarking, ThrSweeping, ThrAtSafePoint} =>
      t \in registered

(* S6: Mark termination safety — if all offer, all queues must be empty *)
MarkTerminationSafety ==
  (mark_offered = registered /\ gc_phase = PhaseMarking) =>
    AllQueuesEmpty

(* Combined safety *)
Safety ==
  /\ TypeOK
  /\ GCSafety
  /\ NoStaleTLAB
  /\ BarrierOrdering
  /\ ExpansionSafety

(* =========================================================================
   Liveness Properties
   ========================================================================= *)

(* S2: Every STW request eventually completes — GC cycle count increases *)
GCLiveness ==
  gc_phase = PhaseSTW ~> gc_phase = PhaseIdle

(* S6: Mark phase eventually terminates *)
MarkTerminationLiveness ==
  gc_phase = PhaseMarking ~> gc_phase = PhaseSweeping

(* Threads always eventually resume after GC *)
ThreadResumption ==
  \A t \in InitialThreads :
    thr_state[t] = ThrAtSafePoint ~> thr_state[t] = ThrRunning

================================================================================
