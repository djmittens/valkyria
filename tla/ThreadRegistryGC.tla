--------------------------- MODULE ThreadRegistryGC ----------------------------
(*
 * Thread Registration/Deregistration vs GC Stop-The-World
 *
 * BUGS FOUND BY TLC:
 *
 * Bug 1 (Index Collision): fetch_add/fetch_sub for index allocation allows
 *   two threads to get the same index after unregister+re-register.
 *   Fix: mutex-protected free list for index recycling.
 *
 * Bug 2 (Barrier Deadlock): A thread can pass SAFE_POINT() when phase=IDLE,
 *   then the leader starts GC before the thread finishes unregistering.
 *   The barrier expects N threads but only N-1 participate.
 *   Fix: Use the same mutex for threadCount changes and GC barrier setup.
 *   This ensures atomicity between "how many threads?" and "set up barrier."
 *
 * THE FIXED PROTOCOL:
 *
 *   Register:
 *     lock(thread_mutex)
 *     idx = pop free_list or fresh
 *     threadCount++
 *     threads[idx].active = true
 *     unlock(thread_mutex)
 *
 *   Unregister:
 *     loop:
 *       SAFE_POINT()              -- participate in GC if active
 *       lock(thread_mutex)        -- blocks if leader is setting up GC
 *       if phase != IDLE:         -- GC started while we were waiting for lock
 *         unlock(thread_mutex)
 *         continue loop           -- re-enter safe point
 *       threads[idx].active = false
 *       threadCount--
 *       push idx to free_list
 *       unlock(thread_mutex)
 *       break
 *
 *   Request STW (leader):
 *     lock(thread_mutex)          -- prevents concurrent unregister
 *     n = threadCount             -- guaranteed accurate while locked
 *     CAS phase IDLE -> PREPARING
 *     barrier_reset(n)
 *     phase = STW_REQUESTED
 *     unlock(thread_mutex)        -- now unregister can proceed but sees REQUESTED
 *     wake_threads()
 *     barrier_wait()
 *
 * MODELING THE BARRIER:
 *
 *   The real code uses 5 barrier_wait() calls per GC cycle. The final barrier
 *   synchronizes all threads before any can proceed to the next cycle. We model
 *   this as: leader can only move from InGC to Complete when all workers have
 *   entered InBarrier (first barrier), and workers can only exit InBarrier
 *   after the leader finishes GC (moves to Complete). This correctly captures
 *   the synchronization property without modeling all 5 barriers.
 *)
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  MainThread,
  Workers,
  MaxIdx

ASSUME MainThread \notin Workers
ASSUME Workers # {}
ASSUME MaxIdx >= Cardinality(Workers) + 1

AllThreads == Workers \union {MainThread}

PhaseIdle       == "IDLE"
PhasePreparing  == "PREPARING"
PhaseRequested  == "STW_REQUESTED"

AllPhases == {PhaseIdle, PhasePreparing, PhaseRequested}

(* Worker states *)
Unregistered     == "unregistered"
Registered       == "registered"
SafePointing     == "safe_pointing"
WaitForIdle      == "wait_for_idle"
UnregLocking     == "unreg_locking"
UnregLocked      == "unreg_locked"     \* Holds mutex, checking phase
InBarrier        == "in_barrier"
ExitingGC        == "exiting_gc"       \* Worker acknowledged GC complete

AllWorkerStates == {Unregistered, Registered, SafePointing, WaitForIdle,
                    UnregLocking, UnregLocked, InBarrier, ExitingGC}

(* Leader states *)
LeaderIdle         == "idle"
LeaderLocked       == "locked"
LeaderResetDone    == "reset_done"
LeaderPublished    == "published"
LeaderInBarrier    == "in_barrier"
LeaderInGC         == "in_gc"
LeaderComplete     == "complete"

AllLeaderStates == {LeaderIdle, LeaderLocked, LeaderResetDone,
                    LeaderPublished, LeaderInBarrier, LeaderInGC, LeaderComplete}

VARIABLES
  phase,
  threadCount,
  threadIdx,
  threadActive,
  freeList,
  nextFreshIdx,
  workerState,
  leaderState,
  barrierCount,
  barrierWaiting,
  barrierReleased,
  mutexHolder

vars == <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
          workerState, leaderState,
          barrierCount, barrierWaiting, barrierReleased, mutexHolder>>

(* =========================================================================
   Init
   ========================================================================= *)

Init ==
  /\ phase = PhaseIdle
  /\ threadCount = 1
  /\ threadIdx = [t \in AllThreads |-> IF t = MainThread THEN 0 ELSE -1]
  /\ threadActive = [i \in 0..MaxIdx |-> IF i = 0 THEN TRUE ELSE FALSE]
  /\ freeList = <<>>
  /\ nextFreshIdx = 1
  /\ workerState = [w \in Workers |-> Unregistered]
  /\ leaderState = LeaderIdle
  /\ barrierCount = 0
  /\ barrierWaiting = 0
  /\ barrierReleased = FALSE
  /\ mutexHolder = "none"

(* =========================================================================
   Worker: Register (atomic under mutex)
   ========================================================================= *)

WorkerRegister(w) ==
  /\ workerState[w] = Unregistered
  /\ mutexHolder = "none"
  /\ phase = PhaseIdle
  /\ IF freeList # <<>>
     THEN /\ threadIdx' = [threadIdx EXCEPT ![w] = Head(freeList)]
          /\ freeList' = Tail(freeList)
          /\ UNCHANGED nextFreshIdx
     ELSE /\ nextFreshIdx < MaxIdx
          /\ threadIdx' = [threadIdx EXCEPT ![w] = nextFreshIdx]
          /\ nextFreshIdx' = nextFreshIdx + 1
          /\ UNCHANGED freeList
  /\ threadCount' = threadCount + 1
  /\ threadActive' = [threadActive EXCEPT ![threadIdx'[w]] = TRUE]
  /\ workerState' = [workerState EXCEPT ![w] = Registered]
  /\ UNCHANGED <<phase, leaderState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* =========================================================================
   Worker: Unregister
   ========================================================================= *)

WorkerBeginUnregister(w) ==
  /\ workerState[w] = Registered
  /\ workerState' = [workerState EXCEPT ![w] = SafePointing]
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* Safe point: sees REQUESTED -> enter barrier *)
WorkerSafePointJoinGC(w) ==
  /\ workerState[w] \in {SafePointing, WaitForIdle}
  /\ phase = PhaseRequested
  /\ workerState' = [workerState EXCEPT ![w] = InBarrier]
  /\ barrierWaiting' = barrierWaiting + 1
  /\ barrierReleased' = IF barrierWaiting + 1 = barrierCount
                         THEN TRUE ELSE barrierReleased
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, mutexHolder>>

(* Safe point: sees PREPARING -> wait *)
WorkerSafePointWait(w) ==
  /\ workerState[w] = SafePointing
  /\ phase = PhasePreparing
  /\ workerState' = [workerState EXCEPT ![w] = WaitForIdle]
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* Wait resolved: phase back to IDLE *)
WorkerWaitResolved(w) ==
  /\ workerState[w] = WaitForIdle
  /\ phase = PhaseIdle
  /\ workerState' = [workerState EXCEPT ![w] = SafePointing]
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* Safe point: IDLE -> try acquire mutex *)
WorkerSafePointClear(w) ==
  /\ workerState[w] = SafePointing
  /\ phase = PhaseIdle
  /\ workerState' = [workerState EXCEPT ![w] = UnregLocking]
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* Acquire mutex *)
WorkerAcquireMutex(w) ==
  /\ workerState[w] = UnregLocking
  /\ mutexHolder = "none"
  /\ mutexHolder' = w
  /\ workerState' = [workerState EXCEPT ![w] = UnregLocked]
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, barrierWaiting,
                  barrierReleased>>

(* Under mutex, re-check phase. IDLE -> proceed with deactivation *)
WorkerUnregComplete(w) ==
  /\ workerState[w] = UnregLocked
  /\ mutexHolder = w
  /\ phase = PhaseIdle
  /\ LET idx == threadIdx[w]
     IN  /\ threadActive' = [threadActive EXCEPT ![idx] = FALSE]
         /\ freeList' = Append(freeList, idx)
         /\ threadCount' = threadCount - 1
         /\ threadIdx' = [threadIdx EXCEPT ![w] = -1]
  /\ workerState' = [workerState EXCEPT ![w] = Unregistered]
  /\ mutexHolder' = "none"
  /\ UNCHANGED <<phase, nextFreshIdx, leaderState, barrierCount,
                  barrierWaiting, barrierReleased>>

(* Under mutex, phase is not IDLE -> release mutex and re-enter safe point *)
WorkerUnregAbort(w) ==
  /\ workerState[w] = UnregLocked
  /\ mutexHolder = w
  /\ phase # PhaseIdle
  /\ mutexHolder' = "none"
  /\ workerState' = [workerState EXCEPT ![w] = SafePointing]
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, barrierWaiting,
                  barrierReleased>>

(* Waiting for mutex but GC is requested -> join directly *)
WorkerMutexWaitGC(w) ==
  /\ workerState[w] = UnregLocking
  /\ phase = PhaseRequested
  /\ mutexHolder # w    \* Don't have mutex
  /\ workerState' = [workerState EXCEPT ![w] = InBarrier]
  /\ barrierWaiting' = barrierWaiting + 1
  /\ barrierReleased' = IF barrierWaiting + 1 = barrierCount
                         THEN TRUE ELSE barrierReleased
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, mutexHolder>>

(* =========================================================================
   Worker: GC from normal registered state
   ========================================================================= *)

WorkerSafePointGC(w) ==
  /\ workerState[w] = Registered
  /\ phase = PhaseRequested
  /\ workerState' = [workerState EXCEPT ![w] = InBarrier]
  /\ barrierWaiting' = barrierWaiting + 1
  /\ barrierReleased' = IF barrierWaiting + 1 = barrierCount
                         THEN TRUE ELSE barrierReleased
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, mutexHolder>>

(* Worker sees GC is done (leader in Complete state, phase IDLE).
   Models the final barrier_wait synchronization in the real code:
   all threads must pass through the final barrier together before
   any can proceed. *)
WorkerExitGC(w) ==
  /\ workerState[w] = InBarrier
  /\ leaderState = LeaderComplete
  /\ workerState' = [workerState EXCEPT ![w] = ExitingGC]
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* Worker fully exits GC, back to registered.
   This can only happen after phase is IDLE (leader has reset). *)
WorkerCompleteGC(w) ==
  /\ workerState[w] = ExitingGC
  /\ phase = PhaseIdle
  /\ workerState' = [workerState EXCEPT ![w] = Registered]
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  leaderState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* =========================================================================
   Leader: GC Request
   ========================================================================= *)

(* Leader can only start new GC when all workers have exited previous cycle.
   This models the final barrier synchronization. *)
LeaderStartGC ==
  /\ leaderState = LeaderIdle
  /\ phase = PhaseIdle
  /\ mutexHolder = "none"
  /\ \A w \in Workers :
       workerState[w] \notin {InBarrier, ExitingGC}
  /\ mutexHolder' = MainThread
  /\ leaderState' = LeaderLocked
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  workerState, barrierCount, barrierWaiting,
                  barrierReleased>>

(* Under mutex: read count, CAS to PREPARING, reset barrier *)
LeaderSetupGC ==
  /\ leaderState = LeaderLocked
  /\ mutexHolder = MainThread
  /\ phase = PhaseIdle
  /\ phase' = PhasePreparing
  /\ barrierCount' = threadCount
  /\ barrierWaiting' = 0
  /\ barrierReleased' = FALSE
  /\ leaderState' = LeaderResetDone
  /\ UNCHANGED <<threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  workerState, mutexHolder>>

(* Publish STW_REQUESTED, release mutex *)
LeaderPublishAndUnlock ==
  /\ leaderState = LeaderResetDone
  /\ mutexHolder = MainThread
  /\ phase' = PhaseRequested
  /\ mutexHolder' = "none"
  /\ leaderState' = LeaderPublished
  /\ UNCHANGED <<threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  workerState, barrierCount, barrierWaiting,
                  barrierReleased>>

(* Leader enters barrier *)
LeaderEnterBarrier ==
  /\ leaderState = LeaderPublished
  /\ leaderState' = LeaderInBarrier
  /\ barrierWaiting' = barrierWaiting + 1
  /\ barrierReleased' = IF barrierWaiting + 1 = barrierCount
                         THEN TRUE ELSE barrierReleased
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  workerState, barrierCount, mutexHolder>>

(* Leader exits barrier, does GC *)
LeaderExitBarrier ==
  /\ leaderState = LeaderInBarrier
  /\ barrierReleased
  /\ leaderState' = LeaderInGC
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  workerState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* Leader finishes GC, marks complete *)
LeaderFinishGC ==
  /\ leaderState = LeaderInGC
  /\ leaderState' = LeaderComplete
  /\ UNCHANGED <<phase, threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  workerState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* Leader resets phase to IDLE after all workers have acknowledged GC completion.
   In real code: the final barrier_wait ensures all threads exit together,
   then the leader sets phase=IDLE. *)
LeaderReset ==
  /\ leaderState = LeaderComplete
  /\ \A w \in Workers :
       workerState[w] \in {InBarrier, ExitingGC} => workerState[w] = ExitingGC
  /\ phase' = PhaseIdle
  /\ leaderState' = LeaderIdle
  /\ UNCHANGED <<threadCount, threadIdx, threadActive, freeList, nextFreshIdx,
                  workerState, barrierCount, barrierWaiting,
                  barrierReleased, mutexHolder>>

(* =========================================================================
   Next-State Relation
   ========================================================================= *)

Next ==
  \/ LeaderStartGC
  \/ LeaderSetupGC
  \/ LeaderPublishAndUnlock
  \/ LeaderEnterBarrier
  \/ LeaderExitBarrier
  \/ LeaderFinishGC
  \/ LeaderReset
  \/ \E w \in Workers :
       \/ WorkerRegister(w)
       \/ WorkerBeginUnregister(w)
       \/ WorkerSafePointJoinGC(w)
       \/ WorkerSafePointWait(w)
       \/ WorkerWaitResolved(w)
       \/ WorkerSafePointClear(w)
       \/ WorkerAcquireMutex(w)
       \/ WorkerUnregComplete(w)
       \/ WorkerUnregAbort(w)
       \/ WorkerMutexWaitGC(w)
       \/ WorkerSafePointGC(w)
       \/ WorkerExitGC(w)
       \/ WorkerCompleteGC(w)

Fairness ==
  /\ WF_vars(LeaderStartGC)
  /\ WF_vars(LeaderSetupGC)
  /\ WF_vars(LeaderPublishAndUnlock)
  /\ WF_vars(LeaderEnterBarrier)
  /\ WF_vars(LeaderExitBarrier)
  /\ WF_vars(LeaderFinishGC)
  /\ WF_vars(LeaderReset)
  /\ \A w \in Workers :
       /\ WF_vars(WorkerRegister(w))
       /\ WF_vars(WorkerBeginUnregister(w))
       /\ WF_vars(WorkerSafePointJoinGC(w))
       /\ WF_vars(WorkerSafePointWait(w))
       /\ WF_vars(WorkerWaitResolved(w))
       /\ WF_vars(WorkerSafePointClear(w))
       /\ WF_vars(WorkerAcquireMutex(w))
       /\ WF_vars(WorkerUnregComplete(w))
       /\ WF_vars(WorkerUnregAbort(w))
       /\ WF_vars(WorkerMutexWaitGC(w))
       /\ WF_vars(WorkerSafePointGC(w))
       /\ WF_vars(WorkerExitGC(w))
       /\ WF_vars(WorkerCompleteGC(w))

Spec == Init /\ [][Next]_vars /\ Fairness

(* =========================================================================
   Type Invariant
   ========================================================================= *)

TypeOK ==
  /\ phase \in AllPhases
  /\ threadCount \in 0..MaxIdx
  /\ leaderState \in AllLeaderStates
  /\ \A w \in Workers : workerState[w] \in AllWorkerStates
  /\ \A w \in Workers : threadIdx[w] \in -1..(MaxIdx-1)
  /\ \A i \in 0..MaxIdx : threadActive[i] \in BOOLEAN
  /\ nextFreshIdx \in 0..MaxIdx
  /\ mutexHolder \in {"none"} \union AllThreads

(* =========================================================================
   Safety Properties
   ========================================================================= *)

(* P1: No two workers share an index *)
UniqueIndices ==
  \A w1, w2 \in Workers :
    w1 # w2 /\ threadIdx[w1] >= 0 /\ threadIdx[w2] >= 0 =>
      threadIdx[w1] # threadIdx[w2]

(* P2: No worker shares index with main thread *)
NoMainCollision ==
  \A w \in Workers :
    threadIdx[w] >= 0 => threadIdx[w] # threadIdx[MainThread]

(* P3: Main thread always at index 0 *)
MainThreadAlwaysRegistered ==
  /\ threadIdx[MainThread] = 0
  /\ threadActive[0] = TRUE

(* P4: threadCount matches number of active slots *)
ThreadCountAccurate ==
  LET activeSlots == {i \in 0..(MaxIdx-1) : threadActive[i]}
  IN  threadCount = Cardinality(activeSlots)

(* P5: Registered workers have active slots *)
IndexActiveConsistency ==
  \A w \in Workers :
    workerState[w] \in {Registered, SafePointing, WaitForIdle,
                         UnregLocking, UnregLocked, InBarrier, ExitingGC} =>
      (threadIdx[w] >= 0 /\ threadActive[threadIdx[w]])

(* P6: Free list has no active indices *)
FreeListSafety ==
  \A i \in 1..Len(freeList) :
    ~threadActive[freeList[i]]

(* P7: Free list has no duplicates *)
FreeListNoDuplicates ==
  \A i, j \in 1..Len(freeList) :
    i # j => freeList[i] # freeList[j]

(* P8: When barrier is set up and leader is waiting,
   enough threads exist to satisfy it *)
BarrierAchievable ==
  (phase = PhaseRequested /\ ~barrierReleased) =>
    LET willParticipate ==
      {w \in Workers : workerState[w] \in {Registered, SafePointing, WaitForIdle,
                                            UnregLocking, UnregLocked, InBarrier}}
        \union {MainThread}
    IN  Cardinality(willParticipate) >= barrierCount

(* P9: Mutex exclusion *)
MutexExclusion ==
  mutexHolder # "none" =>
    \A w \in Workers :
      (workerState[w] \in {UnregLocked} /\ mutexHolder = w) \/
      (workerState[w] \notin {UnregLocked})

(* =========================================================================
   Liveness Properties
   ========================================================================= *)

GCLiveness ==
  (leaderState = LeaderLocked) ~> (leaderState = LeaderIdle)

WorkerBarrierLiveness ==
  \A w \in Workers :
    (workerState[w] = InBarrier) ~> (workerState[w] = Registered)

================================================================================
