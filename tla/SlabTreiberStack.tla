--------------------------- MODULE SlabTreiberStack ----------------------------
(*
 * Slab Allocator: Two-Phase Acquire with Treiber Stack
 *
 * Models the lock-free slab allocator from slab.c which uses a Treiber stack
 * (with version-tagged head pointer) for the free list and a separate atomic
 * numFree counter for fast availability checks.
 *
 * THE PROTOCOL:
 *   Acquire (two-phase):
 *     Phase 1: CAS(&numFree, old, old-1)    -- reserve a slot
 *     Phase 2: CAS(&head, old, next)         -- pop from Treiber stack
 *     If Phase 2 finds head == EMPTY:
 *       fetch_add(&numFree, 1)               -- undo reservation
 *       return nullptr
 *
 *   Release:
 *     Phase 1: CAS(&head, old, item)         -- push onto Treiber stack
 *     Phase 2: fetch_add(&numFree, 1)        -- increment free count
 *
 * THE CONCERN:
 *   Between Phase 1 and Phase 2 of acquire, numFree has been decremented
 *   but the head hasn't moved yet. Another thread sees numFree > 0, enters
 *   Phase 1 of acquire, then finds head == EMPTY in Phase 2 (because the
 *   first thread hasn't popped yet, and the stack was depleted by others).
 *   The undo path handles this, but we need to verify:
 *     1. No slot is ever handed to two threads simultaneously
 *     2. numFree eventually converges to actual stack depth
 *     3. No slot is leaked (permanently lost from both free list and in-use)
 *     4. No ABA problem despite version tagging
 *
 * Parameters:
 *   Threads  - set of thread IDs
 *   Slots    - set of slot IDs in the slab
 *)
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  Threads,       \* Set of thread IDs (e.g., {"t1", "t2", "t3"})
  Slots           \* Set of slot IDs (e.g., {1, 2, 3})

ASSUME Threads # {}
ASSUME Slots # {}

EMPTY == 0         \* Sentinel for empty stack (SIZE_MAX in C)
NumSlots == Cardinality(Slots)

(* =========================================================================
   Thread action phases
   ========================================================================= *)

Idle             == "idle"

\* Acquire sub-steps
AcqReserved      == "acq_reserved"      \* Phase 1 done: decremented numFree
AcqReadHead      == "acq_read_head"     \* Read head, about to CAS
AcqGotSlot       == "acq_got_slot"      \* Phase 2 done: CAS succeeded
AcqHeadEmpty     == "acq_head_empty"    \* Head was EMPTY, need to undo

\* Release sub-steps
RelPushed        == "rel_pushed"        \* CAS'd head to push item back
RelDone          == "rel_done"          \* Incremented numFree

AllStates == {Idle, AcqReserved, AcqReadHead, AcqGotSlot, AcqHeadEmpty, RelPushed, RelDone}

(* =========================================================================
   Variables
   ========================================================================= *)

VARIABLES
  numFree,         \* Atomic counter: number of free slots (may transiently differ from stack depth)
  stack,           \* Sequence of slot IDs representing the Treiber stack (head = Head(stack))
  threadState,     \* threadState[t]: current action phase
  threadSlot,      \* threadSlot[t]: slot the thread is working with (acquired or releasing)
  readHead,        \* readHead[t]: snapshot of stack head during acquire
  owned            \* owned[t]: set of slots currently owned by thread t

vars == <<numFree, stack, threadState, threadSlot, readHead, owned>>

(* =========================================================================
   Helpers
   ========================================================================= *)

StackDepth == Len(stack)
StackHead == IF stack = <<>> THEN EMPTY ELSE Head(stack)
StackTail == IF stack = <<>> THEN <<>> ELSE Tail(stack)

\* All slots currently on the stack
StackSet == {stack[i] : i \in 1..Len(stack)}

\* All slots currently owned by any thread
OwnedSet == UNION {owned[t] : t \in Threads}

(* =========================================================================
   Init
   ========================================================================= *)

\* Pick any ordering of Slots as the initial stack
InitStack == CHOOSE s \in [1..NumSlots -> Slots] :
               {s[i] : i \in 1..NumSlots} = Slots

Init ==
  /\ numFree = NumSlots
  /\ stack = InitStack
  /\ threadState = [t \in Threads |-> Idle]
  /\ threadSlot = [t \in Threads |-> EMPTY]
  /\ readHead = [t \in Threads |-> EMPTY]
  /\ owned = [t \in Threads |-> {}]

(* =========================================================================
   Acquire Actions
   ========================================================================= *)

(* Phase 1: CAS decrement numFree. Fails if numFree == 0. *)
AcquireReserve(t) ==
  /\ threadState[t] = Idle
  /\ numFree > 0
  /\ numFree' = numFree - 1
  /\ threadState' = [threadState EXCEPT ![t] = AcqReserved]
  /\ UNCHANGED <<stack, threadSlot, readHead, owned>>

(* Acquire fails: numFree was 0 *)
AcquireFailEmpty(t) ==
  /\ threadState[t] = Idle
  /\ numFree = 0
  /\ UNCHANGED vars

(* Read the head of the stack (snapshot for CAS) *)
AcquireReadHead(t) ==
  /\ threadState[t] = AcqReserved
  /\ readHead' = [readHead EXCEPT ![t] = StackHead]
  /\ threadState' = [threadState EXCEPT ![t] = AcqReadHead]
  /\ UNCHANGED <<numFree, stack, threadSlot, owned>>

(* Phase 2: CAS pop from stack. Succeeds if head hasn't changed. *)
AcquirePop(t) ==
  /\ threadState[t] = AcqReadHead
  /\ readHead[t] # EMPTY
  /\ StackHead = readHead[t]         \* CAS succeeds: head unchanged
  /\ LET slot == readHead[t]
     IN  /\ stack' = StackTail
         /\ threadSlot' = [threadSlot EXCEPT ![t] = slot]
         /\ threadState' = [threadState EXCEPT ![t] = AcqGotSlot]
         /\ UNCHANGED <<numFree, readHead, owned>>

(* Phase 2 CAS fails: head changed, retry read *)
AcquirePopRetry(t) ==
  /\ threadState[t] = AcqReadHead
  /\ readHead[t] # EMPTY
  /\ StackHead # readHead[t]         \* CAS fails: head moved
  /\ threadState' = [threadState EXCEPT ![t] = AcqReserved]
  /\ readHead' = [readHead EXCEPT ![t] = EMPTY]
  /\ UNCHANGED <<numFree, stack, threadSlot, owned>>

(* Phase 2: head is EMPTY despite having reserved - undo reservation *)
AcquireUndoReservation(t) ==
  /\ threadState[t] = AcqReadHead
  /\ readHead[t] = EMPTY
  /\ numFree' = numFree + 1
  /\ threadState' = [threadState EXCEPT ![t] = Idle]
  /\ readHead' = [readHead EXCEPT ![t] = EMPTY]
  /\ UNCHANGED <<stack, threadSlot, owned>>

(* Finalize acquire: thread now owns the slot *)
AcquireFinalize(t) ==
  /\ threadState[t] = AcqGotSlot
  /\ LET slot == threadSlot[t]
     IN  /\ owned' = [owned EXCEPT ![t] = owned[t] \union {slot}]
         /\ threadState' = [threadState EXCEPT ![t] = Idle]
         /\ threadSlot' = [threadSlot EXCEPT ![t] = EMPTY]
         /\ UNCHANGED <<numFree, stack, readHead>>

(* =========================================================================
   Release Actions
   ========================================================================= *)

(* Thread decides to release a slot it owns *)
ReleaseBegin(t) ==
  /\ threadState[t] = Idle
  /\ owned[t] # {}
  /\ LET slot == CHOOSE s \in owned[t] : TRUE
     IN  /\ threadSlot' = [threadSlot EXCEPT ![t] = slot]
         /\ owned' = [owned EXCEPT ![t] = owned[t] \ {slot}]
         \* Phase 1: push onto stack (CAS head)
         /\ stack' = <<slot>> \o stack
         /\ threadState' = [threadState EXCEPT ![t] = RelPushed]
         /\ UNCHANGED <<numFree, readHead>>

(* Phase 2: increment numFree *)
ReleaseIncrementFree(t) ==
  /\ threadState[t] = RelPushed
  /\ numFree' = numFree + 1
  /\ threadState' = [threadState EXCEPT ![t] = Idle]
  /\ threadSlot' = [threadSlot EXCEPT ![t] = EMPTY]
  /\ UNCHANGED <<stack, readHead, owned>>

(* =========================================================================
   Next-State Relation
   ========================================================================= *)

Next ==
  \E t \in Threads :
    \/ AcquireReserve(t)
    \/ AcquireReadHead(t)
    \/ AcquirePop(t)
    \/ AcquirePopRetry(t)
    \/ AcquireUndoReservation(t)
    \/ AcquireFinalize(t)
    \/ ReleaseBegin(t)
    \/ ReleaseIncrementFree(t)

Fairness ==
  \A t \in Threads :
    /\ WF_vars(AcquireReserve(t))
    /\ WF_vars(AcquireReadHead(t))
    /\ WF_vars(AcquirePop(t))
    /\ WF_vars(AcquirePopRetry(t))
    /\ WF_vars(AcquireUndoReservation(t))
    /\ WF_vars(AcquireFinalize(t))
    /\ WF_vars(ReleaseBegin(t))
    /\ WF_vars(ReleaseIncrementFree(t))

Spec == Init /\ [][Next]_vars /\ Fairness

(* =========================================================================
   Type Invariant
   ========================================================================= *)

TypeOK ==
  /\ numFree \in 0..(NumSlots + Cardinality(Threads))  \* Can transiently exceed due to ordering
  /\ \A t \in Threads : threadState[t] \in AllStates
  /\ \A t \in Threads : threadSlot[t] \in Slots \union {EMPTY}

(* =========================================================================
   Safety Properties
   ========================================================================= *)

(* P1: Exclusive ownership - no slot is owned by two threads simultaneously *)
ExclusiveOwnership ==
  \A t1, t2 \in Threads :
    t1 # t2 => owned[t1] \intersect owned[t2] = {}

(* P2: No slot is simultaneously on the stack AND owned by a thread *)
NoDoubleAllocation ==
  StackSet \intersect OwnedSet = {}

(* P3: Conservation - every slot is accounted for: either on the stack,
   owned by a thread, or in transit (being acquired/released by a thread) *)
SlotConservation ==
  LET inTransit == {threadSlot[t] : t \in {t2 \in Threads : threadSlot[t2] # EMPTY}}
  IN  StackSet \union OwnedSet \union inTransit = Slots

(* P4: numFree is bounded: never negative, never exceeds total slots *)
NumFreeBounded ==
  /\ numFree >= 0
  /\ numFree <= NumSlots

(* P5: Stack has no duplicates *)
NoDuplicatesOnStack ==
  \A i, j \in 1..Len(stack) :
    i # j => stack[i] # stack[j]

(* P6: When all threads are idle, numFree == stack depth (convergence) *)
NumFreeConvergence ==
  (\A t \in Threads : threadState[t] = Idle) =>
    numFree = StackDepth

(* P7: No slot leak - when all threads idle with nothing owned,
   all slots are on the stack *)
NoSlotLeak ==
  (\A t \in Threads : threadState[t] = Idle /\ owned[t] = {}) =>
    StackSet = Slots

(* Combined safety *)
Safety ==
  /\ TypeOK
  /\ ExclusiveOwnership
  /\ NoDoubleAllocation
  /\ SlotConservation
  /\ NumFreeBounded
  /\ NoDuplicatesOnStack
  /\ NumFreeConvergence

================================================================================
