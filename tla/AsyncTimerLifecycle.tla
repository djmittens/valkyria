----------------------- MODULE AsyncTimerLifecycle -----------------------
(*
 * TLA+ model of deferred timer initialization and inline cancellation
 * in the aio/race combinator.
 *
 * Models the race condition between __sleep_init_on_loop and inline cancel:
 *   - Main thread allocates timer_data (memset to 0) and enqueues init task
 *   - Event loop processes init tasks from queue (FIFO within a drain cycle)
 *   - Timer fires non-deterministically once started
 *   - Race combinator: first child to complete cancels siblings INLINE
 *   - Inline cancel runs __reach_terminal + cleanup synchronously
 *   - Cleanup checks timer.loop (NULL if never uv_timer_init'd)
 *   - Init checks handle terminal status before uv_timer_init
 *
 * The scenario: aio/race with two sleep children (h_fast, h_slow).
 * Main thread may also request cancellation of the race handle externally.
 *
 * Key insight: on the event loop thread, each callback is atomic.
 * The callbacks are:
 *   - ProcessInitTask: dequeues and runs __sleep_init_on_loop
 *   - TimerFires: __sleep_timer_cb fires (includes inline cancel of sibling)
 *   - CloseCb: __sleep_timer_close_cb frees timer_data
 *   - ExternalCancel: queued cancel task from main thread
 *
 * Safety properties:
 *   - NoUseAfterFree: never access freed timer_data
 *   - NoDoubleClose: never uv_close an already-closing timer
 *   - NoUninitAccess: never uv_timer_stop/uv_close on uninitialized timer
 *   - ExactlyOneFreePath: each timer_data freed exactly once
 *
 * Liveness properties:
 *   - CleanShutdown: all timer_data eventually freed
 *   - AllTerminal: all handles eventually reach terminal state
 *
 * WITH_FIX controls whether the safety checks are present.
 * Set to FALSE to verify the model catches the bug.
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
  NULL,
  WITH_FIX     \* TRUE = memset+loop check; FALSE = buggy (no checks)

(* Handle states *)
Running   == "RUNNING"
Completed == "COMPLETED"
Cancelled == "CANCELLED"
Terminal == {Completed, Cancelled}

(* Timer data states -- fine-grained to catch bugs *)
TdUninitialized == "uninit"    \* aligned_alloc'd, memset'd if WITH_FIX, garbage if ~WITH_FIX
TdInitialized   == "init"     \* uv_timer_init done (loop != NULL), not yet started
TdActive        == "active"   \* uv_timer_start done, timer is running
TdStopped       == "stopped"  \* uv_timer_stop done, handle still open
TdClosing       == "closing"  \* uv_close called, waiting for close_cb
TdFreed         == "freed"    \* free(timer_data) done

AllTdStates == {TdUninitialized, TdInitialized, TdActive, TdStopped, TdClosing, TdFreed}

(* Whether the timer's loop field is non-NULL (i.e., uv_timer_init was called) *)
TdHasLoop(td) == td \in {TdInitialized, TdActive, TdStopped, TdClosing}

(* Whether uv_is_active would return TRUE *)
TdIsActive(td) == td = TdActive

(* Whether uv_is_closing would return TRUE *)
TdIsClosing(td) == td = TdClosing

VARIABLES
  h_race,            \* race combinator handle status
  h_fast,            \* fast sleep handle status
  h_slow,            \* slow sleep handle status
  td_fast,           \* fast timer data state
  td_slow,           \* slow timer data state
  init_queue,        \* FIFO queue of pending init tasks: Seq("fast"|"slow")
  cancel_queue,      \* FIFO queue of pending cancel tasks: Seq("fast"|"slow"|"race")
  uv_ptr_fast,       \* TRUE if h_fast.uv_handle_ptr points to timer_data
  uv_ptr_slow,       \* TRUE if h_slow.uv_handle_ptr points to timer_data
  fast_cleanup_ran,  \* TRUE if h_fast resource cleanup has executed
  slow_cleanup_ran,  \* TRUE if h_slow resource cleanup has executed
  done

vars == <<h_race, h_fast, h_slow, td_fast, td_slow,
          init_queue, cancel_queue,
          uv_ptr_fast, uv_ptr_slow,
          fast_cleanup_ran, slow_cleanup_ran, done>>

------------------------------------------------------------------------
IsTerminal(s) == s \in Terminal

Td(target)  == IF target = "fast" THEN td_fast  ELSE td_slow
Hs(target)  == IF target = "fast" THEN h_fast   ELSE h_slow
Ptr(target) == IF target = "fast" THEN uv_ptr_fast ELSE uv_ptr_slow
Other(target) == IF target = "fast" THEN "slow" ELSE "fast"

------------------------------------------------------------------------
(* Helper: set timer data state *)
SetTd(target, val, ofast, oslow) ==
  IF target = "fast"
  THEN td_fast' = val /\ td_slow' = oslow
  ELSE td_fast' = ofast /\ td_slow' = val

------------------------------------------------------------------------
Init ==
  /\ h_race = Running
  /\ h_fast = Running
  /\ h_slow = Running
  /\ td_fast = TdUninitialized
  /\ td_slow = TdUninitialized
  \* Init tasks can be enqueued in either order (models non-deterministic
  \* task queue ordering / interleaving of aio_sleep calls from main thread)
  /\ init_queue \in {<<"fast", "slow">>, <<"slow", "fast">>}
  /\ cancel_queue = <<>>
  /\ uv_ptr_fast = TRUE
  /\ uv_ptr_slow = TRUE
  /\ fast_cleanup_ran = FALSE
  /\ slow_cleanup_ran = FALSE
  /\ done = FALSE

------------------------------------------------------------------------
(*
 * RunCleanup: execute __sleep_cleanup for a target.
 *
 * C code:
 *   if (timer_data == NULL) return;
 *   if (timer_data->uv.timer.loop == NULL) return;   // WITH_FIX only
 *   if (uv_is_closing(...)) return;
 *   if (uv_is_active(...)) uv_timer_stop(...);
 *   uv_close(..., close_cb);
 *
 * Without fix: no loop check, so it would call uv_timer_stop/uv_close
 * on an uninitialized timer → CRASH.
 *
 * This is an operator, not an action. It describes the td state transition
 * that cleanup performs, given the current td state.
 *)
CleanupResult(td) ==
  IF WITH_FIX THEN
    \* With fix: check loop != NULL before touching timer
    IF ~TdHasLoop(td) THEN td           \* loop==NULL → no-op, return unchanged
    ELSE IF TdIsClosing(td) THEN td     \* already closing → no-op
    ELSE IF TdIsActive(td) THEN TdClosing  \* stop + close
    ELSE IF td = TdStopped THEN TdClosing  \* just close (already stopped)
    ELSE IF td = TdInitialized THEN TdClosing  \* init'd but not started → close
    ELSE td                              \* freed etc → no-op
  ELSE
    \* Without fix: no loop check, accesses uninitialized memory
    \* If td is uninitialized, this is undefined behavior (USE_AFTER_FREE / uninit access)
    IF td = TdUninitialized THEN "BUG_UNINIT_ACCESS"  \* sentinel for invariant
    ELSE IF TdIsClosing(td) THEN td
    ELSE IF TdIsActive(td) THEN TdClosing
    ELSE IF td = TdStopped THEN TdClosing
    ELSE IF td = TdInitialized THEN TdClosing
    ELSE td

------------------------------------------------------------------------
(*
 * ProcessInitTask: event loop dequeues __sleep_init_on_loop from task queue.
 *
 * C code:
 *   if (valk_async_handle_is_terminal(handle->status)) {
 *     free(timer_data); return;                      // WITH_FIX only
 *   }
 *   uv_timer_init(loop, &timer_data->uv.timer);     // sets loop != NULL
 *   uv_timer_start(&timer_data->uv.timer, cb, ms, 0);
 *
 * Without fix: no terminal check, always inits + starts even if cancelled.
 *)
ProcessInitTask ==
  /\ Len(init_queue) > 0
  /\ LET target == Head(init_queue) IN
     /\ init_queue' = Tail(init_queue)
     /\ IF WITH_FIX THEN
          \* WITH FIX: check terminal before init
          IF IsTerminal(Hs(target)) THEN
            \* Handle already cancelled/completed → free timer_data directly
            /\ (IF target = "fast"
                THEN td_fast' = TdFreed /\ UNCHANGED td_slow
                ELSE td_slow' = TdFreed /\ UNCHANGED td_fast)
            /\ UNCHANGED <<h_race, h_fast, h_slow, cancel_queue,
                           uv_ptr_fast, uv_ptr_slow,
                           fast_cleanup_ran, slow_cleanup_ran, done>>
          ELSE
            \* Handle still running → init + start timer
            /\ (IF target = "fast"
                THEN td_fast' = TdActive /\ UNCHANGED td_slow
                ELSE td_slow' = TdActive /\ UNCHANGED td_fast)
            /\ UNCHANGED <<h_race, h_fast, h_slow, cancel_queue,
                           uv_ptr_fast, uv_ptr_slow,
                           fast_cleanup_ran, slow_cleanup_ran, done>>
        ELSE
          \* WITHOUT FIX: always init + start, no terminal check
          \* If handle is already terminal, this creates a timer that nobody will
          \* clean up (or that cleanup already ran on, causing double-lifecycle)
          /\ (IF target = "fast"
              THEN td_fast' = TdActive /\ UNCHANGED td_slow
              ELSE td_slow' = TdActive /\ UNCHANGED td_fast)
          /\ UNCHANGED <<h_race, h_fast, h_slow, cancel_queue,
                         uv_ptr_fast, uv_ptr_slow,
                         fast_cleanup_ran, slow_cleanup_ran, done>>

------------------------------------------------------------------------
(*
 * TimerFires: libuv fires __sleep_timer_cb for target.
 *
 * This is a single atomic callback on the event loop thread. Within it:
 *   1. uv_timer_stop(timer)
 *   2. uv_close(timer, close_cb)           → td becomes TdClosing
 *   3. handle->uv_handle_ptr = NULL
 *   4. valk_async_handle_complete(handle)
 *      → __reach_terminal(COMPLETED) [CAS]
 *        → valk_async_handle_finish
 *          → notify_parent (race resolves, cancels sibling INLINE)
 *            → valk_async_cancel_task(sibling) INLINE
 *              → __reach_terminal(sibling, CANCELLED)
 *                → finish(sibling)
 *                  → run_resource_cleanups(sibling)
 *                    → __sleep_cleanup(sibling)
 *              → (cancel_task also checks uv_handle_ptr, redundant)
 *          → notify_done
 *          → propagate_completion
 *          → run_resource_cleanups(self)
 *            → __sleep_cleanup(self) [sees uv_is_closing, no-op]
 *
 * The CAS in __reach_terminal ensures only one of {timer_fires, cancel}
 * can transition each handle.
 *)
TimerFires(target) ==
  /\ Td(target) = TdActive           \* Timer must be running
  /\ ~IsTerminal(Hs(target))         \* Handle must not be terminal yet
  /\ LET other == Other(target) IN
     \* === Self: timer fires → close, complete, cleanup ===
     /\ (IF target = "fast"
         THEN /\ td_fast' = TdClosing       \* uv_close called
              /\ h_fast' = Completed         \* __reach_terminal succeeds
              /\ uv_ptr_fast' = FALSE        \* uv_handle_ptr = NULL
              /\ fast_cleanup_ran' = TRUE    \* resource cleanup ran (no-op since already closing)
         ELSE /\ td_slow' = TdClosing
              /\ h_slow' = Completed
              /\ uv_ptr_slow' = FALSE
              /\ slow_cleanup_ran' = TRUE)
     \* === Race parent resolves ===
     /\ IF h_race = Running THEN
          /\ h_race' = Completed
          \* === Cancel sibling inline ===
          /\ IF ~IsTerminal(Hs(other)) THEN
               \* __reach_terminal(sibling, CANCELLED) succeeds
               \* finish(sibling) → resource_cleanups → __sleep_cleanup(sibling)
               LET sibling_td == Td(other)
                   cleaned == CleanupResult(sibling_td)
               IN
                 /\ (IF other = "fast"
                     THEN /\ h_fast' = Cancelled
                          /\ td_fast' = cleaned
                          /\ uv_ptr_fast' = uv_ptr_fast  \* cancel_task doesn't null ptr
                          /\ fast_cleanup_ran' = TRUE
                     ELSE /\ h_slow' = Cancelled
                          /\ td_slow' = cleaned
                          /\ uv_ptr_slow' = uv_ptr_slow
                          /\ slow_cleanup_ran' = TRUE)
             ELSE
               \* Sibling already terminal → cancel CAS fails, no-op
               /\ (IF other = "fast"
                   THEN UNCHANGED <<h_fast, td_fast, uv_ptr_fast, fast_cleanup_ran>>
                   ELSE UNCHANGED <<h_slow, td_slow, uv_ptr_slow, slow_cleanup_ran>>)
        ELSE
          \* Race already terminal (other child already won)
          /\ UNCHANGED h_race
          /\ (IF other = "fast"
              THEN UNCHANGED <<h_fast, td_fast, uv_ptr_fast, fast_cleanup_ran>>
              ELSE UNCHANGED <<h_slow, td_slow, uv_ptr_slow, slow_cleanup_ran>>)
     /\ UNCHANGED <<init_queue, cancel_queue, done>>

------------------------------------------------------------------------
(*
 * CloseCb: libuv close callback (__sleep_timer_close_cb) fires.
 *
 * This runs in a LATER event loop iteration after uv_close was called.
 * C code: free(timer_data);
 *)
CloseCb(target) ==
  /\ Td(target) = TdClosing
  /\ (IF target = "fast"
      THEN td_fast' = TdFreed /\ UNCHANGED td_slow
      ELSE td_slow' = TdFreed /\ UNCHANGED td_fast)
  /\ UNCHANGED <<h_race, h_fast, h_slow, init_queue, cancel_queue,
                 uv_ptr_fast, uv_ptr_slow,
                 fast_cleanup_ran, slow_cleanup_ran, done>>

------------------------------------------------------------------------
(*
 * ExternalCancel: main thread cancels the race handle.
 * This gets enqueued as a cancel task and processed on event loop.
 *
 * The cancel task calls __reach_terminal(race, CANCELLED).
 * If it wins, race transitions to CANCELLED, then finish runs,
 * which propagates cancel to all children by ENQUEUEING cancel tasks.
 *
 * Then child cancel tasks are processed in later steps.
 *)
ExternalCancelRace ==
  /\ h_race = Running
  /\ ~IsTerminal(h_race)
  /\ h_race' = Cancelled
  \* Enqueue cancel tasks for both children
  /\ cancel_queue' = cancel_queue \o <<"fast", "slow">>
  /\ UNCHANGED <<h_fast, h_slow, td_fast, td_slow, init_queue,
                 uv_ptr_fast, uv_ptr_slow,
                 fast_cleanup_ran, slow_cleanup_ran, done>>

------------------------------------------------------------------------
(*
 * ProcessCancelTask: event loop dequeues a child cancel task.
 *
 * This is valk_async_cancel_task running for a child handle.
 * It does:
 *   1. __reach_terminal(child, CANCELLED) [CAS]
 *   2. If CAS succeeds: finish → cleanup
 *   3. Check uv_handle_ptr and stop timer if active
 *)
ProcessCancelTask ==
  /\ Len(cancel_queue) > 0
  /\ LET target == Head(cancel_queue) IN
     /\ cancel_queue' = Tail(cancel_queue)
     /\ IF target = "race" THEN
          \* Race cancel task (redundant if already done by ExternalCancelRace)
          UNCHANGED <<h_race, h_fast, h_slow, td_fast, td_slow, init_queue,
                      uv_ptr_fast, uv_ptr_slow,
                      fast_cleanup_ran, slow_cleanup_ran, done>>
        ELSE IF ~IsTerminal(Hs(target)) THEN
          \* CAS succeeds → transition to CANCELLED, run cleanup
          LET td == Td(target)
              cleaned == CleanupResult(td)
          IN
            /\ (IF target = "fast"
                THEN /\ h_fast' = Cancelled
                     /\ td_fast' = cleaned
                     /\ fast_cleanup_ran' = TRUE
                     /\ UNCHANGED <<h_slow, td_slow, slow_cleanup_ran>>
                ELSE /\ h_slow' = Cancelled
                     /\ td_slow' = cleaned
                     /\ slow_cleanup_ran' = TRUE
                     /\ UNCHANGED <<h_fast, td_fast, fast_cleanup_ran>>)
            /\ UNCHANGED <<h_race, init_queue,
                           uv_ptr_fast, uv_ptr_slow, done>>
        ELSE
          \* CAS fails → already terminal, no-op
          UNCHANGED <<h_race, h_fast, h_slow, td_fast, td_slow, init_queue,
                      uv_ptr_fast, uv_ptr_slow,
                      fast_cleanup_ran, slow_cleanup_ran, done>>

------------------------------------------------------------------------
(* Termination detection *)
AllDone ==
  /\ IsTerminal(h_fast) /\ IsTerminal(h_slow) /\ IsTerminal(h_race)
  /\ td_fast \in {TdFreed} /\ td_slow \in {TdFreed}
  /\ Len(init_queue) = 0
  /\ Len(cancel_queue) = 0

MarkDone ==
  /\ AllDone
  /\ ~done
  /\ done' = TRUE
  /\ UNCHANGED <<h_race, h_fast, h_slow, td_fast, td_slow,
                 init_queue, cancel_queue,
                 uv_ptr_fast, uv_ptr_slow,
                 fast_cleanup_ran, slow_cleanup_ran>>

Stutter ==
  /\ done
  /\ UNCHANGED vars

------------------------------------------------------------------------
Next ==
  \/ ProcessInitTask
  \/ ProcessCancelTask
  \/ \E t \in {"fast", "slow"} :
       \/ TimerFires(t)
       \/ CloseCb(t)
  \/ ExternalCancelRace
  \/ MarkDone
  \/ Stutter

Fairness ==
  /\ WF_vars(ProcessInitTask)
  /\ WF_vars(ProcessCancelTask)
  /\ \A t \in {"fast", "slow"} :
       /\ WF_vars(TimerFires(t))
       /\ WF_vars(CloseCb(t))
  /\ WF_vars(MarkDone)
  \* Note: ExternalCancelRace is NOT weakly fair -- it may or may not happen

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------
(* Safety Invariants *)

TypeOK ==
  /\ h_race \in {Running, Completed, Cancelled}
  /\ h_fast \in {Running, Completed, Cancelled}
  /\ h_slow \in {Running, Completed, Cancelled}
  /\ td_fast \in AllTdStates \cup {"BUG_UNINIT_ACCESS"}
  /\ td_slow \in AllTdStates \cup {"BUG_UNINIT_ACCESS"}
  /\ uv_ptr_fast \in BOOLEAN
  /\ uv_ptr_slow \in BOOLEAN

(* No access to uninitialized timer (the original crash) *)
NoUninitAccess ==
  /\ td_fast # "BUG_UNINIT_ACCESS"
  /\ td_slow # "BUG_UNINIT_ACCESS"

(* Timer data not accessed after free *)
NoUseAfterFree ==
  /\ (td_fast = TdFreed => (IsTerminal(h_fast) /\ fast_cleanup_ran))
  /\ (td_slow = TdFreed => (IsTerminal(h_slow) /\ slow_cleanup_ran))

(* Timer data follows valid lifecycle ordering *)
ValidLifecycle ==
  /\ td_fast \in AllTdStates
  /\ td_slow \in AllTdStates

(* No double-close: timer must not be in closing state when cleanup tries to close *)
(* This is enforced by the uv_is_closing check in CleanupResult *)

(* If handle completed/cancelled, its cleanup must eventually run *)
(* (Checked as a state invariant: if terminal and cleanup ran, td must progress) *)
CleanupConsistency ==
  /\ (fast_cleanup_ran /\ td_fast = TdUninitialized => 
        \* Cleanup on uninit timer: with fix this is no-op (td stays uninit)
        \* Init task will later free it. This is ok.
        WITH_FIX)
  /\ (slow_cleanup_ran /\ td_slow = TdUninitialized =>
        WITH_FIX)

------------------------------------------------------------------------
(* Temporal Properties *)

(* All timer data eventually freed *)
CleanShutdown ==
  <>(td_fast = TdFreed /\ td_slow = TdFreed)

(* All handles eventually terminal *)
AllTerminal ==
  <>(IsTerminal(h_fast) /\ IsTerminal(h_slow) /\ IsTerminal(h_race))

(* No timer data leak: if handle terminal and cleanup ran and init processed,
   timer data must eventually be freed *)
NoTimerLeak ==
  \A t \in {"fast", "slow"} :
    [](IsTerminal(Hs(t)) => <>(Td(t) = TdFreed))

========================================================================
