------------------------ MODULE AllSettledRace -------------------------
(*
 * Models the race condition in aio/all-settled setup.
 *
 * The C code has three phases on the main thread:
 *   Phase 1 (scan):  read each handle status; if terminal, fill results[i]
 *                     and increment local `completed` counter
 *   Phase 2 (store): atomic_store(&ctx->completed, completed)
 *   Phase 3 (wire):  for each handle, call add_child(); add_child checks
 *                     if child is already terminal and fires notify_parent,
 *                     which calls all_settled_child_completed callback
 *
 * The event loop thread can complete any running handle at any time.
 * The callback does: results[idx] = ...; fetch_add(&completed, 1);
 * if completed == total, build result list and finish.
 *
 * Bug hypothesis: a handle that is terminal at scan time gets counted in
 * the local `completed` (phase 1), then add_child re-fires the callback
 * (phase 3), double-incrementing the atomic counter. This causes the
 * counter to reach `total` before all results[] slots are filled.
 *
 * We model N=3 child handles to keep the state space small.
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS NULL

N == 3  \* number of child handles

Handles == 1..N

\* Main thread setup phases
VARIABLES
  child_status,         \* child_status[i] : "running" | "completed"
  
  \* --- Main thread state ---
  main_phase,           \* "scan" | "store" | "wire" | "done"
  scan_idx,             \* which handle we're scanning (1..N+1, N+1 = done scanning)
  wire_idx,             \* which handle we're wiring (1..N+1)
  local_completed,      \* main thread's local completed count from scan
  scan_saw_terminal,    \* scan_saw_terminal[i] : TRUE if scan saw handle i as terminal
  
  \* --- Shared ctx state (created after store phase) ---
  ctx_exists,           \* TRUE once ctx is set up
  ctx_completed,        \* atomic completed counter in ctx
  ctx_total,            \* total (= N)
  results_filled,       \* results_filled[i] : TRUE if results[i] has been written
  parent_set,           \* parent_set[i] : TRUE if child->parent has been set
  
  \* --- Combinator handle state ---
  combinator_terminal,  \* TRUE if all-settled handle reached terminal
  result_count          \* number of non-NULL entries when result list was built

vars == <<child_status, main_phase, scan_idx, wire_idx, local_completed,
          scan_saw_terminal, ctx_exists, ctx_completed, ctx_total,
          results_filled, parent_set, combinator_terminal, result_count>>

------------------------------------------------------------------------
(* Initialization *)

Init ==
  /\ child_status = [i \in Handles |-> "running"]
  /\ main_phase = "scan"
  /\ scan_idx = 1
  /\ wire_idx = 1
  /\ local_completed = 0
  /\ scan_saw_terminal = [i \in Handles |-> FALSE]
  /\ ctx_exists = FALSE
  /\ ctx_completed = 0
  /\ ctx_total = N
  /\ results_filled = [i \in Handles |-> FALSE]
  /\ parent_set = [i \in Handles |-> FALSE]
  /\ combinator_terminal = FALSE
  /\ result_count = -1

------------------------------------------------------------------------
(* Event loop: complete a child handle at any time *)

EventLoopComplete(i) ==
  /\ child_status[i] = "running"
  /\ child_status' = [child_status EXCEPT ![i] = "completed"]
  \* If parent is set and ctx exists, the completion fires the callback
  /\ IF parent_set[i] /\ ctx_exists /\ ~combinator_terminal
     THEN /\ results_filled' = [results_filled EXCEPT ![i] = TRUE]
          /\ LET new_c == ctx_completed + 1
             IN /\ ctx_completed' = new_c
                /\ IF new_c = ctx_total
                   THEN /\ combinator_terminal' = TRUE
                        \* Count how many results are actually filled
                        /\ result_count' = Cardinality({j \in Handles : results_filled'[j]})
                   ELSE /\ UNCHANGED combinator_terminal
                        /\ UNCHANGED result_count
     ELSE UNCHANGED <<results_filled, ctx_completed, combinator_terminal, result_count>>
  /\ UNCHANGED <<main_phase, scan_idx, wire_idx, local_completed,
                 scan_saw_terminal, ctx_exists, ctx_total, parent_set>>

------------------------------------------------------------------------
(* Main thread: scan phase — read handle status one at a time *)

MainScan ==
  /\ main_phase = "scan"
  /\ scan_idx <= N
  /\ IF child_status[scan_idx] = "completed"
     THEN /\ local_completed' = local_completed + 1
          /\ scan_saw_terminal' = [scan_saw_terminal EXCEPT ![scan_idx] = TRUE]
          /\ results_filled' = [results_filled EXCEPT ![scan_idx] = TRUE]
     ELSE UNCHANGED <<local_completed, scan_saw_terminal, results_filled>>
  /\ scan_idx' = scan_idx + 1
  /\ IF scan_idx + 1 > N
     THEN main_phase' = "store"
     ELSE UNCHANGED main_phase
  /\ UNCHANGED <<child_status, wire_idx, ctx_exists, ctx_completed,
                 ctx_total, parent_set, combinator_terminal, result_count>>

------------------------------------------------------------------------
(* Main thread: store phase — write local_completed to ctx *)

MainStore ==
  /\ main_phase = "store"
  /\ ctx_exists' = TRUE
  /\ ctx_completed' = local_completed
  /\ main_phase' = "wire"
  /\ wire_idx' = 1
  /\ UNCHANGED <<child_status, scan_idx, local_completed, scan_saw_terminal,
                 ctx_total, results_filled, parent_set, combinator_terminal,
                 result_count>>

------------------------------------------------------------------------
(* Main thread: wire phase — add_child for each handle *)
(* add_child sets parent, then checks if child is terminal and fires callback *)

MainWire ==
  /\ main_phase = "wire"
  /\ wire_idx <= N
  /\ ~combinator_terminal
  \* Step 1: set parent
  /\ parent_set' = [parent_set EXCEPT ![wire_idx] = TRUE]
  \* Step 2: check if child is terminal; if so, fire callback
  /\ IF child_status[wire_idx] = "completed" /\ ~combinator_terminal
     THEN /\ results_filled' = [results_filled EXCEPT ![wire_idx] = TRUE]
          /\ LET new_c == ctx_completed + 1
             IN /\ ctx_completed' = new_c
                /\ IF new_c = ctx_total
                   THEN /\ combinator_terminal' = TRUE
                        /\ result_count' = Cardinality({j \in Handles : results_filled'[j]})
                   ELSE /\ UNCHANGED combinator_terminal
                        /\ UNCHANGED result_count
     ELSE UNCHANGED <<results_filled, ctx_completed, combinator_terminal, result_count>>
  /\ wire_idx' = wire_idx + 1
  /\ IF wire_idx + 1 > N
     THEN main_phase' = "done"
     ELSE UNCHANGED main_phase
  /\ UNCHANGED <<child_status, scan_idx, local_completed, scan_saw_terminal,
                 ctx_exists, ctx_total>>

MainWireDone ==
  /\ main_phase = "wire"
  /\ wire_idx > N
  /\ main_phase' = "done"
  /\ UNCHANGED <<child_status, scan_idx, wire_idx, local_completed,
                 scan_saw_terminal, ctx_exists, ctx_completed, ctx_total,
                 results_filled, parent_set, combinator_terminal, result_count>>

------------------------------------------------------------------------
(* Next state *)

Next ==
  \/ \E i \in Handles : EventLoopComplete(i)
  \/ MainScan
  \/ MainStore
  \/ MainWire
  \/ MainWireDone

------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
  /\ \A i \in Handles : child_status[i] \in {"running", "completed"}
  /\ main_phase \in {"scan", "store", "wire", "done"}
  /\ scan_idx \in 1..(N+1)
  /\ wire_idx \in 1..(N+1)
  /\ local_completed \in 0..N
  /\ ctx_completed \in 0..(2*N)  \* can exceed N due to double-counting!
  /\ ctx_total = N

(*
 * THE KEY INVARIANT: when the combinator finishes, ALL results must be filled.
 * If this is violated, we have a bug where completed counter reaches total
 * but some results[] slots are still NULL.
 *)
AllResultsFilled ==
  combinator_terminal => result_count = N

(*
 * Counter should never exceed total.
 * Double-counting causes this violation.
 *)
CounterNeverExceedsTotal ==
  ctx_completed <= ctx_total

========================================================================
