---------------------- MODULE AllSettledRaceFix -------------------------
(*
 * Fixed version of AllSettledRace.
 *
 * Fix: remove the scan phase entirely. Initialize ctx_completed=0 and
 * rely solely on add_child + callbacks. The wire phase sets parent and
 * fires the callback for already-terminal handles. No double-counting.
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS NULL

N == 3

Handles == 1..N

VARIABLES
  child_status,
  main_phase,           \* "setup" | "wire" | "done"
  wire_idx,
  ctx_completed,
  ctx_total,
  results_filled,
  parent_set,
  combinator_terminal,
  result_count

vars == <<child_status, main_phase, wire_idx,
          ctx_completed, ctx_total, results_filled,
          parent_set, combinator_terminal, result_count>>

------------------------------------------------------------------------
Init ==
  /\ child_status = [i \in Handles |-> "running"]
  /\ main_phase = "setup"
  /\ wire_idx = 1
  /\ ctx_completed = 0
  /\ ctx_total = N
  /\ results_filled = [i \in Handles |-> FALSE]
  /\ parent_set = [i \in Handles |-> FALSE]
  /\ combinator_terminal = FALSE
  /\ result_count = -1

------------------------------------------------------------------------
(* Event loop: complete a child handle *)
EventLoopComplete(i) ==
  /\ child_status[i] = "running"
  /\ child_status' = [child_status EXCEPT ![i] = "completed"]
  /\ IF parent_set[i] /\ ~combinator_terminal
     THEN /\ results_filled' = [results_filled EXCEPT ![i] = TRUE]
          /\ LET new_c == ctx_completed + 1
             IN /\ ctx_completed' = new_c
                /\ IF new_c = ctx_total
                   THEN /\ combinator_terminal' = TRUE
                        /\ result_count' = Cardinality({j \in Handles : results_filled'[j]})
                   ELSE /\ UNCHANGED combinator_terminal
                        /\ UNCHANGED result_count
     ELSE UNCHANGED <<results_filled, ctx_completed, combinator_terminal, result_count>>
  /\ UNCHANGED <<main_phase, wire_idx, ctx_total, parent_set>>

------------------------------------------------------------------------
(* Main thread: setup phase — create ctx with completed=0, skip to wire *)
MainSetup ==
  /\ main_phase = "setup"
  /\ main_phase' = "wire"
  /\ UNCHANGED <<child_status, wire_idx, ctx_completed, ctx_total,
                 results_filled, parent_set, combinator_terminal, result_count>>

------------------------------------------------------------------------
(* Main thread: wire phase — add_child sets parent, fires callback if terminal *)
MainWire ==
  /\ main_phase = "wire"
  /\ wire_idx <= N
  /\ ~combinator_terminal
  /\ parent_set' = [parent_set EXCEPT ![wire_idx] = TRUE]
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
  /\ UNCHANGED <<child_status, ctx_total>>

MainWireDone ==
  /\ main_phase = "wire"
  /\ wire_idx > N
  /\ main_phase' = "done"
  /\ UNCHANGED <<child_status, wire_idx, ctx_completed, ctx_total,
                 results_filled, parent_set, combinator_terminal, result_count>>

------------------------------------------------------------------------
Next ==
  \/ \E i \in Handles : EventLoopComplete(i)
  \/ MainSetup
  \/ MainWire
  \/ MainWireDone

------------------------------------------------------------------------
TypeOK ==
  /\ \A i \in Handles : child_status[i] \in {"running", "completed"}
  /\ main_phase \in {"setup", "wire", "done"}
  /\ wire_idx \in 1..(N+1)
  /\ ctx_completed \in 0..N
  /\ ctx_total = N

AllResultsFilled ==
  combinator_terminal => result_count = N

CounterNeverExceedsTotal ==
  ctx_completed <= ctx_total

========================================================================
