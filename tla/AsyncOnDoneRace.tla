--------------------------- MODULE AsyncOnDoneRace ----------------------------
(*
 * TLA+ model of the on_done set-after-create race in http2/client-request.
 *
 * Models the race condition where:
 *   1. Main thread creates connect_handle via valk_aio_http2_connect_host()
 *   2. Task is enqueued to event loop
 *   3. Main thread sets connect_handle->on_done = callback   (line 814)
 *   4. Event loop completes connect_handle, calls notify_done
 *      which does atomic_exchange(&on_done, NULL) — if on_done is still
 *      NULL (step 3 hasn't happened), the callback is LOST
 *
 * The same pattern repeats for request_handle (line 738-739).
 *
 * This models N sequential client requests, each with:
 *   - outer_handle (returned to Lisp, awaited by main thread)
 *   - connect_handle (internal, on_done links to request phase)
 *   - request_handle (internal, on_done links back to outer_handle)
 *
 * Verifies:
 *   Liveness — every outer_handle eventually reaches terminal
 *   Safety  — on_done fires exactly once per handle
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
  N,            \* number of sequential requests (e.g. 3)
  NULL

VARIABLES
  \* Per-request state (indexed 1..N)
  phase,            \* phase[i]: "idle" | "connecting" | "requesting" | "done"
  
  \* Connect handle state
  conn_status,      \* conn_status[i]: "pending" | "completed"
  conn_on_done,     \* conn_on_done[i]: NULL | "callback"
  conn_on_done_fired, \* conn_on_done_fired[i]: count of on_done firings
  
  \* Request handle state
  req_status,       \* req_status[i]: "pending" | "completed"
  req_on_done,      \* req_on_done[i]: NULL | "callback"
  req_on_done_fired, \* req_on_done_fired[i]: count of on_done firings
  
  \* Outer handle state (what Lisp awaits)
  outer_status,     \* outer_status[i]: "pending" | "completed"
  
  \* Sequencing
  current_req,      \* which request the main thread is working on (1..N+1)
  
  \* Main thread progress within a request
  main_step,        \* "create_conn" | "set_conn_on_done" | "awaiting" | "idle"
  conn_step         \* "create_req" | "set_req_on_done" | "waiting" | "idle"

vars == <<phase, conn_status, conn_on_done, conn_on_done_fired,
          req_status, req_on_done, req_on_done_fired,
          outer_status, current_req, main_step, conn_step>>

Requests == 1..N

------------------------------------------------------------------------
(* Init *)

Init ==
  /\ phase = [i \in Requests |-> "idle"]
  /\ conn_status = [i \in Requests |-> "pending"]
  /\ conn_on_done = [i \in Requests |-> NULL]
  /\ conn_on_done_fired = [i \in Requests |-> 0]
  /\ req_status = [i \in Requests |-> "pending"]
  /\ req_on_done = [i \in Requests |-> NULL]
  /\ req_on_done_fired = [i \in Requests |-> 0]
  /\ outer_status = [i \in Requests |-> "pending"]
  /\ current_req = 1
  /\ main_step = "create_conn"
  /\ conn_step = "idle"

------------------------------------------------------------------------
(* Main thread actions *)

(* Step 1: Main creates connect_handle and enqueues task.
   At this point on_done is NULL — task is already queued. *)
MainCreateConn ==
  /\ current_req <= N
  /\ main_step = "create_conn"
  /\ phase' = [phase EXCEPT ![current_req] = "connecting"]
  /\ main_step' = "set_conn_on_done"
  /\ UNCHANGED <<conn_status, conn_on_done, conn_on_done_fired,
                  req_status, req_on_done, req_on_done_fired,
                  outer_status, current_req, conn_step>>

(* Step 2: Main sets connect_handle->on_done = callback.
   This races with event loop completing the connect. *)
MainSetConnOnDone ==
  /\ current_req <= N
  /\ main_step = "set_conn_on_done"
  /\ conn_on_done' = [conn_on_done EXCEPT ![current_req] = "callback"]
  /\ main_step' = "awaiting"
  /\ UNCHANGED <<phase, conn_status, conn_on_done_fired,
                  req_status, req_on_done, req_on_done_fired,
                  outer_status, current_req, conn_step>>

(* Main thread awaits outer_handle (polls until terminal) *)
MainAwaitComplete ==
  /\ current_req <= N
  /\ main_step = "awaiting"
  /\ outer_status[current_req] = "completed"
  /\ phase' = [phase EXCEPT ![current_req] = "done"]
  /\ current_req' = current_req + 1
  /\ main_step' = IF current_req + 1 <= N THEN "create_conn" ELSE "idle"
  /\ conn_step' = "idle"
  /\ UNCHANGED <<conn_status, conn_on_done, conn_on_done_fired,
                  req_status, req_on_done, req_on_done_fired, outer_status>>

------------------------------------------------------------------------
(* Event loop thread actions *)

(* Event loop completes the connect_handle.
   Calls notify_done which does atomic_exchange(&on_done, NULL).
   If on_done was "callback", fires it. If NULL, lost. *)
EvLoopCompleteConn(i) ==
  /\ phase[i] = "connecting"
  /\ conn_status[i] = "pending"
  /\ conn_status' = [conn_status EXCEPT ![i] = "completed"]
  \* atomic_exchange: take whatever is in on_done, replace with NULL
  /\ LET had_callback == conn_on_done[i] = "callback"
     IN /\ conn_on_done' = [conn_on_done EXCEPT ![i] = NULL]
        /\ IF had_callback
           THEN \* Callback fires: creates request_handle
                /\ conn_on_done_fired' = [conn_on_done_fired EXCEPT ![i] = @ + 1]
                /\ phase' = [phase EXCEPT ![i] = "requesting"]
                /\ conn_step' = "set_req_on_done"
           ELSE \* Callback LOST — on_done was NULL when we exchanged
                /\ UNCHANGED conn_on_done_fired
                /\ UNCHANGED phase
                /\ UNCHANGED conn_step
  /\ UNCHANGED <<req_status, req_on_done, req_on_done_fired,
                  outer_status, current_req, main_step>>

(* The connect callback creates request_handle and enqueues request task.
   on_done for request_handle is NOT yet set. *)
(* This is folded into EvLoopCompleteConn when had_callback=TRUE:
   phase moves to "requesting", conn_step moves to "set_req_on_done" *)

(* Connect callback sets request_handle->on_done.
   Same race pattern as connect. *)
ConnCallbackSetReqOnDone(i) ==
  /\ phase[i] = "requesting"
  /\ conn_step = "set_req_on_done"
  /\ i = current_req  \* only the current request's callback runs
  /\ req_on_done' = [req_on_done EXCEPT ![i] = "callback"]
  /\ conn_step' = "waiting"
  /\ UNCHANGED <<phase, conn_status, conn_on_done, conn_on_done_fired,
                  req_status, req_on_done_fired,
                  outer_status, current_req, main_step>>

(* Event loop completes the request_handle (response arrived).
   Same atomic_exchange pattern. *)
EvLoopCompleteReq(i) ==
  /\ phase[i] = "requesting"
  /\ req_status[i] = "pending"
  /\ req_status' = [req_status EXCEPT ![i] = "completed"]
  \* atomic_exchange: take whatever is in on_done, replace with NULL
  /\ LET had_callback == req_on_done[i] = "callback"
     IN /\ req_on_done' = [req_on_done EXCEPT ![i] = NULL]
        /\ IF had_callback
           THEN \* Callback fires: completes outer_handle
                /\ req_on_done_fired' = [req_on_done_fired EXCEPT ![i] = @ + 1]
                /\ outer_status' = [outer_status EXCEPT ![i] = "completed"]
           ELSE \* Callback LOST — outer_handle stays pending forever
                /\ UNCHANGED req_on_done_fired
                /\ UNCHANGED outer_status
  /\ UNCHANGED <<phase, conn_status, conn_on_done, conn_on_done_fired,
                  current_req, main_step, conn_step>>

------------------------------------------------------------------------
(* Specification *)

AllDone == current_req > N

Stutter == AllDone /\ UNCHANGED vars

Next ==
  \/ MainCreateConn
  \/ MainSetConnOnDone
  \/ MainAwaitComplete
  \/ \E i \in Requests :
       \/ EvLoopCompleteConn(i)
       \/ ConnCallbackSetReqOnDone(i)
       \/ EvLoopCompleteReq(i)
  \/ Stutter

Fairness ==
  /\ WF_vars(MainCreateConn)
  /\ WF_vars(MainSetConnOnDone)
  /\ WF_vars(MainAwaitComplete)
  /\ \A i \in Requests :
       /\ WF_vars(EvLoopCompleteConn(i))
       /\ WF_vars(ConnCallbackSetReqOnDone(i))
       /\ WF_vars(EvLoopCompleteReq(i))

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
  /\ \A i \in Requests :
       /\ phase[i] \in {"idle", "connecting", "requesting", "done"}
       /\ conn_status[i] \in {"pending", "completed"}
       /\ conn_on_done[i] \in {NULL, "callback"}
       /\ conn_on_done_fired[i] \in 0..1
       /\ req_status[i] \in {"pending", "completed"}
       /\ req_on_done[i] \in {NULL, "callback"}
       /\ req_on_done_fired[i] \in 0..1
       /\ outer_status[i] \in {"pending", "completed"}

(* No double-fire of on_done callbacks *)
NoDoubleFire ==
  \A i \in Requests :
    /\ conn_on_done_fired[i] <= 1
    /\ req_on_done_fired[i] <= 1

------------------------------------------------------------------------
(* Temporal properties *)

(* LIVENESS: Every request eventually completes.
   This SHOULD FAIL with the buggy code — when on_done is lost,
   the outer handle stays pending forever. *)
AllRequestsComplete ==
  \A i \in Requests : <>(outer_status[i] = "completed")

(* SAFETY: If a handle completed and had on_done set, the callback must fire *)
CallbackIntegrity ==
  \A i \in Requests :
    (conn_status[i] = "completed" /\ conn_on_done_fired[i] = 0) =>
      conn_on_done[i] = NULL

========================================================================
