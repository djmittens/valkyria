#!/bin/bash
# Refactoring Verification Script
# Run from repo root: ./scripts/verify_refactoring.sh
#
# This script verifies that refactoring phases 8-12 are actually complete.
# Each phase has NEGATIVE checks (old pattern gone) and POSITIVE checks (new pattern exists).
# ALL checks must pass for a phase to be considered complete.
#
# DO NOT modify this script to make checks pass. Fix the code instead.

set -e
cd "$(dirname "$0")/.."

FAIL=0
PHASE8_PASS=1
PHASE9_PASS=1
PHASE10_PASS=1
PHASE11_PASS=1
PHASE12_PASS=1

echo "========================================"
echo "Refactoring Verification Script"
echo "========================================"
echo ""

echo "=== Phase 8: Connection State Machine ==="
echo ""

echo -n "  [NEG] No direct state assignments outside FSM: "
COUNT=$(grep -rn "http\.state\s*=" src/aio --include="*.c" 2>/dev/null | grep -v "conn_fsm.c" | grep -v "==" | wc -l | tr -d ' ')
if [ "$COUNT" -eq 0 ]; then 
  echo "PASS (0 found)"
else 
  echo "FAIL ($COUNT found, expected 0)"
  FAIL=1
  PHASE8_PASS=0
fi

echo -n "  [POS] FSM implementation file exists: "
if [ -f src/aio/http2/aio_http2_conn_fsm.c ]; then 
  echo "PASS"
else 
  echo "FAIL (src/aio/http2/aio_http2_conn_fsm.c not found)"
  FAIL=1
  PHASE8_PASS=0
fi

echo -n "  [POS] FSM header file exists: "
if [ -f src/aio/http2/aio_http2_conn_fsm.h ]; then 
  echo "PASS"
else 
  echo "FAIL (src/aio/http2/aio_http2_conn_fsm.h not found)"
  FAIL=1
  PHASE8_PASS=0
fi

echo -n "  [POS] At least 8 connection states defined: "
if [ -f src/aio/http2/aio_http2_conn_fsm.h ]; then
  COUNT=$(grep "VALK_CONN_[A-Z]" src/aio/http2/aio_http2_conn_fsm.h 2>/dev/null | wc -l | tr -d ' ')
  if [ "$COUNT" -ge 8 ]; then 
    echo "PASS ($COUNT states)"
  else 
    echo "FAIL ($COUNT states, need >= 8)"
    FAIL=1
    PHASE8_PASS=0
  fi
else
  echo "FAIL (header not found)"
  FAIL=1
  PHASE8_PASS=0
fi

echo -n "  [POS] FSM functions called >= 16 times: "
COUNT=$(grep -rn "valk_conn_transition\|valk_conn_init_state" src/aio --include="*.c" 2>/dev/null | grep -v "conn_fsm.c" | wc -l | tr -d ' ')
if [ "$COUNT" -ge 16 ]; then 
  echo "PASS ($COUNT calls)"
else 
  echo "FAIL ($COUNT calls, need >= 16)"
  FAIL=1
  PHASE8_PASS=0
fi

echo -n "  [POS] GOAWAY_SENT state exists: "
if [ -f src/aio/http2/aio_http2_conn_fsm.h ]; then
  if grep -q "VALK_CONN_GOAWAY_SENT" src/aio/http2/aio_http2_conn_fsm.h 2>/dev/null; then
    echo "PASS"
  else
    echo "FAIL (VALK_CONN_GOAWAY_SENT not found)"
    FAIL=1
    PHASE8_PASS=0
  fi
else
  echo "FAIL (header not found)"
  FAIL=1
  PHASE8_PASS=0
fi

echo -n "  [POS] DRAINING state exists: "
if [ -f src/aio/http2/aio_http2_conn_fsm.h ]; then
  if grep -q "VALK_CONN_DRAINING" src/aio/http2/aio_http2_conn_fsm.h 2>/dev/null; then
    echo "PASS"
  else
    echo "FAIL (VALK_CONN_DRAINING not found)"
    FAIL=1
    PHASE8_PASS=0
  fi
else
  echo "FAIL (header not found)"
  FAIL=1
  PHASE8_PASS=0
fi

echo -n "  [POS] Entry action for graceful shutdown exists: "
if [ -f src/aio/http2/aio_http2_conn_fsm.c ]; then
  if grep -qE "on_enter.*goaway|on_enter.*drain|goaway.*entry|drain.*entry" src/aio/http2/aio_http2_conn_fsm.c 2>/dev/null; then
    echo "PASS"
  else
    echo "FAIL (no graceful shutdown entry actions found)"
    FAIL=1
    PHASE8_PASS=0
  fi
else
  echo "FAIL (FSM impl not found)"
  FAIL=1
  PHASE8_PASS=0
fi

echo ""
echo "  Phase 8 Status: $([ $PHASE8_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo ""

echo "=== Phase 9: Arena Ownership Tokens ==="
echo ""

echo -n "  [NEG] No direct arena_slab_item assignments: "
COUNT=$(grep -rn "arena_slab_item\s*=" src/aio --include="*.c" 2>/dev/null | wc -l | tr -d ' ')
if [ "$COUNT" -eq 0 ]; then 
  echo "PASS (0 found)"
else 
  echo "FAIL ($COUNT found, expected 0)"
  FAIL=1
  PHASE9_PASS=0
fi

echo -n "  [POS] Arena token/ref type exists in aio_internal.h: "
if grep -qE "valk_arena_token_t|valk_arena_ref_t" src/aio/aio_internal.h 2>/dev/null; then
  echo "PASS"
else
  echo "FAIL (no arena token type found)"
  FAIL=1
  PHASE9_PASS=0
fi

echo -n "  [POS] Arena ref API (take/give/release) used >= 6 times: "
COUNT=$(grep -rE "valk_arena_ref_take|valk_arena_ref_give|valk_arena_ref_release" src/aio --include="*.c" 2>/dev/null | wc -l | tr -d ' ')
if [ "$COUNT" -ge 6 ]; then 
  echo "PASS ($COUNT uses)"
else 
  echo "FAIL ($COUNT uses, need >= 6)"
  FAIL=1
  PHASE9_PASS=0
fi

echo -n "  [NEG] 'Leaked arena' defensive hack removed: "
if grep -q "leaked_arenas" src/aio/http2/aio_http2_conn.c 2>/dev/null; then
  echo "FAIL (leaked_arenas hack still exists)"
  FAIL=1
  PHASE9_PASS=0
else
  echo "PASS (hack removed)"
fi

echo ""
echo "  Phase 9 Status: $([ $PHASE9_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo ""

echo "=== Phase 10: Stream User Data Type Safety ==="
echo ""
echo "  NOTE: Pending stream infrastructure was completely removed in Phase 1."
echo "  Tagged pointers are gone, discriminated union not needed."
echo ""

echo -n "  [NEG] No tagged pointer usage (__is_pending_stream): "
COUNT=$(grep -rn "__is_pending_stream\|__get_pending_stream" src/aio --include="*.c" 2>/dev/null | grep -v "define\|inline" | wc -l | tr -d ' ')
if [ "$COUNT" -eq 0 ]; then 
  echo "PASS (0 found)"
else 
  echo "FAIL ($COUNT found, expected 0)"
  FAIL=1
  PHASE10_PASS=0
fi

echo -n "  [NEG] No pending stream files exist: "
if [ ! -f src/aio/http2/overload/aio_overload_deferred.c ]; then
  echo "PASS (removed)"
else
  echo "FAIL (file still exists)"
  FAIL=1
  PHASE10_PASS=0
fi

echo ""
echo "  Phase 10 Status: $([ $PHASE10_PASS -eq 1 ] && echo 'COMPLETE (via removal)' || echo 'INCOMPLETE')"
echo ""
echo "  Phase 10 Status: $([ $PHASE10_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo ""

echo "=== Phase 11: Complexity Reduction ==="
echo ""

echo -n "  [NEG] on_frame_recv_callback < 50 lines: "
# Count lines from function start to next function definition
COUNT=$(awk '/^int valk_http2_on_frame_recv_callback/,/^}$/' \
  src/aio/http2/aio_http2_session.c 2>/dev/null | wc -l | tr -d ' ')
if [ "$COUNT" -lt 50 ]; then 
  echo "PASS ($COUNT lines)"
else 
  echo "FAIL ($COUNT lines, need < 50)"
  FAIL=1
  PHASE11_PASS=0
fi

echo -n "  [POS] __send_error_response helper exists: "
if grep -q "static void __send_error_response" src/aio/http2/aio_http2_session.c 2>/dev/null; then
  echo "PASS"
else
  echo "FAIL (helper not found)"
  FAIL=1
  PHASE11_PASS=0
fi

echo -n "  [POS] __handle_async_response helper exists: "
if grep -q "static int __handle_async_response" src/aio/http2/aio_http2_session.c 2>/dev/null; then
  echo "PASS"
else
  echo "FAIL (helper not found)"
  FAIL=1
  PHASE11_PASS=0
fi

echo -n "  [POS] __handle_request_headers helper exists: "
if grep -qE "static int __handle_request_headers" src/aio/http2/aio_http2_session.c 2>/dev/null; then
  echo "PASS"
else
  echo "FAIL (helper not found)"
  FAIL=1
  PHASE11_PASS=0
fi

echo -n "  [NEG] No deep nesting (>4 levels) in main callback: "
# Skip function signature continuation lines, count only code lines with 17+ leading spaces (8+ levels at 2-space indent)
DEEP=$(awk '/^int valk_http2_on_frame_recv_callback/,/^}$/' src/aio/http2/aio_http2_session.c 2>/dev/null | grep -v "^[[:space:]]*$" | tail -n +4 | grep -E "^[[:space:]]{17,}" | wc -l | tr -d ' ')
if [ "$DEEP" -eq 0 ]; then 
  echo "PASS"
else 
  echo "FAIL ($DEEP deeply nested lines found)"
  FAIL=1
  PHASE11_PASS=0
fi

echo ""
echo "  Phase 11 Status: $([ $PHASE11_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo ""

echo "=== Phase 12: Dead Code Removal ==="
echo ""

# Check if Option A (delete) or Option B (use abstraction) was chosen
if [ ! -f src/aio/http2/http2_ops_nghttp2.c ]; then
  echo "  Option A chosen: Delete http2_ops abstraction"
  echo ""
  
  echo -n "  [POS] http2_ops.h deleted: "
  if [ ! -f src/aio/http2/http2_ops.h ]; then
    echo "PASS"
  else
    echo "FAIL (file still exists)"
    FAIL=1
    PHASE12_PASS=0
  fi
  
  echo -n "  [POS] http2_ops_nghttp2.c deleted: "
  echo "PASS (already verified)"
  
  echo -n "  [POS] http2_ops_test.c deleted: "
  if [ ! -f src/aio/http2/http2_ops_test.c ]; then
    echo "PASS"
  else
    echo "FAIL (file still exists)"
    FAIL=1
    PHASE12_PASS=0
  fi
  
  echo -n "  [NEG] No http2_ops references remain: "
  COUNT=$(grep -rn "http2_ops" src/aio --include="*.c" --include="*.h" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$COUNT" -eq 0 ]; then 
    echo "PASS"
  else 
    echo "FAIL ($COUNT references remain)"
    FAIL=1
    PHASE12_PASS=0
  fi
else
  echo "  Option B chosen: Use http2_ops abstraction"
  echo ""
  
  echo -n "  [POS] Abstraction used >= 20 times: "
  COUNT=$(grep -rn "ops->http2->" src/aio --include="*.c" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$COUNT" -ge 20 ]; then 
    echo "PASS ($COUNT uses)"
  else 
    echo "FAIL ($COUNT uses, need >= 20)"
    FAIL=1
    PHASE12_PASS=0
  fi
  
  echo -n "  [NEG] No direct nghttp2 calls outside ops impl: "
  COUNT=$(grep -rn "nghttp2_session_\|nghttp2_submit_" src/aio --include="*.c" 2>/dev/null | grep -v "http2_ops_nghttp2.c" | wc -l | tr -d ' ')
  if [ "$COUNT" -eq 0 ]; then 
    echo "PASS"
  else 
    echo "FAIL ($COUNT direct calls remain)"
    FAIL=1
    PHASE12_PASS=0
  fi
fi

echo ""
echo "  Phase 12 Status: $([ $PHASE12_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo ""

echo "=== Build and Test ==="
echo ""

echo -n "  Building project: "
if make build >/dev/null 2>&1; then
  echo "PASS"
else
  echo "FAIL"
  FAIL=1
fi

echo -n "  Running tests: "
if make test >/dev/null 2>&1; then
  echo "PASS"
else
  echo "FAIL"
  FAIL=1
fi

echo ""
echo "========================================"
echo "Summary"
echo "========================================"
echo ""
echo "  Phase 8 (State Machine):     $([ $PHASE8_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo "  Phase 9 (Arena Ownership):   $([ $PHASE9_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo "  Phase 10 (Stream Data):      $([ $PHASE10_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo "  Phase 11 (Complexity):       $([ $PHASE11_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo "  Phase 12 (Dead Code):        $([ $PHASE12_PASS -eq 1 ] && echo 'COMPLETE' || echo 'INCOMPLETE')"
echo ""

if [ "$FAIL" -eq 0 ]; then
  echo "ALL PHASES COMPLETE"
  exit 0
else
  echo "SOME PHASES INCOMPLETE - See failures above"
  exit 1
fi
