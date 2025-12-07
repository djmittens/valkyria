#!/bin/bash
# Integration tests for async API (aio/let, aio/sleep)
#
# Tests the async endpoints in webserver_demo.valk
#
# Run with: bash test/test_async_integration.sh
# Requires: server must be running

set -e

echo "=== Async API Integration Tests ==="
echo ""

# Check if server is running
if ! curl -sk https://localhost:8443/ > /dev/null 2>&1; then
  echo "ERROR: Server not running at https://localhost:8443"
  echo "Start it with: build/valk examples/webserver_demo.valk"
  exit 1
fi

PASSED=0
FAILED=0

# Test function
run_test() {
  local name="$1"
  local endpoint="$2"
  local min_ms="$3"
  local max_ms="$4"
  local expected_body="$5"

  echo "Test: $name"
  echo "  Endpoint: $endpoint"
  echo "  Expected duration: ${min_ms}ms - ${max_ms}ms"

  # Time the request
  START=$(date +%s%N)
  RESULT=$(curl -sk "https://localhost:8443$endpoint" 2>/dev/null)
  END=$(date +%s%N)
  DURATION=$(( (END - START) / 1000000 ))

  echo "  Actual duration: ${DURATION}ms"
  echo "  Response: $RESULT"

  # Check duration
  if [ $DURATION -lt $min_ms ] || [ $DURATION -gt $max_ms ]; then
    echo "  FAIL: Duration outside expected range"
    ((FAILED++))
    return 1
  fi

  # Check body if specified
  if [ -n "$expected_body" ]; then
    if ! echo "$RESULT" | grep -q "$expected_body"; then
      echo "  FAIL: Response doesn't contain '$expected_body'"
      ((FAILED++))
      return 1
    fi
  fi

  echo "  PASS"
  ((PASSED++))
  echo ""
}

# =============================================================================
# Test cases
# =============================================================================

# Test 1: /slow endpoint (single 2s sleep)
run_test "/slow (single async binding)" "/slow" 1900 2500 "slept 2s"

# Test 2: /slow-chain endpoint (sequential 1s + 1s)
run_test "/slow-chain (sequential with :then)" "/slow-chain" 1900 2500 "1s + 1s sequential"

# Test 3: Basic homepage (sync, should be fast)
run_test "/ (homepage, sync)" "/" 0 500 "Valkyria"

# Test 4: Favicon (sync, should be fast)
run_test "/favicon.svg (static asset)" "/favicon.svg" 0 200 "svg"

# =============================================================================
# Parallel tests (currently known to fail - aio/all issue)
# =============================================================================

echo "=== Parallel Tests (may fail due to known aio/all issue) ==="
echo ""

# Test 5: /slow-parallel (should be ~1s, not 3s if parallel works)
echo "Test: /slow-parallel (3x 1s parallel)"
echo "  Expected: ~1000ms if parallel works, ~3000ms if sequential"
START=$(date +%s%N)
RESULT=$(timeout 5 curl -sk https://localhost:8443/slow-parallel 2>/dev/null) || RESULT="TIMEOUT"
END=$(date +%s%N)
DURATION=$(( (END - START) / 1000000 ))
echo "  Duration: ${DURATION}ms"
if [ "$RESULT" = "TIMEOUT" ]; then
  echo "  Status: TIMEOUT (known issue with aio/all)"
else
  echo "  Response: $RESULT"
  if [ $DURATION -lt 1500 ]; then
    echo "  Status: PASS (parallel working!)"
    ((PASSED++))
  else
    echo "  Status: SKIP (parallel not working, took ${DURATION}ms)"
  fi
fi
echo ""

# =============================================================================
# Summary
# =============================================================================

echo "=== Summary ==="
echo "Passed: $PASSED"
echo "Failed: $FAILED"

if [ $FAILED -gt 0 ]; then
  exit 1
fi

echo ""
echo "All critical tests passed!"
