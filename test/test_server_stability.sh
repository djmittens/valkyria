#!/bin/bash

echo "Starting server..."
build/valk examples/hello_server.valk 2>&1 &
SERVERPID=$!

sleep 2

echo "Running 10 requests..."
SUCCESS=0
FAILED=0

for i in $(seq 1 10); do
  RESPONSE=$(curl -k -s https://localhost:8443 2>&1)
  if echo "$RESPONSE" | grep -q "Valkyria"; then
    echo "  Request $i: OK"
    SUCCESS=$((SUCCESS + 1))
  else
    echo "  Request $i: FAILED"
    echo "    Response: $RESPONSE"
    FAILED=$((FAILED + 1))
  fi
  sleep 0.2
done

echo ""
echo "Results: $SUCCESS successful, $FAILED failed"

if kill -0 $SERVERPID 2>/dev/null; then
  echo "✓ Server still running"
  kill -TERM $SERVERPID 2>/dev/null
  wait $SERVERPID 2>/dev/null || true
  exit 0
else
  echo "✗ Server crashed"
  exit 1
fi
