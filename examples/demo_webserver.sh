#!/bin/bash
# Demonstration of Valkyria HTTP/2 Web Server
#
# This script starts the server, makes a test request, and shows the results.

set -e

echo "╔════════════════════════════════════════════════════════════╗"
echo "║       Valkyria HTTP/2 Web Server Demonstration            ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Clean up any existing servers
pkill -9 valk 2>/dev/null || true
sleep 1

echo "→ Starting REST API demo server..."
build/valk examples/rest_api_demo.valk > /tmp/server_output.txt 2>&1 &
SERVER_PID=$!

# Wait for server to start
sleep 3

if ! kill -0 $SERVER_PID 2>/dev/null; then
  echo "✗ Server failed to start"
  cat /tmp/server_output.txt
  exit 1
fi

echo "✓ Server started (PID: $SERVER_PID)"
echo ""

echo "→ Making test request to https://localhost:8443"
echo ""

RESPONSE=$(curl -k -s https://localhost:8443 2>&1)

if echo "$RESPONSE" | grep -q "Valkyria"; then
  echo "✓ Request successful!"
  echo ""
  echo "Response:"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo "$RESPONSE"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo ""
  SUCCESS=true
else
  echo "✗ Request failed"
  echo "Response: $RESPONSE"
  SUCCESS=false
fi

echo ""
echo "→ Stopping server..."
kill -TERM $SERVER_PID 2>/dev/null || kill -KILL $SERVER_PID 2>/dev/null || true
wait $SERVER_PID 2>/dev/null || true

if [ "$SUCCESS" = true ]; then
  echo "✓ Demo completed successfully!"
  echo ""
  echo "Try it yourself:"
  echo "  ./build/valk examples/rest_api_demo.valk"
  echo ""
  echo "Then in another terminal:"
  echo "  curl -k https://localhost:8443"
  exit 0
else
  echo "✗ Demo failed"
  exit 1
fi
