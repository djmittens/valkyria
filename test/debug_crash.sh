#!/bin/bash
# Start server in background and get core dump on crash

# Enable core dumps
ulimit -c unlimited

# Run server
build/valk examples/hello_server.valk &
PID=$!

sleep 2

# Make requests until it crashes
for i in {1..10}; do
  echo "Request $i..."
  curl -k -s https://localhost:8443 > /dev/null 2>&1 || true
  sleep 0.2

  # Check if still alive
  if ! kill -0 $PID 2>/dev/null; then
    echo "Server crashed on request $i"
    ls -lh core* 2>/dev/null || echo "No core dump found"
    exit 1
  fi
done

echo "Server survived 10 requests"
kill -TERM $PID 2>/dev/null
exit 0
