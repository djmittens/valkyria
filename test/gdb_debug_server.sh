#!/bin/bash
# Debug server crash with GDB

# Create GDB command file
cat > /tmp/gdb_commands.txt << 'EOF'
# Run the server
run examples/hello_server.valk

# When it crashes, print backtrace
backtrace
thread apply all backtrace
info threads
print conn
print conn->handle
quit
EOF

echo "Starting server under GDB..."
echo "The server will run and GDB will catch the crash."
echo ""

# Run under GDB
gdb -batch -x /tmp/gdb_commands.txt build/valk 2>&1 | tee /tmp/gdb_output.txt &
GDB_PID=$!

# Wait for server to start
sleep 3

echo "Making requests to trigger crash..."

# Make multiple requests to trigger the crash
for i in {1..5}; do
  echo "Request $i..."
  curl -k -s https://localhost:8443 > /dev/null 2>&1 || true
  sleep 0.3
done

# Wait for GDB to finish
wait $GDB_PID || true

echo ""
echo "GDB output saved to /tmp/gdb_output.txt"
echo ""
echo "Key information:"
grep -A 20 "Program received signal\|Program terminated" /tmp/gdb_output.txt || echo "No crash detected in output"
