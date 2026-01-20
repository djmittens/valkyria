---
name: cpu-profile
description: CPU profiling with perf (Linux) and Instruments/sample (macOS) - find hotspots, analyze cache misses, and optimize performance
license: MIT
metadata:
  platform: linux,macos
  category: profiling
---

# CPU Profiling for Valkyria

Profile CPU usage to find performance bottlenecks, hot functions, and optimization opportunities.

## Linux: perf

perf is the standard Linux profiler with low overhead.

### Basic Profiling

```bash
# Record CPU samples (99 Hz to avoid lockstep sampling)
perf record -F 99 -g build/valk src/prelude.valk test/test_prelude.valk

# View report
perf report

# Text report
perf report --stdio

# View annotated source (requires debug symbols)
perf annotate valk_lval_eval
```

### Profiling Options

```bash
# System-wide profiling
perf record -F 99 -a -g -- sleep 30

# Profile specific process
perf record -F 99 -p $(pgrep valk) -g -- sleep 30

# Profile with call graph (frame pointer)
perf record -F 99 -g --call-graph fp build/valk src/prelude.valk

# Profile with DWARF unwinding (works without frame pointers)
perf record -F 99 -g --call-graph dwarf build/valk src/prelude.valk

# Profile with LBR (Last Branch Record, Intel)
perf record -F 99 -g --call-graph lbr build/valk src/prelude.valk
```

### perf stat (Counters)

```bash
# Basic CPU counters
perf stat build/valk src/prelude.valk test/test_prelude.valk

# Detailed counters
perf stat -d build/valk src/prelude.valk

# Specific events
perf stat -e cycles,instructions,cache-misses,branch-misses build/valk src/prelude.valk

# IPC (Instructions Per Cycle)
perf stat -e cycles,instructions build/valk src/prelude.valk
# IPC = instructions / cycles (higher is better, max ~4-6 on modern CPUs)
```

### perf top (Live View)

```bash
# Live profiling (system-wide)
perf top

# For specific process
perf top -p $(pgrep valk)

# With call graph
perf top -g
```

### Advanced Events

```bash
# Cache analysis
perf stat -e L1-dcache-loads,L1-dcache-load-misses,LLC-loads,LLC-load-misses \
  build/valk src/prelude.valk

# Branch prediction
perf stat -e branches,branch-misses build/valk src/prelude.valk

# Memory bandwidth (needs PMU support)
perf stat -e mem_load_retired.l3_miss build/valk src/prelude.valk

# List available events
perf list
```

### Specific Analysis

```bash
# Find cache-miss hotspots
perf record -e cache-misses -g build/valk src/prelude.valk
perf report

# Find branch misprediction hotspots
perf record -e branch-misses -g build/valk src/prelude.valk
perf report

# Memory access patterns
perf mem record build/valk src/prelude.valk
perf mem report
```

## macOS: Instruments

Instruments is Apple's profiling tool with a rich GUI.

### Time Profiler

```bash
# GUI
open -a Instruments

# Or launch from Xcode: Product -> Profile (Cmd+I)
```

In Instruments:
1. Choose "Time Profiler" template
2. Click the target dropdown, choose "Other..."
3. Navigate to `build/valk`
4. Add arguments: `src/prelude.valk test/test_prelude.valk`
5. Click Record

### Command-Line Profiling

```bash
# sample command (built-in)
sample valk -wait -file profile.txt

# Attach to running process
sample $(pgrep valk) 10 -file profile.txt  # 10 seconds

# View profile
cat profile.txt
```

### xctrace (Modern CLI)

```bash
# Record with Time Profiler
xcrun xctrace record --template "Time Profiler" \
  --output profile.trace \
  --launch -- build/valk src/prelude.valk

# View in Instruments
open profile.trace

# Export symbols
xcrun xctrace export --input profile.trace --output profile.xml
```

### Activity Monitor

For quick checks, Activity Monitor (Applications/Utilities) shows:
- CPU usage per process
- Threads
- Energy impact
- Sample process (double-click process -> Sample)

## Interpreting Results

### perf report Output

```
Overhead  Command  Shared Object     Symbol
  25.00%  valk     valk              [.] valk_lval_eval
  15.00%  valk     valk              [.] valk_gc_mark
  10.00%  valk     libc.so.6         [.] malloc
   5.00%  valk     [kernel.vmlinux]  [k] copy_page
```

- **Overhead**: Percentage of samples in this function
- **Command**: Process name
- **Shared Object**: Binary/library
- **Symbol**: Function name (`[.]` = user, `[k]` = kernel)

### Hot Spots

1. Look for functions with high overhead (>5%)
2. Check if kernel time is significant (may indicate I/O or syscall overhead)
3. Look at call graph to understand context

### Instruments Analysis

1. **Call Tree**: Shows time spent in each function including callees
2. **Heaviest Stack Trace**: Path taking most time
3. **Self Weight**: Time in function itself (not callees)
4. **Total Weight**: Time including callees

## Profiling Scenarios

### Find CPU Hotspots

```bash
# Linux
perf record -F 99 -g build/valk src/prelude.valk test/test_prelude.valk
perf report --sort=overhead --stdio | head -20

# macOS
sample valk 10 -file profile.txt
grep -A2 "Sort by" profile.txt | head -20
```

### Check IPC (Instruction Efficiency)

```bash
# Linux
perf stat -e cycles,instructions,cache-references,cache-misses build/valk src/prelude.valk

# Interpret:
# IPC < 1.0 = likely memory-bound
# IPC > 2.0 = compute-efficient
# High cache-miss ratio = memory access pattern issues
```

### Profile Memory Allocation

```bash
# Linux - trace malloc/free
perf probe -x /lib/x86_64-linux-gnu/libc.so.6 --add malloc
perf probe -x /lib/x86_64-linux-gnu/libc.so.6 --add free
perf record -e probe_libc:malloc,probe_libc:free -g build/valk src/prelude.valk
perf report

# Or use BPF (if available)
# sudo bpftrace -e 'uprobe:/lib/x86_64-linux-gnu/libc.so.6:malloc { @[ustack] = count(); }'
```

### Compare Before/After

```bash
# Baseline
perf stat -r 5 build/valk src/prelude.valk test/test_prelude.valk 2>&1 | tee baseline.txt

# After optimization
perf stat -r 5 build/valk src/prelude.valk test/test_prelude.valk 2>&1 | tee optimized.txt

# Compare
diff baseline.txt optimized.txt
```

## Project-Specific Profiling

### Profile GC

```bash
# Focus on GC functions
perf record -g build/valk src/prelude.valk test/test_prelude.valk
perf report --symbol-filter='gc'
```

### Profile Parser

```bash
# Use perf with source annotation
perf record -g build/valk src/prelude.valk
perf annotate valk_lval_read
perf annotate valk_lval_eval
```

### Profile Event Loop

```bash
# Focus on libuv/event loop
perf record -g build/valk src/prelude.valk
perf report --symbol-filter='uv_'
```

## Building for Profiling

```bash
# Ensure frame pointers are preserved (for call graphs)
# Add to CMakeLists.txt or CFLAGS:
-fno-omit-frame-pointer

# Or use DWARF unwinding with perf:
perf record --call-graph dwarf build/valk src/prelude.valk
```

## Tips

1. Use 99Hz or 997Hz sampling to avoid lockstep artifacts
2. Profile realistic workloads, not micro-benchmarks
3. Check kernel vs user time - high kernel may mean I/O bound
4. Use `-g` for call graphs - essential for understanding context
5. Profile multiple runs for statistical significance (`perf stat -r 5`)
6. Look at IPC first - low IPC suggests memory/cache issues
7. Use `perf annotate` to see hot instructions
8. Generate flame graphs for visualization (see flamegraph skill)
9. On macOS, use Instruments for detailed analysis
10. Compare profiles before/after changes quantitatively
