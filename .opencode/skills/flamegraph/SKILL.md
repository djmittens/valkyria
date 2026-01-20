---
name: flamegraph
description: Generate flame graphs from profiling data - visualize CPU hotspots, off-CPU time, memory allocations, and call stacks
license: MIT
metadata:
  platform: linux,macos
  category: profiling
---

# Flame Graphs for Valkyria

Flame graphs visualize profiled stack traces, making it easy to identify performance bottlenecks at a glance.

## Quick Start

### Install FlameGraph Tools

```bash
# Clone Brendan Gregg's FlameGraph repository
git clone https://github.com/brendangregg/FlameGraph.git
export PATH="$PATH:$(pwd)/FlameGraph"

# Or on macOS with Homebrew
brew install flamegraph
```

### Generate a CPU Flame Graph (Linux)

```bash
# Record with perf
perf record -F 99 -g build/valk src/prelude.valk test/test_prelude.valk

# Generate flame graph
perf script | stackcollapse-perf.pl | flamegraph.pl > cpu.svg

# Open in browser
xdg-open cpu.svg  # Linux
open cpu.svg      # macOS
```

## Linux: perf-based Flame Graphs

### CPU Flame Graph

```bash
# Record (99 Hz sampling, call graphs)
perf record -F 99 -g build/valk src/prelude.valk test/test_prelude.valk

# Convert to flame graph
perf script | stackcollapse-perf.pl | flamegraph.pl > cpu.svg

# Or save intermediate file for filtering
perf script > out.perf
stackcollapse-perf.pl out.perf > out.folded
flamegraph.pl out.folded > cpu.svg
```

### Filtered Flame Graphs

```bash
# Create folded file
perf script | stackcollapse-perf.pl > out.folded

# Filter for specific functions
grep valk_gc out.folded | flamegraph.pl > gc.svg
grep valk_lval_eval out.folded | flamegraph.pl > eval.svg

# Exclude idle
grep -v cpu_idle out.folded | flamegraph.pl > active.svg
```

### Differential Flame Graphs

Compare before/after:
```bash
# Baseline profile
perf record -F 99 -g -o perf-baseline.data build/valk src/prelude.valk
perf script -i perf-baseline.data | stackcollapse-perf.pl > baseline.folded

# After optimization
perf record -F 99 -g -o perf-optimized.data build/valk src/prelude.valk
perf script -i perf-optimized.data | stackcollapse-perf.pl > optimized.folded

# Generate diff flame graph (red = regression, blue = improvement)
difffolded.pl baseline.folded optimized.folded | flamegraph.pl > diff.svg
```

## macOS: dtrace-based Flame Graphs

### CPU Flame Graph

```bash
# Sample user stacks
sudo dtrace -x ustackframes=100 -n '
  profile-99 /execname == "valk"/ {
    @[ustack()] = count();
  }
  tick-30s { exit(0); }
' -o out.stacks

# Convert to flame graph
stackcollapse.pl out.stacks | flamegraph.pl > cpu.svg
```

### Using sample Command

```bash
# Sample for 30 seconds
sample valk 30 -f sample.txt

# Convert (need a converter script)
# Note: sample output needs custom parsing
```

## Flame Graph Types

### CPU On-CPU Flame Graph

Shows where CPU time is spent (functions executing on CPU).

```bash
# Linux
perf record -F 99 -g build/valk src/prelude.valk
perf script | stackcollapse-perf.pl | flamegraph.pl > cpu-on.svg
```

### Off-CPU Flame Graph

Shows where time is spent waiting (I/O, locks, sleep).

```bash
# Linux (requires BPF tools)
# Install bcc-tools first
sudo offcputime-bpfcc -df -p $(pgrep valk) 30 > out.offcpu
flamegraph.pl --color=io --title="Off-CPU" out.offcpu > offcpu.svg

# Or with perf sched
perf sched record -g build/valk src/prelude.valk
perf script | stackcollapse-perf.pl | flamegraph.pl --color=io > offcpu.svg
```

### Memory Flame Graph

Shows where memory is allocated.

```bash
# Linux with BPF
sudo memleak-bpfcc -p $(pgrep valk) -af > out.memleak
flamegraph.pl --color=mem --title="Memory Allocations" out.memleak > memory.svg

# Or trace malloc with perf
perf probe -x /lib/x86_64-linux-gnu/libc.so.6 --add malloc
perf record -e probe_libc:malloc -g build/valk src/prelude.valk
perf script | stackcollapse-perf.pl | flamegraph.pl --color=mem > malloc.svg
```

### Hot/Cold Flame Graph

Combine on-CPU and off-CPU for full picture.

```bash
# Requires both on-CPU and off-CPU data, then merge
cat oncpu.folded offcpu.folded | flamegraph.pl --color=chain > hotcold.svg
```

## Flame Graph Options

```bash
# flamegraph.pl options
flamegraph.pl \
  --title "Valkyria CPU Profile" \
  --subtitle "build/valk src/prelude.valk" \
  --width 1200 \
  --height 16 \        # Per-frame height
  --minwidth 0.1 \     # Min % width to show
  --fonttype "Verdana" \
  --fontsize 12 \
  --countname "samples" \
  --nametype "Function:" \
  --colors hot \       # hot, mem, io, wakeup, java, perl, js
  --hash \             # Consistent colors for same function
  --reverse \          # Reverse stack order
  --inverted \         # Icicle graph (top-down)
  out.folded > flame.svg
```

### Color Schemes

```bash
# CPU hot (default)
flamegraph.pl --colors hot out.folded > cpu.svg

# Memory allocations
flamegraph.pl --colors mem out.folded > mem.svg

# I/O related
flamegraph.pl --colors io out.folded > io.svg

# Java-style (green=Java, yellow=C++, orange=kernel)
flamegraph.pl --colors java out.folded > java.svg

# For C code, use hash for consistent colors
flamegraph.pl --hash out.folded > cpu.svg
```

## Reading Flame Graphs

### X-Axis

- Width = frequency (how often this stack was sampled)
- Wider = more time spent
- Order is alphabetical (not chronological!)

### Y-Axis

- Stack depth
- Bottom = root (main, start_thread)
- Top = currently executing function

### Colors

- Default: random warm colors (no meaning)
- With `--hash`: same function gets same color
- With `--colors java`: green=Java, yellow=native, red=kernel

### Interpreting

1. **Plateaus at top**: Function doing actual work
2. **Wide base, narrow top**: Many callers, one hot function
3. **Wide tower**: Single hot code path
4. **Lots of thin spikes**: Diverse workload or interrupt noise

## Project-Specific Examples

### Profile GC Performance

```bash
# Record
perf record -F 99 -g build/valk src/prelude.valk test/test_prelude.valk

# GC-specific flame graph
perf script | stackcollapse-perf.pl > out.folded
grep -E "gc_|GC" out.folded | flamegraph.pl --title "GC Profile" > gc.svg
```

### Profile Parser

```bash
perf script | stackcollapse-perf.pl > out.folded
grep -E "parse|read|eval" out.folded | flamegraph.pl --title "Parser Profile" > parser.svg
```

### Profile Event Loop

```bash
perf script | stackcollapse-perf.pl > out.folded
grep -E "uv_|libuv|epoll|kqueue" out.folded | flamegraph.pl --title "Event Loop" > eventloop.svg
```

### Compare ASAN vs Normal Build

```bash
# Normal build profile
perf record -F 99 -g -o perf-normal.data build/valk src/prelude.valk test/test_prelude.valk
perf script -i perf-normal.data | stackcollapse-perf.pl > normal.folded

# ASAN build profile
perf record -F 99 -g -o perf-asan.data build-asan/valk src/prelude.valk test/test_prelude.valk
perf script -i perf-asan.data | stackcollapse-perf.pl > asan.folded

# Diff
difffolded.pl normal.folded asan.folded | flamegraph.pl --title "ASAN Overhead" > asan-diff.svg
```

## Alternative Tools

### speedscope (Interactive)

```bash
# Install
npm install -g speedscope

# Convert and open
perf script | speedscope -

# Or save and open
perf script > perf.txt
speedscope perf.txt
```

### Firefox Profiler

```bash
# Export perf data
perf script -F +pid > profile.perf

# Import at https://profiler.firefox.com/
```

### Hotspot (GUI for Linux)

```bash
# Install
sudo apt install hotspot  # or build from source

# Profile and open
perf record -g build/valk src/prelude.valk
hotspot
```

## Automated Script

Create `scripts/flamegraph.sh`:
```bash
#!/bin/bash
# Usage: ./scripts/flamegraph.sh [output.svg] [extra args...]

OUTPUT="${1:-cpu.svg}"
shift

# Record
perf record -F 99 -g -- "$@"

# Generate
perf script | stackcollapse-perf.pl | flamegraph.pl \
  --title "Valkyria CPU Profile" \
  --hash \
  > "$OUTPUT"

echo "Generated: $OUTPUT"

# Open if possible
if command -v xdg-open &>/dev/null; then
  xdg-open "$OUTPUT"
elif command -v open &>/dev/null; then
  open "$OUTPUT"
fi
```

Usage:
```bash
./scripts/flamegraph.sh profile.svg build/valk src/prelude.valk
```

## Tips

1. **Sample at 99/997 Hz** - avoid lockstep with timers
2. **Use `--hash`** for consistent colors across runs
3. **Filter with grep** before generating - focus on areas of interest
4. **Diff flame graphs** to see impact of changes
5. **Check top plateaus** first - that's where work happens
6. **Wide towers** indicate hot paths worth optimizing
7. **Many thin spikes** may indicate profiling noise
8. **Use `--reverse --inverted`** to see callers (who called this?)
9. **Interactive SVG** - click to zoom, mouse over for details
10. **Save folded files** - they're small and can regenerate graphs
