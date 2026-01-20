# AGENTS.md - Valkyria Lisp Interpreter (C23)

## Build & Test Commands
- `make build` - Build into `build/` (CMake+Ninja)
- `make test` - Run all C and Valk tests
- `make lint` - Run clang-tidy (must pass before committing)
- `make coverage` - Generate aggregated C+Valk coverage (HTML: `coverage-report/index.html`)
- `python3 scripts/find-uncovered-branches.py <file.c>` - Find specific uncovered branches
- Single C test: `build/test_memory` (binary name matches `test/*.c`)
- Single Valk test: `build/valk test/test_prelude.valk`
- ASAN tests: `make test-c-asan`, `make test-valk-asan`
- TSAN tests: `make test-c-tsan`, `make test-valk-tsan`

## Sanitizer Output (CRITICAL)
Sanitizer output can flood context. **Always redirect to file, then summarize.**

```bash
# TSAN - redirect and summarize
TSAN_OPTIONS="log_path=build/tsan.log" make test-c-tsan
echo "TSAN: $(grep -c 'WARNING: ThreadSanitizer' build/tsan.log 2>/dev/null || echo 0) races"
grep -A2 "WARNING: ThreadSanitizer" build/tsan.log | grep "#0" | sort -u | head -5

# ASAN - redirect and summarize  
ASAN_OPTIONS="log_path=build/asan.log" make test-c-asan
grep -c "ERROR: AddressSanitizer" build/asan.log 2>/dev/null || echo "0 errors"
```

**NEVER** run sanitizer tests without redirecting output - it will flood your context.

## Code Style
- C23 with GNU extensions, 2-space indent, no comments unless essential
- `snake_case` for functions/variables, `UPPER_SNAKE` for macros
- `*_t` suffix for types, `*_e` for enums, `valk_` prefix for public symbols
- Headers mirror sources: `memory.c` -> `memory.h`
- DO NOT ADD COMMENTS to code unless explicitly asked

## Project Layout
- `src/` - C runtime + `.valk` stdlib; core: `parser.c`, `memory.c`, `gc.c`
- `test/` - `test_*.c` (C) and `test_*.valk` (Lisp); `stress/` for long tests
- `build/` - Generated; never commit

## Error Handling
- Return `valk_lval_err()` for recoverable errors in builtins
- Use `VALK_ASSERT()` for invariant violations

## Defensive Code Principles

### Validate at API Boundaries, Trust Internally
- Type checking happens via `LVAL_ASSERT_TYPE` in builtins (parser.c)
- Internal functions trust these guarantees - no redundant type/null checks
- Don't re-validate what the API boundary already guarantees

### Don't Sanity-Check Other Subsystems
- If GC is broken, fix GC - don't scatter forward-pointer checks everywhere
- If memory is corrupted, fix the corruption source - don't add magic number validation
- Each subsystem is responsible for its own correctness

### LCOV Exclusions - Only for Truly Untestable Code
Use `// LCOV_EXCL_START` / `// LCOV_EXCL_STOP` ONLY for:
- OOM paths (malloc/aligned_alloc failures)
- Platform API failures that essentially never fail (e.g., uv_timer_init)
- Impossible branches required by API contracts

DO NOT exclude:
- Error handling that can be triggered by bad input
- Callback paths that just need integration tests
- Code that's "hard to test" but not impossible

### Anti-Patterns to Remove
When refactoring, eliminate these patterns:
- **Magic number validation**: `if (x->magic != EXPECTED_MAGIC)` - unreliable, masks real bugs
- **Forward pointer chasing**: `while (val->forward) val = val->forward` - GC's job, not caller's
- **Redundant null/type checks**: Already validated at API boundary
- **Atomic loads/stores**: Unnecessary with stop-the-world GC
- **Debug fprintf/tracing**: Remove or gate behind compile-time flag

## Required Workflow (CRITICAL - MUST FOLLOW)

### Before ANY Code Change
1. READ the file(s) you intend to modify - NEVER edit without reading first
2. Understand the existing code conventions and patterns
3. Verify any libraries/utilities exist before using them

### After ANY Code Change
1. Run `make build` to verify compilation succeeds
2. Run `make test` to verify all tests pass
3. If ANYTHING fails, fix it immediately and re-run
4. ONLY report completion after build AND tests pass

### Task Completion Rules
- NEVER mark a task complete if tests are failing
- NEVER mark a task complete if build is broken
- NEVER mark a task complete if implementation is partial
- NEVER stop mid-task - continue until fully done or user stops you
- NEVER claim a task is "too large" - break it down and complete it

## Communication Style
- Be concise and direct - no fluff
- Don't add preamble like "I'll help you with that" - just do it
- Don't use sycophantic phrases like "Great question!"
- Prioritize accuracy over validation

## Debugging Flaky Tests and Crashes

### Approach: Post-Mortem, Not Logging
Don't add logging to debug transient issues - you can never log enough, and logging changes timing.
Instead, capture full execution state on failure via core dumps or rr recordings.

### When a Test Fails (MANDATORY WORKFLOW)

**Step 1: If it's a crash (SIGSEGV, SIGABRT), check core dumps first:**
```bash
make cores                         # List recent crashes
make debug-core                    # Debug most recent crash in GDB
```

**Step 2: If it's a flaky/intermittent failure, capture with rr:**
```bash
# Run until failure (for flaky tests)
make test-rr-until-fail TEST=test_networking MAX=100

# Replay the recording
rr replay
```

**Step 3: In rr replay, find root cause:**
```gdb
reverse-continue     # Run backwards to previous breakpoint/watchpoint
reverse-step         # Step backwards
watch -l variable    # Hardware watchpoint - stops when value changes
                     # Then reverse-continue to find who changed it
when                 # Show current event number
run 12345            # Jump to specific event
```

### Known Flaky Tests (test/flaky.txt)
Tests listed in `test/flaky.txt` are known to be flaky. Run them under rr:
```bash
make test-flaky      # Run all flaky tests under rr, recordings saved on failure
```

When adding a new flaky test to the list, or when a flaky test fails:
1. Add/keep the test in `test/flaky.txt`
2. Run `make test-flaky` to get a recording
3. Debug with `rr replay`
4. Fix the root cause
5. Remove from `test/flaky.txt` once stable

### Core Dumps (for crashes/SIGSEGV)
Core dumps are already captured automatically via systemd-coredump:
```bash
make cores                         # List recent crashes
make debug-core                    # Debug most recent crash in GDB
coredumpctl debug test_networking  # Debug specific crash
```

### Time-Travel Debugging with rr (for flaky tests)
rr records execution deterministically. Replay unlimited times, step backwards, find root cause.

```bash
# Setup (one-time)
apt install rr
echo 1 | sudo tee /proc/sys/kernel/perf_event_paranoid

# Record a single test
RR=1 make test-c TEST=test_networking
RR=1 make test-valk TEST=test/test_http_integration.valk

# Record with chaos mode (exposes races)
RR=chaos make test-c TEST=test_networking

# Run until failure (for flaky tests)
make test-rr-until-fail TEST=test_networking MAX=100

# Replay the recording
rr replay
```

### ASAN/TSAN with Core Dumps
```bash
make test-asan-abort  # ASAN failures produce core dumps
make test-core        # Run tests with core dumps enabled
```

### macOS Alternatives (no rr)
macOS doesn't have rr. Use these alternatives:

```bash
# Core dumps (enable first: sudo sysctl kern.coredump=1)
make cores                    # List /cores/
lldb -c /cores/core.PID build/test_networking

# Debug directly
lldb -- build/test_networking

# Run until failure, then debug
for i in {1..100}; do build/test_networking || break; done
lldb -- build/test_networking

# Use Instruments for profiling/tracing
xcrun xctrace record --template 'Time Profiler' --launch -- build/test_networking
```

## Debugging Hangs and Concurrency Issues

### When Tests Hang
1. **Identify the hanging test** - run tests individually with timeout:
   ```bash
   for test in test/*.valk; do
     echo -n "$test: "
     timeout 15 build/valk "$test" >/dev/null 2>&1 && echo "PASS" || echo "TIMEOUT"
   done
   ```

2. **Use rr to capture the hang** (preferred over adding prints):
   ```bash
   RR=chaos make test-c TEST=test_networking
   # When it hangs, Ctrl+C, then:
   rr replay
   # In GDB: info threads, thread apply all bt
   ```

3. **Check for GC coordination deadlocks** - common patterns:
   - Event loop thread stuck in `valk_gc_safe_point_slow()` waiting for `gc_done`
   - Main thread stuck in `valk_checkpoint_request_stw()` waiting for threads to pause
   - Race between checkpoint release and next checkpoint request

### GC Coordination Architecture
- Main thread calls `valk_checkpoint()` between top-level expressions (repl.c)
- `valk_checkpoint_request_stw()` sets phase to CHECKPOINT_REQUESTED
- Event loop threads respond via `__gc_wakeup_cb` -> `valk_gc_safe_point_slow()`
- `valk_checkpoint_release_stw()` broadcasts `gc_done` to wake waiting threads

### Key Concurrency Invariants
- `valk_gc_thread_register()` must happen BEFORE `uv_sem_post` in event loop startup
- `valk_gc_safe_point_slow()` must NOT re-enter wait loop if a new checkpoint starts
- `uv_async_send()` to `gc_wakeup` wakes event loop for GC coordination

### Adding Debug Output (LAST RESORT)
Only if rr is not available. Always remove after fixing.
```c
fprintf(stderr, "[GC] checkpoint: phase=%d paused=%llu/%llu\n",
        phase, paused, registered);
```

## What NOT To Do
- Don't make changes without reading code first
- Don't skip running tests after changes
- Don't add comments unless explicitly asked
- Don't commit unless explicitly asked
- Don't add unnecessary abstractions
- Don't create documentation files unless asked
