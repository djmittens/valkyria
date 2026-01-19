# Dashboard Concurrency & SSE Validation

## Overview

Validate the ralph debug dashboard under high concurrency conditions. This spec covers SSE (Server-Sent Events) streaming, metrics system correctness, FIFO communication, thread safety, and UI responsiveness under stress.

## Background

The ralph dashboard has multiple concurrent systems:
1. **FIFO communication** (`output.fifo`) - named pipe for watch mode
2. **Output streaming** - thread that reads process stdout and updates buffer
3. **Metrics parsing** - cost/token extraction from stream
4. **UI rendering** - Textual TUI or ANSI fallback dashboard
5. **Keyboard input** - non-blocking stdin polling with key coalescing

## Requirements

### 1. Thread-Safe Output Buffer

The `OutputBuffer` class must handle concurrent writes from the reader thread and reads from the UI thread without data corruption or deadlocks.

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T1.1 | Concurrent writer stress | 10 threads writing 1000 lines each simultaneously; all 10000 lines present in buffer |
| T1.2 | Reader during heavy writes | UI thread reads while writer thread is actively appending; no exceptions, no missing lines |
| T1.3 | Buffer overflow handling | Write 5000 lines (exceeds maxlen=100 for lines deque); oldest lines evicted, newest retained |
| T1.4 | total_output accumulation | Verify total_output list captures ALL lines regardless of lines deque overflow |

### 2. FIFO Communication

The named pipe (`output.fifo`) must handle disconnections, reconnections, and multiple watchers gracefully.

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T2.1 | FIFO creation | `cmd_run` creates FIFO if missing, replaces regular file if exists |
| T2.2 | Writer without reader | Writing to FIFO with no reader doesn't block (O_RDWR mode) |
| T2.3 | Reader reconnect | Watcher disconnects and reconnects; resumes receiving new lines |
| T2.4 | Multiple watchers | Two `ralph watch` processes receive same stream data |
| T2.5 | FIFO cleanup on error | OSError during FIFO write closes fd and retries next write |

### 3. Metrics Parsing

The `parse_cost_line` function and metrics accumulation must correctly extract cost/token data from stream output.

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T3.1 | Valid cost line parsing | `"\x00Cost: $0.1234 \| Tokens: 5000in/1000out"` → (0.1234, 5000, 1000) |
| T3.2 | Hidden metrics filtering | Lines starting with `\x00` not added to display buffer |
| T3.3 | Metrics accumulation | Multiple cost lines update metrics.total_cost, metrics.total_tokens_in, metrics.total_tokens_out |
| T3.4 | Malformed cost lines | Invalid format returns None, doesn't crash |
| T3.5 | Cache token handling | `cache.read` tokens added to input count |

### 4. FallbackDashboard Thread Safety

The ANSI fallback dashboard must handle concurrent state updates and input without races.

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T4.1 | Scroll coalescing | Hold 'j' key for 100 rapid presses; scroll_delta coalesces into single offset update |
| T4.2 | Auto-scroll tracking | New lines while auto_scroll=True keep view at bottom |
| T4.3 | Manual scroll disables auto | Pressing 'k' sets auto_scroll=False |
| T4.4 | Terminal resize | SIGWINCH during render doesn't crash |
| T4.5 | Non-blocking input | get_input() returns immediately when no input available |

### 5. Textual TUI Concurrency

The Textual-based dashboard must handle async workers, process monitoring, and reactive updates correctly.

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T5.1 | FIFO reader worker | Background worker reads FIFO without blocking UI |
| T5.2 | Process monitor exit | When monitored process exits, app exits within 0.5s |
| T5.3 | Output log append from thread | `call_from_thread` safely appends to RichLog |
| T5.4 | Reactive property updates | StatusPanel updates when branch/cost/status change |
| T5.5 | Follow mode toggle | 'f' key toggles follow_mode, updates header indicator |

### 6. Stream Processing Pipeline

The `opencode | ralph stream` pipeline must handle JSON parsing, tool events, and metrics extraction.

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T6.1 | Text event | `{"type":"text","part":{"text":"hello"}}` outputs formatted text |
| T6.2 | Tool use events | bash/read/edit/write/grep/glob/task tools display with correct emoji/color |
| T6.3 | Step finish metrics | `step_finish` event outputs hidden metrics line (`\x00Cost:...`) |
| T6.4 | Invalid JSON skip | Malformed JSON lines skipped without error |
| T6.5 | Streaming throughput | 1000 events/second processed without backpressure |

### 7. Run Loop Concurrency

The main `cmd_run` loop must handle process spawning, threading, and cleanup correctly.

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T7.1 | Reader thread join | Thread joins within 1s timeout after process exits |
| T7.2 | Keyboard interrupt cleanup | Ctrl+C terminates process, joins thread, restores terminal |
| T7.3 | Process termination | 'q' in UI sends SIGTERM to child process |
| T7.4 | Exit code propagation | Non-zero exit from opencode increments consecutive_failures |
| T7.5 | Metrics sync to dashboard | Dashboard displays same cost as metrics object |

### 8. Watch Mode Concurrency

The `cmd_watch` and `_cmd_watch_fallback` functions must handle continuous monitoring.

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T8.1 | Process count detection | `count_running_opencode` correctly counts ralph-spawned opencode processes |
| T8.2 | Periodic expensive updates | Branch/process count refresh every 1s, not every frame |
| T8.3 | FIFO reconnect loop | FIFO fd closed and reopened after read error |
| T8.4 | State file reload | Dashboard reflects plan.jsonl changes from external mutations |
| T8.5 | Clean exit | Ctrl+C restores terminal state (cursor, alternate screen) |

### 9. Edge Cases & Error Recovery

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T9.1 | Missing FIFO | Watch mode continues polling until FIFO appears |
| T9.2 | Broken pipe recovery | FIFO write failure closes fd, next write reopens |
| T9.3 | Empty output buffer | Dashboard renders correctly with no output lines |
| T9.4 | Very long lines | 10KB line truncated for display, stored in full |
| T9.5 | Unicode handling | UTF-8, emoji, ANSI codes preserved through pipeline |
| T9.6 | Rapid iteration restarts | 10 iterations in quick succession don't leak threads/fds |

### 10. Integration Scenarios

End-to-end scenarios testing the full system under realistic conditions.

#### Tests

| ID | Test | Acceptance |
|----|------|------------|
| T10.1 | Build with watch | `ralph` in one terminal, `ralph watch` in another; watch receives all output |
| T10.2 | High-frequency output | Process outputting 100 lines/sec displays smoothly at 60fps |
| T10.3 | Long-running session | 1 hour simulated session with periodic output; no memory growth |
| T10.4 | Multiple specs | Switch specs mid-session; dashboard updates correctly |
| T10.5 | Network push during render | `git push` during dashboard render doesn't cause glitch |

## Test Implementation Notes

### Test Harness Requirements

1. **Mock subprocess** - Simulate opencode output without actual AI calls
2. **Time control** - Fast-forward periodic timers for testing refresh intervals
3. **PTY simulation** - Test terminal handling without real terminal
4. **Thread synchronization** - Barriers and events to create race conditions
5. **Memory profiling** - Track allocations to detect leaks

### Instrumentation Points

Add optional debug counters (gated by `RALPH_DEBUG=1`):
- `_debug_buffer_writes` - total OutputBuffer.add() calls
- `_debug_fifo_writes` - total FIFO write attempts
- `_debug_fifo_errors` - FIFO write failures
- `_debug_render_frames` - dashboard render calls
- `_debug_input_events` - keyboard events processed

### Test File Structure

```
test/
  test_dashboard_buffer.py      # T1.x tests
  test_dashboard_fifo.py        # T2.x tests
  test_dashboard_metrics.py     # T3.x tests
  test_dashboard_fallback.py    # T4.x tests
  test_dashboard_textual.py     # T5.x tests (requires textual)
  test_stream_processing.py     # T6.x tests
  test_run_loop.py              # T7.x tests
  test_watch_mode.py            # T8.x tests
  test_edge_cases.py            # T9.x tests
  test_integration.py           # T10.x tests (slow, marked)
```

## Acceptance Criteria

The spec is complete when:
1. All 50 tests implemented and passing
2. No flaky tests (run 10x each)
3. Test coverage > 90% for dashboard-related code paths
4. No memory leaks detected in 1-hour stress test
5. Manual verification of smooth 60fps rendering under load
