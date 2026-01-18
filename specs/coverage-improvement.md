# Coverage Improvement

## Overview

Improve test coverage for all runtime code in `src/` to meet requirements:
- **90% line coverage**
- **85% branch coverage**

## Current State

35 files are below threshold. Priority files (sorted by gap to target):

### Critical Priority (>50% gap)
| File | Line | Branch | Line Gap | Branch Gap |
|------|------|--------|----------|------------|
| aio/aio_ctx_builtins.c | 11.7% | 0.0% | -78.3% | -85.0% |
| aio/aio_request_ctx.c | 23.5% | 2.1% | -66.5% | -82.9% |
| aio/aio_http_builtins.c | 30.9% | 100.0% | -59.1% | - |

### High Priority (30-50% gap)
| File | Line | Branch | Line Gap | Branch Gap |
|------|------|--------|----------|------------|
| aio/http2/stream/aio_stream_body_conn.c | 46.7% | 31.0% | -43.3% | -54.0% |
| aio/http2/overload/aio_overload_backpressure.c | 56.6% | 43.1% | -33.4% | -41.9% |
| aio/http2/stream/aio_stream_body.c | 53.4% | 39.9% | -36.6% | -45.1% |
| aio/http2/aio_http2_conn_fsm.c | 57.9% | 60.0% | -32.1% | -25.0% |

### Medium Priority (15-30% gap)
| File | Line | Branch | Line Gap | Branch Gap |
|------|------|--------|----------|------------|
| aio/http2/stream/aio_stream_builtins.c | 62.1% | 39.8% | -27.9% | -45.2% |
| aio/http2/aio_http2_conn.c | 64.8% | 51.7% | -25.2% | -33.3% |
| aio/http2/aio_http2_server.c | 65.9% | 42.1% | -24.1% | -42.9% |
| io/io_loop_ops_uv.c | 68.6% | 44.4% | -21.4% | -40.6% |
| io/io_tcp_ops_uv.c | 69.2% | 40.6% | -20.8% | -44.4% |
| aio/http2/aio_http2_client.c | 71.0% | 50.7% | -19.0% | -34.3% |
| gc.c | 72.0% | 57.2% | -18.0% | -27.8% |
| aio/aio_async.c | 72.4% | 53.2% | -17.6% | -31.8% |
| aio/http2/aio_ssl.c | 72.1% | 63.8% | -17.9% | -21.2% |
| parser.c | 75.1% | 50.0% | -14.9% | -35.0% |

### Low Priority (<15% gap)
| File | Line | Branch | Line Gap | Branch Gap |
|------|------|--------|----------|------------|
| aio/http2/overload/aio_overload_admission.c | 76.8% | 52.4% | -13.2% | -32.6% |
| aio/system/aio_task_queue.c | 77.3% | 55.9% | -12.7% | -29.1% |
| io/io_timer_ops_uv.c | 81.8% | 100.0% | -8.2% | - |
| aio/http2/aio_http2_session.c | 83.9% | 66.1% | -6.1% | -18.9% |
| aio/aio_combinators.c | 84.8% | 66.9% | -5.2% | -18.1% |
| aio/aio_diagnostics_builtins.c | 87.2% | 49.5% | -2.8% | -35.5% |
| aio/http2/aio_conn_io.c | 88.2% | 88.9% | -1.8% | - |
| memory.c | 88.2% | 71.2% | -1.8% | -13.8% |
| aio/aio_metrics.c | 89.0% | 51.2% | -1.0% | -33.8% |

## Strategy

### For each file:
1. Read the source file to understand what code paths exist
2. Check existing tests in `test/` for that module
3. Identify untested code paths (error handling, edge cases, branches)
4. Write tests that exercise those paths
5. Run `make coverage` to verify improvement
6. Repeat until file meets 90% line, 85% branch

### Test file naming:
- C runtime tests: `test/test_<module>.c`
- Valk integration tests: `test/test_<feature>.valk`

### Testing approaches:
- **Unit tests**: Test individual functions in isolation
- **Integration tests**: Test module interactions
- **Error path tests**: Force error conditions (invalid input, resource exhaustion)
- **Edge case tests**: Boundary conditions, empty inputs, max values

## Acceptance Criteria

- [ ] All files in `src/` achieve ≥90% line coverage
- [ ] All files in `src/` achieve ≥85% branch coverage
- [ ] `make coverage` passes without failures
- [ ] No regressions in existing tests
- [ ] LCOV exclusions only for truly untestable code (OOM, platform-specific)

## Validation

```bash
make coverage
```

Must show all files passing with green checkmarks.

## Notes

- Focus on one file at a time
- Start with critical priority (biggest gaps)
- Some files may need refactoring to be testable
- Use LCOV_EXCL markers sparingly and only for genuinely untestable code
