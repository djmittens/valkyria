# Implementation Plan

**Branch:** `networking`
**Last updated:** 2026-01-18 17:30

## Spec: coverage-improvement.md

**Goal:** 90% line coverage, 85% branch coverage for all files

**Current Status:** 86.4% lines, 71.9% branches

## Pending Tasks

### Priority 1: Core C Files (high impact, fewer dependencies)

- [ ] Improve parser.c branch coverage (79.4% → 85%)
- [ ] Improve memory.c branch coverage (72.5% → 85%)
- [ ] Improve gc.c coverage (75.1% line, 61.9% branch → 90%/85%)

### Priority 2: AIO System Files

- [ ] Improve aio/system/aio_chase_lev.c branch coverage (75.0% → 85%)
- [ ] Improve aio/system/aio_maintenance.c coverage (89.8%/50.0% → 90%/85%)
- [ ] Improve aio/aio_combinators.c coverage (84.8%/66.9% → 90%/85%)
- [ ] Improve aio/aio_diagnostics_builtins.c branch coverage (51.5% → 85%)
- [ ] Improve aio/aio_metrics.c branch coverage (52.6% → 85%)
- [ ] Improve aio/aio_request_ctx.c branch coverage (81.6% → 85%)

### Priority 3: AIO I/O Layer

- [ ] Improve aio/io/io_loop_ops_uv.c coverage (73.3%/40.0% → 90%/85%)
- [ ] Improve aio/io/io_tcp_ops_uv.c coverage (74.4%/50.0% → 90%/85%)
- [ ] Improve aio/io/io_timer_ops_uv.c line coverage (81.8% → 90%)

### Priority 4: HTTP/2 Stack (most complex, may need test infrastructure)

- [ ] Improve aio/http2/aio_http2_client.c coverage (73.6%/51.6% → 90%/85%)
- [ ] Improve aio/http2/aio_http2_conn.c coverage (72.5%/66.1% → 90%/85%)
- [ ] Improve aio/http2/aio_http2_server.c coverage (69.8%/45.7% → 90%/85%)
- [ ] Improve aio/http2/aio_http2_session.c coverage (83.9%/66.1% → 90%/85%)
- [ ] Improve aio/http2/aio_ssl.c coverage (74.6%/65.2% → 90%/85%)

### Priority 5: Stream Body Handling

- [ ] Improve aio/http2/stream/aio_stream_body.c coverage (70.2%/58.7% → 90%/85%)
- [ ] Improve aio/http2/stream/aio_stream_body_conn.c coverage (76.0%/81.0% → 90%/85%)
- [ ] Improve aio/http2/stream/aio_stream_builtins.c branch coverage (79.6% → 85%)

### Priority 6: Valk Stdlib Files

- [ ] Improve async_handles.valk expr coverage (80.2% → 90%)
- [ ] Improve async_monadic.valk expr coverage (86.1% → 90%)
- [ ] Improve http_api.valk expr coverage (89.1% → 90%)
- [ ] Improve modules/aio/debug.valk expr coverage (84.7% → 90%)
- [ ] Improve modules/aio/sse.valk expr coverage (76.5% → 90%)
- [ ] Improve modules/test.valk expr coverage (86.0% → 90%)

## Completed

- [x] Improve parser.c branch coverage 69.9% → 74.0% (added 57 new tests for type error branches)
- [x] Improve parser.c branch coverage 74.0% → 79.4% (added 63 new tests for AIO, HTTP, shutdown, init, set, ord/cmp, eval, load error branches)

## Discovered Issues

- Many remaining uncovered branches in parser.c are internal implementation details (memory allocation null checks, dynamic array growth logic) that require mocking infrastructure to test effectively
