# Memory Diagnostics Dashboard - Implementation Plan

This document details remaining work for the SSE-powered memory diagnostics endpoint.

**Completed phases have been moved to [MEMORY_DIAGNOSTICS_COMPLETED.md](MEMORY_DIAGNOSTICS_COMPLETED.md).**

## Status Summary

| Phase | Status |
|-------|--------|
| Phase 1: Core Infrastructure (Backend) | ✅ DONE |
| Phase 2: Lisp Integration | ✅ DONE |
| Phase 3: Frontend | ✅ DONE |
| Phase 4: Testing & Polish | ⏳ PENDING |
| Phase 5: Connection-Aware Diagnostics | ✅ DONE |

---

## Phase 4: Testing & Polish (PENDING)

### 4.1 Test with Load

1. Start HTTP server
2. Generate load to see slab activity
3. Verify overflow counters work
4. Check high water mark tracking

### 4.2 Performance Validation

1. Verify 100ms push doesn't impact server performance
2. Check browser rendering stays under 16.7ms/frame

---

## Future Work: True SSE Streaming

The current implementation sends a single snapshot per request rather than keeping the HTTP/2 stream open. To implement true SSE streaming over HTTP/2:

1. **Keep stream open**: Use `NGHTTP2_DATA_FLAG_NO_END_STREAM` in the initial response
2. **Timer-based pushes**: Set up a `uv_timer_t` that calls `nghttp2_submit_data()` every 100ms
3. **Track SSE connections**: Maintain a list of active SSE streams per connection
4. **Handle disconnects**: Clean up timers when streams are reset or connection closes
5. **Backpressure**: Check `nghttp2_session_get_stream_remote_window_size()` before pushing

---

## Sources

- [Memory Heat Map: Anomaly detection in real-time embedded systems](https://ieeexplore.ieee.org/document/7167219)
- [Arena allocator tips and tricks](https://nullprogram.com/blog/2023/09/27/)
- [Untangling Lifetimes: The Arena Allocator](https://www.rfleury.com/p/untangling-lifetimes-the-arena-allocator)
- [Using server-sent events - MDN](https://developer.mozilla.org/en-US/docs/Web/API/Server-sent_events/Using_server-sent_events)
- [Server-Sent Events: A Practical Guide](https://tigerabrodi.blog/server-sent-events-a-practical-guide-for-the-real-world)
- [Optimizing Canvas Rendering - AG Grid](https://blog.ag-grid.com/optimising-html5-canvas-rendering-best-practices-and-techniques/)
- [heatmap.js - Dynamic Heatmaps for the Web](https://www.patrick-wied.at/static/heatmapjs/)
- [Wwise AkMemoryArena Profiler](https://www.audiokinetic.com/en/blog/ak-memory-arenas/)
