# Why Phase 0 (Critical Infrastructure) is Required

## The Problem

We discovered that to implement HTTP handlers in Lisp, we need:
1. Handlers that don't block the event loop
2. Ability to handle thousands of concurrent requests
3. Recursive code that doesn't blow the stack

Without these, the networking phase is DOA.

## Missing Infrastructure

### 1. Tail Call Optimization (TCO)

**Why critical**:
- Async code is heavily recursive (event loops, continuations)
- Current evaluator will stack overflow after ~1000 calls
- Real servers need infinite loops

**Example that breaks now**:
```lisp
(def {server-loop} (\ {}
  {do
    (handle-request (get-next-request))
    (server-loop)}))  ; Stack overflow!
```

### 2. Async/Await in Lisp

**Why critical**:
- HTTP handlers MUST be non-blocking
- Can't use C futures directly from Lisp
- Need to compose multiple async operations

**What we need**:
```lisp
(def {handler} (async (\ {req}
  {let [user (await (db/get-user (req-param req "id")))
        posts (await (db/get-posts (:id user)))]
    {response 200 (json/encode posts)}})))
```

Without this, handlers would block the entire server on each database call.

### 3. Continuations

**Why critical**:
- Proper error handling in async code
- Implementing generators/streams
- Advanced control flow

## Real-World Requirements

### For HTTP Servers
- Handle 10,000+ concurrent connections
- Non-blocking I/O throughout
- Stream large responses
- WebSocket support needs continuations

### For Data Processing
- **Protobuf/gRPC**: Industry standard for services
- **Parquet**: Required for analytics/ML workloads
- **Streaming**: Can't load 1GB files into memory

### For Production Use
- Stack safety (TCO)
- Concurrent request handling (async)
- Memory efficiency (streaming)

## Timeline Impact

**Original Plan**: 3 weeks to finish networking
**Reality**:
- 3 weeks for Phase 0 (infrastructure)
- 2 weeks for Phase 1 (networking with async)
- 6 weeks for validation

**Total**: 11 weeks instead of 3 weeks

## The Good News

Once we have:
- TCO
- Async/await
- Continuations

Then we can build:
- Production HTTP servers
- Real concurrent systems
- Data processing pipelines
- Game engines with update loops

These are foundational features that unblock everything else.

## Implementation Order

1. **TCO First** - Everything else needs recursion
2. **Async/Await Second** - Built on top of TCO
3. **HTTP Handlers Third** - Now they can be async
4. **Validation Last** - Prove it all works

---

Without Phase 0, we're building a toy. With Phase 0, we're building a production language.