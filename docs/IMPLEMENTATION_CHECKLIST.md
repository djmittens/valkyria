# Valkyria Implementation Checklist

## How to Use This Document

1. Each task has clear acceptance criteria
2. Mark items with [x] when complete
3. Each section has validation requirements
4. For agents: Reference this file and current section when starting work

---

## PHASE 0: Critical Infrastructure [BLOCKING PHASE 1]

### 0.1 Tail Call Optimization [REQUIRED FOR ASYNC]
**Owner**: Next session
**Files**: `src/vm.c`, `src/parser.c`
**Why**: Without TCO, async/continuation code will blow the stack

- [ ] Detect tail position in evaluator
  - [ ] Mark tail calls in `valk_lval_eval()`
  - [ ] Add LVAL_FLAG_TAIL_CALL flag
  - [ ] Identify self-recursive calls
  - [ ] Identify mutual recursion

- [ ] Implement tail call elimination
  - [ ] Replace call with jump for self-recursion
  - [ ] Trampoline for mutual recursion
  - [ ] Preserve environment correctly

**Validation**:
```lisp
; This must not blow stack:
(def {loop} (\ {n}
  {if (== n 0)
    {0}
    {loop (- n 1)}}))
(loop 100000)  ; Should return 0, not stack overflow
```

### 0.2 Async/Await in Lisp [REQUIRED FOR HTTP]
**Owner**: After 0.1
**Files**: `src/parser.c`, `src/concurrency.c`
**Why**: HTTP handlers need to be async, can't block the event loop

- [ ] Expose futures to Lisp
  - [ ] `(future body)` - Create future
  - [ ] `(await future)` - Block on future
  - [ ] `(then future callback)` - Chain futures
  - [ ] Future becomes LVAL_FUTURE type

- [ ] Async function support
  - [ ] `(async fn)` - Mark function as async
  - [ ] Async functions return futures
  - [ ] `(await)` only valid in async context

- [ ] Continuation support
  - [ ] `(call/cc fn)` - Call with current continuation
  - [ ] Store continuation as LVAL_CONTINUATION
  - [ ] Resume continuation with value

**Validation**:
```lisp
(def {fetch-async} (async (\ {url}
  {await (http/get url)})))

(def {result} (await (fetch-async "https://example.com")))
(print result)  ; Should work without blocking REPL
```

### 0.3 Lisp-Level Promise Composition
**Owner**: With 0.2
**Files**: `src/prelude.valk`

- [ ] Promise combinators
  - [ ] `(promise/all futures)` - Wait for all
  - [ ] `(promise/race futures)` - First one wins
  - [ ] `(promise/map fn futures)` - Map over futures
  - [ ] `(promise/timeout ms future)` - Add timeout

**Validation**:
```lisp
(def {results} (await
  (promise/all {
    (http/get "https://api1.com")
    (http/get "https://api2.com")
    (http/get "https://api3.com")})))
; Should fetch all three in parallel
```

---

## PHASE 1: Complete Networking (With Async Support)

### 1.0 PREREQUISITE: Phase 0 Complete
- [ ] TCO working (0.1)
- [ ] Async/await working (0.2)
- [ ] Promise composition (0.3)

### 1.1 Async Server Request Handler API
**Owner**: After Phase 0
**Files**: `src/aio_uv.c`, `src/parser.c`

- [ ] Request/Response objects (same as before)
  - [ ] Add `http2_request_t` type
  - [ ] Request accessors
  - [ ] Response builder

- [ ] Async handler support
  - [ ] Handler returns future
  - [ ] Server waits on future for response
  - [ ] Non-blocking handler execution

**Validation**:
```lisp
(def {handler} (async (\ {req}
  {let [path (http2/request-path req)]
    {if (== path "/slow")
      {do
        (await (sleep 1000))  ; Non-blocking sleep
        (http2/response :status 200 :body "Slow response")}
      {http2/response :status 200 :body "Fast response"}}})))

(def {server} (http2/listen aio "127.0.0.1" 8080 "key" "cert" handler))
; Server should handle multiple requests concurrently
```

### 1.2 Test Framework (same as before)
### 1.3 REPL Safety (same as before)
### 1.4 HTTP Convenience Functions (same as before)

---

## PHASE 1.5: Production Validation

### Validation must demonstrate:
- [ ] Async handlers don't block each other
- [ ] TCO prevents stack overflow in recursive handlers
- [ ] 10,000+ concurrent connections handled
- [ ] Memory stable over 24 hours

---

## PHASE 2: Type System (With Protocol Support Planning)

### 2.1 Basic Types (same as before)
### 2.2 Type Inference (same as before)

### 2.3 Protocol Type Preparation
**Why**: Need types before we can do protobuf/gRPC/parquet

- [ ] Struct types
  - [ ] Named fields with types
  - [ ] Recursive types
  - [ ] Type aliases

- [ ] Serialization hints
  - [ ] Mark fields as required/optional
  - [ ] Field numbers for protobuf
  - [ ] Default values

**Validation**:
```lisp
(type User {
  :id Int :required
  :name String :required
  :email String :optional
  :age Int :default 0})
```

---

## PHASE 3: Protocol Support (Expanded)

### 3.1 Data Formats
**Owner**: After Phase 2
**Files**: `src/protocols/` (new directory)

- [ ] Protobuf support
  - [ ] Parse .proto files
  - [ ] Generate type definitions
  - [ ] Serialization/deserialization
  - [ ] Wire format compliance

- [ ] Parquet support
  - [ ] Read parquet files
  - [ ] Write parquet files
  - [ ] Schema inference
  - [ ] Columnar operations

- [ ] JSON with schema
  - [ ] JSON schema validation
  - [ ] Type-safe parsing
  - [ ] Error on schema mismatch

### 3.2 RPC Protocols

- [ ] gRPC
  - [ ] Client stub generation
  - [ ] Server skeleton generation
  - [ ] Streaming support
  - [ ] Error handling

- [ ] GraphQL
  - [ ] Schema definition
  - [ ] Query execution
  - [ ] Resolver functions

**Validation**:
```lisp
; Load protobuf
(import-proto "user.proto")

; Use generated types
(def {user} (User/new :id 1 :name "Alice"))
(def {bytes} (User/serialize user))
(def {user2} (User/deserialize bytes))

; gRPC call
(def {client} (grpc/connect "localhost:50051"))
(def {response} (await (UserService/GetUser client {:id 1})))
```

---

## Missing Pieces Added

### Critical Infrastructure
1. **Tail Call Optimization** - Required for any serious recursion
2. **Async/Await in Lisp** - Not just C futures, but Lisp-level async
3. **Continuations** - For advanced control flow

### Data Handling
1. **Protobuf** - Industry standard serialization
2. **Parquet** - Columnar data for analytics
3. **gRPC** - Service communication
4. **GraphQL** - Modern API standard

### Performance
1. **TCO** - Prevents stack overflow
2. **Async** - Prevents blocking
3. **Streaming** - Handle large data

---

## Revised Timeline

### Phase 0: Infrastructure (2-3 weeks)
- Week 1: Tail call optimization
- Week 2: Async/await in Lisp
- Week 3: Testing and validation

### Phase 1: Networking (2 weeks after Phase 0)
- Now with async handlers
- Non-blocking throughout
- Concurrent request handling

### Phase 1.5: Validation (4-6 weeks)
- Must handle real concurrent load
- Must demonstrate TCO working
- Must show async composition

### Phase 2: Types (1-2 months)
- With protocol support in mind
- Struct types for data formats
- Serialization annotations

### Phase 3: Protocols (1-2 months)
- Protobuf/gRPC/Parquet
- Real-world data handling
- Service communication

---

## Current Status

**Active Phase**: Phase 0 (Critical Infrastructure)
**Next Task**: 0.1 Tail Call Optimization
**Blocker**: Cannot do async HTTP handlers without TCO and async/await
**Files**: `src/vm.c`, `src/parser.c`

**Last Updated**: 2025-11-12