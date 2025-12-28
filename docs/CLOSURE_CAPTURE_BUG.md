# Closure Behavior Investigation (Dec 2024)

## Status: RED HERRING

During implementation of a `test/wait-for-server` health check helper, callbacks appeared to fail when passed through HTTP response chains. After investigation, simplified reproductions work correctly.

## What Actually Happened

1. Attempted to add `test/wait-for-server` helper to `src/modules/test.valk`
2. The helper would do health checks with retry, then call an `on-ready` callback
3. When integrated with `test_sse_integration.valk`, the callback appeared to not execute
4. Created minimal reproduction tests - all passed

## Root Causes Found

1. **SSE handler bug** - `test_sse_integration.valk` was returning `{:status "200" :body "done"}` after calling `sse/open`. This is wrong because `sse/open` already submits HTTP/2 response headers. Fixed by returning `:deferred` instead.

2. **Debug trace crash** - Adding `(type callback)` or `(str callback)` in debug output caused crashes. This was a red herring that made it look like the callback itself was broken.

3. **Timing issues** - The original test had insufficient delays, causing checks to run before handlers completed.

## Resolution

- Removed the `test/wait-for-server` helper (not needed for now)
- Fixed `test_sse_integration.valk` to use `:deferred` and timer-based state checking
- Tests pass without the health check helper

## Test File

`test/test_closure_bug.valk` contains a working reproduction that demonstrates closures DO work through HTTP callback chains:

```bash
./build/valk test/test_closure_bug.valk
# Outputs: on-ready executed correctly
```

## Future Work

If health check helpers are needed later, the pattern works - just need to be careful about:
- Not using `(type ...)` or `(str ...)` on lambdas in debug output
- Ensuring SSE handlers return `:deferred`
- Using sufficient delays for server startup
