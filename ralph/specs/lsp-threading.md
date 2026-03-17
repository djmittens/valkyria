# LSP Threaded I/O

## Overview

The Valk LSP server (`src/lsp.valk`) currently uses blocking C `stdio` for
all I/O (`fgetc`, `fread`, `fwrite`). This blocks the main thread during
reads, preventing concurrent request handling and making neovim unresponsive
during heavy operations (semantic tokens, workspace indexing). This spec
replaces blocking stdio with `uv_pipe_t` on the AIO event loop, enabling
read-only LSP requests to be dispatched to worker event loop threads while
a single event loop thread owns all stdin/stdout I/O.

## Architecture

```
  stdin ──► uv_pipe_t (read) ──► loop-0 parse callback
                                       │
                          ┌─────────────┼─────────────┐
                          ▼             ▼             ▼
                      loop-1        loop-2        loop-N
                    (read-only    (read-only    (read-only
                     handler)      handler)      handler)
                          │             │             │
                          └─────────────┼─────────────┘
                                        ▼
                              loop-0 write callback
                                        │
                                        ▼
  stdout ◄── uv_pipe_t (write) ◄────────┘
```

Loop-0 owns: stdin pipe, stdout pipe, document state mutations.
Loop-1..N: execute read-only request handlers (hover, completion, etc.).
Results return to loop-0 via `valk_aio_loop_enqueue_task` for serialization.

## Dependencies

- Requires the AIO system (`src/aio/`) to be functional (it is)
- Requires existing `valk_aio_loop_enqueue_task` API (exists in `aio_task_queue.c`)

## Non-Requirements

- No changes to the GC or STW protocol
- No new combinator types (all/race/etc.)
- No changes to the HTTP/2 server infrastructure
- SQLite concurrency (WAL mode already enabled) — no schema changes

## Requirements

### UV Pipe Builtins

Add a new file `src/builtins_pipe.c` with builtins that create `uv_pipe_t`
handles on the AIO event loop for stdin/stdout.

| Builtin | Signature | Purpose |
|---------|-----------|---------|
| `pipe/stdin-open` | `(pipe/stdin-open)` → pipe-handle | Open fd 0 as `uv_pipe_t` on loop-0, start reading |
| `pipe/stdout-open` | `(pipe/stdout-open)` → pipe-handle | Open fd 1 as `uv_pipe_t` on loop-0 |
| `pipe/write` | `(pipe/write handle str)` → nil | Queue async write to pipe |
| `pipe/on-data` | `(pipe/on-data handle callback)` → nil | Set read callback; called with chunk string |
| `pipe/close` | `(pipe/close handle)` → nil | Close pipe handle |

Pipe handles are stored as `LVAL_CPTR` (like sqlite db handles). The
underlying C struct wraps `uv_pipe_t` plus a read buffer and a Valk
callback handle-ref for the on-data callback.

`pipe/stdin-open` must call `uv_pipe_init(loop-0->uv_loop, ...)` then
`uv_pipe_open(..., 0)` then `uv_read_start(...)`. The alloc callback uses
a stack buffer. The read callback accumulates into a growable buffer and
invokes the Valk on-data callback with each chunk.

`pipe/write` must call `uv_write(...)` with a copy of the string data.
The write callback frees the copy.

Register in `valk_register_pipe_builtins(env)`, called from `builtins.c`.

### LSP Message Framer (C)

Add framing logic in `src/builtins_pipe.c` (or a small helper) that
handles Content-Length delimited LSP messages:

| Builtin | Signature | Purpose |
|---------|-----------|---------|
| `pipe/lsp-reader` | `(pipe/lsp-reader pipe callback)` → reader-handle | Attach LSP framer to pipe; calls callback with each complete JSON body string |

The framer accumulates chunks from `pipe/on-data`, parses
`Content-Length: N\r\n\r\n`, reads N bytes of body, then calls the Valk
callback with the body string. This replaces `lsp/read-content-length` +
`lsp/read-message` (currently in Valk using blocking stdio).

Doing framing in C avoids per-byte overhead of Valk string ops and keeps
the hot path (header parsing) in native code.

### AIO Task Dispatch Builtin

Add a builtin to dispatch a Valk closure to a worker event loop thread and
deliver the result back to loop-0:

| Builtin | Signature | Purpose |
|---------|-----------|---------|
| `aio/dispatch` | `(aio/dispatch fn arg callback)` → nil | Evaluate `(fn arg)` on a worker loop, then call `(callback result)` on loop-0 |

Implementation pattern (follows `aio/pmap`):
1. Evacuate `fn`, `arg`, `callback` to heap via `valk_handle_store`
2. Pick next worker loop via round-robin (`sys->loops[1 + (counter++ % (N-1))]`)
3. Call `valk_aio_loop_enqueue_task(worker_loop, worker_fn, ctx)`
4. `worker_fn`: resolve handles, eval `(fn arg)`, store result handle,
   then `valk_aio_loop_enqueue_task(loop_0, completion_fn, ctx)`
5. `completion_fn`: resolve result + callback handles, eval
   `(callback result)`, release all handles

If only one loop exists (N=1), execute synchronously on loop-0.

### LSP Main Loop Rewrite

Replace the current blocking `lsp/loop` (recursive, blocking `stdin/read-line`)
with an event-driven architecture in `src/lsp.valk`:

```
(fun {lsp/start} {do
  (= {stdin-pipe}  (pipe/stdin-open))
  (= {stdout-pipe} (pipe/stdout-open))

  ;; Store stdout-pipe in a global for lsp/write-message
  (def {lsp/out} stdout-pipe)

  ;; Attach LSP message framer — calls lsp/on-message for each request
  (pipe/lsp-reader stdin-pipe (\ {body} {lsp/on-message body}))

  ;; Start the event loop (blocks until shutdown)
  (aio/run)

  ;; Cleanup
  (if (not (nil? lsp/db)) {symdb/close lsp/db} {})
  (stderr/write "[valk-lsp] shutdown\n")})
```

`lsp/on-message` runs on loop-0. It:
1. Parses JSON: `(json/parse body)`
2. Classifies the method as mutating or read-only
3. Mutating methods (`didOpen`, `didChange`, `didClose`, `didSave`):
   execute inline on loop-0 (they modify `lsp/documents`)
4. Read-only methods with an `id` (requests needing a response):
   dispatch via `aio/dispatch` with handler fn and a response-writer callback
5. Notifications without response (`$/cancelRequest`): handle inline

### Response Writer

`lsp/write-message` must change from `stdout/write` + `stdout/flush` to
`pipe/write` using the stored `lsp/out` pipe handle:

```
(fun {lsp/write-message json-body} {do
  (= {msg} (json/encode json-body))
  (pipe/write lsp/out (str "Content-Length: " (len msg) "\r\n\r\n" msg))})
```

All calls to `lsp/write-message` MUST happen on loop-0. Worker threads
must NOT call `lsp/write-message` directly — they return results via the
`aio/dispatch` callback which runs on loop-0.

### Method Classification

Define which methods are mutating vs read-only in `lsp/on-message`:

**Mutating (run on loop-0):**
- `initialize`, `initialized`, `shutdown`, `exit`
- `textDocument/didOpen`, `textDocument/didChange`,
  `textDocument/didClose`, `textDocument/didSave`

**Read-only (dispatch to worker):**
- `textDocument/hover`, `textDocument/definition`,
  `textDocument/references`, `textDocument/completion`,
  `textDocument/documentSymbol`, `textDocument/semanticTokens/full`,
  `textDocument/semanticTokens/range`, `textDocument/prepareRename`,
  `textDocument/rename`, `textDocument/inlayHint`,
  `textDocument/signatureHelp`, `textDocument/documentHighlight`,
  `textDocument/documentLink`, `textDocument/foldingRange`,
  `textDocument/selectionRange`, `textDocument/codeLens`,
  `textDocument/codeAction`, `workspace/symbol`

Read-only handlers receive a snapshot of `lsp/documents` (it's a plist,
which is immutable/COW in Valk) and the shared `lsp/db` (SQLite WAL
supports concurrent readers).

### Workspace Indexing

The current `lsp/drain-scan` interleaves indexing with `stdin/has-data`
checks. With event-driven I/O this is unnecessary — indexing can run as
a dispatched task on a worker thread:

After `initialized`, dispatch workspace scanning to a worker via
`aio/dispatch`. The worker iterates files and indexes them, calling back
to loop-0 periodically for progress notifications. Since indexing does
SQLite writes, it must either:
- Use a separate SQLite connection (WAL allows one writer + readers), or
- Batch index results and apply them on loop-0

The simpler approach: keep indexing on loop-0 but use `uv_timer_t` to
yield between files (non-blocking cooperative scheduling), allowing
incoming requests to interleave naturally.

### Entry Point

Update `src/lsp-main.valk` to call `(lsp/start)` instead of `(lsp/main)`.
The old `lsp/main` and `lsp/loop` functions can be removed after the
rewrite.

## Error Handling

| Error Condition | Response |
|-----------------|----------|
| `uv_pipe_init` fails | Log to stderr, exit with code 1 |
| `uv_pipe_open` fails | Log to stderr, exit with code 1 |
| `uv_read_start` fails | Log to stderr, exit with code 1 |
| `uv_write` fails | Log to stderr, send LSP error if request had id |
| Worker eval raises error | Catch in worker, return `lval_err` to callback, send LSP error response |
| stdin EOF (editor closed) | Framer detects `nread == UV_EOF`, triggers clean shutdown |
| Malformed Content-Length | Framer logs warning to stderr, skips to next `\r\n\r\n` |

## Acceptance Criteria

- [ ] `pipe/stdin-open` creates a `uv_pipe_t` on loop-0 for fd 0: `grep -c 'pipe/stdin-open' src/builtins_pipe.c` returns >= 1
- [ ] `pipe/stdout-open` creates a `uv_pipe_t` on loop-0 for fd 1: `grep -c 'pipe/stdout-open' src/builtins_pipe.c` returns >= 1
- [ ] `pipe/write` performs async write: `grep -c 'uv_write' src/builtins_pipe.c` returns >= 1
- [ ] `pipe/lsp-reader` parses Content-Length framed messages: `grep -c 'Content-Length' src/builtins_pipe.c` returns >= 1
- [ ] `aio/dispatch` dispatches closure to worker and delivers result to loop-0: `grep -c 'aio/dispatch' src/builtins_pipe.c` returns >= 1
- [ ] LSP main loop is event-driven (no `stdin/read-line` calls): `grep -c 'stdin/read-line' src/lsp.valk` returns 0
- [ ] LSP read-only requests dispatch to worker threads: `grep -c 'aio/dispatch' src/lsp.valk` returns >= 1
- [ ] LSP mutating requests run on loop-0 (no dispatch): `lsp/on-message` contains inline calls for didOpen/didChange/didClose/didSave
- [ ] `make build` succeeds
- [ ] `make test` passes
- [ ] `make lint` passes
- [ ] LSP responds to hover request via pipe-based I/O: test in `test/test_lsp_pipe.valk` passes
