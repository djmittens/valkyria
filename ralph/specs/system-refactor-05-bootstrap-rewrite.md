# Bootstrap and Shutdown Rewrite

## Overview

Rewrite `repl.c` to use `valk_system_shutdown`/`valk_system_destroy` at both exit paths (script mode and REPL mode). Simplify `(shutdown N)` to only set `VALK_EXIT_CODE` — the bootstrap loop calls `valk_system_shutdown` which stops all subsystems generically. Make `(exit N)` an alias for `(shutdown N)` instead of calling `exit()` directly.

## Dependencies

- Requires `system-refactor-04-aio-integration.md` (AIO registers as subsystem, `valk_system_shutdown` stops it)

## Requirements

### Script Mode Exit Path

In `src/repl.c` (lines ~134-153):

1. Remove `valk_aio_wait_for_all_systems()` call (line ~143) — subsystem shutdown is now handled by `valk_system_shutdown`
2. The exit path should: read `VALK_EXIT_CODE` from env, call `valk_system_shutdown(sys, 5000)`, coverage report, `free(scratch)`, `valk_system_destroy(sys)`, return exit code

### REPL Exit Path

In `src/repl.c` (lines ~209-218):

1. Remove the manual AIO stop code (lines ~210-215 that look up `aio` symbol in env and call `valk_aio_stop`)
2. Replace with: `valk_system_shutdown(sys, 5000)`, `free(scratch)`, `valk_system_destroy(sys)`

### Simplify (shutdown N) Builtin

In `src/builtins_aio.c`, rewrite `valk_builtin_shutdown` (lines 304-321):

1. Keep: argument validation (0 or 1 args), `VALK_EXIT_CODE` env definition
2. Remove: the `aio` symbol lookup (lines ~314-318) and `valk_aio_stop()` call
3. Return the exit code number

The function should only set `VALK_EXIT_CODE` in the env and return. The bootstrap loop reads this value and calls `valk_system_shutdown`.

### Make (exit N) Alias (shutdown N)

In `src/builtins_aio.c`:

1. Remove `valk_builtin_exit()` function body (lines 293-301) — it calls `exit()` directly which is the wrong behavior
2. In `valk_register_aio_builtins()` (line ~339), change `"exit"` to point to `valk_builtin_shutdown` instead

### Add Valk Tests

Create `test/test_shutdown.valk`:
```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")
(def {aio} (aio/await (aio/start)))
(def {result} (shutdown 0))
(test/run (list
  (test "shutdown-returns-code" {(== result 0)})
) {:suite-name "Shutdown"})
```

Create `test/test_exit_alias.valk`:
```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")
(def {result} (exit 42))
(test/run (list
  (test "exit-is-shutdown-alias" {(== result 42)})
) {:suite-name "Exit Alias"})
```

## Acceptance Criteria

- [ ] `make build` succeeds
- [ ] `make test-c` passes
- [ ] `make test-valk` passes
- [ ] `build/valk test/test_shutdown.valk` exits with code 0 (shutdown returns control, does not call exit())
- [ ] `build/valk test/test_exit_alias.valk` exits with code 0 (exit is alias for shutdown)
- [ ] `grep -rn 'valk_aio_wait_for_all_systems\|valk_aio_stop' src/repl.c` returns no matches
- [ ] `grep -rn 'valk_builtin_exit' src/builtins_aio.c` returns no matches (function removed)
