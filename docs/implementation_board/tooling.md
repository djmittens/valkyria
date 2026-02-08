# Tooling

**Status**: REPL, logging, stack traces, testing complete

**Timeline**: ~2-4 months (can work in parallel)

---

## Current State

### Complete ✓
- [x] REPL (editline integration)
- [x] Command history (editline)
- [x] Load files (`load` builtin)
- [x] Test framework (Lisp-based: `test/suite`, `test/skip`)
- [x] C test framework (`testing.{c,h}` with ASSERT macros)
- [x] Logging system (`log.{c,h}` with log levels)
- [x] `VALK_LOG` env var (runtime config)
- [x] Stack traces (`debug.{c,h}`, libbacktrace for symbols)

### Remaining Work
- [ ] Tab completion (M - 1-2 weeks)
- [ ] Syntax highlighting (S - 1-3 days)
- [ ] Hot reload (M - 1-2 weeks)
- [ ] Test runner improvements (M - 1-2 weeks)
- [ ] Debugger (L - 2-4 weeks)
- [ ] Profiler (L - 2-4 weeks)
- [ ] LSP Server (L - 2-4 weeks)

---

## Feature 1: Tab Completion (M - 1-2 weeks)

**Unlocks**: Better REPL UX

### Tasks

- [ ] **T.1: Symbol Completion** (3-4 days)
  - Complete variable/function names from environment
  - Use editline completion API
  - **Test**: Press TAB, see completions

- [ ] **T.2: File Path Completion** (2-3 days)
  - Complete paths for `load` command
  - **Test**: `(load "/tmp/te<TAB>` completes

- [ ] **T.3: Smart Completion** (2-3 days)
  - Context-aware: complete function names after `(`
  - Complete keywords in appropriate contexts
  - **Test**: `(fun add <TAB>` suggests parameters

---

## Feature 2: Syntax Highlighting (S - 1-3 days)

**Unlocks**: Readable REPL

### Tasks

- [ ] **T.4: ANSI Color Output** (1-2 days)
  - Highlight keywords, strings, numbers
  - Use ANSI escape codes
  - **Test**: REPL output colorized

---

## Feature 3: Hot Reload (M - 1-2 weeks)

**Unlocks**: Live coding, no restart

### Tasks

- [ ] **T.5: File Watching** (3-4 days)
  - Watch source files for changes
  - Use inotify (Linux) or FSEvents (macOS)
  - **Test**: File change detected

- [ ] **T.6: Reload Modified Code** (3-4 days)
  - Re-evaluate changed files
  - Preserve REPL state
  - **Test**: Edit file, see changes immediately

---

## Feature 4: Test Runner (M - 1-2 weeks)

**Unlocks**: Better test organization

### Tasks

- [ ] **T.7: Pattern Filtering** (2-3 days)
  - Run specific tests: `make test PATTERN=gc`
  - **Test**: Filter works

- [ ] **T.8: Parallel Execution** (3-4 days)
  - Run tests in parallel for speed
  - Isolate test environments
  - **Test**: Tests run faster

---

## Feature 5: Debugger (L - 2-4 weeks)

**Unlocks**: Step through code, inspect state

### Tasks

- [ ] **T.9: Breakpoints** (1 week)
  - Set breakpoints in code
  - Pause execution at breakpoint
  - **Test**: Set breakpoint, hit it

- [ ] **T.10: Step/Continue** (1 week)
  - Step over, step into, continue
  - **Test**: Step through function

- [ ] **T.11: Inspect Variables** (3-4 days)
  - Print variable values at breakpoint
  - **Test**: Inspect locals

---

## Feature 6: Profiler (L - 2-4 weeks)

**Unlocks**: Performance analysis

### Tasks

- [ ] **T.12: Sampling Profiler** (1-2 weeks)
  - Sample stack periodically
  - Build call graph
  - **Test**: Profile program

- [ ] **T.13: Flame Graphs** (3-4 days)
  - Visualize profiler output
  - Generate SVG flame graphs
  - **Test**: Generate flame graph

---

## Feature 7: LSP Server (L - 2-4 weeks)

**Unlocks**: IDE integration (VS Code, etc.)

### Tasks

- [ ] **T.14: LSP Protocol** (1 week)
  - Implement LSP server
  - Handle textDocument/didOpen, etc.
  - **Test**: LSP client connects

- [ ] **T.15: Diagnostics** (3-4 days)
  - Report parse/type errors
  - **Test**: See errors in editor

- [ ] **T.16: Go to Definition** (3-4 days)
  - Jump to function definition
  - **Test**: Go to definition works

- [ ] **T.17: Autocomplete** (3-4 days)
  - Context-sensitive completions
  - **Test**: Autocomplete in editor

---

## Resources

- editline: https://thrysoee.dk/editline/
- LSP spec: https://microsoft.github.io/language-server-protocol/
- libbacktrace: https://github.com/ianlancetaylor/libbacktrace
- Flame graphs: https://www.brendangregg.com/flamegraphs.html
