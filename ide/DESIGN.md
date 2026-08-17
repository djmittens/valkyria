# Valkyria IDE — Design

Status: v3 — implemented through phase 2 core (see section 0)
Scope: architecture for an IDE implemented in Valk, running inside the Valk
runtime, browser frontend first, native Vulkan frontend later.

## 0. Implementation status

Phases 0–1 are complete; phase 2's runtime primitives, wire protocol, and
debugger pane are built, including step-in/over/out (launch/attach of child
processes remains). Run with `build/valk ide/main.valk` → https://localhost:7777/.
A demo debug target lives in `ide/demo-target.valk`.

| Area | Files | Notes |
|---|---|---|
| Machine core | `ide/machine.valk` | tools, commands, clients, key routing, config |
| Interaction | `ide/keys.valk`, `ide/chrome.valk` | leader engine, which-key, palette, per-client chrome |
| Editing | `ide/edit.valk` | modal buffer machine (small vim subset) |
| REPL | `ide/repl.valk` | sessions via `env/new`, eval on work-sys |
| Highlight/inspect | `ide/hl.valk`, `ide/inspect.valk` | sem/* → runs; value trees |
| LSP engine | `ide/lsp.valk` + `nav/hover*`, `nav/completion*` | pure cores shared with stdio valk-lsp |
| Cards | `ide/cards.valk` | tiers, stat providers, procedural art seed |
| Debugger | `ide/debugger.valk`, `stdlib/aio/debug-server.valk` | attach client + pane; DAP-shaped wire |
| UI server | `ide/server.valk`, `ide/web/` | routes, SSE, JS renderer |
| Runtime (C) | `runtime/src/debugger.c`, `builtins_debug.c`, env builtins in `builtins_env.c` | primitives #1, #3, #4, #5 |
| Tests | `ide/test/`, `runtime/test/lang/test_{env_builtins,debugger}.valk`, `stdlib/test/test_debug_server.valk` | ~100 tests; latency UAT gates the echo budget |

Key implementation decisions and deviations, recorded inline in the sections
below and in the risks (section 12):

- **Machine state lives in dicts**, not env globals: `def` is refused inside
  request-handler context, and `dict/set!` evacuates values to the heap —
  exactly the semantics shared handler-touched state needs (section 3.1).
- **Session isolation** required a new env flag: `LENV_FLAG_DEF_BOUNDARY`
  stops `valk_lenv_def`'s walk at `env/new` envs (section 4).
- **Source positions** ship under `VALK_SRC_LOC` (= `VALK_COVERAGE` or
  `VALK_DEBUG_INFO`); debug info default-ON for dev builds, measured cost in
  section 12.
- **Debug pause** uses the `aio/run` eventcount park loop so parked threads
  still rendezvous with the GC's STW barrier (section 5.2).
- Two pre-existing LSP defects were fixed en route: doc comments above
  `(sig ...)` indexed to nothing, and `symbol-hover-in` dropped docs held by
  sibling rows.
- The server-side HTTP stack gained request-body collection (handlers now
  run at END_STREAM) and the client gained `http2/client-post` — neither
  existed and both are prerequisites for `POST /event` and the debug wire.

## 1. Vision

The IDE is a **lisp machine**: a long-running Valk process that hosts every
development service (LSP engine, REPL kernel, debugger, build orchestration,
documentation) and exposes them to frontends. You interact with the machine;
frontends are displays. The machine can build, run, debug, and attach to the
env of target applications (including game engines) that are themselves Valk
runtimes.

Principles (in priority order — when they conflict, the lower number wins):

1. **Responsiveness above everything.** Input handling and rendering are
   never blocked by IDE workloads. Indexing, session eval, builds, debug I/O,
   doc rendering — all of it runs off the UI path; a stuck eval or a
   full-workspace re-index must not delay a keystroke echo by even a frame.
   The input path has an explicit latency budget, is instrumented from phase
   0, and every phase gates on it (section 3.3, "Latency").
2. **Keyboard-first, modal.** Every action is a named command reachable from
   the keyboard; the mouse works (clicks, buttons) but is strictly a secondary
   alias — nothing is mouse-only. Vim grammar inside text-editing widgets,
   leader-key sequences (which-key style) for everything else. Mode state and
   keymaps live in the machine as data (section 3.3), so the model is
   identical across frontends.
3. **Artistic, informationally dense.** Trading-terminal density with RPG
   flavor, not minimal-web-app whitespace. Motion and ornament are semantic
   (fixed effect vocabulary, section 3.4); symbol popups are item cards
   backed by real metrics; density never sacrifices the latency budget —
   all animation is frontend-local, zero transport. **GUI frontends design
   to the top of their medium**: the browser and Vulkan renderers use full
   graphics power (GPU animation, real typography, unconstrained overlays).
   Text-mode rendering (valk-lsp text-cards, a possible future TUI frontend)
   is a per-renderer degradation concern, never a design ceiling — the
   widget protocol carries full semantic information and each renderer maxes
   out what its medium can do with it.
4. **All IDE logic in Valk.** C work is limited to missing runtime primitives.
5. **UI is data.** Tools produce widget trees (Valk data); render backends
   (browser now, Vulkan/imgui later) interpret them. No tool knows how it is
   drawn.
6. **In-process over RPC.** The LSP engine, symdb, and profiler are libraries
   linked into the machine, not subprocesses. RPC is reserved for process
   boundaries that must exist: the browser, the debugged target, neovim.
7. **Remote access = thin client, not wasm.** The machine runs natively; the
   browser is a display over HTTP/2. A wasm build of the runtime is explicitly
   deferred (GC + libuv + LLVM port is out of scope).

## 2. System architecture

```
              ┌──────────────────────────────────────────────┐
              │  valk-ide (the machine, one Valk process)     │
              │                                               │
              │  ui-sys (dedicated aio system, input path)    │
              │  └── UI server        HTTP/2 + SSE, keymaps   │
              │  work systems (separate aio systems/loops)    │
              │  ├── LSP engine       lsp/* in-process        │
              │  ├── symdb            .valk/symdb.sqlite      │
              │  ├── REPL kernel      sessions -> envs        │
              │  ├── Debug client     attaches to targets     │
              │  ├── Build/run        aio/exec, fs/watch      │
              │  └── Doc service      symdb doc column        │
              └───────┬───────────────────────┬───────────────┘
                      │ widget protocol       │ debug protocol
                      │ (HTTP/2 + SSE)        │ (HTTP/2 + SSE)
        ┌─────────────┴───┐          ┌────────┴──────────────┐
        │ browser client  │          │ target app             │
        │ (thin JS render)│          │ (game/engine, child or │
        └─────────────────┘          │  attached Valk process, │
        ┌─────────────────┐          │  runs debug/serve)      │
        │ vulkan client   │          └────────────────────────┘
        │ (phase 5, same  │          ┌────────────────────────┐
        │  protocol)      │          │ nvim --embed (phase 3)  │
        └─────────────────┘          │ msgpack-rpc child       │
                                     └────────────────────────┘
```

Existing infrastructure this builds on (verified):

- `http2/server-listen sys port handler` with plist responses and async-handle
  responses (`runtime/src/builtins_server.c:14`); `req/*` accessors
  (`runtime/src/aio/aio_http_builtins.c:174`).
- Incremental streaming: `stream/open`, `stream/write`, `stream/closed`
  (`runtime/src/aio/http2/stream/aio_stream_builtins.c:416`) and the SSE layer
  `stdlib/aio/sse.valk` + multi-client `stdlib/aio/debug-broadcaster.valk`.
  The route-table pattern in `stdlib/aio/debug.valk:147` is the template for
  the UI server.
- LSP feature functions are plain Valk (`lsp/nav.valk`, `lsp/features.valk`)
  over pure layers `symdb/*` and `sem/*`; workspace init is self-contained
  (`lsp/init-workspace`, `lsp/workspace.valk:331`).
- `json/parse` / `json/encode` (`runtime/src/builtins_json.c:199`).
- AOT (`valk --build`) for shipping `build/valk-ide` like `build/valk-lsp`.

## 3. UI model: Elm-style tools over a widget protocol

### 3.1 Tool contract

A tool (pane) is a record:

```lisp
{:id        :repl
 :title     "REPL"
 :init      (\ {} initial-state)
 :update    (\ {state event} new-state)     ; pure
 :view      (\ {state} widget-tree)         ; pure
 :subs      (\ {state} subscriptions)       ; optional: timers, process events
 :commands  (\ {state} command-list)}       ; named commands (section 3.3)
```

The machine owns state, runs `update` on events, re-runs `view`, and ships the
result to connected clients. This model works identically for the browser
backend (tree diffed and patched into DOM) and the future imgui backend (tree
interpreted per frame). Tools never touch transport.

### 3.2 Widget tree

Widget trees are plists, JSON-encodable with the existing `json/encode`
plist->object mapping. Core widget set for phases 0–2:

```lisp
{:w :root    :panes [...] :layout {:type :dock :splits [...]}}
{:w :panel   :id "repl" :title "REPL" :children [...]}
{:w :text    :runs [{:t "(defun" :style :keyword} {:t " foo" :style :symbol}]}
{:w :input   :id "repl-in" :multiline :true :submit :repl/eval :complete :true}
{:w :list    :id "..." :items [...] :on-select :repl/inspect}   ; command id
{:w :tree    :id "..." :nodes [{:label ... :children-lazy :true :key ...}]}
{:w :table   :id "..." :cols [...] :rows [...]}
{:w :tabs    :id "..." :tabs [...] :active ...}
{:w :button  :id "..." :label "Run" :cmd :repl/eval}   ; click = run command
{:w :badge   ...}  {:w :divider}  {:w :spinner}
{:w :statusline ...}   ; mode, pending key sequence, focused pane
{:w :keyhints   ...}   ; which-key popup: available continuations of a sequence
{:w :card    ...}      ; API item card: tier, art, stats (section 3.4)
{:w :sparkline :vals [...]}   ; inline micro-chart for dense stat rows
```

Any widget or `:text` run may additionally carry `:effect` (`:blink`,
`:flash`, `:pulse`, `:dim`, `:shimmer` — semantics and rationing in section
3.4).

Interactive widgets (`:input`, `:list`, `:tree`, `:table`, `:tabs`,
`:button`) are **focusable** and participate in the focus order (section
3.3). They never bind raw keys themselves: `:list`/`:tree`/`:table` receive
navigation *commands* (down, up, expand, primary-action, filter), and
`:button`/`:on-select` wire to command ids. The pane framework rejects widget
trees that attach actions to anything other than a command, which makes
mouse-only interactions unrepresentable by construction.

Later widgets: `:grid` (nvim cell grid), `:timeline` (profiler), `:nodegraph`
(node editors), `:memview` (debugger memory), `:canvas` (custom draw list for
the imgui backend).

Styles are semantic (`:keyword`, `:string`, `:error`, `:dim`, ...) and mapped
to colors by the frontend theme, so semantic-token output from `sem/*` maps
directly onto `:text` runs.

### 3.3 Interaction model: commands, modes, keymaps, focus

Frontends send **raw key events**; the machine interprets them. Mode state,
keymap tables, and pending-sequence state live in the machine, so keybindings
are data, behave identically in the browser and imgui frontends, and are
inspectable/rebindable like everything else.

**Commands are the primitive.**

```lisp
{:cmd :repl/eval  :title "Eval input"  :pane :repl
 :keys ["<CR>"]              ; bindings, in pane keymap
 :when (\ {state} bool)}     ; optional availability predicate
```

- Every action in the IDE is a named command: key sequences, palette
  entries, buttons, and list selections all resolve to a command invocation,
  dispatched to the owning tool's `update` as `{:type :cmd :id :repl/eval}`.
- The machine merges tool `:commands` lists into a global registry. The
  **command palette** (`SPC SPC`) fuzzy-searches it and shows each command's
  current binding — discoverability is a registry query, not documentation.
- A `:button` is a mouse alias for a command; hover shows the binding.

**Modes.** Two global modes, tracked per client, shown in `:statusline`:

- `:normal` — keys are commands and navigation. Default mode; `Esc` always
  returns here from anywhere.
- `:insert` — keys are text for the focused editable widget.

Within them:

- **Vim grammar in text-editing widgets.** Multiline `:input` widgets (REPL
  input, eval-in-frame, search fields) run a shared modal editing machine,
  `ide/edit.valk`: a pure `(keymap-state, key) -> action` reducer implementing
  a deliberately small vim subset (motions, counts, operators d/c/y, a few
  text objects). Implemented once, used by every `:input`. Full vim lives in
  the nvim pane (section 8); `ide/edit.valk` must not grow toward it.
- **Leader sequences everywhere else.** `SPC` in normal mode starts a
  sequence; after each key the machine pushes a `:keyhints` popup with the
  available continuations (which-key). The binding tree is generated from the
  command registry under mnemonic namespaces: `SPC f` files, `SPC b`
  panes/buffers, `SPC w` windows/layout, `SPC r` REPL, `SPC d` debugger,
  `SPC s` search, `SPC SPC` palette.
- **Normal-mode navigation in data widgets.** `:list`/`:tree`/`:table` get
  `hjkl`, `gg`/`G`, counts (`3j`), `/` filter, `Enter` primary action,
  `za`-style expand/collapse — bound once per widget class as navigation
  commands, not per tool.

**Focus.** Exactly one focused widget per client, tracked by the machine.
`SPC w h/j/k/l` moves pane focus directionally; `Tab`/`S-Tab` cycles
focusables within a pane; a mouse click also focuses (secondary path).
Key routing: raw key -> client mode + pending sequence -> resolved against
focused-widget keymap, then pane keymap, then global keymap -> command
dispatch or text insert.

**Latency.** The key-to-glyph path is the hottest path in the IDE and is
engineered as one (principle 1):

- **Isolation.** The UI server, key routing, and `ide/edit.valk` run on a
  dedicated aio system (`ide/ui-sys`, the `lsp/idx-sys` isolation pattern).
  Session eval, indexing, builds, and debug I/O run on other systems. A stuck
  eval, a scan of the workspace, or a blocked debug target can never delay a
  keystroke. Tool `update`/`view` for heavy panes may be dispatched off
  ui-sys, but key resolution and input echo never are.
- **Input fast path.** A key event does not trigger a full `view` re-run.
  For insert-mode text and normal-mode motions, `ide/edit.valk` applies the
  edit and the machine immediately emits a minimal `ui-patch` scoped to the
  focused widget (buffer delta + cursor). Full `view` re-renders of affected
  panes are coalesced behind it (per SSE flush tick, ~one frame), so heavy
  panes redraw lazily while the echo is instant.
- **Budget.** Machine-side key-event-in to echo-patch-flushed: p99 ≤ 5 ms,
  localhost key-to-glyph well inside one 60 Hz frame. Every key event carries
  a client timestamp; the echo patch returns it, so the frontend measures
  true key-to-glyph. Histograms live in a latency pane (`SPC m l`) and are
  asserted by a scripted latency UAT per phase — a budget regression blocks
  the phase.
- **Backpressure.** SSE writes to a slow client must never queue behind other
  clients or grow unboundedly: per-client outbound buffers, coalesce
  full-tree patches (drop superseded), never coalesce echo patches.
- **Remote clients.** Insert-mode local echo (apply optimistically, confirm
  via `ui-patch`) is a frontend optimization requiring no protocol change;
  build it when remote use is real.

### 3.4 Visual language: artistic, dense, semantic motion

Direction: **informationally dense and artistic**. The reference points are
trading terminals, RAD debugger, and RPG item screens — not minimal web
apps. Prefer small type, multi-column stat rows, sparklines, and saturated
information over whitespace; every pixel earns its place. Density stays
readable because color, motion, and ornament are all *semantic* — drawn from
a fixed vocabulary, never ad hoc.

**Semantic effects.** Alongside semantic styles (`:keyword`, `:error`, ...),
any widget or text run may carry an `:effect`. Effects are declarative
attributes: the machine ships the attribute once and the frontend animates
locally (CSS in the browser, per-frame interpolation in imgui). The machine
never streams animation frames — motion costs zero transport (principle 1).

- `:blink` — **requires action now**. Strictly rationed: valid only on a
  framework-level whitelist of conditions (breakpoint hit, fatal error,
  data-loss prompt). The pane framework rejects other uses, same as the
  command-only action rule (section 3.2).
- `:flash` — one-shot highlight that decays (~300 ms): a value changed
  (watch table, metrics cell) — the RAD-debugger change signal.
- `:pulse` — ongoing activity: eval running, target attached, stream live.
- `:dim` — stale, inactive, unfocused, dead code, unavailable command.
- `:shimmer` — cosmetic: tier frames (below), fresh-result glint.

**API cards.** Every symbol popup — hover, completion detail, palette
preview, doc pages — renders as an **item card** (`:card` widget), because
the machine actually holds the stats to back it:

```lisp
{:w :card
 :symbol "aio/race"
 :tier :legendary               ; computed maturity tier
 :art  {:proc "a3f9..."}        ; procedural seed, or {:asset "aio-race.svg"}
 :sig  "[handles] -> handle"
 :doc  "Settles when the first child settles; ..."
 :stats [{:k :used    :v 47}      ; symdb refs
         {:k :cov     :v 0.92}    ; coverage tooling
         {:k :age     :v "2y"}    ; git history
         {:k :churn   :v :low}    ; git history
         {:k :fan-out :v 6}       ; quality snapshot
         {:k :lat-p50 :v "3µs"}   ; bench/profile data, when available
         {:k :cx      :v "O(n)"}]}; declared annotation, when present
```

- **Tier = composite maturity score** (coverage, doc presence, age, churn,
  usage) mapped to `:common`/`:uncommon`/`:rare`/`:epic`/`:legendary`. The
  frame treatment carries the tier — gray edge up to `:shimmer` legendary
  border. The tier is an incentive mechanism: documenting and testing your
  API visibly upgrades its card.
- **Never computed on the hover path.** A card service computes tiers and
  stat rows at index time and caches them in symdb (parallel table, refreshed
  by `lsp/scan-file`). Showing a card is a single cached lookup — popups are
  on the input hot path and inherit the latency budget (section 3.3).
- Algorithmic complexity is a declared annotation (extend `sig`/doc
  metadata), shown only when present; measured latency from bench data is
  the honest default stat.

**Artwork.** Procedural-first: each symbol's art is generated
deterministically from its identity hash — palette, geometry, and motion
parameters rendered natively by each frontend (CSS/canvas now, imgui draw
list later). Every API gets unique animated art for free, and it works as a
**visual fingerprint**: you recognize `aio/race` by its art the way a card
player recognizes card art. Curated overrides live in `ide/art/` (static SVG
plus optional motion params in the same procedural format) for APIs someone
cares enough to illustrate. No heavyweight animation formats (Lottie, video)
— every format must be cheap to render in both backends.

The visual language is designed **GUI-first** (principle 3): effects, tier
frames, and art assume real graphics — gradients, glow, alpha, GPU-cheap
motion. A future TUI frontend would reuse the text-card renderer (section 8)
and collapse effects to what cells allow (bold/reverse/blink-attr); that is
that renderer's problem, and it never constrains what the GUI ships.

`:card` and `:sparkline` join the core widget set in phase 1 alongside the
rich REPL.

### 3.5 Transport (browser backend)

- `GET /` — shell HTML + single JS renderer file (served from `ide/web/`,
  embedded as strings for the AOT build).
- `GET /events?client=ID` — SSE stream. Machine pushes:
  - `ui-patch` — widget-tree patches (v0: full tree per dirty pane; diffing is
    an optimization, not a protocol change)
  - tool-specific events (e.g. `repl-out` chunks)
- `POST /event` — JSON `{:client ID :event {:type :key :key "j" :mods []}}`
  or `{:type :click :widget "run-btn"}`. Response `{:ok :true}`; resulting UI
  changes arrive via SSE. The frontend sends every key raw (section 3.3) and
  never interprets bindings; clicks carry only the widget id and are resolved
  to the same commands as keys. The frontend does no local editing — `:input`
  contents are machine state rendered like everything else (local echo is an
  optional optimization, section 3.3).
- Multi-client: the broadcaster pattern from `debug-broadcaster.valk`; each
  client has its own layout state, tools' domain state is shared.

Known issue: `http2/server-listen` is hardcoded TLS with self-signed
`build/server.{key,crt}` (`builtins_server.c:69`). Browsers will warn.
Resolution options (pick during phase 0): (a) document one-time cert trust,
(b) mkcert-style local CA generation in `make ide`, (c) add an h2c/HTTP1
cleartext option to the server builtin for localhost. (c) is preferred
long-term; (a) is acceptable for phase 0.

*Decided (phase 0)*: the Makefile already generates `build/server.{key,crt}`
via mkcert when installed (browser-trusted, zero friction) with an openssl
self-signed fallback — option (b) was effectively already built. (c) remains
open as a long-term nicety.

*Implemented protocol notes*: `POST /event` required server-side request
bodies, which the HTTP/2 stack did not collect — handlers fired on HEADERS
before DATA arrived. The server now buffers bodies (capped by the existing
`max_request_body_size` config) and invokes handlers at END_STREAM. Keys
are normalized client-side to the binding notation (`SPC`, `CR`, `ESC`,
`BS`, `TAB`, `UP`, `DOWN`); echo latency is measured with µs client
timestamps riding the chrome patch.

### 3.6 Tunability: mechanism vs policy

Everything in 3.1–3.5 will need tuning — tier weights, effect timings, key
bindings, stat selection, art parameters, density. The implementation rule
is uniform: **mechanisms are small pure functions; policy is data in
registries.** A tuning change is a data edit, never a code change. And since
the machine *is* a lisp machine, policy is editable live: open a REPL
session on the IDE's own env (section 4), redefine an entry, re-render,
judge, iterate. `ide/config.valk` holds user/project overrides merged over
defaults; a reload command (`SPC m r`) re-applies it, `fs/watch` makes it
automatic in phase 4.

The registries:

- **Keymaps, leader tree, commands** — already data (section 3.3); rebind
  and extend at runtime.
- **Stat providers** — `{:k :cov :label "COV" :render :percent
  :provider (\ {sym ctx} val)}`. The card service folds the provider list at
  index time; a new card stat is one entry, the service never changes.
- **Tier scoring** — a list of scorers `{:k :coverage :weight 0.3
  :score (\ {stats} unit-interval)}` plus a threshold table mapping the
  weighted sum to `:common..:legendary`. Weights and thresholds are the
  expected tuning surface; scorers compose and individual scores are kept on
  the card data for debugging ("why is this rare?").
- **Effects + theme** — `style -> color` and `effect -> motion params`
  (period, decay, amplitude) tables, shipped to frontends as data at connect
  time. Retuning a pulse rate or retheming touches no renderer code; only a
  genuinely new effect *kind* needs frontend work (one CSS class, one imgui
  interpolator).
- **Art generators** — registry keyed by generator id; `{:proc {:gen :v1
  :seed ...}}` is versioned data, so generators can be added or evolved
  without touching card code or invalidating curated overrides.
- **Card fragments** — a card `view` is composed from fragment functions
  (art band, tier frame, stat row, doc excerpt, refs list), each
  `(\ {card-data} widget)`. Compact hover card vs full doc-page card are
  different compositions of the same fragments over the same data; other
  panes reuse fragments directly (the inspector embeds just the stat row).

Two guardrails: registries never override framework invariants (`:blink`
whitelist, command-only actions, the latency budget hold regardless of
config); and a registry is added only when a tuning surface is proven —
default to a plain function until the second consumer or the second tuning
request shows up.

## 4. Session model (REPL kernel)

A **session** is a named, first-class environment plus history:

```lisp
{:id "main" :env <env-ref> :history [...] :created-at ...}
```

Semantics:

- Sessions eval in their own env whose parent is the machine's root env, so
  IDE internals are callable but session bindings don't leak.
- `attach` sessions: a session whose eval is proxied to a *target process*
  over the debug protocol (section 5). The REPL UI is identical; only the
  executor differs. This is how "attach to the app's env" works.
- Eval runs via `aio/dispatch` on a worker loop (the LSP's threading model,
  `runtime/src/builtins_pipe.c:577`), so a long eval never blocks the UI
  server. Cancel = `aio/cancel` on the dispatch handle.

Rich REPL features, all in-process:

- **Modal input**: the REPL input is a multiline `:input` driven by
  `ide/edit.valk` (section 3.3) — vim motions/operators on the buffer,
  `Enter` in normal mode evals, history walk (`C-p`/`C-n` or `k`/`j` at
  buffer edges) as commands.
- **Highlighting**: `sem/lex-tokenize` / `sem/tokenize-ast` on the input
  buffer -> `:text` runs. Re-tokenized on input events (debounced).
- **Completion**: `symdb/completion-all` + session env bindings via `penv`
  (`runtime/src/builtins_env.c:130` returns bindings as data). The selected
  completion's detail is its item card (section 3.4); hover likewise.
- **Value inspectors**: eval results are rendered as lazy `:tree` widgets, not
  strings — plists/lists expand on demand; refs/handles show type + state;
  large values paginate. An `inspect` protocol (multimethod on type) lets
  tools register custom renderings (e.g. an aio handle shows its state
  machine).
- **Env browser**: table over `penv` of the session env; editing a binding is
  `(env/eval session-env (list 'def (list name) value))`.

**Required C work** — envs are not reified in Valk today (`eval` takes no env
arg, `builtins_list.c:170`). Add a small builtin group wrapping `valk_lenv_t`
(already first-class in C, `parser.h:135`) as an `LVAL_REF`:

```lisp
(env/new)              ; child of root env -> env ref
(env/new parent-ref)   ; child of given env
(env/eval env expr)    ; valk_lval_eval(env, expr)
(env/bindings env)     ; penv, but for a given env, one level
(env/parent env)
```

*Implemented (phase 1)*, with three findings the original sketch missed:

1. **GC tracing**: an env ref is the first `LVAL_REF` whose payload is GC
   memory. `ref.mark` is wired to an exported `valk_gc_mark_env_ref` shim so
   the ref traces its env like a closure's `fun.env`. Envs never move, so
   the raw pointer stays valid; without the mark the env's arrays are swept.
2. **Session isolation is not free**: `def` walks to the outermost env, so
   session defs landed in the global env. `env/new` envs now carry
   `LENV_FLAG_DEF_BOUNDARY`, which stops the walk — root builtins callable,
   session bindings contained, exactly the semantics promised above.
3. **`env/eval` mirrors `eval`** (unwraps a quoted top-level form so the
   `(env/eval env {code})` idiom works), which is wrong for evaluating
   *parsed* source: a literal `{...}` typed at the REPL would be called.
   The REPL therefore skips eval for `quoted?` top-level forms, matching
   loader semantics. Both idioms hold.

`env/bindings` uses `valk_lenv_snapshot` (works on the cmap-backed root
env), which is also what feeds REPL completion with builtin names.

## 5. Debugger

### 5.1 Model

Every Valk runtime can host a **debug server**; the IDE is a **debug client**.
Same protocol whether the target is:

- a child process the IDE launched (`run` button),
- an already-running app you attach to (the game),
- the IDE machine itself (self-debugging; guarded, see risks).

### 5.2 Runtime support (C work)

1. **Unconditional source positions.** Today `cov_file_id/cov_line/cov_column`
   exist only under `VALK_COVERAGE` (`runtime/src/parser.h:163`). Make them
   available in debug-info builds (`VALK_DEBUG_INFO`, default-on for dev
   builds; measure lval size impact — 6 bytes/lval — before deciding
   default-on for release).
2. **Eval hook.** Single insertion point at the top of the continuation-stack
   loop, `runtime/src/eval.c:498-508`, where `valk_thread_ctx.eval_expr/
   eval_value/eval_env` are already published and `VALK_GC_SAFE_POINT()`
   runs. Add a thread-local `debug_flags` check (same cost profile as the
   safepoint check):
   - breakpoint table lookup keyed `(file_id, line)` — hash set, only when
     debugging enabled;
   - step state: `:in`, `:over` (target continuation-stack depth), `:out`.
3. **Pause = park at the hook.** On hit, the paused thread publishes
   `{stack, expr, env}` and blocks on a condvar until resume. The debug
   server runs on a **dedicated aio system** (like `lsp/idx-sys`), so it can
   serve inspection requests while worker/main threads are parked. Interaction
   with GC STW must be defined: a parked thread counts as at-safepoint.
4. **Stack + frames.** The explicit continuation stack in
   `valk_lval_eval_iterative` is walkable: expose frames as
   `(expr src-pos env)` triples. `debug/frames`, `debug/frame-env i`.
5. **`debug/serve sys port`** builtin/stdlib fn: starts the debug HTTP/2
   endpoint inside any app that opts in (a game adds one line; the IDE injects
   it automatically for processes it launches, via a `--debug-port` runtime
   flag).

### 5.3 Wire protocol

JSON over HTTP/2, events over SSE — reuses the exact stack from section 3.5.

```
POST /dbg/break        {:file "src/game.valk" :line 42}     -> {:id N}
POST /dbg/unbreak      {:id N}
POST /dbg/continue     {}
POST /dbg/step         {:mode :in|:over|:out}
POST /dbg/pause        {}                    ; async interrupt via safepoint
GET  /dbg/stack        -> [{:i 0 :file ... :line ... :expr "..."}]
GET  /dbg/frame/N/env  -> [{:name ... :preview ... :key ...}]   ; lazy values
POST /dbg/eval         {:frame N :expr "..."}                   ; eval-in-frame
GET  /dbg/events       SSE: breakpoint-hit, paused, resumed, exited, output
GET  /dbg/mem          -> mem/stats, mem/gc/*, arena stats     ; already exist
GET  /dbg/aio          -> aio/systems-json, aio/metrics-json   ; already exist
```

The protocol is deliberately DAP-shaped so a thin `valk-dap` adapter can later
expose it to nvim/VS Code without touching the runtime.

*Implemented (phase 2)*: `stdlib/aio/debug-server.valk` serves everything
above except `/dbg/pause` and `/dbg/events` (SSE). `POST /dbg/step` takes
`{:mode "in"|"over"|"out"}` (default in): step-in pauses at the next
expression on a different line at any depth; step-over additionally requires
same-or-shallower call depth (`valk_thread_ctx.call_depth`, snapshotted at
resume by the stepping thread itself); step-out requires strictly shallower
depth and ignores the line. The IDE
polls `/dbg/state` on its tick instead of subscribing to SSE; both are listed
as remaining work in section 11. `/dbg/frame/N/env` shipped as
`/dbg/frame/N/bindings`. Frame envs are first-class env refs on the serving
side, so eval-in-frame and locals are just `env/eval` + `env/bindings` —
the section 4 builtins doing double duty, no new inspection machinery.

Runtime details that were only sketches above and are now real
(`runtime/src/debugger.c`):

- the eval hook is one relaxed atomic load + predicted-not-taken branch at
  the safepoint site; overhead measured (section 12);
- a paused thread parks with the `aio/run` eventcount loop
  (`park_prepare` / `SAFE_POINT` / `park_seq`) — a bare condvar would
  deadlock the STW barrier, since every registered thread must actively
  rendezvous and participate in collection. Parked threads keep their eval
  state rooted and evacuation-updated for free;
- frame snapshots are built by the pausing thread itself (data into the
  GC-rooted handle table, env pointers in a C array — envs don't move);
- sub-expressions share source lines, so resume suppresses re-hits on the
  resume line until the thread reaches a different line; suppression and
  step state are packed into single atomic words (TSAN-clean);
- v1 pauses one thread at a time; a second thread hitting a breakpoint
  while one is paused skips through.

### 5.4 Visualization (RAD-debugger-inspired)

All frontend-side, built from the protocol + existing introspection:

- all debugger actions are commands (section 3.3): `SPC d` namespace
  globally, plus single-key normal-mode bindings while a debugger pane is
  focused (`n` step-over, `s` step-in, `f` step-out, `c` continue, `b`
  toggle breakpoint on cursor line) — gdb muscle memory, no clicking through
  toolbars;
- watch table with live re-eval on step; structured value trees (same
  inspector as the REPL); changed values `:flash`, stale frames `:dim`,
  breakpoint-hit `:blink` (the canonical whitelisted use, section 3.4);
- aio topology view: systems/loops/handles from `aio/systems-json`, handle
  state machines, parent/child chains — live handles `:pulse`, settled ones
  `:dim` — this is the "game engine async" killer feature;
- memory pane: GC generations, arena pools, allocation deltas per step;
- profiler pane: drive `profile/flamegraph.valk` (perf -> SVG already works)
  against the target pid, render inline;
- source pane: file with breakpoint gutter + current-line highlight, semantic
  highlighting from `sem/*` (read-only in phase 2; the real editor is nvim).

*Implemented (phase 2)*: the debugger pane (`ide/debugger.valk`) covers
attach/detach, the paused banner (`:blink` — the whitelisted use), stack
table, and frame-0 locals; `SPC d a/q/c/s/n/f` globally plus bare
`c`/`s`/`n`/`f` (continue, step-in, step-over, step-out — the gdb muscle
memory promised above) when the pane is focused (pane-scoped commands may
carry `:run`, so effectful bindings stay pane-keyed). Breakpoints are set from the REPL via
`(ide/dbg-break file line)` until the source pane exists. Watch table, aio
topology, memory and profiler panes remain.

### 5.5 Native-code debugging

Out of scope for the Valk debugger. The IDE drives `gdb`/`rr` via the
interactive subprocess primitive (section 8) speaking GDB/MI, shown in the
same frontend panes. Phase 6+.

## 6. LSP engine reuse

The feature handlers (`nav/handle-hover` etc.) respond by side effect via
`lsp/send-response` (`lsp/io.valk`) rather than returning values. Bridge:

- **Refactor, don't rebind**: split each handler into a pure core
  `nav/hover* params -> result` and a thin JSON-RPC wrapper that calls it and
  sends. The stdio LSP keeps working; the IDE calls the cores directly.
  This is a mechanical refactor in `lsp/nav.valk` + `lsp/features.valk` and
  benefits LSP testing independently.
- Pure cores return **data, not prose**: `nav/hover*` returns card data
  (section 3.4). The IDE renders it as a `:card` widget; the stdio wrapper
  renders it as a markdown/unicode text-card for external editors (section
  8). One data source, per-client renderers.
- The IDE creates its own workspace via `lsp/init-workspace` +
  `lsp/collect-workspace-files` + `lsp/scan-all` on a dedicated indexing
  system, exactly like `lsp/start` (`lsp/lsp.valk:332`) minus the stdio
  loops.
- One symdb (`.valk/symdb.sqlite`) shared by design with external valk-lsp
  instances (nvim's client), since indexing is idempotent and sqlite handles
  concurrent readers. Verify locking behavior under concurrent scan in phase
  1; fall back to separate DBs if contention shows.

*Implemented (phase 1)*, with deviations:

- `nav/hover*` and `nav/completion*` exist as pure cores; the remaining
  handlers still await the same mechanical split. Hover cores return the
  LSP result shape, not card data — the card service (`ide/cards.valk`)
  builds cards from `symdb/symbol-hover-in` directly, so the "cores return
  card data" refinement is still open.
- The IDE indexes **synchronously at startup** via per-file
  `lsp/seed-from-disk` (fingerprint-checked, warm runs near-instant) rather
  than `lsp/scan-all` on a dedicated system — scan-all hard-codes the
  lsp/sys + lsp/idx-sys globals and progress notifications. Background
  re-indexing arrives with `fs/watch` (phase 4).
- Fixed upstream while wiring hover: doc comments above `(sig ...)` forms
  indexed to nothing (the stdlib's own doc convention was invisible), and
  `symbol-hover-in` dropped a doc held by a sibling row of the same name.
  Both fixed at the source (`lsp_index.c`, `symdb-query.valk:doc-of-any`)
  — external editors benefit too.
- Practical note for embedders: record accessors (`SymInfo:name x`) resolve
  against types known at *load* time — load `symdb/symdb-types.valk` before
  any file whose body names them; bare `info:field` syntax needs a sig'd
  param type and otherwise silently degrades to plist lookup.

## 7. Documentation viewer

- Source of truth: symdb `symbols.doc` (doc comments already extracted,
  `runtime/src/lsp_index_emit.c:57`) + `sig` declarations + refs (examples =
  call sites).
- Doc service renders: symbol pages as **full-size item cards** (section
  3.4: tier frame, artwork, stat rows, then doc, signature, source excerpt,
  references, load-graph location), module pages (per-file symbol listing —
  a card gallery, sortable by tier/usage/coverage), search (symdb
  `search-symbols`). The hover popup is the compact form of the same card.
- Rendered as widget trees like any pane — no separate browser engine, no
  chromium embed. Markdown in doc comments is parsed to `:text`/`:list`
  widgets (small pure-Valk markdown subset parser).
- When a real documentation system lands, it publishes into symdb (or a
  parallel table) and the viewer picks it up; the pane is the integration
  point, deliberately thin now.

## 8. Editor integration (neovim)

Phase 3. Architecture is the Neovide model:

- machine spawns `nvim --embed` (interactive subprocess, section 9.1), speaks
  msgpack-rpc, calls `nvim_ui_attach` with `ext_linegrid`;
- redraw events -> `:grid` widget (cells + highlight ids -> semantic styles);
  keyboard events from the frontend -> `nvim_input`;
- **the grid is data, not a terminal** (principle 3): GUI renderers put full
  graphics on top of it, exactly Neovide's move — GPU-smooth scrolling,
  animated cursor trail, per-float shadows and rounded corners, semantic
  effect treatments on diagnostic cells, card overlays composited above with
  real alpha. nvim supplies cell contents; the frontend owns everything
  about how cells look and move. The cell grid constrains buffer text
  *layout*, never rendering quality;
- **key routing**: when the editor pane is focused, the machine forwards raw
  keys straight to `nvim_input` — nvim owns its modes, no double
  interpretation. Leader UX stays uniform: nvim's normal-mode `SPC` is mapped
  (via the injected config) to `rpcnotify` back to the machine, entering the
  same leader-sequence engine as every other pane. One global prefix
  (`C-SPC`, machine-handled in all panes unconditionally) is the escape hatch
  for pane switching even if nvim is stuck in a pending state;
- nvim is configured to use `build/valk-lsp` (stdio, as today) so editor
  intelligence is identical inside and outside the IDE;
- **hover = card overlay, not nvim float.** nvim's cell grid cannot render
  tier frames, art, or effects, and we control both sides of the embed, so:
  the injected config disables nvim's own LSP hover UI; `K` (and CursorHold,
  if enabled) `rpcnotify`s the machine with buffer + cursor; the machine
  resolves the symbol via the in-process LSP core, fetches the *cached* card
  (section 3.4 — single lookup, no index work on the hover path), and
  renders it as an **overlay widget anchored to the cursor cell** above the
  `:grid` (ext_linegrid gives exact cell coordinates from redraw state).
  Dismissal mirrors float semantics: any cursor-move or mode-change redraw
  event clears the overlay, so scrolling can never desync a stale card;
- **completion via `ext_popupmenu`.** The completion menu is externalized
  through nvim's UI protocol: nvim sends items + selection, the machine
  renders the menu as widgets with the selected item's compact card as the
  detail panel — identical to REPL completion. Selection state stays in
  nvim; the machine only renders;
- **in-buffer decoration stays nvim-native.** Semantic highlight groups are
  generated from the theme table (section 3.6), so editor and IDE colors
  share one source; diagnostics and breakpoints use signs/gutter as usual.
  Cell-grid effects are limited to highlight changes; full effects live in
  overlays;
- **standalone nvim degrades gracefully.** The section 6 pure cores return
  card *data*; renderers differ per client. The IDE renders `:card` widgets;
  the stdio valk-lsp wrapper renders the same data as a unicode/markdown
  text-card (tier as `★★★★`, stat row as aligned text) in the normal hover
  float. External editors get the density without the chrome — one data
  source, two renderers;
- the debugger surfaces to nvim via the DAP adapter (5.3), so breakpoints set
  in the editor and in the debugger pane are the same breakpoints (machine is
  the source of truth).
- msgpack codec: pure Valk first (encode/decode over strings); move to C
  builtin only if profiling demands it.

## 9. Build / run / live loop

- `run`: `aio/exec` (batch) is insufficient; use `proc/spawn` (9.1) so the
  IDE gets incremental stdout/stderr (streamed to an output pane) and can
  signal/kill. Launched processes get `--debug-port 0` and report the bound
  port on a handshake line, enabling one-click attach.
- `build`: `valk --build` via `proc/spawn`, errors parsed into diagnostics
  (same shape as LSP diagnostics, shown in the same problems pane).
- `watch`: `fs/watch` (9.2) triggers re-index (`lsp/scan-file`) and optional
  rebuild/rerun. The LSP's polling fallback remains for the stdio server.
- live-coding path for the game case: attach session (section 4) + re-eval
  changed top-level forms in the target env — form-level hot reload without
  restarting the process. Requires nothing beyond `debug/eval` on an attach
  session; granularity/rollback policies are tool-level concerns.

## 10. New runtime primitives (all C work, consolidated)

| # | Primitive | Notes | Phase | Status |
|---|-----------|-------|-------|--------|
| 1 | `env/new`, `env/eval`, `env/bindings`, `env/parent` | wrap `valk_lenv_t` as REF; small | 1 | **done** (+ `LENV_FLAG_DEF_BOUNDARY`, GC-traced env refs) |
| 2 | `proc/spawn` interactive subprocess | uv_spawn + UV_CREATE_PIPE stdio; returns `{:proc :stdin :stdout :stderr}` pipes; `proc/kill`, `proc/wait`. Pipe machinery generalizes from `builtins_pipe.c` (fd is already ctx-supplied, `builtins_pipe.c:143`) | 2 | open |
| 3 | `VALK_DEBUG_INFO` source positions | decouple from `VALK_COVERAGE` | 2 | **done** (`VALK_SRC_LOC` gate; dev default ON) |
| 4 | Eval debug hook + breakpoint table + park/resume | `eval.c:498` insertion point; GC-safepoint interaction | 2 | **done** (`runtime/src/debugger.c`; single paused thread v1) |
| 5 | Frame walk of continuation stack | expose to debug server | 2 | **done** (snapshot + env refs per frame) |
| 6 | `fs/watch` | `uv_fs_event` | 4 | open |
| 7 | h2c/cleartext option for `http2/server-listen` | localhost UX | 0–1 | not needed (mkcert certs from the Makefile are browser-trusted) |
| 8 | `gfx/*` (GLFW+Vulkan+imgui) | native frontend only | 5 | open |

Everything else is Valk. In particular the entire interaction model —
command registry, keymap engine, modes, `ide/edit.valk`, focus — is pure
Valk with zero new primitives — this held in practice.

Unplanned runtime work that turned out to be prerequisite:

- server-side HTTP request-body collection + handler dispatch at END_STREAM
  (bodies were never captured; `max_request_body_size` was config-only);
- `http2/client-post` (the client could not send bodies — needed for the
  debug wire client and for testing POST routes in-process);
- `valk_gc_mark_env_ref` export (first LVAL_REF with a GC payload).

## 11. Phases

Each phase ends with `make build && make test` green, lint clean, quality
diff clean, and a UAT-style scripted test where applicable.

- **Phase 0 — machine + shell.** `ide/` project: `ide/main.valk` starts aio
  systems, UI server (routes: shell, SSE, event POST), pane framework
  (init/update/view loop, broadcaster), **interaction core** (command
  registry, keymap engine, modes, focus model, key routing, `:statusline`,
  `:keyhints` which-key popup, command palette), **config layer**
  (`ide/config.valk` overrides merged over defaults, reload command —
  section 3.6), one trivial pane (machine
  status: mem/stats + aio metrics — reusing debug.valk data). ui-sys
  isolation, input fast path, and latency instrumentation land here — they
  are the foundation, not an optimization pass. The JS renderer implements
  semantic styles + the effect vocabulary (section 3.4) from the start —
  effects are CSS classes, near-free. Browser shows dockable panes.
  Acceptance: the status pane is fully drivable without touching the mouse,
  and the latency UAT passes its budget (section 3.3) while a worker loop is
  deliberately saturated. Decide TLS approach.
  **Done.** Latency UAT measured mean 150µs / worst 581µs machine-side under
  an allocation-churning work system — comfortably inside the 5ms p99
  budget. Deviation: the input fast path is not the minimal-`ui-patch`
  design — every keystroke re-renders the focused pane in full; the budget
  holds anyway at current pane sizes, so the coalesced echo patch remains
  an optimization for when it doesn't.
- **Phase 1 — rich REPL.** Env builtins (#1). Sessions, eval-on-worker,
  cancel, `ide/edit.valk` modal input machine, highlighting, completion,
  value inspector trees, env browser. LSP pure-core refactor (section 6) for
  completion/hover reuse. **Card service**: stat-provider and tier-scorer
  registries (section 3.6) folded into symdb at index time,
  `:card`/`:sparkline` widgets, card fragments, procedural art generator
  (`:gen :v1`), hover/completion rendered as cards.
  **Done except**: eval cancel (`aio/dispatch` returns no handle), the env
  browser pane (bindings feed completion but have no pane), `:sparkline`,
  and index-time card caching — cards are assembled on demand from single
  indexed lookups, which meets the latency budget today; the cache becomes
  necessary when stat providers grow git/coverage inputs. Card stats v1 =
  used/doc/sig; age/churn/coverage providers are registry entries waiting
  for their data sources. Only the `"main"` session is surfaced in the UI.
- **Phase 2 — debugger.** Primitives #2–5. `debug/serve`, wire protocol,
  debugger pane (source view, breakpoints, step, stack, frame env, watch,
  eval-in-frame), launch+attach of child Valk processes. aio topology and
  memory panes.
  **Core done** (see 5.2–5.4 notes): primitives #3–5, `debug/serve`, wire
  protocol, attach-based debugger pane with continue/step and live locals,
  verified end-to-end against a separate process from the browser.
  Step-over/out landed after the core: `call_depth`-gated step modes in the
  runtime, `{:mode ...}` on the wire, `n`/`f` pane bindings.
  Remaining: `proc/spawn` (#2) for launch+attach,
  `/dbg/pause`, SSE debug events (IDE currently polls on its tick), source
  pane with breakpoint gutter, watch table, aio topology + memory panes,
  multi-thread pause.
- **Phase 3 — editor.** `nvim --embed`, msgpack, `:grid` widget, input
  routing, card hover overlay (anchored to grid cells), `ext_popupmenu`
  completion with card detail, theme-generated highlight groups, text-card
  renderer in the stdio valk-lsp wrapper, DAP adapter for shared
  breakpoints.
- **Phase 4 — docs + build loop.** Doc viewer panes, `fs/watch`,
  build/run/problems panes, live re-eval into attach sessions.
- **Phase 5 — native frontend.** `gfx/*` builtins; imgui interpreter for the
  widget protocol; same IDE code, second display.
- **Phase 6 — engine tooling.** `:nodegraph`/`:timeline`/`:memview` widgets,
  profiler integration (flamegraph pane), gdb/rr MI driver, custom
  per-project config widgets.

## 12. Risks and open questions

- **Paused-thread vs GC/aio interplay** (phase 2): parked debug threads must
  count as at-safepoint; pausing loop-0 of the target while its debug system
  keeps serving needs a dedicated-system design like `lsp/idx-sys`. Prototype
  early in phase 2 before building UI on top.
  *Resolved*: "counts as at-safepoint" turned out to be the wrong model —
  the STW barrier requires every registered thread to actively participate
  in collection, so a passively-blocked thread deadlocks the coordinator.
  The pause loop is the `aio/run` eventcount pattern instead: STW wakes the
  parked thread, it collects, it re-parks. Verified by test (explicit
  collection while paused; frame envs stay valid). TSAN-clean.
- **Self-debugging reentrancy**: breakpoints in code the debug server itself
  runs would deadlock. Mitigate by scoping breakpoints to non-debug systems
  first; full self-debug is a stretch goal. *Still open; v1's
  single-paused-thread CAS additionally makes a second hit skip through
  rather than deadlock.*
- **TLS/browser friction** (phase 0 decision, section 3.5). *Resolved:
  mkcert certs from the Makefile; no browser warnings, no C work.*
- **symdb concurrent writers** (IDE indexer + external valk-lsp): verify in
  phase 1. *Held in practice — the IDE indexed the live workspace while a
  valk-lsp instance served the same db throughout development; sqlite
  locking plus idempotent indexing was sufficient.*
- **Widget protocol churn**: keep v0 minimal (full-tree updates, small widget
  set); diffing and exotic widgets only when a real pane needs them.
- **GC STW pauses vs the latency budget**: ui-sys isolation protects against
  blocked *loops*, but GC stop-the-world pauses are process-wide — a heavy
  in-process session eval allocating hard can pause ui-sys mid-keystroke.
  Mitigations, in order: keep the input fast path allocation-light; measure
  GC pause contribution in the latency UAT from phase 0 (the saturated-worker
  acceptance test must include an allocation-heavy eval); if budgets still
  blow, move heavy sessions out-of-process — the attach-session model
  (section 4) already proxies eval over the debug protocol, so demoting
  "in-process session" to "child-process session" changes no UX, only the
  executor. This escape hatch is why sessions and attach sessions share one
  interface.
  *Observed (phase 1)*: the risk is real. A pathological REPL eval (3M-frame
  non-tail recursion) filled the 800MB heap; GC entered a death spiral of
  ~450ms process-wide pauses with near-zero reclaim. The UI degraded but
  stayed alive (ticks kept flowing). Under normal churn the latency UAT
  holds its 5ms budget with margin. The child-process-session escape hatch
  is now concretely buildable — it needs exactly `proc/spawn` plus the
  debug protocol that already exists.
- **Remote keystroke latency**: machine-side key interpretation round-trips
  every keystroke. Acceptable on localhost; over a WAN, insert-mode typing
  will lag. Mitigation is frontend local echo with `ui-patch` confirmation
  (section 3.3) — plan for it, don't build it until remote use is real.
- **Injected nvim config vs user config** (phase 3): the embed relies on
  injected overrides (SPC rpcnotify, hover UI disabled, ext_popupmenu,
  theme-generated highlights). Users will want their own nvim config loaded
  too, and it may fight the overrides (its own LSP client, hover mappings,
  colorscheme). Policy: load user config first, apply IDE overrides after,
  document exactly what is overridden; keep the override layer small and
  inspectable (`:IdeOverrides` command listing them).
- **Registry sprawl**: "policy as data" invites premature abstraction. The
  section 3.6 guardrail (no registry before a proven tuning surface) is the
  defense; review at phase boundaries whether each registry earned itself,
  and collapse any that didn't back into plain functions.
- **Visual noise vs density**: density only works if the semantic vocabulary
  stays fixed and rationed. The `:blink` whitelist and effect lint are
  load-bearing; if ornament stops encoding data, cut it. Procedural art is a
  fun tar pit — timebox the generator, ship a simple param space first, and
  let curated overrides absorb ambition.
  *Status*: `:blink` used exactly once (breakpoint hit). The whitelist and
  command-only-action rules are convention today, not framework validation
  — the enforcement lint is still owed. Art generator was timeboxed as
  prescribed: `:gen v1` is a seeded bar-field, ~40 lines of JS.
- **Card staleness**: tiers/stats are cached at index time; a symbol edited
  but not yet re-indexed shows old numbers. Acceptable (same staleness as
  diagnostics); the card shows its index timestamp `:dim` when the file has
  unsaved/unindexed changes. *v1 computes on demand from indexed lookups
  instead of caching, so staleness currently tracks the index directly;
  the timestamp treatment arrives with the cache.*
- **`ide/edit.valk` scope creep**: a vim emulator is a tar pit. The shared
  input machine stays a small fixed subset (motions, counts, d/c/y, a few
  text objects); anything more belongs in the nvim pane. Review its size at
  each phase boundary. *Phase 2 review: 180 lines; h/l/j/k, 0/$, x, D,
  i/a/A/o — even smaller than the allowed subset (no counts/operators yet);
  pressure to grow it has been absent so far.*
- **eval hook overhead**: must be a single predictable branch when debugging
  is off; benchmark with `bench/` before/after. *Measured (phase 2)*: the
  hook branch is noise; the +8 bytes/lval from `VALK_DEBUG_INFO` costs ~16%
  on an allocation-bound microbenchmark (247ms → 286ms for 100k interpreted
  tail calls) — pure GC-churn scaling, far less on typical workloads.
  Decision: default ON for dev builds, `-DVALK_DEBUG_INFO=OFF` for release.
- **TUI frontend**: possible future backend (same widget protocol rendered
  into a terminal, reusing the text-card renderer and cell-safe effect
  subset). Explicitly not a current target; its existence must never pull
  GUI design toward lowest-common-denominator (principle 3).
- **Wasm**: consciously deferred. Revisit only if remote-thin-client proves
  insufficient (e.g. offline use). The widget protocol keeps the door open.
