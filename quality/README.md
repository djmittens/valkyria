# quality

Structural code-quality tracking built on the symbol database (`symdb/`).
Snapshots a workspace's structure as JSON; diffs snapshots to catch
regressions like dead code and increased coupling.

## Layout

| File | Purpose |
|---|---|
| `quality.valk` | The snapshot: invoked by `valk --quality-snapshot <dir>`, emits JSON metrics to stdout |
| `quality-diff.valk` | Diffs two snapshots and reports regressions/improvements |

## Usage

```bash
# 1. Snapshot before changes
build/valk --quality-snapshot . 2>/dev/null > /tmp/quality_before.json

# 2. Make changes, build, test ...

# 3. Snapshot after + diff
build/valk --quality-snapshot . 2>/dev/null > /tmp/quality_after.json
build/valk quality/quality-diff.valk -- /tmp/quality_before.json /tmp/quality_after.json
```

## What the diff reports

| Regression | Meaning |
|---|---|
| `dead symbols +N` | Functions/variables nobody calls |
| `fan-out of X: +N` | A function depends on too many things |
| `coupling A -> B: +N refs` | Two files became more tightly coupled |
| `new coupling: A -> B` | Previously independent files are now coupled |
| `lines: +N (+M%)` / `symbols: +N` | File grew substantially |
| `hotspot X: +N refs` | Central symbol became even more central |

Note: renaming/moving files shows up as paired regression+improvement noise
(old path removed, new path added). Clear `.valk/symdb.sqlite` after large
moves to avoid stale rows.
