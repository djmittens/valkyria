# check

Workspace-wide static checks. Both run as gates inside `make test`.

## Layout

| File | Purpose |
|---|---|
| `valk-check.valk` | Workspace diagnostics: indexes every `.valk` file (via `symdb/`), then validates — undefined symbols, arity errors, sig violations. Caches in `.valk/check.sqlite`; honors `.valkcheckignore` |
| `check-no-globals.valk` | Global-mutation lint: scans `.valk` sources for global mutable state; per-file exemptions via `; lint:allow-globals *name*  reason` markers |

## Usage

```bash
make check                        # both checks (also part of `make test`)
build/valk check/valk-check.valk -- <dir>
build/valk check/check-no-globals.valk
```

Files with intentional errors (negative fixtures) are listed in the root
`.valkcheckignore`.
