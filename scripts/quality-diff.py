#!/usr/bin/env python3
"""
Diff two quality snapshots and produce an opinionated summary.

Usage:
    python3 scripts/quality-diff.py before.json after.json

Exit codes:
    0 — no regressions
    1 — regressions detected
"""

import json
import sys
from pathlib import Path


def load(path):
    with open(path) as f:
        return json.load(f)


def file_index(snapshot):
    return {f["path"]: f for f in snapshot.get("files", [])}


def dead_index(snapshot):
    by_file = {}
    for d in snapshot.get("dead_symbols", []):
        by_file.setdefault(d["file"], set()).add(d["name"])
    return by_file


def coupling_index(snapshot):
    idx = {}
    for c in snapshot.get("file_coupling", []):
        key = (c["source"], c["target"])
        idx[key] = c["refs"]
    return idx


def hotspot_index(snapshot):
    return {h["name"]: h["refs"] for h in snapshot.get("hotspots", [])}


def fanout_index(snapshot):
    return {(f["name"], f["file"]): f["deps"]
            for f in snapshot.get("high_fan_out", [])}


def diff_snapshots(before, after):
    regressions = []
    improvements = []

    sb = before["summary"]
    sa = after["summary"]

    # --- Global summary deltas ---
    dead_delta = sa["dead_symbols"] - sb["dead_symbols"]
    if dead_delta > 0:
        regressions.append(
            f"dead symbols: {sb['dead_symbols']} -> {sa['dead_symbols']} (+{dead_delta})")
    elif dead_delta < 0:
        improvements.append(
            f"dead symbols: {sb['dead_symbols']} -> {sa['dead_symbols']} ({dead_delta})")

    cov_delta = sa.get("test_coverage_pct", 0) - sb.get("test_coverage_pct", 0)
    if cov_delta < -5:
        regressions.append(
            f"test coverage: {sb.get('test_coverage_pct', 0)}% -> "
            f"{sa.get('test_coverage_pct', 0)}% ({cov_delta:+d}%)")
    elif cov_delta > 5:
        improvements.append(
            f"test coverage: {sb.get('test_coverage_pct', 0)}% -> "
            f"{sa.get('test_coverage_pct', 0)}% ({cov_delta:+d}%)")

    # --- Per-file deltas ---
    fb = file_index(before)
    fa = file_index(after)

    for path, af in fa.items():
        bf = fb.get(path)
        if not bf:
            if af["symbols"] > 0:
                improvements.append(f"new file: {path} ({af['symbols']} symbols, {af['lines']} lines)")
            continue

        # Dead symbol increase per file
        dd = af["dead"] - bf["dead"]
        if dd > 0:
            regressions.append(f"{path} -- dead symbols: {bf['dead']} -> {af['dead']} (+{dd})")
        elif dd < -1:
            improvements.append(f"{path} -- dead symbols: {bf['dead']} -> {af['dead']} ({dd})")

        # Fan-out spike
        fo_delta = af["max_fan_out"] - bf["max_fan_out"]
        if fo_delta > 3:
            fn = af.get("max_fan_out_fn", "?")
            regressions.append(
                f"{path} -- fan-out of `{fn}`: {bf['max_fan_out']} -> {af['max_fan_out']} (+{fo_delta})")

        # File size growth
        line_delta = af["lines"] - bf["lines"]
        if bf["lines"] > 0 and line_delta > 50:
            pct = int(line_delta * 100 / bf["lines"])
            if pct > 20:
                regressions.append(
                    f"{path} -- lines: {bf['lines']} -> {af['lines']} (+{line_delta}, +{pct}%)")

        # Symbol count explosion
        sym_delta = af["symbols"] - bf["symbols"]
        if sym_delta > 5:
            regressions.append(
                f"{path} -- symbols: {bf['symbols']} -> {af['symbols']} (+{sym_delta})")

    # Removed files
    for path in fb:
        if path not in fa:
            improvements.append(f"removed file: {path}")

    # --- Dead symbol specifics ---
    db = dead_index(before)
    da = dead_index(after)

    new_dead = []
    for f, names in da.items():
        old = db.get(f, set())
        for n in sorted(names - old):
            new_dead.append(f"  {f}: {n}")

    removed_dead = []
    for f, names in db.items():
        cur = da.get(f, set())
        for n in sorted(names - cur):
            removed_dead.append(f"  {f}: {n}")

    # --- Coupling changes ---
    cb = coupling_index(before)
    ca = coupling_index(after)

    for key, refs_after in ca.items():
        refs_before = cb.get(key, 0)
        delta = refs_after - refs_before
        if delta > 5:
            regressions.append(
                f"coupling {key[0]} -> {key[1]}: {refs_before} -> {refs_after} (+{delta} refs)")

    for key in cb:
        if key not in ca:
            improvements.append(f"decoupled: {key[0]} -> {key[1]}")

    # --- New coupling edges ---
    new_edges = set(ca.keys()) - set(cb.keys())
    for edge in sorted(new_edges):
        regressions.append(
            f"new coupling: {edge[0]} -> {edge[1]} ({ca[edge]} refs)")

    # --- Hotspot changes ---
    hb = hotspot_index(before)
    ha = hotspot_index(after)
    for name, refs in ha.items():
        old = hb.get(name, 0)
        if refs - old > 10:
            regressions.append(
                f"hotspot `{name}`: {old} -> {refs} refs (+{refs - old})")

    # --- Fan-out changes ---
    fob = fanout_index(before)
    foa = fanout_index(after)
    for key, deps in foa.items():
        old = fob.get(key, 0)
        if deps - old > 5:
            regressions.append(
                f"fan-out `{key[0]}` in {key[1]}: {old} -> {deps} deps (+{deps - old})")

    return regressions, improvements, new_dead, removed_dead


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} before.json after.json", file=sys.stderr)
        sys.exit(2)

    before = load(sys.argv[1])
    after = load(sys.argv[2])

    regressions, improvements, new_dead, removed_dead = diff_snapshots(before, after)

    total = len(regressions) + len(improvements)
    if total == 0:
        print("No quality changes detected.")
        sys.exit(0)

    print(f"Quality delta: {len(regressions)} regressions, {len(improvements)} improvements")
    print()

    if regressions:
        print("REGRESSIONS:")
        for r in regressions:
            print(f"  - {r}")
        print()

    if new_dead:
        print(f"New dead symbols ({len(new_dead)}):")
        for d in new_dead[:20]:
            print(d)
        if len(new_dead) > 20:
            print(f"  ... and {len(new_dead) - 20} more")
        print()

    if improvements:
        print("IMPROVEMENTS:")
        for i in improvements:
            print(f"  + {i}")
        print()

    if removed_dead:
        print(f"Removed dead symbols ({len(removed_dead)}):")
        for d in removed_dead[:20]:
            print(d)
        if len(removed_dead) > 20:
            print(f"  ... and {len(removed_dead) - 20} more")
        print()

    sys.exit(1 if regressions else 0)


if __name__ == "__main__":
    main()
