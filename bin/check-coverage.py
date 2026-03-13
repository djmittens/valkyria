#!/usr/bin/env python3
"""
Coverage Gate Checker for Valkyria Runtime

Enforces 90% line, 85% branch coverage for ALL runtime code in src/

Exit code 0 = pass, 1 = fail (blocks CI)
"""

import sys
from pathlib import Path
import argparse

from coverage_common import (
    FileCoverage, collect_coverage, 
    filter_runtime_files, filter_stdlib_files
)

RUNTIME_REQUIREMENT_LINE = 90.0
RUNTIME_REQUIREMENT_BRANCH = 85.0
RUNTIME_REQUIREMENT_EXPR = 90.0

VALK_KNOWN_BLOCKED = {
    "src/http_api.valk": "stdlib utility library - many functions not exercised by tests",
    "src/modules/test.valk": "test framework - error/timeout/skip paths not exercised in normal runs",
}

def meets_requirement(actual: float, required: float) -> bool:
    """Check if coverage meets requirement, rounding to 1 decimal place (matching display)."""
    return round(actual, 1) >= required


def check_coverage_requirements(runtime_files: dict, stdlib_files: dict, show_passing: bool = False) -> bool:
    """Check if coverage meets requirements. Returns True if all pass."""
    all_pass = True
    failures = []
    passes = []
    blocked = []
    
    all_filenames = [p.replace("src/", "") for p in list(runtime_files.keys()) + list(stdlib_files.keys())]
    max_width = max(len(f) for f in all_filenames) if all_filenames else 30
    
    print("=" * 80)
    print("VALKYRIA RUNTIME COVERAGE GATE CHECK")
    print("=" * 80)
    print()
    print(f"Runtime (src/*.c):    {RUNTIME_REQUIREMENT_LINE}% line, {RUNTIME_REQUIREMENT_BRANCH}% branch")
    print(f"Stdlib (src/*.valk):  {RUNTIME_REQUIREMENT_EXPR}% expr, {RUNTIME_REQUIREMENT_BRANCH}% branch")
    print()
    
    for rel_path, fc in sorted(runtime_files.items()):
        filename = rel_path.replace("src/", "")
        line_pass = meets_requirement(fc.line_coverage_pct, RUNTIME_REQUIREMENT_LINE)
        branch_pass = meets_requirement(fc.branch_coverage_pct, RUNTIME_REQUIREMENT_BRANCH)
        status = "✓" if (line_pass and branch_pass) else "✗"
        
        line = f"  {filename:{max_width}s} {status}  {fc.line_coverage_pct:5.1f}% line, {fc.branch_coverage_pct:5.1f}% branch"
        
        if not line_pass or not branch_pass:
            gaps = []
            if not line_pass:
                gaps.append(f"-{RUNTIME_REQUIREMENT_LINE - fc.line_coverage_pct:.1f}% line")
            if not branch_pass:
                gaps.append(f"-{RUNTIME_REQUIREMENT_BRANCH - fc.branch_coverage_pct:.1f}% branch")
            line += f"  ({', '.join(gaps)})"
            failures.append(line)
            all_pass = False
        else:
            passes.append(line)
    
    for rel_path, fc in sorted(stdlib_files.items()):
        filename = rel_path.replace("src/", "")
        expr_pct = fc.expr_coverage_pct
        expr_pass = meets_requirement(expr_pct, RUNTIME_REQUIREMENT_EXPR)
        branch_pass = meets_requirement(fc.branch_coverage_pct, RUNTIME_REQUIREMENT_BRANCH)
        status = "✓" if (expr_pass and branch_pass) else "✗"
        
        line = f"  {filename:{max_width}s} {status}  {expr_pct:5.1f}% expr, {fc.branch_coverage_pct:5.1f}% branch"
        
        if not expr_pass or not branch_pass:
            gaps = []
            if not expr_pass:
                gaps.append(f"-{RUNTIME_REQUIREMENT_EXPR - expr_pct:.1f}% expr")
            if not branch_pass:
                gaps.append(f"-{RUNTIME_REQUIREMENT_BRANCH - fc.branch_coverage_pct:.1f}% branch")
            line += f"  ({', '.join(gaps)})"
            if rel_path in VALK_KNOWN_BLOCKED:
                line += f"  [BLOCKED: {VALK_KNOWN_BLOCKED[rel_path]}]"
                blocked.append(line)
            else:
                failures.append(line)
                all_pass = False
        else:
            passes.append(line)
    
    if failures:
        print("FAILING FILES:")
        for line in failures:
            print(line)
        print()
    
    if blocked:
        print("BLOCKED FILES (documented exceptions):")
        for line in blocked:
            print(line)
        print()
    
    if show_passing and passes:
        print("PASSING FILES:")
        for line in passes:
            print(line)
        print()
    
    print("=" * 80)
    blocked_msg = f", {len(blocked)} blocked" if blocked else ""
    print(f"Results: {len(passes)} passing, {len(failures)} failing{blocked_msg}")
    print()
    
    if all_pass:
        print("✓ ALL COVERAGE REQUIREMENTS MET")
        if blocked:
            print(f"  ({len(blocked)} files have documented blocking issues)")
    else:
        print("✗ COVERAGE REQUIREMENTS NOT MET")
        print()
        print(f"All runtime code in src/ requires {RUNTIME_REQUIREMENT_LINE}% line, {RUNTIME_REQUIREMENT_BRANCH}% branch.")
        print("See docs/COVERAGE_REQUIREMENTS.md for rationale.")
    print("=" * 80)
    print()
    
    return all_pass


def main():
    parser = argparse.ArgumentParser(
        description="Check Valkyria runtime coverage requirements"
    )
    parser.add_argument(
        "--build-dir",
        default="build-coverage",
        help="Coverage build directory (default: build-coverage)"
    )
    parser.add_argument(
        "--show-passing",
        action="store_true",
        help="Show passing files (default: only show failures)"
    )
    
    args = parser.parse_args()
    
    build_dir = Path(args.build_dir).resolve()
    source_root = build_dir.parent
    
    if not build_dir.exists():
        print(f"Error: Build directory {build_dir} does not exist")
        print("Run: make build-coverage && make test")
        sys.exit(1)
    
    print(f"Build directory: {build_dir}")
    print()
    
    report = collect_coverage(build_dir, source_root)
    runtime_files = filter_runtime_files(report, source_root)
    stdlib_files = filter_stdlib_files(report, source_root)
    
    print(f"Found {len(runtime_files)} runtime C files, {len(stdlib_files)} stdlib Valk files")
    print()
    
    if not runtime_files and not stdlib_files:
        print("Error: No coverage data found")
        print("Run: make test")
        sys.exit(1)
    
    passed = check_coverage_requirements(runtime_files, stdlib_files, args.show_passing)
    
    sys.exit(0 if passed else 1)


if __name__ == "__main__":
    main()
