#!/usr/bin/env python3
"""
Coverage Gate Checker for Valkyria Runtime

Enforces 90% line, 85% branch coverage for ALL runtime code in src/

Exit code 0 = pass, 1 = fail (blocks CI)
"""

import sys
import subprocess
import re
from pathlib import Path
from dataclasses import dataclass
from typing import Dict, Optional
import argparse


@dataclass
class FileCoverage:
    filename: str
    line_pct: float
    branch_pct: float
    expr_pct: Optional[float] = None
    is_valk: bool = False


# All src/ runtime code requires 90% line, 85% branch
RUNTIME_REQUIREMENT_LINE = 90.0
RUNTIME_REQUIREMENT_BRANCH = 85.0
RUNTIME_REQUIREMENT_EXPR = 90.0


def find_llvm_cov() -> Optional[str]:
    """Find llvm-cov executable."""
    candidates = [
        "llvm-cov",
        "/opt/homebrew/opt/llvm/bin/llvm-cov",
        "/usr/local/opt/llvm/bin/llvm-cov",
        "/Library/Developer/CommandLineTools/usr/bin/llvm-cov",
    ]
    
    for candidate in candidates:
        try:
            result = subprocess.run(
                [candidate, "--version"],
                capture_output=True,
                text=True,
                timeout=2
            )
            if result.returncode == 0:
                return candidate
        except (FileNotFoundError, subprocess.TimeoutExpired):
            continue
    
    try:
        result = subprocess.run(
            ["xcrun", "--find", "llvm-cov"],
            capture_output=True,
            text=True,
            timeout=2
        )
        if result.returncode == 0:
            path = result.stdout.strip()
            if path:
                return path
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    
    return None


def parse_valk_coverage(lcov_path: Path, source_root: Path) -> Dict[str, FileCoverage]:
    """Parse Valk coverage from LCOV file.

    Handles multiple records for the same file by merging expression data.
    An expression is identified by (line, col) and is considered hit if
    any record shows it was executed.
    """
    if not lcov_path.exists():
        return {}

    # Accumulate per-file data across multiple records
    # file_exprs[filepath][(line, col)] = max_hit_count
    file_exprs: Dict[str, Dict[tuple, int]] = {}
    file_branches: Dict[str, Dict[tuple, int]] = {}
    file_lines: Dict[str, Dict[int, int]] = {}

    current_file = None

    with open(lcov_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue

            if line.startswith("SF:"):
                filepath = line[3:]
                if not filepath.startswith("/"):
                    filepath = str(source_root / filepath)
                current_file = filepath
                # Initialize dicts if first time seeing this file
                if filepath not in file_exprs:
                    file_exprs[filepath] = {}
                    file_branches[filepath] = {}
                    file_lines[filepath] = {}

            elif line.startswith("DA:") and current_file:
                parts = line[3:].split(",")
                if len(parts) >= 2:
                    line_num = int(parts[0])
                    hit_count = int(parts[1])
                    # Take max hit count for this line
                    file_lines[current_file][line_num] = max(
                        file_lines[current_file].get(line_num, 0), hit_count
                    )

            elif line.startswith("EXPRDATA:") and current_file:
                parts = line[9:].split(",")
                if len(parts) >= 4:
                    expr_line = int(parts[0])
                    expr_col = int(parts[1])
                    hit_count = int(parts[3])
                    key = (expr_line, expr_col)
                    # Take max hit count for this expression
                    file_exprs[current_file][key] = max(
                        file_exprs[current_file].get(key, 0), hit_count
                    )

            elif line.startswith("BRDA:") and current_file:
                parts = line[5:].split(",")
                if len(parts) >= 4:
                    br_line = int(parts[0])
                    br_block = int(parts[1])
                    br_branch = int(parts[2])
                    taken_str = parts[3]
                    key = (br_line, br_block, br_branch)
                    taken = 0 if taken_str == "-" else int(taken_str)
                    # Take max taken count for this branch
                    file_branches[current_file][key] = max(
                        file_branches[current_file].get(key, 0), taken
                    )

            elif line == "end_of_record":
                current_file = None

    # Convert accumulated data to FileCoverage objects
    coverage = {}
    for filepath, exprs in file_exprs.items():
        if filepath.startswith(str(source_root / "src")) and filepath.endswith(".valk"):
            rel_path = filepath[len(str(source_root))+1:]
            if not rel_path.startswith("src/modules/test"):
                exprs_found = len(exprs)
                exprs_hit = sum(1 for count in exprs.values() if count > 0)

                branches = file_branches.get(filepath, {})
                branches_found = len(branches)
                branches_hit = sum(1 for count in branches.values() if count > 0)

                lines = file_lines.get(filepath, {})
                lines_found = len(lines)
                lines_hit = sum(1 for count in lines.values() if count > 0)

                expr_pct = (exprs_hit / exprs_found * 100) if exprs_found > 0 else 0
                branch_pct = (branches_hit / branches_found * 100) if branches_found > 0 else 0
                line_pct = (lines_hit / lines_found * 100) if lines_found > 0 else 0

                filename = rel_path.replace("src/", "")
                coverage[filename] = FileCoverage(
                    filename=filename,
                    line_pct=line_pct,
                    branch_pct=branch_pct,
                    expr_pct=expr_pct,
                    is_valk=True
                )

    return coverage


def get_coverage_data(build_dir: Path, llvm_cov: str) -> Dict[str, FileCoverage]:
    """Extract coverage data for all C source files in src/."""
    # Try different possible CMake target names
    possible_dirs = [
        build_dir / "CMakeFiles" / "valkyria.dir" / "src",
        build_dir / "CMakeFiles" / "libvalkyria.dir" / "src",
        build_dir / "CMakeFiles" / "valk.dir" / "src",
    ]
    
    gcda_dir = None
    for d in possible_dirs:
        if d.exists() and list(d.glob("*.gcno")):
            gcda_dir = d
            break
    
    if not gcda_dir:
        print(f"Error: No coverage build found in {build_dir}/CMakeFiles/")
        print("Expected directories: valkyria.dir/src, libvalkyria.dir/src")
        print("Run: make build-coverage && make test")
        sys.exit(1)
    
    # Only process gcda files that have corresponding gcno files
    gcda_files = []
    for gcda in gcda_dir.glob("*.gcda"):
        gcno = gcda.with_suffix(".gcno")
        if gcno.exists():
            gcda_files.append(gcda)
    
    if not gcda_files:
        print("Error: No valid coverage data (gcda+gcno pairs) found")
        print("Run: make build-coverage && make test")
        sys.exit(1)
    
    # Run gcov from build directory with relative paths to gcda files
    gcda_relative = [gcda.relative_to(build_dir) for gcda in gcda_files]
    
    result = subprocess.run(
        [llvm_cov, "gcov", "-b"] + [str(f) for f in gcda_relative],
        cwd=str(build_dir),
        capture_output=True,
        text=True
    )
    
    coverage = {}
    current_file = None
    current_line_pct = None
    
    # llvm-cov gcov outputs to stdout on some systems, stderr on others
    output = result.stderr if result.stderr else result.stdout
    
    for line in output.split('\n'):
        if line.startswith("File"):
            match = re.search(r"File '.*src/([\w_]+\.c)'", line)
            if match:
                current_file = match.group(1)
        elif "Lines executed:" in line and current_file:
            match = re.search(r'(\d+\.?\d*)%', line)
            if match:
                current_line_pct = float(match.group(1))
        elif "Taken at least once:" in line and current_file and current_line_pct is not None:
            match = re.search(r'(\d+\.?\d*)%', line)
            if match:
                branch_pct = float(match.group(1))
                
                coverage[current_file] = FileCoverage(
                    filename=current_file,
                    line_pct=current_line_pct,
                    branch_pct=branch_pct
                )
                
                current_file = None
                current_line_pct = None
    
    return coverage


def check_coverage_requirements(coverage: Dict[str, FileCoverage], show_passing: bool = False) -> bool:
    """Check if coverage meets requirements. Returns True if all pass."""
    all_pass = True
    failures = []
    passes = []
    
    c_files = {k: v for k, v in coverage.items() if not v.is_valk}
    valk_files = {k: v for k, v in coverage.items() if v.is_valk}
    
    print("=" * 80)
    print("VALKYRIA RUNTIME COVERAGE GATE CHECK")
    print("=" * 80)
    print()
    print(f"Runtime (src/*.c):    {RUNTIME_REQUIREMENT_LINE}% line, {RUNTIME_REQUIREMENT_BRANCH}% branch")
    print(f"Stdlib (src/*.valk):  {RUNTIME_REQUIREMENT_EXPR}% expr, {RUNTIME_REQUIREMENT_BRANCH}% branch")
    print()
    
    for filename, cov in sorted(c_files.items()):
        line_pass = cov.line_pct >= RUNTIME_REQUIREMENT_LINE
        branch_pass = cov.branch_pct >= RUNTIME_REQUIREMENT_BRANCH
        status = "✓" if (line_pass and branch_pass) else "✗"
        
        line = f"  {filename:30s} {status}  {cov.line_pct:5.1f}% line, {cov.branch_pct:5.1f}% branch"
        
        if not line_pass or not branch_pass:
            gaps = []
            if not line_pass:
                gaps.append(f"-{RUNTIME_REQUIREMENT_LINE - cov.line_pct:.1f}% line")
            if not branch_pass:
                gaps.append(f"-{RUNTIME_REQUIREMENT_BRANCH - cov.branch_pct:.1f}% branch")
            line += f"  ({', '.join(gaps)})"
            failures.append(line)
            all_pass = False
        else:
            passes.append(line)
    
    for filename, cov in sorted(valk_files.items()):
        expr_pct = cov.expr_pct if cov.expr_pct is not None else cov.line_pct
        expr_pass = expr_pct >= RUNTIME_REQUIREMENT_EXPR
        branch_pass = cov.branch_pct >= RUNTIME_REQUIREMENT_BRANCH
        status = "✓" if (expr_pass and branch_pass) else "✗"
        
        line = f"  {filename:30s} {status}  {expr_pct:5.1f}% expr, {cov.branch_pct:5.1f}% branch"
        
        if not expr_pass or not branch_pass:
            gaps = []
            if not expr_pass:
                gaps.append(f"-{RUNTIME_REQUIREMENT_EXPR - expr_pct:.1f}% expr")
            if not branch_pass:
                gaps.append(f"-{RUNTIME_REQUIREMENT_BRANCH - cov.branch_pct:.1f}% branch")
            line += f"  ({', '.join(gaps)})"
            failures.append(line)
            all_pass = False
        else:
            passes.append(line)
    
    # Show failures first
    if failures:
        print("FAILING FILES:")
        for line in failures:
            print(line)
        print()
    
    # Optionally show passing files
    if show_passing and passes:
        print("PASSING FILES:")
        for line in passes:
            print(line)
        print()
    
    print("=" * 80)
    print(f"Results: {len(passes)} passing, {len(failures)} failing")
    print()
    
    if all_pass:
        print("✓ ALL COVERAGE REQUIREMENTS MET")
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
    if not build_dir.exists():
        print(f"Error: Build directory {build_dir} does not exist")
        print("Run: make build-coverage && make test")
        sys.exit(1)
    
    llvm_cov = find_llvm_cov()
    if not llvm_cov:
        print("Error: llvm-cov not found")
        print("Install via: brew install llvm")
        sys.exit(1)
    
    print(f"Using llvm-cov: {llvm_cov}")
    print(f"Build directory: {build_dir}")
    print()
    
    coverage = get_coverage_data(build_dir, llvm_cov)
    
    valk_lcov = build_dir / "coverage-valk.info"
    if valk_lcov.exists():
        valk_coverage = parse_valk_coverage(valk_lcov, build_dir.parent)
        coverage.update(valk_coverage)
        print(f"Found {len(valk_coverage)} Valk files with coverage data")
        print()
    
    if not coverage:
        print("Error: No coverage data found")
        print("Run: make test")
        sys.exit(1)
    
    passed = check_coverage_requirements(coverage, args.show_passing)
    
    sys.exit(0 if passed else 1)


if __name__ == "__main__":
    main()
