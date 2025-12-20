#!/usr/bin/env python3
"""
Shared coverage data structures and parsing logic for Valkyria coverage tools.
"""

import re
import subprocess
import sys
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional, Dict
from datetime import datetime


@dataclass
class BranchCoverage:
    line_no: int
    branch_id: int
    taken: int


@dataclass
class ExprCoverage:
    line_no: int
    column: int
    end_column: int
    hit_count: int


@dataclass
class LineCoverage:
    line_no: int
    hit_count: int
    source: str = ""
    branches: list = field(default_factory=list)
    exprs: list = field(default_factory=list)


@dataclass
class FileCoverage:
    filename: str
    lines: dict = field(default_factory=dict)
    functions_found: int = 0
    functions_hit: int = 0
    branch_data: dict = field(default_factory=dict)
    
    @property
    def branches_found(self) -> int:
        return len(self.branch_data)
    
    @property
    def branches_hit(self) -> int:
        return sum(1 for taken in self.branch_data.values() if taken > 0)
    
    @property
    def lines_found(self) -> int:
        return sum(1 for l in self.lines.values() if l.hit_count >= 0)
    
    @property
    def lines_hit(self) -> int:
        return sum(1 for l in self.lines.values() if l.hit_count > 0)
    
    @property
    def line_coverage_pct(self) -> float:
        if self.lines_found == 0:
            return 0.0
        return (self.lines_hit / self.lines_found) * 100
    
    @property
    def branch_coverage_pct(self) -> float:
        if self.branches_found == 0:
            return 100.0
        return (self.branches_hit / self.branches_found) * 100
    
    @property
    def exprs_found(self) -> int:
        return sum(len(l.exprs) for l in self.lines.values())
    
    @property
    def exprs_hit(self) -> int:
        return sum(1 for l in self.lines.values() for e in l.exprs if e.hit_count > 0)
    
    @property
    def expr_coverage_pct(self) -> float:
        if self.exprs_found == 0:
            return 0.0
        return (self.exprs_hit / self.exprs_found) * 100


@dataclass
class CoverageReport:
    files: dict = field(default_factory=dict)
    timestamp: str = field(default_factory=lambda: datetime.now().isoformat())
    
    @property
    def total_lines_found(self) -> int:
        return sum(f.lines_found for f in self.files.values())
    
    @property
    def total_lines_hit(self) -> int:
        return sum(f.lines_hit for f in self.files.values())
    
    @property
    def total_functions_found(self) -> int:
        return sum(f.functions_found for f in self.files.values())
    
    @property
    def total_functions_hit(self) -> int:
        return sum(f.functions_hit for f in self.files.values())
    
    @property
    def total_branches_found(self) -> int:
        return sum(f.branches_found for f in self.files.values())
    
    @property
    def total_branches_hit(self) -> int:
        return sum(f.branches_hit for f in self.files.values())
    
    @property
    def line_coverage_pct(self) -> float:
        if self.total_lines_found == 0:
            return 0.0
        return (self.total_lines_hit / self.total_lines_found) * 100
    
    @property
    def branch_coverage_pct(self) -> float:
        if self.total_branches_found == 0:
            return 0.0
        return (self.total_branches_hit / self.total_branches_found) * 100


def find_llvm_cov() -> Optional[str]:
    """Find llvm-cov executable on the system."""
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


def parse_lcov_file(lcov_path: Path, report: CoverageReport, source_root: Path):
    """Parse LCOV format coverage file, merging multiple records for the same file."""
    if not lcov_path.exists():
        return
    
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
                if filepath not in report.files:
                    report.files[filepath] = FileCoverage(filename=filepath)
                current_file = report.files[filepath]
                
            elif line.startswith("DA:"):
                if current_file:
                    parts = line[3:].split(",")
                    if len(parts) >= 2:
                        line_no = int(parts[0])
                        hit_count = int(parts[1])
                        if line_no in current_file.lines:
                            existing_lc = current_file.lines[line_no]
                            existing_lc.hit_count = max(existing_lc.hit_count, hit_count)
                        else:
                            current_file.lines[line_no] = LineCoverage(line_no=line_no, hit_count=hit_count)
            
            elif line.startswith("EXPRDATA:"):
                if current_file:
                    parts = line[9:].split(",")
                    if len(parts) >= 4:
                        line_no = int(parts[0])
                        column = int(parts[1])
                        end_column = int(parts[2])
                        hit_count = int(parts[3])
                        if line_no not in current_file.lines:
                            current_file.lines[line_no] = LineCoverage(line_no=line_no, hit_count=-1)
                        lc = current_file.lines[line_no]
                        existing = None
                        for e in lc.exprs:
                            if e.column == column:
                                existing = e
                                break
                        if existing:
                            existing.hit_count = max(existing.hit_count, hit_count)
                        else:
                            lc.exprs.append(
                                ExprCoverage(line_no=line_no, column=column, end_column=end_column, hit_count=hit_count)
                            )
            
            elif line.startswith("BRDA:"):
                if current_file:
                    parts = line[5:].split(",")
                    if len(parts) >= 4:
                        line_no = int(parts[0])
                        block_id = int(parts[1])
                        branch_id = int(parts[2])
                        taken_str = parts[3]
                        taken = 0 if taken_str == "-" else int(taken_str)
                        key = (line_no, branch_id)
                        current_file.branch_data[key] = max(current_file.branch_data.get(key, 0), taken)
                        if line_no not in current_file.lines:
                            current_file.lines[line_no] = LineCoverage(line_no=line_no, hit_count=-1)
                        lc = current_file.lines[line_no]
                        existing = None
                        for b in lc.branches:
                            if b.branch_id == branch_id:
                                existing = b
                                break
                        if existing:
                            existing.taken = max(existing.taken, taken)
                        else:
                            lc.branches.append(
                                BranchCoverage(line_no=line_no, branch_id=branch_id, taken=taken)
                            )
                            
            elif line.startswith("FNF:"):
                if current_file:
                    current_file.functions_found = max(current_file.functions_found, int(line[4:]))
            elif line.startswith("FNH:"):
                if current_file:
                    current_file.functions_hit = max(current_file.functions_hit, int(line[4:]))
            elif line.startswith("BRF:"):
                pass
            elif line.startswith("BRH:"):
                pass
            elif line == "end_of_record":
                current_file = None


def parse_gcov_files(build_dir: Path, source_root: Path, report: CoverageReport):
    """Parse gcov output files using llvm-cov gcov."""
    gcda_dir = build_dir / "CMakeFiles" / "valkyria.dir" / "src"
    if not gcda_dir.exists():
        return
    
    llvm_cov = find_llvm_cov()
    if not llvm_cov:
        print("Warning: llvm-cov not found, skipping C coverage", file=sys.stderr)
        return
    
    for gcda_file in gcda_dir.glob("*.gcda"):
        try:
            result = subprocess.run(
                [llvm_cov, "gcov", "-b", "-o", str(gcda_dir), str(gcda_file)],
                cwd=str(build_dir),
                capture_output=True,
                text=True
            )
        except FileNotFoundError:
            print("Warning: llvm-cov not found, skipping C coverage", file=sys.stderr)
            return
        
        for gcov_file in build_dir.glob("*.gcov"):
            parse_gcov_output(gcov_file, report, source_root)
            gcov_file.unlink()
    
    for gcov_file in source_root.glob("*.gcov"):
        gcov_file.unlink()


def parse_gcov_output(gcov_path: Path, report: CoverageReport, source_root: Path):
    """Parse a .gcov file and add to report.
    
    Respects LCOV exclusion markers:
    - LCOV_EXCL_LINE: Exclude single line
    - LCOV_EXCL_START/STOP: Exclude region
    - LCOV_EXCL_BR_LINE: Exclude branches on single line
    - LCOV_EXCL_BR_START/STOP: Exclude branches in region
    """
    source_file = None
    current_line_no = 0
    in_excl_region = False
    in_br_excl_region = False
    
    with open(gcov_path) as f:
        for line in f:
            if line.startswith("        -:    0:Source:"):
                source_file = line.split(":", 3)[3].strip()
                if not source_file.startswith("/"):
                    source_file = str(source_root / source_file)
                if source_file not in report.files:
                    report.files[source_file] = FileCoverage(filename=source_file)
                continue
            
            if not source_file:
                continue
            
            fc = report.files[source_file]
            
            # Check for LCOV exclusion markers in the source portion
            source_content = ""
            match_check = re.match(r'\s*(\d+|-|#####):\s*(\d+):(.*)$', line)
            if match_check:
                source_content = match_check.group(3)
                
                # Check for region markers
                if "LCOV_EXCL_START" in source_content:
                    in_excl_region = True
                if "LCOV_EXCL_STOP" in source_content:
                    in_excl_region = False
                if "LCOV_EXCL_BR_START" in source_content:
                    in_br_excl_region = True
                if "LCOV_EXCL_BR_STOP" in source_content:
                    in_br_excl_region = False
            
            # Check for single-line exclusion
            excl_line = "LCOV_EXCL_LINE" in source_content
            excl_br_line = "LCOV_EXCL_BR_LINE" in source_content
            
            # Skip this line entirely if in exclusion region or has line marker
            if in_excl_region or excl_line:
                # Still need to track line number for branch association
                if match_check:
                    line_no_str = match_check.group(2)
                    if line_no_str != "0":
                        current_line_no = int(line_no_str)
                continue
            
            branch_match = re.match(r'branch\s+(\d+)\s+(taken\s+(\d+)|never executed)', line)
            if branch_match:
                # Skip branches if in branch exclusion region or line has branch exclusion
                if in_br_excl_region or excl_br_line:
                    continue
                    
                branch_id = int(branch_match.group(1))
                taken = int(branch_match.group(3)) if branch_match.group(3) else 0
                key = (current_line_no, branch_id)
                fc.branch_data[key] = max(fc.branch_data.get(key, 0), taken)
                if current_line_no not in fc.lines:
                    fc.lines[current_line_no] = LineCoverage(line_no=current_line_no, hit_count=-1)
                lc = fc.lines[current_line_no]
                existing = None
                for b in lc.branches:
                    if b.branch_id == branch_id:
                        existing = b
                        break
                if existing:
                    existing.taken = max(existing.taken, taken)
                else:
                    lc.branches.append(
                        BranchCoverage(line_no=current_line_no, branch_id=branch_id, taken=taken)
                    )
                continue
            
            match = re.match(r'\s*(\d+|-|#####):\s*(\d+):(.*)$', line)
            if match:
                count_str, line_no_str, source = match.groups()
                line_no = int(line_no_str)
                if line_no == 0:
                    continue
                
                current_line_no = line_no
                
                if count_str == "-":
                    if line_no not in fc.lines:
                        fc.lines[line_no] = LineCoverage(line_no=line_no, hit_count=-1, source=source)
                elif count_str == "#####":
                    if line_no not in fc.lines:
                        fc.lines[line_no] = LineCoverage(line_no=line_no, hit_count=0, source=source)
                    fc.lines[line_no].source = source
                else:
                    hit_count = int(count_str)
                    if line_no in fc.lines:
                        fc.lines[line_no].hit_count = max(fc.lines[line_no].hit_count, hit_count)
                    else:
                        fc.lines[line_no] = LineCoverage(line_no=line_no, hit_count=hit_count, source=source)


def collect_coverage(build_dir: Path, source_root: Path, valk_lcov: Optional[Path] = None) -> CoverageReport:
    """Collect all coverage data into a single report."""
    report = CoverageReport()
    
    parse_gcov_files(build_dir, source_root, report)
    
    if valk_lcov is None:
        valk_lcov = build_dir / "coverage-valk.info"
    
    if valk_lcov.exists():
        parse_lcov_file(valk_lcov, report, source_root)
    
    return report


def filter_runtime_files(report: CoverageReport, source_root: Path) -> Dict[str, FileCoverage]:
    """Filter report to only include runtime C files (src/*.c, excluding test/vendor)."""
    runtime = {}
    for filepath, fc in report.files.items():
        if fc.lines_found == 0:
            continue
        rel_path = filepath
        if filepath.startswith(str(source_root)):
            rel_path = filepath[len(str(source_root))+1:]
        if (rel_path.startswith("src/") and 
            rel_path.endswith(".c") and
            not rel_path.startswith("src/test") and
            not "vendor" in rel_path):
            runtime[rel_path] = fc
    return runtime


def filter_stdlib_files(report: CoverageReport, source_root: Path) -> Dict[str, FileCoverage]:
    """Filter report to only include stdlib Valk files (src/*.valk, excluding test)."""
    stdlib = {}
    for filepath, fc in report.files.items():
        if fc.lines_found == 0 and fc.exprs_found == 0:
            continue
        rel_path = filepath
        if filepath.startswith(str(source_root)):
            rel_path = filepath[len(str(source_root))+1:]
        if (rel_path.startswith("src/") and 
            rel_path.endswith(".valk") and
            not rel_path.startswith("test/") and
            not rel_path.startswith("examples/")):
            stdlib[rel_path] = fc
    return stdlib
