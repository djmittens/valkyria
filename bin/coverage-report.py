#!/usr/bin/env python3
"""
Unified Coverage Report Generator for Valkyria

Generates aggregated HTML and XML (Cobertura) reports from:
1. C coverage data (gcov/llvm-cov format)
2. Valk coverage data (LCOV format)

Output: coverage-report/index.html with file-by-file browsing
"""

import os
import sys
import json
import gzip
import re
import html
import subprocess
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional
from datetime import datetime
from xml.etree import ElementTree as ET

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
    expr_hit: int = 0
    expr_total: int = 0
    exprs: list = field(default_factory=list)

@dataclass
class FileCoverage:
    filename: str
    lines: dict = field(default_factory=dict)
    functions_found: int = 0
    functions_hit: int = 0
    branches_found: int = 0
    branches_hit: int = 0

    
    @property
    def lines_found(self) -> int:
        return len(self.lines)
    
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
            return 0.0
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


def parse_lcov_file(lcov_path: Path, report: CoverageReport, source_root: Path):
    """Parse LCOV format coverage file."""
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
                            current_file.lines[line_no].hit_count += hit_count
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
                        if line_no in current_file.lines:
                            existing = None
                            for e in current_file.lines[line_no].exprs:
                                if e.column == column:
                                    existing = e
                                    break
                            if existing:
                                existing.hit_count += hit_count
                            else:
                                current_file.lines[line_no].exprs.append(
                                    ExprCoverage(line_no=line_no, column=column, end_column=end_column, hit_count=hit_count)
                                )
            
            elif line.startswith("EXPR:"):
                if current_file:
                    parts = line[5:].split(",")
                    if len(parts) >= 3:
                        line_no = int(parts[0])
                        expr_hit = int(parts[1])
                        expr_total = int(parts[2])
                        if line_no in current_file.lines:
                            current_file.lines[line_no].expr_hit = expr_hit
                            current_file.lines[line_no].expr_total = expr_total
            
            elif line.startswith("BRDA:"):
                if current_file:
                    parts = line[5:].split(",")
                    if len(parts) >= 4:
                        line_no = int(parts[0])
                        block_id = int(parts[1])
                        branch_id = int(parts[2])
                        taken_str = parts[3]
                        taken = 0 if taken_str == "-" else int(taken_str)
                        current_file.branches_found += 1
                        if taken > 0:
                            current_file.branches_hit += 1
                        if line_no in current_file.lines:
                            current_file.lines[line_no].branches.append(
                                BranchCoverage(line_no=line_no, branch_id=branch_id, taken=taken)
                            )
                            
            elif line.startswith("FNF:"):
                if current_file:
                    current_file.functions_found = int(line[4:])
            elif line.startswith("FNH:"):
                if current_file:
                    current_file.functions_hit = int(line[4:])
            elif line.startswith("BRF:"):
                pass
            elif line.startswith("BRH:"):
                pass
            elif line == "end_of_record":
                current_file = None


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
    """Parse a .gcov file and add to report."""
    source_file = None
    current_line_no = 0
    
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
            
            branch_match = re.match(r'branch\s+(\d+)\s+(taken\s+(\d+)|never executed)', line)
            if branch_match:
                branch_id = int(branch_match.group(1))
                fc.branches_found += 1
                if branch_match.group(3):
                    taken = int(branch_match.group(3))
                    if taken > 0:
                        fc.branches_hit += 1
                    if current_line_no in fc.lines:
                        fc.lines[current_line_no].branches.append(
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
                        fc.lines[line_no].hit_count += hit_count
                    else:
                        fc.lines[line_no] = LineCoverage(line_no=line_no, hit_count=hit_count, source=source)


def load_source_file(filepath: str) -> list:
    """Load source file lines."""
    try:
        with open(filepath) as f:
            return f.readlines()
    except:
        return []





def byte_col_to_char_col(source_line: str, byte_col: int) -> int:
    """Convert a 1-based byte column to a 0-based character index.
    
    The coverage system records byte positions (from the C parser), but Python
    strings are indexed by Unicode code points. Multi-byte characters like
    emojis need this conversion.
    """
    try:
        line_bytes = source_line.encode('utf-8')
        byte_idx = byte_col - 1
        if byte_idx < 0:
            return 0
        if byte_idx >= len(line_bytes):
            return len(source_line)
        prefix = line_bytes[:byte_idx].decode('utf-8', errors='replace')
        return len(prefix)
    except (UnicodeDecodeError, UnicodeEncodeError):
        return byte_col - 1


VALK_KEYWORDS = {
    'if', 'else', 'cond', 'case', 'when', 'unless',
    'do', 'begin', 'let', 'let*', 'letrec',
    'lambda', 'fun', 'def', 'define', 'defun', 'defmacro', 'macro',
    'quote', 'quasiquote', 'unquote', 'unquote-splicing',
    'and', 'or', 'not',
    'loop', 'while', 'for', 'recur', 'return',
    'try', 'catch', 'throw',
    'import', 'require', 'module',
    'true', 'false', 'nil', 't',
    'eq', 'equal', 'eql',
    'set', 'setq', 'set!',
}

VALK_BUILTINS = {
    '+', '-', '*', '/', '%', 'mod', '\\',
    '=', '==', '!=', '<', '>', '<=', '>=', '/=',
    'type', 'typeof', 'string', 'number', 'symbol',
    'atom', 'pair', 'null', 'empty',
    'car', 'cdr', 'cons', 'list', 'append', 'reverse', 'map', 'filter', 'reduce', 'fold',
    'head', 'tail', 'init', 'last', 'take', 'drop', 'nth', 'len', 'join', 'split',
    'range', 'repeat', 'apply',
    'eval', 'penv', 'ord', 'exit', 'shutdown',
    'error', 'error?',
    'load', 'read', 'read-file', 'write',
    'print', 'printf', 'println', 'str', 'make-string',
    'time-us', 'sleep', 'stack-depth',
    'async-shift', 'async-reset', 'async-resume',
    'aio/run', 'aio/start', 'aio/delay', 'aio/sleep',
    'aio/pure', 'aio/fail', 'aio/then', 'aio/catch', 'aio/finally',
    'aio/let', 'aio/do', 'aio/all', 'aio/any', 'aio/race',
    'aio/bracket', 'aio/scope', 'aio/cancel', 'aio/cancelled?',
    'aio/on-cancel', 'aio/status',
    'aio/metrics', 'aio/metrics-json', 'aio/metrics-prometheus',
    'aio/systems-json', 'aio/system-stats-prometheus', 'aio/diagnostics-state-json',
    'http2/request', 'http2/request-add-header', 'http2/connect-async', 'http2/send-async',
    'http2/response-body', 'http2/response-headers', 'http2/response-status',
    'http2/server-handle', 'http2/server-listen',
    'http-client/register', 'http-client/on-cache', 'http-client/on-operation',
    'http-client/metrics-prometheus',
    'sse/open', 'sse/send', 'sse/close', 'sse/on-drain', 'sse/writable?',
    'mem/stats', 'mem/arena/capacity', 'mem/arena/high-water', 'mem/arena/usage',
    'mem/checkpoint/stats', 'mem/gc/collect', 'mem/gc/set-threshold',
    'mem/gc/stats', 'mem/gc/threshold',
    'mem/heap/hard-limit', 'mem/heap/set-hard-limit', 'mem/heap/usage',
    'metrics/collect-delta', 'metrics/counter', 'metrics/counter-inc',
    'metrics/delta-json', 'metrics/gauge', 'metrics/gauge-dec',
    'metrics/gauge-inc', 'metrics/gauge-set', 'metrics/histogram',
    'metrics/histogram-observe', 'metrics/json', 'metrics/prometheus',
    'vm/metrics-json', 'vm/metrics-prometheus',
    'sys/log/set-level',
}

C_KEYWORDS = {
    'auto', 'break', 'case', 'char', 'const', 'continue', 'default', 'do',
    'double', 'else', 'enum', 'extern', 'float', 'for', 'goto', 'if',
    'inline', 'int', 'long', 'register', 'restrict', 'return', 'short',
    'signed', 'sizeof', 'static', 'struct', 'switch', 'typedef', 'union',
    'unsigned', 'void', 'volatile', 'while', '_Bool', '_Complex', '_Imaginary',
    'bool', 'true', 'false', 'NULL', 'nullptr',
    '_Atomic', '_Alignas', '_Alignof', '_Generic', '_Noreturn', '_Static_assert',
    '_Thread_local', 'alignas', 'alignof', 'noreturn', 'static_assert', 'thread_local',
}

C_TYPES = {
    'int8_t', 'int16_t', 'int32_t', 'int64_t',
    'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t',
    'size_t', 'ssize_t', 'ptrdiff_t', 'intptr_t', 'uintptr_t',
    'FILE', 'DIR', 'pthread_t', 'pthread_mutex_t',
    'atomic_int', 'atomic_bool', 'atomic_size_t',
}


def syntax_highlight_valk(source_line: str) -> str:
    """Apply syntax highlighting to a Valk source line."""
    result = []
    i = 0
    n = len(source_line)
    
    while i < n:
        ch = source_line[i]
        
        if ch == ';':
            result.append(f'<span class="syn-comment">{html.escape(source_line[i:])}</span>')
            break
        
        if ch == '"':
            j = i + 1
            while j < n:
                if source_line[j] == '\\' and j + 1 < n:
                    j += 2
                elif source_line[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            result.append(f'<span class="syn-string">{html.escape(source_line[i:j])}</span>')
            i = j
            continue
        
        if ch.isdigit() or (ch == '-' and i + 1 < n and source_line[i + 1].isdigit()):
            j = i + 1 if ch == '-' else i
            while j < n and (source_line[j].isdigit() or source_line[j] == '.'):
                j += 1
            result.append(f'<span class="syn-number">{html.escape(source_line[i:j])}</span>')
            i = j
            continue
        
        if ch in '(){}[]':
            result.append(f'<span class="syn-paren">{html.escape(ch)}</span>')
            i += 1
            continue
        
        if ch.isalpha() or ch in '_-+*/<>=!?&|%':
            j = i
            while j < n and (source_line[j].isalnum() or source_line[j] in '_-+*/<>=!?&|%'):
                j += 1
            word = source_line[i:j]
            if word in VALK_KEYWORDS:
                result.append(f'<span class="syn-keyword">{html.escape(word)}</span>')
            elif word in VALK_BUILTINS:
                result.append(f'<span class="syn-builtin">{html.escape(word)}</span>')
            else:
                result.append(html.escape(word))
            i = j
            continue
        
        result.append(html.escape(ch))
        i += 1
    
    return ''.join(result)


def syntax_highlight_c(source_line: str) -> str:
    """Apply syntax highlighting to a C source line."""
    result = []
    i = 0
    n = len(source_line)
    in_preprocessor = source_line.lstrip().startswith('#')
    
    while i < n:
        ch = source_line[i]
        
        if ch == '/' and i + 1 < n:
            if source_line[i + 1] == '/':
                result.append(f'<span class="syn-comment">{html.escape(source_line[i:])}</span>')
                break
            if source_line[i + 1] == '*':
                end = source_line.find('*/', i + 2)
                if end == -1:
                    result.append(f'<span class="syn-comment">{html.escape(source_line[i:])}</span>')
                    break
                result.append(f'<span class="syn-comment">{html.escape(source_line[i:end + 2])}</span>')
                i = end + 2
                continue
        
        if ch == '#' and i == len(source_line) - len(source_line.lstrip()):
            j = i
            while j < n and source_line[j] not in ' \t':
                j += 1
            result.append(f'<span class="syn-preproc">{html.escape(source_line[i:j])}</span>')
            i = j
            continue
        
        if ch == '"':
            j = i + 1
            while j < n:
                if source_line[j] == '\\' and j + 1 < n:
                    j += 2
                elif source_line[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            result.append(f'<span class="syn-string">{html.escape(source_line[i:j])}</span>')
            i = j
            continue
        
        if ch == "'":
            j = i + 1
            while j < n and j < i + 4:
                if source_line[j] == '\\' and j + 1 < n:
                    j += 2
                elif source_line[j] == "'":
                    j += 1
                    break
                else:
                    j += 1
            result.append(f'<span class="syn-string">{html.escape(source_line[i:j])}</span>')
            i = j
            continue
        
        if ch.isdigit() or (ch == '.' and i + 1 < n and source_line[i + 1].isdigit()):
            j = i
            if j + 1 < n and source_line[j] == '0' and source_line[j + 1] in 'xX':
                j += 2
                while j < n and source_line[j] in '0123456789abcdefABCDEF':
                    j += 1
            else:
                while j < n and (source_line[j].isdigit() or source_line[j] in '.eEfFuUlL'):
                    j += 1
            result.append(f'<span class="syn-number">{html.escape(source_line[i:j])}</span>')
            i = j
            continue
        
        if ch.isalpha() or ch == '_':
            j = i
            while j < n and (source_line[j].isalnum() or source_line[j] == '_'):
                j += 1
            word = source_line[i:j]
            if word in C_KEYWORDS:
                result.append(f'<span class="syn-keyword">{html.escape(word)}</span>')
            elif word in C_TYPES or word.endswith('_t') or word.endswith('_e'):
                result.append(f'<span class="syn-type">{html.escape(word)}</span>')
            elif word.isupper() and len(word) > 1:
                result.append(f'<span class="syn-macro">{html.escape(word)}</span>')
            elif j < n and source_line[j] == '(':
                result.append(f'<span class="syn-function">{html.escape(word)}</span>')
            else:
                result.append(html.escape(word))
            i = j
            continue
        
        result.append(html.escape(ch))
        i += 1
    
    return ''.join(result)


def syntax_highlight(source_line: str, is_valk: bool) -> str:
    """Apply syntax highlighting based on file type."""
    if is_valk:
        return syntax_highlight_valk(source_line)
    else:
        return syntax_highlight_c(source_line)


def highlight_expressions(source_line: str, exprs: list, is_valk: bool) -> str:
    """Highlight individual expressions within a source line with syntax highlighting."""
    if not exprs:
        return syntax_highlight(source_line, is_valk)
    
    sorted_exprs = sorted(exprs, key=lambda e: e.column)
    
    covered = [None] * len(source_line)
    
    for expr in sorted_exprs:
        col = byte_col_to_char_col(source_line, expr.column)
        if col < 0 or col >= len(source_line):
            continue
        
        end_col = col + find_expr_end(source_line, col)
        
        for i in range(col, min(end_col, len(source_line))):
            if covered[i] is None or (expr.hit_count > 0 and covered[i].hit_count == 0):
                covered[i] = expr
    
    result = []
    i = 0
    while i < len(source_line):
        if covered[i] is None:
            j = i
            while j < len(source_line) and covered[j] is None:
                j += 1
            result.append(syntax_highlight(source_line[i:j], is_valk))
            i = j
        else:
            expr = covered[i]
            j = i
            while j < len(source_line) and covered[j] is expr:
                j += 1
            expr_text = syntax_highlight(source_line[i:j], is_valk)
            if expr.hit_count > 0:
                result.append(f'<span class="expr-hit" title="Executed {expr.hit_count}x">{expr_text}</span>')
            else:
                result.append(f'<span class="expr-miss-span" title="Not executed">{expr_text}</span>')
            i = j
    
    return ''.join(result)


def find_expr_end(source_line: str, start: int) -> int:
    """Find the end of an S-expression starting at start."""
    if start >= len(source_line):
        return 1
    
    ch = source_line[start]
    if ch == '(':
        depth = 1
        i = start + 1
        while i < len(source_line) and depth > 0:
            if source_line[i] == '(':
                depth += 1
            elif source_line[i] == ')':
                depth -= 1
            i += 1
        return i - start
    elif ch == '{':
        depth = 1
        i = start + 1
        while i < len(source_line) and depth > 0:
            if source_line[i] == '{':
                depth += 1
            elif source_line[i] == '}':
                depth -= 1
            i += 1
        return i - start
    else:
        i = start
        while i < len(source_line) and source_line[i] not in ' \t\n\r(){}':
            i += 1
        return max(1, i - start)


def generate_cobertura_xml(report: CoverageReport, output_path: Path, source_root: Path):
    """Generate Cobertura XML format coverage report."""
    coverage = ET.Element("coverage")
    coverage.set("version", "1.0")
    coverage.set("timestamp", str(int(datetime.now().timestamp() * 1000)))
    coverage.set("lines-valid", str(report.total_lines_found))
    coverage.set("lines-covered", str(report.total_lines_hit))
    coverage.set("line-rate", f"{report.line_coverage_pct / 100:.4f}")
    coverage.set("branches-valid", str(report.total_branches_found))
    coverage.set("branches-covered", str(report.total_branches_hit))
    coverage.set("branch-rate", f"{report.branch_coverage_pct / 100:.4f}")
    coverage.set("complexity", "0")
    
    sources = ET.SubElement(coverage, "sources")
    source = ET.SubElement(sources, "source")
    source.text = str(source_root)
    
    packages = ET.SubElement(coverage, "packages")
    
    c_pkg = ET.SubElement(packages, "package")
    c_pkg.set("name", "c")
    c_pkg.set("line-rate", "0")
    c_pkg.set("branch-rate", "0")
    c_pkg.set("complexity", "0")
    c_classes = ET.SubElement(c_pkg, "classes")
    
    valk_pkg = ET.SubElement(packages, "package")
    valk_pkg.set("name", "valk")
    valk_pkg.set("line-rate", "0")
    valk_pkg.set("branch-rate", "0")
    valk_pkg.set("complexity", "0")
    valk_classes = ET.SubElement(valk_pkg, "classes")
    
    for filepath, fc in sorted(report.files.items()):
        rel_path = filepath
        if filepath.startswith(str(source_root)):
            rel_path = filepath[len(str(source_root))+1:]
        
        is_valk = filepath.endswith(".valk")
        parent = valk_classes if is_valk else c_classes
        
        cls = ET.SubElement(parent, "class")
        cls.set("name", Path(rel_path).name)
        cls.set("filename", rel_path)
        cls.set("line-rate", f"{fc.line_coverage_pct / 100:.4f}")
        cls.set("branch-rate", f"{fc.branch_coverage_pct / 100:.4f}")
        cls.set("complexity", "0")
        
        methods = ET.SubElement(cls, "methods")
        lines_elem = ET.SubElement(cls, "lines")
        
        for line_no, lc in sorted(fc.lines.items()):
            if lc.hit_count >= 0:
                line_elem = ET.SubElement(lines_elem, "line")
                line_elem.set("number", str(line_no))
                line_elem.set("hits", str(max(0, lc.hit_count)))
                if lc.branches:
                    line_elem.set("branch", "true")
                    total = len(lc.branches)
                    taken = sum(1 for b in lc.branches if b.taken > 0)
                    line_elem.set("condition-coverage", f"{(taken/total*100) if total else 0:.0f}% ({taken}/{total})")
    
    tree = ET.ElementTree(coverage)
    ET.indent(tree, space="  ")
    tree.write(output_path, encoding="utf-8", xml_declaration=True)


def coverage_class(pct: float) -> str:
    """Return CSS class based on coverage percentage."""
    if pct >= 80:
        return "cov-high"
    elif pct >= 50:
        return "cov-med"
    return "cov-low"


def generate_file_html(fc: FileCoverage, output_dir: Path, source_root: Path) -> str:
    """Generate HTML page for a single file."""
    rel_path = fc.filename
    if fc.filename.startswith(str(source_root)):
        rel_path = fc.filename[len(str(source_root))+1:]
    
    safe_name = rel_path.replace("/", "_").replace(".", "_") + ".html"
    is_valk = fc.filename.endswith(".valk")
    
    source_lines = load_source_file(fc.filename)
    

    
    lines_html = []
    for i, source_line in enumerate(source_lines, 1):
        lc = fc.lines.get(i)
        
        has_exprs = lc is not None and len(lc.exprs) > 0
        if has_exprs:
            source_highlighted = highlight_expressions(source_line.rstrip(), lc.exprs, is_valk)
        else:
            source_highlighted = syntax_highlight(source_line.rstrip(), is_valk)
        
        if lc is None or lc.hit_count == -1:
            line_class = "line-none"
            count_display = ""
            branch_display = ""
        elif lc.hit_count == 0:
            line_class = "line-miss" if not has_exprs else "line-has-exprs"
            count_display = "0"
            branch_display = ""
        else:
            line_class = "line-hit" if not has_exprs else "line-has-exprs"
            count_display = str(lc.hit_count)
            branch_display = ""
        
        if lc and lc.branches:
            total_branches = len(lc.branches)
            taken_branches = sum(1 for b in lc.branches if b.taken > 0)
            if taken_branches < total_branches:
                branch_display = f'<span class="branch-partial" title="{taken_branches}/{total_branches} branches taken">[{taken_branches}/{total_branches}]</span>'
            else:
                branch_display = f'<span class="branch-full" title="All branches taken">[{taken_branches}/{total_branches}]</span>'
        
        expr_display = ""
        if lc and lc.expr_total > 0:
            if lc.expr_hit == 0:
                expr_display = f'<span class="expr-miss" title="0/{lc.expr_total} eval points hit">miss</span>'
            elif lc.expr_hit < lc.expr_total:
                expr_display = f'<span class="expr-partial" title="{lc.expr_hit}/{lc.expr_total} eval points hit">{lc.expr_hit}/{lc.expr_total}</span>'
            else:
                expr_display = ""
        
        lines_html.append(f'''<tr class="{line_class}" id="L{i}">
<td class="line-no"><a href="#L{i}">{i}</a></td>
<td class="line-count">{count_display}</td>
<td class="line-expr">{expr_display}</td>
<td class="line-branch">{branch_display}</td>
<td class="line-src"><pre>{source_highlighted}</pre></td>
</tr>''')
    
    file_html = f'''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Coverage: {html.escape(rel_path)}</title>
<style>
:root {{
  --bg: #1a1a2e;
  --bg-alt: #16213e;
  --text: #eee;
  --text-muted: #888;
  --border: #333;
  --hit-bg: rgba(76, 175, 80, 0.15);
  --miss-bg: rgba(244, 67, 54, 0.25);
  --line-border: #444;
}}
body {{
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
  background: var(--bg);
  color: var(--text);
  margin: 0;
  padding: 20px;
}}
.header {{
  background: var(--bg-alt);
  padding: 20px;
  border-radius: 8px;
  margin-bottom: 20px;
}}
.header h1 {{
  margin: 0 0 10px 0;
  font-size: 1.5em;
  word-break: break-all;
}}
.header a {{
  color: #64b5f6;
}}
.stats {{
  display: flex;
  gap: 30px;
  margin-top: 15px;
}}
.stat {{
  text-align: center;
}}
.stat-value {{
  font-size: 2em;
  font-weight: bold;
}}
.stat-label {{
  font-size: 0.8em;
  color: var(--text-muted);
  text-transform: uppercase;
}}
.cov-high {{ color: #4caf50; }}
.cov-med {{ color: #ff9800; }}
.cov-low {{ color: #f44336; }}
.coverage-bar {{
  height: 8px;
  background: #333;
  border-radius: 4px;
  margin-top: 10px;
  overflow: hidden;
}}
.coverage-fill {{
  height: 100%;
  border-radius: 4px;
}}
table {{
  width: 100%;
  border-collapse: collapse;
  font-family: "SF Mono", "Consolas", "Monaco", monospace;
  font-size: 13px;
}}
tr {{
  border-bottom: 1px solid var(--border);
}}
td {{
  padding: 0;
  vertical-align: top;
}}
.line-no {{
  width: 60px;
  text-align: right;
  padding: 2px 10px;
  color: var(--text-muted);
  background: var(--bg-alt);
  user-select: none;
  border-right: 1px solid var(--line-border);
}}
.line-no a {{
  color: inherit;
  text-decoration: none;
}}
.line-no a:hover {{
  color: var(--text);
}}
.line-count {{
  width: 60px;
  text-align: right;
  padding: 2px 10px;
  color: var(--text-muted);
  border-right: 1px solid var(--line-border);
  font-size: 11px;
}}
.line-src {{
  padding: 2px 10px;
}}
.line-src pre {{
  margin: 0;
  white-space: pre-wrap;
  word-break: break-all;
}}
.line-hit {{
  background: var(--hit-bg);
}}
.line-hit .line-count {{
  color: #4caf50;
  font-weight: bold;
}}
.line-miss {{
  background: var(--miss-bg);
}}
.line-miss .line-count {{
  color: #f44336;
  font-weight: bold;
}}
.line-none {{}}
.line-has-exprs {{}}
.line-expr {{
  width: 50px;
  text-align: center;
  padding: 2px 5px;
  border-right: 1px solid var(--line-border);
  font-size: 10px;
}}
.expr-miss {{
  color: #f44336;
  font-weight: bold;
}}
.expr-partial {{
  color: #ff9800;
  font-weight: bold;
}}
.expr-full {{
  color: #4caf50;
}}
.expr-hit {{
  background: rgba(76, 175, 80, 0.3);
  border-radius: 3px;
  padding: 0 2px;
}}
.expr-miss-span {{
  background: rgba(244, 67, 54, 0.4);
  border-radius: 3px;
  padding: 0 2px;
  text-decoration: underline wavy #f44336;
}}
.line-branch {{
  width: 50px;
  text-align: center;
  padding: 2px 5px;
  border-right: 1px solid var(--line-border);
  font-size: 10px;
}}
.branch-partial {{
  color: #ff9800;
  font-weight: bold;
}}
.branch-full {{
  color: #4caf50;
}}
:target {{
  background: rgba(255, 235, 59, 0.3) !important;
}}
tr.selected {{
  outline: 2px solid #64b5f6;
  outline-offset: -2px;
}}
tr.selected .line-no {{
  background: #64b5f6 !important;
  color: #000 !important;
}}
.syn-keyword {{
  color: #c792ea;
  font-weight: bold;
}}
.syn-builtin {{
  color: #82aaff;
}}
.syn-string {{
  color: #c3e88d;
}}
.syn-number {{
  color: #f78c6c;
}}
.syn-comment {{
  color: #676e95;
  font-style: italic;
}}
.syn-paren {{
  color: #89ddff;
}}
.syn-type {{
  color: #ffcb6b;
}}
.syn-function {{
  color: #82aaff;
}}
.syn-macro {{
  color: #ff5370;
}}
.syn-preproc {{
  color: #c792ea;
}}
</style>
</head>
<body>
<div class="header">
<a href="index.html">&larr; Back to Coverage Report</a>
<h1>{html.escape(rel_path)}</h1>
<div class="stats">
{'<div class="stat"><div class="stat-value ' + coverage_class(fc.expr_coverage_pct) + '">' + f'{fc.expr_coverage_pct:.1f}%' + '</div><div class="stat-label">Expression Coverage</div></div>' if is_valk and fc.exprs_found > 0 else '<div class="stat"><div class="stat-value ' + coverage_class(fc.line_coverage_pct) + '">' + f'{fc.line_coverage_pct:.1f}%' + '</div><div class="stat-label">Line Coverage</div></div>'}
<div class="stat">
<div class="stat-value {coverage_class(fc.branch_coverage_pct) if fc.branches_found > 0 else ''}">{f'{fc.branch_coverage_pct:.1f}%' if fc.branches_found > 0 else '-'}</div>
<div class="stat-label">Branch Coverage</div>
</div>
<div class="stat">
<div class="stat-value">{fc.exprs_hit}/{fc.exprs_found if is_valk and fc.exprs_found > 0 else f'{fc.lines_hit}/{fc.lines_found}'}</div>
<div class="stat-label">{'Expressions' if is_valk and fc.exprs_found > 0 else 'Lines'}</div>
</div>
<div class="stat">
<div class="stat-value">{fc.branches_hit}/{fc.branches_found if fc.branches_found > 0 else '-'}</div>
<div class="stat-label">Branches</div>
</div>
</div>
<div class="coverage-bar">
<div class="coverage-fill {coverage_class(fc.expr_coverage_pct if is_valk and fc.exprs_found > 0 else fc.line_coverage_pct)}-bg" style="width:{fc.expr_coverage_pct if is_valk and fc.exprs_found > 0 else fc.line_coverage_pct}%;background:{'#4caf50' if (fc.expr_coverage_pct if is_valk and fc.exprs_found > 0 else fc.line_coverage_pct) >= 80 else '#ff9800' if (fc.expr_coverage_pct if is_valk and fc.exprs_found > 0 else fc.line_coverage_pct) >= 50 else '#f44336'}"></div>
</div>
</div>
<table>
<tbody>
{"".join(lines_html)}
</tbody>
</table>
<script>
(function() {{
  let lastClickedLine = null;
  const rows = document.querySelectorAll('tr[id^="L"]');
  
  function getLineNum(row) {{
    return parseInt(row.id.substring(1), 10);
  }}
  
  function clearSelection() {{
    rows.forEach(r => r.classList.remove('selected'));
  }}
  
  function selectRange(start, end) {{
    const min = Math.min(start, end);
    const max = Math.max(start, end);
    rows.forEach(r => {{
      const n = getLineNum(r);
      if (n >= min && n <= max) r.classList.add('selected');
    }});
    history.replaceState(null, '', '#L' + min + (min !== max ? '-L' + max : ''));
  }}
  
  function applyHashSelection() {{
    const hash = window.location.hash;
    const match = hash.match(/^#L(\d+)(?:-L(\d+))?$/);
    if (match) {{
      const start = parseInt(match[1], 10);
      const end = match[2] ? parseInt(match[2], 10) : start;
      clearSelection();
      selectRange(start, end);
      lastClickedLine = start;
      const row = document.getElementById('L' + start);
      if (row) row.scrollIntoView({{block: 'center'}});
    }}
  }}
  
  document.querySelectorAll('.line-no').forEach(cell => {{
    cell.style.cursor = 'pointer';
    cell.addEventListener('click', function(e) {{
      e.preventDefault();
      const row = cell.parentElement;
      const lineNum = getLineNum(row);
      
      if (e.shiftKey && lastClickedLine !== null) {{
        clearSelection();
        selectRange(lastClickedLine, lineNum);
      }} else {{
        clearSelection();
        row.classList.add('selected');
        lastClickedLine = lineNum;
        history.replaceState(null, '', '#L' + lineNum);
      }}
    }});
  }});
  
  document.addEventListener('keydown', function(e) {{
    if (e.key === 'Escape') {{
      clearSelection();
      lastClickedLine = null;
      history.replaceState(null, '', window.location.pathname);
    }}
  }});
  
  applyHashSelection();
  window.addEventListener('hashchange', applyHashSelection);
}})();
</script>
</body>
</html>'''
    
    (output_dir / safe_name).write_text(file_html)
    return safe_name


def generate_html_report(report: CoverageReport, output_dir: Path, source_root: Path):
    """Generate HTML coverage report with file browsing."""
    output_dir.mkdir(parents=True, exist_ok=True)
    
    c_files = []
    valk_files = []
    file_links = {}
    
    for filepath, fc in sorted(report.files.items()):
        if fc.lines_found == 0:
            continue
        
        rel_path = filepath
        if filepath.startswith(str(source_root)):
            rel_path = filepath[len(str(source_root))+1:]
        
        if rel_path.startswith("test/") or rel_path.startswith("vendor/") or rel_path.endswith(".h"):
            continue
        
        file_html_name = generate_file_html(fc, output_dir, source_root)
        file_links[filepath] = file_html_name
        
        entry = (rel_path, fc, file_html_name)
        if filepath.endswith(".valk"):
            valk_files.append(entry)
        else:
            c_files.append(entry)
    
    c_lines_found = sum(fc.lines_found for _, fc, _ in c_files)
    c_lines_hit = sum(fc.lines_hit for _, fc, _ in c_files)
    c_pct = (c_lines_hit / c_lines_found * 100) if c_lines_found > 0 else 0
    c_branches_found = sum(fc.branches_found for _, fc, _ in c_files)
    c_branches_hit = sum(fc.branches_hit for _, fc, _ in c_files)
    c_branch_pct = (c_branches_hit / c_branches_found * 100) if c_branches_found > 0 else 0
    
    valk_exprs_found = sum(fc.exprs_found for _, fc, _ in valk_files)
    valk_exprs_hit = sum(fc.exprs_hit for _, fc, _ in valk_files)
    valk_pct = (valk_exprs_hit / valk_exprs_found * 100) if valk_exprs_found > 0 else 0
    valk_branches_found = sum(fc.branches_found for _, fc, _ in valk_files)
    valk_branches_hit = sum(fc.branches_hit for _, fc, _ in valk_files)
    valk_branch_pct = (valk_branches_hit / valk_branches_found * 100) if valk_branches_found > 0 else 0

    combined_branches_found = c_branches_found + valk_branches_found
    combined_branches_hit = c_branches_hit + valk_branches_hit
    combined_branch_pct = (combined_branches_hit / combined_branches_found * 100) if combined_branches_found > 0 else 0

    def file_table_rows(files, is_valk=False):
        rows = []
        for rel_path, fc, link in files:
            if is_valk and fc.exprs_found > 0:
                pct = fc.expr_coverage_pct
                count_str = f"{fc.exprs_hit}/{fc.exprs_found}"
            else:
                pct = fc.line_coverage_pct
                count_str = f"{fc.lines_hit}/{fc.lines_found}"
            branch_pct = fc.branch_coverage_pct
            rows.append(f'''<tr>
<td><a href="{link}">{html.escape(rel_path)}</a></td>
<td class="{coverage_class(pct)}">{pct:.1f}%</td>
<td class="{coverage_class(branch_pct)}">{branch_pct:.1f}%</td>
<td>{count_str}</td>
<td>{fc.branches_hit}/{fc.branches_found}</td>
<td>
<div class="mini-bar">
<div class="mini-fill {coverage_class(pct)}" style="width:{pct}%"></div>
</div>
</td>
</tr>''')
        return "\n".join(rows)
    
    index_html = f'''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Valkyria Coverage Report</title>
<style>
:root {{
  --bg: #1a1a2e;
  --bg-alt: #16213e;
  --card-bg: #0f3460;
  --text: #eee;
  --text-muted: #888;
  --border: #333;
  --accent: #e94560;
}}
* {{
  box-sizing: border-box;
}}
body {{
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
  background: var(--bg);
  color: var(--text);
  margin: 0;
  padding: 20px;
  min-height: 100vh;
}}
.container {{
  max-width: 1400px;
  margin: 0 auto;
}}
h1 {{
  margin: 0 0 30px 0;
  font-size: 2em;
  display: flex;
  align-items: center;
  gap: 15px;
}}
h1::before {{
  content: "🎯";
}}
.summary {{
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
  gap: 20px;
  margin-bottom: 40px;
}}
.card {{
  background: var(--card-bg);
  border-radius: 12px;
  padding: 25px;
  box-shadow: 0 4px 20px rgba(0,0,0,0.3);
}}
.card h2 {{
  margin: 0 0 20px 0;
  font-size: 1.2em;
  color: var(--text-muted);
  text-transform: uppercase;
  letter-spacing: 1px;
}}
.big-stat {{
  font-size: 3.5em;
  font-weight: bold;
  line-height: 1;
}}
.stat-detail {{
  color: var(--text-muted);
  margin-top: 10px;
  font-size: 0.9em;
}}
.coverage-bar {{
  height: 12px;
  background: #333;
  border-radius: 6px;
  margin-top: 15px;
  overflow: hidden;
}}
.coverage-fill {{
  height: 100%;
  border-radius: 6px;
  transition: width 0.3s;
}}
.cov-high {{ color: #4caf50; }}
.cov-high-bg {{ background: #4caf50; }}
.cov-med {{ color: #ff9800; }}
.cov-med-bg {{ background: #ff9800; }}
.cov-low {{ color: #f44336; }}
.cov-low-bg {{ background: #f44336; }}
.section {{
  background: var(--bg-alt);
  border-radius: 12px;
  padding: 25px;
  margin-bottom: 30px;
}}
.section h2 {{
  margin: 0 0 20px 0;
  display: flex;
  align-items: center;
  gap: 10px;
}}
table {{
  width: 100%;
  border-collapse: collapse;
}}
th, td {{
  padding: 12px 15px;
  text-align: left;
  border-bottom: 1px solid var(--border);
}}
th {{
  color: var(--text-muted);
  font-weight: 600;
  font-size: 0.85em;
  text-transform: uppercase;
  letter-spacing: 0.5px;
}}
tr:hover {{
  background: rgba(255,255,255,0.03);
}}
a {{
  color: #64b5f6;
  text-decoration: none;
}}
a:hover {{
  text-decoration: underline;
}}
.mini-bar {{
  width: 100px;
  height: 6px;
  background: #333;
  border-radius: 3px;
  overflow: hidden;
}}
.mini-fill {{
  height: 100%;
  border-radius: 3px;
}}
.timestamp {{
  text-align: center;
  color: var(--text-muted);
  font-size: 0.85em;
  margin-top: 40px;
  padding-top: 20px;
  border-top: 1px solid var(--border);
}}
.empty {{
  color: var(--text-muted);
  font-style: italic;
  padding: 40px;
  text-align: center;
}}
.tier-section {{
  border-left: 4px solid var(--accent);
}}
.tier-section h2 {{
  font-size: 1em;
}}
tr.tier-pass {{
  background: rgba(76, 175, 80, 0.1);
}}
tr.tier-fail {{
  background: rgba(244, 67, 54, 0.1);
}}
</style>
</head>
<body>
<div class="container">
<h1>Valkyria Coverage Report</h1>

<div class="summary">
<div class="card">
<h2>Runtime</h2>
<div class="big-stat {coverage_class(c_pct)}">{c_pct:.1f}%</div>
<div class="stat-detail">{c_lines_hit:,} / {c_lines_found:,} lines</div>
<div class="coverage-bar">
<div class="coverage-fill {coverage_class(c_pct)}-bg" style="width:{c_pct}%"></div>
</div>
</div>

<div class="card">
<h2>Stdlib</h2>
<div class="big-stat {coverage_class(valk_pct)}">{valk_pct:.1f}%</div>
<div class="stat-detail">{valk_exprs_hit:,} / {valk_exprs_found:,} exprs</div>
<div class="coverage-bar">
<div class="coverage-fill {coverage_class(valk_pct)}-bg" style="width:{valk_pct}%"></div>
</div>
</div>

<div class="card">
<h2>Branches</h2>
<div class="big-stat {coverage_class(combined_branch_pct)}">{combined_branch_pct:.1f}%</div>
<div class="stat-detail">{c_branches_hit + valk_branches_hit:,} / {c_branches_found + valk_branches_found:,} branches</div>
<div class="coverage-bar">
<div class="coverage-fill {coverage_class(combined_branch_pct)}-bg" style="width:{combined_branch_pct}%"></div>
</div>
</div>
</div>

<div class="section">
<h2>📁 Runtime Files ({len(c_files)})</h2>
{'<table><thead><tr><th>File</th><th>Lines</th><th>Branches</th><th>L Hit/Total</th><th>B Hit/Total</th><th></th></tr></thead><tbody>' + file_table_rows(c_files) + '</tbody></table>' if c_files else '<div class="empty">No Runtime coverage data available</div>'}
</div>

<div class="section">
<h2>🚀 Stdlib Files ({len(valk_files)})</h2>
{'<table><thead><tr><th>File</th><th>Exprs</th><th>Branches</th><th>E Hit/Total</th><th>B Hit/Total</th><th></th></tr></thead><tbody>' + file_table_rows(valk_files, is_valk=True) + '</tbody></table>' if valk_files else '<div class="empty">No Stdlib coverage data available</div>'}
</div>

<div class="timestamp">Generated: {report.timestamp}</div>
</div>
</body>
</html>'''
    
    (output_dir / "index.html").write_text(index_html)


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="Generate unified coverage reports")
    parser.add_argument("--build-dir", default="build-coverage", help="Build directory with coverage data")
    parser.add_argument("--source-root", default=".", help="Source root directory")
    parser.add_argument("--output", default="coverage-report", help="Output directory for reports")
    parser.add_argument("--valk-lcov", help="Path to Valk LCOV file (default: <build-dir>/coverage-valk.info)")
    parser.add_argument("--xml", action="store_true", help="Also generate Cobertura XML report")
    
    args = parser.parse_args()
    
    build_dir = Path(args.build_dir).resolve()
    source_root = Path(args.source_root).resolve()
    output_dir = Path(args.output).resolve()
    
    valk_lcov = Path(args.valk_lcov) if args.valk_lcov else build_dir / "coverage-valk.info"
    
    print(f"Collecting coverage data...")
    print(f"  Build dir:    {build_dir}")
    print(f"  Source root:  {source_root}")
    print(f"  Valk LCOV:    {valk_lcov}")
    print(f"  Output:       {output_dir}")
    
    report = CoverageReport()
    
    print("\nParsing C coverage (gcov)...")
    parse_gcov_files(build_dir, source_root, report)
    c_count = len([f for f in report.files.keys() if not f.endswith(".valk")])
    print(f"  Found {c_count} C files")
    
    print("\nParsing Valk coverage (LCOV)...")
    parse_lcov_file(valk_lcov, report, source_root)
    valk_count = len([f for f in report.files.keys() if f.endswith(".valk")])
    print(f"  Found {valk_count} Valk files")
    
    print("\nGenerating HTML report...")
    generate_html_report(report, output_dir, source_root)
    print(f"  HTML: {output_dir}/index.html")
    
    if args.xml:
        xml_path = output_dir / "coverage.xml"
        print("\nGenerating Cobertura XML report...")
        generate_cobertura_xml(report, xml_path, source_root)
        print(f"  XML: {xml_path}")
    
    # Compute Runtime (C) and Stdlib (Valk) stats separately
    runtime_files = {k: v for k, v in report.files.items()
                     if not k.endswith(".valk") and not "/test/" in k and not "/vendor/" in k and not k.endswith(".h")}
    stdlib_files = {k: v for k, v in report.files.items()
                    if k.endswith(".valk") and not "/test/" in k}

    runtime_lines_found = sum(f.lines_found for f in runtime_files.values())
    runtime_lines_hit = sum(f.lines_hit for f in runtime_files.values())
    runtime_pct = (runtime_lines_hit / runtime_lines_found * 100) if runtime_lines_found > 0 else 0

    stdlib_exprs_found = sum(f.exprs_found for f in stdlib_files.values())
    stdlib_exprs_hit = sum(f.exprs_hit for f in stdlib_files.values())
    stdlib_pct = (stdlib_exprs_hit / stdlib_exprs_found * 100) if stdlib_exprs_found > 0 else 0

    total_branches_found = sum(f.branches_found for f in runtime_files.values()) + sum(f.branches_found for f in stdlib_files.values())
    total_branches_hit = sum(f.branches_hit for f in runtime_files.values()) + sum(f.branches_hit for f in stdlib_files.values())
    branches_pct = (total_branches_hit / total_branches_found * 100) if total_branches_found > 0 else 0

    print(f"\n{'='*60}")
    print(f"Coverage Summary:")
    print(f"  Runtime:  {runtime_pct:.1f}% lines ({runtime_lines_hit}/{runtime_lines_found})")
    print(f"  Stdlib:   {stdlib_pct:.1f}% exprs ({stdlib_exprs_hit}/{stdlib_exprs_found})")
    print(f"  Branches: {branches_pct:.1f}% ({total_branches_hit}/{total_branches_found})")
    print(f"{'='*60}")
    print(f"\nOpen {output_dir}/index.html in a browser to view the report.")


if __name__ == "__main__":
    main()
