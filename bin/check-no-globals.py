#!/usr/bin/env python3
"""
Global Mutation Lint for Valkyria

Enforces the no-global-mutation rule for concurrent safety.
Scans .valk files for (def {*...*} ...) patterns that mutate globals.

Exit code 0 = pass, 1 = violations found

Allowed exceptions:
- Atom creation: (def {*name*} (atom ...))
- Constants: (def {nil} ...), (def {true} ...), etc.
- Test infrastructure: modules/test.valk globals (load-time only, documented)
"""

import sys
import re
from pathlib import Path


ALLOWED_PATTERNS = {
    "src/modules/test.valk": {
        "*test-default-timeout-ms*",
        "*test-default-suite-timeout-ms*",
    },
}

ATOM_PATTERN = re.compile(r'\(atom\s')
DEF_GLOBAL_PATTERN = re.compile(r'\(def\s+\{\*([^*}]+)\*\}')


def is_atom_creation(line: str) -> bool:
    return bool(ATOM_PATTERN.search(line))


def scan_file(filepath: Path, base_path: Path) -> list[tuple[int, str, str]]:
    violations = []
    rel_path = str(filepath.relative_to(base_path))
    allowed = ALLOWED_PATTERNS.get(rel_path, {})
    
    try:
        content = filepath.read_text()
    except Exception as e:
        print(f"Warning: Could not read {filepath}: {e}", file=sys.stderr)
        return violations
    
    for line_num, line in enumerate(content.splitlines(), 1):
        line_stripped = line.strip()
        if line_stripped.startswith(';'):
            continue
            
        match = DEF_GLOBAL_PATTERN.search(line)
        if match:
            var_name = f"*{match.group(1)}*"
            
            if var_name in allowed:
                continue
                
            if is_atom_creation(line):
                continue
            
            violations.append((line_num, var_name, line_stripped))
    
    return violations


def main():
    base_path = Path(__file__).parent.parent.resolve()
    
    src_valk_files = list((base_path / "src").rglob("*.valk"))
    test_valk_files = list((base_path / "test").rglob("*.valk"))
    
    all_files = src_valk_files + test_valk_files
    
    print("=" * 80)
    print("VALKYRIA GLOBAL MUTATION LINT")
    print("=" * 80)
    print()
    print(f"Scanning {len(all_files)} .valk files for global mutations...")
    print()
    
    all_violations = []
    
    for filepath in sorted(all_files):
        violations = scan_file(filepath, base_path)
        if violations:
            rel_path = filepath.relative_to(base_path)
            all_violations.append((rel_path, violations))
    
    if all_violations:
        print("VIOLATIONS FOUND:")
        print()
        for rel_path, violations in all_violations:
            print(f"  {rel_path}:")
            for line_num, var_name, line in violations:
                print(f"    Line {line_num}: {var_name}")
                print(f"      {line[:70]}{'...' if len(line) > 70 else ''}")
            print()
        
        print("=" * 80)
        print(f"FAILED: {sum(len(v) for _, v in all_violations)} global mutation(s) in {len(all_violations)} file(s)")
        print()
        print("Global mutable state causes data races in concurrent code.")
        print("Use atoms for thread-safe state, or pass state explicitly.")
        print()
        print("To add an allowed exception, update ALLOWED_PATTERNS in bin/check-no-globals.py")
        print("=" * 80)
        return 1
    
    print("=" * 80)
    print(f"PASSED: No global mutation violations found in {len(all_files)} files")
    print("=" * 80)
    return 0


if __name__ == "__main__":
    sys.exit(main())
