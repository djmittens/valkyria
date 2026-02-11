#!/usr/bin/env python3
"""Unified parallel test runner for Valkyria.

Discovers all test suites (C binaries and Valk test files), runs them in
parallel with one suite per CPU core, produces JUnit XML, and prints a
concise summary with failure details.

Usage:
  run-tests.py                          # Run all tests
  run-tests.py -f memory                # Fuzzy filter: suites matching "memory"
  run-tests.py -f "sse|http"            # Multiple patterns (regex)
  run-tests.py --build-dir build-asan   # Use ASAN build
  run-tests.py --timeout 60             # Per-suite timeout
  run-tests.py --junit-dir /tmp/junit   # Custom JUnit output dir
  run-tests.py --no-stress              # Exclude stress tests
  run-tests.py --only c                 # Only C tests
  run-tests.py --only valk              # Only Valk tests
"""

import argparse
import os
import re
import signal
import subprocess
import sys
import time
import xml.etree.ElementTree as ET
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

TAIL_LINES = 100
EXCLUDE_BINARIES = {"test_demo_server"}


def discover_c_tests(build_dir):
    """Find all test_* executables in build_dir."""
    suites = []
    build = Path(build_dir)
    if not build.is_dir():
        return suites
    for p in sorted(build.iterdir()):
        if not p.name.startswith("test_"):
            continue
        if p.name in EXCLUDE_BINARIES:
            continue
        if not p.is_file():
            continue
        if not os.access(p, os.X_OK):
            continue
        # skip .dSYM directories on macOS (they appear as files sometimes)
        if p.suffix == ".dSYM":
            continue
        suites.append({"name": p.name, "cmd": [str(p)], "kind": "c"})
    return suites


def discover_valk_tests(build_dir, include_stress=True):
    """Find all test_*.valk files in test/ and test/stress/."""
    suites = []
    valk = str(Path(build_dir) / "valk")
    if not os.access(valk, os.X_OK):
        return suites

    test_dir = Path("test")
    if not test_dir.is_dir():
        return suites

    # test/test_*.valk
    for p in sorted(test_dir.glob("test_*.valk")):
        suites.append({"name": p.stem, "cmd": [valk, str(p)], "kind": "valk"})

    # test/stress/test_*.valk
    if include_stress:
        stress_dir = test_dir / "stress"
        if stress_dir.is_dir():
            for p in sorted(stress_dir.glob("test_*.valk")):
                suites.append({
                    "name": f"stress/{p.stem}",
                    "cmd": [valk, str(p)],
                    "kind": "valk",
                })

    return suites


def filter_suites(suites, pattern):
    """Filter suites by regex pattern against name."""
    if not pattern:
        return suites
    try:
        rx = re.compile(pattern, re.IGNORECASE)
    except re.error:
        # Fall back to literal substring
        rx = re.compile(re.escape(pattern), re.IGNORECASE)
    return [s for s in suites if rx.search(s["name"])]


def run_one_suite(suite, junit_dir, timeout):
    """Run a single test suite, write JUnit XML, return result dict."""
    name = suite["name"]
    cmd = suite["cmd"]
    kind = suite["kind"]

    wall_start = time.monotonic()
    death_signal = None
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            env={**os.environ, "VALK_TEST_TIMEOUT_SECONDS": "30"},
        )
        wall_time = time.monotonic() - wall_start
        exit_code = proc.returncode
        stdout = proc.stdout or ""
        stderr = proc.stderr or ""
        if exit_code < 0:
            death_signal = -exit_code
            exit_code = 128 + (-exit_code)
    except subprocess.TimeoutExpired as e:
        wall_time = time.monotonic() - wall_start
        stdout = (e.stdout or b"").decode("utf-8", errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        stderr = (e.stderr or b"").decode("utf-8", errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
        exit_code = 124
        death_signal = None

    # Parse structured test output
    test_line_re = re.compile(
        r"^(?:\u2705|\u274c|\u23f0|\u23ed\ufe0f?\s?|\U0001f41e|\U0001f300|\u2753)\s+"
        r"(.+?)"
        r"\.{2,}\s+"
        r"(PASS|FAIL|TIMEOUT|SKIP|CRSH|UNKNOWN|UNDEFINED)"
        r"(?:\s*:\s*(?:in|after)\s+(\S+))?"
        r"(?:\(type=\d+\))?"
        r"\s*$"
    )

    tests = []
    combined = stdout + "\n" + stderr
    for line in combined.splitlines():
        m = test_line_re.match(line.strip())
        if m:
            tname = m.group(1).rstrip(". ")
            status = m.group(2)
            time_str = m.group(3)
            elapsed = _parse_time(time_str)
            tests.append({"name": tname, "status": status, "time": elapsed})

    # Count results
    passed = sum(1 for t in tests if t["status"] == "PASS")
    failed = sum(1 for t in tests if t["status"] in ("FAIL", "CRSH", "TIMEOUT", "UNKNOWN", "UNDEFINED"))
    skipped = sum(1 for t in tests if t["status"] == "SKIP")

    # Determine suite-level pass/fail
    suite_passed = exit_code == 0

    # Write JUnit XML
    _write_junit(name, tests, stdout, stderr, exit_code, wall_time, death_signal, timeout, junit_dir)

    return {
        "name": name,
        "kind": kind,
        "passed": suite_passed,
        "exit_code": exit_code,
        "death_signal": death_signal,
        "wall_time": wall_time,
        "test_count": len(tests),
        "test_passed": passed,
        "test_failed": failed,
        "test_skipped": skipped,
        "stdout": stdout,
        "stderr": stderr,
    }


def _parse_time(time_str):
    if not time_str:
        return 0.0
    m = re.match(r"([\d.]+)\(?(\u00b5s|us|ms|ns|s)\)?", time_str)
    if not m:
        return 0.0
    val = float(m.group(1))
    unit = m.group(2)
    if unit in ("\u00b5s", "us"):
        return val / 1_000_000
    elif unit == "ms":
        return val / 1_000
    elif unit == "ns":
        return val / 1_000_000_000
    return val


def _xml_safe(text):
    return re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)


def _write_junit(suite_name, tests, stdout, stderr, exit_code, wall_time, death_signal, timeout, junit_dir):
    """Write JUnit XML for one suite."""
    testsuites = ET.Element("testsuites")
    testsuite = ET.SubElement(testsuites, "testsuite")
    testsuite.set("name", suite_name)

    combined = _xml_safe(stdout + "\n" + stderr)
    failures = 0
    errors = 0
    skipped_count = 0
    total_time = 0.0

    if not tests:
        tc = ET.SubElement(testsuite, "testcase")
        tc.set("classname", suite_name)
        tc.set("name", suite_name)
        tc.set("time", f"{wall_time:.6f}")
        total_time = wall_time
        if exit_code == 124:
            errors = 1
            err = ET.SubElement(tc, "error")
            err.set("message", f"test timed out after {timeout}s")
            err.text = combined[-8192:]
        elif death_signal:
            errors = 1
            sig_name = _signal_name(death_signal)
            err = ET.SubElement(tc, "error")
            err.set("message", f"killed by signal {sig_name}")
            err.text = combined[-8192:]
        elif exit_code != 0:
            failures = 1
            fail = ET.SubElement(tc, "failure")
            fail.set("message", f"exited with code {exit_code}")
            fail.text = combined[-8192:]
        tests_count = 1
    else:
        tests_count = len(tests)
        for t in tests:
            tc = ET.SubElement(testsuite, "testcase")
            tc.set("classname", suite_name)
            tc.set("name", t["name"])
            tc.set("time", f"{t['time']:.6f}")
            total_time += t["time"]
            if t["status"] == "PASS":
                pass
            elif t["status"] == "SKIP":
                skipped_count += 1
                ET.SubElement(tc, "skipped")
            elif t["status"] == "FAIL":
                failures += 1
                fail = ET.SubElement(tc, "failure")
                fail.set("message", "test failed")
            elif t["status"] == "TIMEOUT":
                errors += 1
                err = ET.SubElement(tc, "error")
                err.set("message", "timed out")
            elif t["status"] == "CRSH":
                errors += 1
                err = ET.SubElement(tc, "error")
                err.set("message", "crashed")
            else:
                errors += 1
                err = ET.SubElement(tc, "error")
                err.set("message", f"unknown status: {t['status']}")

        if exit_code == 124:
            tc = ET.SubElement(testsuite, "testcase")
            tc.set("classname", suite_name)
            tc.set("name", "(suite timeout)")
            tc.set("time", "0")
            errors += 1
            tests_count += 1
            err = ET.SubElement(tc, "error")
            err.set("message", f"suite timed out after {timeout}s")
        elif death_signal:
            tc = ET.SubElement(testsuite, "testcase")
            tc.set("classname", suite_name)
            tc.set("name", "(suite crashed)")
            tc.set("time", "0")
            errors += 1
            tests_count += 1
            sig_name = _signal_name(death_signal)
            err = ET.SubElement(tc, "error")
            err.set("message", f"suite killed by {sig_name}")
            err.text = combined[-8192:]
        elif exit_code != 0:
            tc = ET.SubElement(testsuite, "testcase")
            tc.set("classname", suite_name)
            tc.set("name", "(suite error)")
            tc.set("time", "0")
            errors += 1
            tests_count += 1
            err = ET.SubElement(tc, "error")
            err.set("message", f"suite exited with code {exit_code}")

    testsuite.set("tests", str(tests_count))
    testsuite.set("failures", str(failures))
    testsuite.set("errors", str(errors))
    testsuite.set("skipped", str(skipped_count))
    testsuite.set("time", f"{total_time:.6f}")

    if (failures > 0 or errors > 0) and combined.strip():
        sysout = ET.SubElement(testsuite, "system-out")
        sysout.text = combined[-16384:]

    tree = ET.ElementTree(testsuites)
    ET.indent(tree, space="  ")
    # Sanitize suite name for filesystem
    safe_name = suite_name.replace("/", "_")
    path = os.path.join(junit_dir, f"{safe_name}.xml")
    tree.write(path, encoding="unicode", xml_declaration=True)


def _signal_name(signum):
    try:
        return signal.Signals(signum).name
    except (ValueError, AttributeError):
        return str(signum)


def _parse_captured_blocks(stdout):
    """Parse <<<CAPTURED name=X ... >>>CAPTURED blocks from test output."""
    blocks = {}
    lines = stdout.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("<<<CAPTURED name="):
            name = line[len("<<<CAPTURED name="):].strip()
            cap_stdout = []
            cap_stderr = []
            target = None
            i += 1
            while i < len(lines) and not lines[i].startswith(">>>CAPTURED"):
                if lines[i] == "<<<STDOUT":
                    target = cap_stdout
                elif lines[i] == ">>>STDOUT":
                    target = None
                elif lines[i] == "<<<STDERR":
                    target = cap_stderr
                elif lines[i] == ">>>STDERR":
                    target = None
                elif target is not None:
                    target.append(lines[i])
                i += 1
            blocks[name] = {
                "stdout": "\n".join(cap_stdout),
                "stderr": "\n".join(cap_stderr),
            }
        i += 1
    return blocks


def _extract_failed_test_lines(stdout):
    """Extract FAIL/TIMEOUT/CRSH result lines from test output."""
    fail_re = re.compile(
        r"^(?:\u274c|\u23f0|\U0001f41e|\U0001f300|\u2753)\s+"
        r".+?\.{2,}\s+"
        r"(?:FAIL|TIMEOUT|CRSH|UNKNOWN|UNDEFINED)"
    )
    failed = []
    for line in stdout.splitlines():
        if fail_re.match(line.strip()):
            failed.append(line.strip())
    return failed


def _test_name_from_result_line(line):
    """Extract test name from a result line like '🌀 test_foo...  CRSH'."""
    # Strip emoji prefix
    m = re.match(
        r"^(?:\u2705|\u274c|\u23f0|\u23ed\ufe0f?\s?|\U0001f41e|\U0001f300|\u2753)\s+"
        r"(.+?)"
        r"\.{2,}",
        line.strip(),
    )
    return m.group(1).strip() if m else None


def _truncate(text, max_lines):
    """Truncate text to max_lines, return as single string with indent."""
    lines = text.splitlines()
    if len(lines) <= max_lines:
        return "\n    ".join(lines)
    return "\n    ".join(lines[-max_lines:])


def print_summary(results, wall_time, junit_dir):
    """Print concise summary to terminal."""
    total = len(results)
    passed_suites = [r for r in results if r["passed"]]
    failed_suites = [r for r in results if not r["passed"]]

    total_tests = sum(r["test_count"] for r in results)
    total_passed = sum(r["test_passed"] for r in results)
    total_failed = sum(r["test_failed"] for r in results)
    total_skipped = sum(r["test_skipped"] for r in results)

    print()
    print("=" * 70)

    if not failed_suites:
        print(f"  ALL PASSED: {total} suites, {total_tests} tests in {wall_time:.1f}s")
    else:
        print(f"  FAILED: {len(failed_suites)}/{total} suites, "
              f"{total_failed} test failures in {wall_time:.1f}s")

    print(f"  Tests: {total_passed} passed, {total_failed} failed, "
          f"{total_skipped} skipped")
    print(f"  JUnit: {junit_dir}/")
    print("=" * 70)

    if failed_suites:
        print()
        print("FAILED SUITES:")
        print()
        for r in failed_suites:
            sig_info = ""
            if r["death_signal"]:
                sig_info = f" (signal {_signal_name(r['death_signal'])})"
            elif r["exit_code"] == 124:
                sig_info = " (timeout)"

            print(f"  [{r['kind']}] {r['name']} - exit {r['exit_code']}{sig_info} "
                  f"({r['wall_time']:.1f}s)")

        print()
        print("-" * 70)
        print("FAILURE DETAILS:")
        print("-" * 70)

        for r in failed_suites:
            print()
            print(f"--- {r['name']} ---")

            stdout = r["stdout"]
            stderr = r["stderr"].rstrip()

            # Extract captured output blocks (C forked tests + Valk per-test capture)
            captured = _parse_captured_blocks(stdout)

            # Show failed/timed-out test result lines
            failed_tests = _extract_failed_test_lines(stdout)
            for ft in failed_tests:
                print(f"  {ft}")
                tname = _test_name_from_result_line(ft)
                if tname and tname in captured:
                    cap = captured[tname]
                    if cap["stdout"].strip():
                        print(f"    stdout: {_truncate(cap['stdout'].strip(), TAIL_LINES)}")
                    if cap["stderr"].strip():
                        print(f"    stderr: {_truncate(cap['stderr'].strip(), TAIL_LINES)}")

            # Show captured blocks for tests without a result line (crash before reporting)
            shown_tests = {_test_name_from_result_line(ft) for ft in failed_tests}
            for name, cap in captured.items():
                if name in shown_tests:
                    continue
                content = (cap["stdout"].strip() + "\n" + cap["stderr"].strip()).strip()
                if content:
                    print(f"  [{name}] captured output:")
                    print(f"    {_truncate(content, TAIL_LINES)}")

            # When there's no captured output, show stderr
            # (fallback for tests without per-test capture)
            if not captured and stderr:
                stderr_lines = stderr.splitlines()
                # Filter out noise: aio_alloc memory tracking, etc.
                useful = [l for l in stderr_lines if not l.startswith("[aio_alloc]")]
                if useful:
                    tail = useful[-TAIL_LINES:]
                    print()
                    print(f"  stderr ({len(useful)} lines, last {len(tail)}):")
                    for line in tail:
                        print(f"    {line}")

            # If nothing useful was shown at all, dump stdout tail
            if not captured and not failed_tests and not stderr:
                stdout_lines = stdout.rstrip().splitlines()
                tail = stdout_lines[-TAIL_LINES:]
                print(f"  stdout ({len(stdout_lines)} lines, last {len(tail)}):")
                for line in tail:
                    print(f"    {line}")

    return len(failed_suites) == 0


def main():
    parser = argparse.ArgumentParser(description="Unified parallel test runner for Valkyria")
    parser.add_argument("-f", "--filter", default="", help="Regex filter for suite names")
    parser.add_argument("--build-dir", default="build", help="Build directory (default: build)")
    parser.add_argument("--timeout", type=int, default=120, help="Per-suite timeout in seconds (default: 120)")
    parser.add_argument("--jobs", "-j", type=int, default=0, help="Parallel jobs (default: CPU count)")
    parser.add_argument("--junit-dir", default="", help="JUnit output dir (default: test-report/<timestamp>/)")
    parser.add_argument("--no-stress", action="store_true", help="Exclude stress tests")
    parser.add_argument("--only", choices=["c", "valk"], help="Only run C or Valk tests")
    args = parser.parse_args()

    build_dir = args.build_dir
    if not Path(build_dir).is_dir():
        print(f"error: build directory '{build_dir}' does not exist", file=sys.stderr)
        print(f"hint: run 'make build' first", file=sys.stderr)
        sys.exit(1)

    # Discover suites
    suites = []
    if args.only != "valk":
        suites.extend(discover_c_tests(build_dir))
    if args.only != "c":
        suites.extend(discover_valk_tests(build_dir, include_stress=not args.no_stress))

    if not suites:
        print("error: no test suites found", file=sys.stderr)
        sys.exit(1)

    # Apply filter
    suites = filter_suites(suites, args.filter)
    if not suites:
        print(f"error: no suites match filter '{args.filter}'", file=sys.stderr)
        sys.exit(1)

    # JUnit output directory
    if args.junit_dir:
        junit_dir = args.junit_dir
    else:
        ts = datetime.now(timezone.utc).strftime("%Y-%m-%d_%H-%M-%S")
        junit_dir = f"test-report/junit-{ts}"
    os.makedirs(junit_dir, exist_ok=True)

    # Also symlink test-report/latest -> this run
    report_root = Path("test-report")
    latest_link = report_root / "latest"
    try:
        latest_link.unlink(missing_ok=True)
        # Use relative symlink so it works if the repo moves
        latest_link.symlink_to(Path(junit_dir).name)
    except OSError:
        pass

    jobs = args.jobs if args.jobs > 0 else os.cpu_count() or 4
    c_count = sum(1 for s in suites if s["kind"] == "c")
    v_count = sum(1 for s in suites if s["kind"] == "valk")

    print(f"Running {len(suites)} suites ({c_count} C, {v_count} Valk) "
          f"with {jobs} parallel workers")
    print(f"JUnit output: {junit_dir}/")
    print()

    wall_start = time.monotonic()
    results = []

    with ProcessPoolExecutor(max_workers=jobs) as pool:
        futures = {
            pool.submit(run_one_suite, suite, junit_dir, args.timeout): suite
            for suite in suites
        }

        completed = 0
        for future in as_completed(futures):
            completed += 1
            result = future.result()
            results.append(result)

            # Live progress
            status = "PASS" if result["passed"] else "FAIL"
            elapsed = result["wall_time"]
            sys.stdout.write(
                f"\r[{completed}/{len(suites)}] {status}: {result['name']}"
                f" ({elapsed:.1f}s)".ljust(78) + "\n"
            )
            sys.stdout.flush()

    wall_time = time.monotonic() - wall_start

    # Sort results: failures first, then by name
    results.sort(key=lambda r: (r["passed"], r["name"]))

    all_passed = print_summary(results, wall_time, junit_dir)
    sys.exit(0 if all_passed else 1)


if __name__ == "__main__":
    main()
