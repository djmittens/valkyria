#!/usr/bin/env python3
"""Universal test wrapper that produces JUnit XML for any test command.

Handles both C test binaries and Valk test files. Always produces JUnit XML,
even if the test crashes, times out, or is killed.

Usage:
  test-to-junit.py --junit-dir <dir> [--timeout <secs>] -- <command> [args...]

Examples:
  # C test binary
  test-to-junit.py --junit-dir build/junit -- build/test_memory

  # Valk test file
  test-to-junit.py --junit-dir build/junit -- build/valk test/test_prelude.valk

  # With timeout
  test-to-junit.py --junit-dir build/junit --timeout 60 -- build/test_memory

The script:
  1. Runs the command, capturing stdout/stderr
  2. Parses structured test output (PASS/FAIL/TIMEOUT/SKIP/CRSH lines)
  3. Writes JUnit XML to <junit-dir>/<suite-name>.xml
  4. ALWAYS writes XML, even on crash/timeout/signal death
  5. Exits with the original command's exit code (or 124 for timeout, 128+sig for signal)
"""

import argparse
import os
import re
import signal
import subprocess
import sys
import time
import xml.etree.ElementTree as ET
from pathlib import Path


# Both C and Valk frameworks emit lines like:
#   ✅ test_name...  PASS : in 123(µs)
#   ❌ test_name...  FAIL : in 123(µs)
#   ⏰ test_name...  TIMEOUT : after 5000ms
#   ⏭️  test_name...  SKIP
#   🐞 test_name...  FAIL : in 123(µs)
#   🌀 test_name...  CRSH : in 123(µs)
#   ❓ test_name...  UNKNOWN(type=0)
TEST_LINE_RE = re.compile(
    r"^(?:✅|❌|⏰|⏭️\s?|🐞|🌀|❓)\s+"
    r"(.+?)"
    r"\.{2,}\s+"
    r"(PASS|FAIL|TIMEOUT|SKIP|CRSH|UNKNOWN|UNDEFINED)"
    r"(?:\s*:\s*(?:in|after)\s+(\S+))?"
    r"(?:\(type=\d+\))?"
    r"\s*$"
)


def parse_time_seconds(time_str):
    """Convert test timing strings like '123(µs)' or '5000ms' to seconds."""
    if not time_str:
        return 0.0
    m = re.match(r"([\d.]+)\(?(µs|us|ms|ns|s)\)?", time_str)
    if not m:
        return 0.0
    val = float(m.group(1))
    unit = m.group(2)
    if unit in ("µs", "us"):
        return val / 1_000_000
    elif unit == "ms":
        return val / 1_000
    elif unit == "ns":
        return val / 1_000_000_000
    return val


def derive_suite_name(cmd_args):
    """Derive a human-readable suite name from the command.

    For 'build/test_memory' -> 'test_memory'
    For 'build/valk test/test_prelude.valk' -> 'test_prelude'
    """
    if len(cmd_args) >= 2 and cmd_args[0].endswith("/valk"):
        return Path(cmd_args[1]).stem
    return Path(cmd_args[0]).stem


def xml_safe(text):
    """Remove control chars that are invalid in XML 1.0."""
    return re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)


def run_test(cmd_args, timeout_secs):
    """Run the test command, return (stdout, stderr, exit_code, wall_time, death_signal)."""
    wall_start = time.monotonic()
    death_signal = None
    try:
        proc = subprocess.run(
            cmd_args,
            capture_output=True,
            text=True,
            timeout=timeout_secs,
        )
        wall_time = time.monotonic() - wall_start
        exit_code = proc.returncode
        stdout = proc.stdout or ""
        stderr = proc.stderr or ""

        # Negative return code means killed by signal on Unix
        if exit_code < 0:
            death_signal = -exit_code
            exit_code = 128 + (-exit_code)

        return stdout, stderr, exit_code, wall_time, death_signal

    except subprocess.TimeoutExpired as e:
        wall_time = time.monotonic() - wall_start
        stdout = (e.stdout or b"").decode("utf-8", errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        stderr = (e.stderr or b"").decode("utf-8", errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
        return stdout, stderr, 124, wall_time, None


def build_junit(suite_name, tests, stdout, stderr, exit_code, wall_time, death_signal, timeout_secs):
    """Build JUnit XML ElementTree from parsed test results."""
    testsuites = ET.Element("testsuites")
    testsuite = ET.SubElement(testsuites, "testsuite")
    testsuite.set("name", suite_name)

    combined = xml_safe(stdout + "\n" + stderr)
    failures = 0
    errors = 0
    skipped = 0
    total_time = 0.0

    if not tests:
        # No parseable test lines - treat entire run as one testcase
        tc = ET.SubElement(testsuite, "testcase")
        tc.set("classname", suite_name)
        tc.set("name", suite_name)
        tc.set("time", f"{wall_time:.6f}")
        total_time = wall_time

        if exit_code == 124:
            errors = 1
            err = ET.SubElement(tc, "error")
            err.set("message", f"test timed out after {timeout_secs}s")
            err.text = combined[-8192:]
        elif death_signal:
            errors = 1
            sig_name = signal.Signals(death_signal).name if death_signal in signal.Signals._value2member_map_ else str(death_signal)
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
        for name, status, elapsed in tests:
            tc = ET.SubElement(testsuite, "testcase")
            tc.set("classname", suite_name)
            tc.set("name", name)
            tc.set("time", f"{elapsed:.6f}")
            total_time += elapsed

            if status == "PASS":
                pass
            elif status == "SKIP":
                skipped += 1
                ET.SubElement(tc, "skipped")
            elif status == "FAIL":
                failures += 1
                fail = ET.SubElement(tc, "failure")
                fail.set("message", "test failed")
            elif status in ("TIMEOUT",):
                errors += 1
                err = ET.SubElement(tc, "error")
                err.set("message", "timed out")
            elif status in ("CRSH",):
                errors += 1
                err = ET.SubElement(tc, "error")
                err.set("message", "crashed")
            else:
                errors += 1
                err = ET.SubElement(tc, "error")
                err.set("message", f"unknown status: {status}")

        # If the process died but some tests were parsed, add a synthetic
        # testcase for the crash so it's visible in the report
        if exit_code == 124:
            tc = ET.SubElement(testsuite, "testcase")
            tc.set("classname", suite_name)
            tc.set("name", "(suite timeout)")
            tc.set("time", "0")
            errors += 1
            tests_count += 1
            err = ET.SubElement(tc, "error")
            err.set("message", f"suite timed out after {timeout_secs}s - remaining tests not executed")
        elif death_signal:
            tc = ET.SubElement(testsuite, "testcase")
            tc.set("classname", suite_name)
            tc.set("name", "(suite crashed)")
            tc.set("time", "0")
            errors += 1
            tests_count += 1
            sig_name = signal.Signals(death_signal).name if death_signal in signal.Signals._value2member_map_ else str(death_signal)
            err = ET.SubElement(tc, "error")
            err.set("message", f"suite killed by {sig_name} - remaining tests not executed")
            err.text = combined[-8192:]
        elif exit_code != 0:
            tc = ET.SubElement(testsuite, "testcase")
            tc.set("classname", suite_name)
            tc.set("name", "(suite error)")
            tc.set("time", "0")
            errors += 1
            tests_count += 1
            err = ET.SubElement(tc, "error")
            err.set("message", f"suite exited with code {exit_code} - remaining tests may not have run")

    testsuite.set("tests", str(tests_count))
    testsuite.set("failures", str(failures))
    testsuite.set("errors", str(errors))
    testsuite.set("skipped", str(skipped))
    testsuite.set("time", f"{total_time:.6f}")

    # Attach full output for any non-clean run
    if (failures > 0 or errors > 0) and combined.strip():
        sysout = ET.SubElement(testsuite, "system-out")
        sysout.text = combined[-16384:]

    return testsuites


def main():
    parser = argparse.ArgumentParser(
        description="Run a test and produce JUnit XML",
        usage="%(prog)s --junit-dir DIR [--timeout SECS] -- command [args...]",
    )
    parser.add_argument("--junit-dir", required=True, help="Directory for JUnit XML output")
    parser.add_argument("--timeout", type=int, default=300, help="Timeout in seconds (default: 300)")
    parser.add_argument("cmd", nargs=argparse.REMAINDER, help="Test command to run")
    args = parser.parse_args()

    # Strip leading '--' from cmd if present
    cmd = args.cmd
    if cmd and cmd[0] == "--":
        cmd = cmd[1:]
    if not cmd:
        parser.error("No command specified")

    os.makedirs(args.junit_dir, exist_ok=True)

    suite_name = derive_suite_name(cmd)
    stdout, stderr, exit_code, wall_time, death_signal = run_test(cmd, args.timeout)

    # Pass through output
    if stdout:
        sys.stdout.write(stdout)
        sys.stdout.flush()
    if stderr:
        sys.stderr.write(stderr)
        sys.stderr.flush()

    # Parse test result lines from combined output
    combined = stdout + "\n" + stderr
    tests = []
    for line in combined.splitlines():
        m = TEST_LINE_RE.match(line.strip())
        if m:
            name = m.group(1).rstrip(". ")
            status = m.group(2)
            elapsed = parse_time_seconds(m.group(3))
            tests.append((name, status, elapsed))

    # Build and write JUnit XML
    tree_root = build_junit(
        suite_name, tests, stdout, stderr,
        exit_code, wall_time, death_signal, args.timeout,
    )
    tree = ET.ElementTree(tree_root)
    ET.indent(tree, space="  ")

    junit_path = os.path.join(args.junit_dir, f"{suite_name}.xml")
    tree.write(junit_path, encoding="unicode", xml_declaration=True)

    sys.exit(exit_code)


if __name__ == "__main__":
    main()
