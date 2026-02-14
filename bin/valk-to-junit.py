#!/usr/bin/env python3
"""Run a Valk test and produce JUnit XML from its output.

Usage:
  valk-to-junit.py <valk-binary> <test-file> <junit-output-dir>

The script runs the test, captures stdout/stderr, parses the structured
test output lines (PASS/FAIL/TIMEOUT/SKIP), and writes a JUnit XML file.
Exit code mirrors the test process exit code.
"""

import os
import re
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

# Match lines like:
#   ✅ test_name...  PASS : in 123(µs)
#   ❌ test_name...  FAIL : in 123(µs)
#   ⏰ test_name...  TIMEOUT : after 5000ms
#   ⏭️  test_name...  SKIP
TEST_LINE_RE = re.compile(
    r"^(?:✅|❌|⏰|⏭️\s?|🐞|🌀|❓)\s+"
    r"(.+?)"
    r"\.{2,}\s+"
    r"(PASS|FAIL|TIMEOUT|SKIP|CRSH|UNKNOWN)"
    r"(?:\s*:\s*(?:in|after)\s+(\S+))?"
    r"\s*$"
)


def parse_time_seconds(time_str):
    if not time_str:
        return 0.0
    # "123(µs)" or "5000ms"
    m = re.match(r"([\d.]+)\(?(µs|ms|ns|s)\)?", time_str)
    if not m:
        return 0.0
    val = float(m.group(1))
    unit = m.group(2)
    if unit == "µs":
        return val / 1_000_000
    elif unit == "ms":
        return val / 1_000
    elif unit == "ns":
        return val / 1_000_000_000
    else:
        return val


def escape_cdata(text):
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def main():
    if len(sys.argv) < 4:
        print(f"Usage: {sys.argv[0]} <valk-binary> <test-file> <junit-output-dir>",
              file=sys.stderr)
        sys.exit(2)

    valk_bin = sys.argv[1]
    test_file = sys.argv[2]
    junit_dir = sys.argv[3]

    os.makedirs(junit_dir, exist_ok=True)

    # Run the test
    result = subprocess.run(
        [valk_bin, test_file],
        capture_output=True,
        text=True,
        timeout=300,
    )

    stdout = result.stdout
    stderr = result.stderr
    combined = stdout + "\n" + stderr

    # Always print the original output
    if stdout:
        sys.stdout.write(stdout)
    if stderr:
        sys.stderr.write(stderr)

    # Parse test results
    tests = []
    for line in combined.splitlines():
        m = TEST_LINE_RE.match(line.strip())
        if m:
            name = m.group(1).rstrip(". ")
            status = m.group(2)
            time_str = m.group(3)
            tests.append((name, status, parse_time_seconds(time_str)))

    # Derive suite name from test file
    suite_name = Path(test_file).stem

    # Build JUnit XML
    testsuites = ET.Element("testsuites")
    testsuite = ET.SubElement(testsuites, "testsuite")
    testsuite.set("name", suite_name)

    failures = 0
    errors = 0
    skipped = 0
    total_time = 0.0

    if not tests:
        # No parseable test lines - treat the whole run as one test
        tc = ET.SubElement(testsuite, "testcase")
        tc.set("classname", suite_name)
        tc.set("name", suite_name)
        tc.set("time", "0.000000")
        if result.returncode != 0:
            failures = 1
            fail_el = ET.SubElement(tc, "failure")
            fail_el.set("message", f"process exited with code {result.returncode}")
            fail_el.text = escape_cdata(combined[-4096:] if len(combined) > 4096 else combined)
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
                fail_el = ET.SubElement(tc, "failure")
                fail_el.set("message", "test failed")
            elif status in ("TIMEOUT", "CRSH", "UNKNOWN"):
                errors += 1
                err_el = ET.SubElement(tc, "error")
                err_el.set("message", status.lower())

    testsuite.set("tests", str(tests_count))
    testsuite.set("failures", str(failures))
    testsuite.set("errors", str(errors))
    testsuite.set("skipped", str(skipped))
    testsuite.set("time", f"{total_time:.6f}")

    # If there were failures/errors, attach combined output to suite
    if (failures > 0 or errors > 0) and combined.strip():
        sysout = ET.SubElement(testsuite, "system-out")
        sysout.text = escape_cdata(combined[-8192:] if len(combined) > 8192 else combined)

    # Write XML
    junit_path = os.path.join(junit_dir, f"{suite_name}.xml")
    tree = ET.ElementTree(testsuites)
    ET.indent(tree, space="  ")
    tree.write(junit_path, encoding="unicode", xml_declaration=True)

    sys.exit(result.returncode)


if __name__ == "__main__":
    main()
