UNAME := $(shell uname -s)

# Shared CMake flags
CMAKE_BASE = cmake -G Ninja -DCMAKE_BUILD_TYPE=Debug
ifeq ($(UNAME), Darwin)
	CMAKE_BASE += -DHOMEBREW_CLANG=on
endif

JOBS := $(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# SSL Certificate Generation
# Uses mkcert if available (browser-trusted), falls back to openssl (untrusted)
# Install mkcert: https://github.com/FiloSottile/mkcert
#   brew install mkcert    (macOS)
#   apt install mkcert     (Debian/Ubuntu)
# Then run once: mkcert -install
define gen_ssl_certs
	@if command -v mkcert >/dev/null 2>&1; then \
		mkcert -cert-file $(1)/server.crt -key-file $(1)/server.key localhost 127.0.0.1 ::1 2>/dev/null; \
	else \
		echo "Warning: mkcert not found, generating untrusted self-signed cert"; \
		openssl req -x509 -newkey rsa:2048 -nodes \
			-keyout $(1)/server.key \
			-out $(1)/server.crt \
			-sha256 \
			-days 365 \
			-subj "/C=US/ST=SomeState/L=SomeCity/O=MyOrg/CN=localhost" 2>/dev/null; \
	fi
endef

# Configure a build directory: $(call cmake_configure,build-dir,asan-flag,tsan-flag)
define cmake_configure
	$(CMAKE_BASE) -DASAN=$(2) -DTSAN=$(3) -S . -B $(1)
	$(call gen_ssl_certs,$(1))
	touch $(1)/.cmake
endef

# Build a directory with optional dsymutil on macOS: $(call do_build,build-dir)
define do_build
	touch $(1)/.cmake
	cmake --build $(1)
	if [ "$(UNAME)" = "Darwin" ]; then \
		find $(1)/ -maxdepth 1 -type f -perm -111 -newer $(1)/.cmake -exec \
			dsymutil {} \; -print; \
	fi
endef

# Default build (no sanitizers)
.ONESHELL:
.PHONY: cmake
cmake build/.cmake: CMakeLists.txt homebrew.cmake Makefile
	$(call cmake_configure,build,0,0)

.ONESHELL:
.PHONY: build
build: build/.cmake
	$(call do_build,build)

# ASAN build
.ONESHELL:
.PHONY: cmake-asan
cmake-asan build-asan/.cmake: CMakeLists.txt homebrew.cmake Makefile
	$(call cmake_configure,build-asan,1,0)

# TSAN build
.ONESHELL:
.PHONY: cmake-tsan
cmake-tsan build-tsan/.cmake: CMakeLists.txt homebrew.cmake Makefile
	$(call cmake_configure,build-tsan,0,1)

.ONESHELL:
.PHONY: build-tsan
build-tsan: build-tsan/.cmake
	$(call do_build,build-tsan)

.ONESHELL:
.PHONY: build-asan
build-asan: build-asan/.cmake
	$(call do_build,build-asan)

# Coverage build
.ONESHELL:
.PHONY: cmake-coverage
cmake-coverage build-coverage/.cmake: CMakeLists.txt homebrew.cmake Makefile
	$(CMAKE_BASE) -DCOVERAGE=1 -DVALK_COVERAGE=1 -DASAN=0 -S . -B build-coverage
	$(call gen_ssl_certs,build-coverage)
	touch build-coverage/.cmake

.ONESHELL:
.PHONY: build-coverage
build-coverage: build-coverage/.cmake
	$(call do_build,build-coverage)

.PHONY: lint
lint : build/.cmake
	run-clang-tidy -p build -j $(JOBS) \
		-extra-arg=-std=c23 \
		-extra-arg=-isysroot -extra-arg=$$(xcrun --show-sdk-path) \
		-source-filter='.*/valkyria-lisp/src/.*\.c$$|.*/valkyria-lisp/test/.*\.c$$' \
		-header-filter='.*/valkyria-lisp/src/.*\.h$$'

# Install editline (uses autotools)
# On macOS: brew install autoconf automake libtool
.PHONY: configure
configure:
	cd vendor/editline && \
	./autogen.sh && \
	./configure && \
	make install

.PHONY: clean
clean:
	rm -rf build build-asan build-tsan build-coverage

.PHONY: cppcheck
cppcheck:
	cppcheck --enable=all --inconclusive --quiet src/ test/

.PHONY: infer
infer:
	docker run -v "$(PWD):/mnt" -w "/mnt/build" --rm -it ghcr.io/facebook/infer:latest infer -- ninja

.PHONY: repl
repl: build
	build/valk --repl src/prelude.valk


.PHONY: debug
debug: build
ifeq ($(UNAME), Darwin)
	lldb build/valk src/prelude.valk
else
	gdb --args build/valk src/prelude.valk
endif

.ONESHELL:
.PHONY: asan
asan: build-asan
	export ASAN_OPTIONS=detect_leaks=1:halt_on_error=1:abort_on_error=1
	export LSAN_OPTIONS=verbosity=1:log_threads=1
	build-asan/valk src/prelude.valk test/test_prelude.valk && echo "exit code = $$?"

# ============================================================================
# Unified Test Runner (bin/run-tests.py)
# ============================================================================
# All test targets use the unified runner which auto-discovers tests, runs them
# in parallel, and produces JUnit XML. No hardcoded test lists needed.
#
# Common options (pass via Makefile variables):
#   F=pattern          Regex filter for suite names
#   ONLY=c|valk        Only C or Valk tests
#   J=N                Parallel job count (0 = auto)
#   TEST=name          Shorthand for F=^name$$ (single test)

F ?=
ONLY ?=
J ?= 0
TIMEOUT ?= 120

TEST_RUN = python3 bin/run-tests.py
TEST_RUN_FILTER =
ifdef F
  TEST_RUN_FILTER = --filter "$(F)"
else ifdef TEST
  TEST_RUN_FILTER = --filter "^$(TEST)$$"
endif
TEST_RUN_ONLY =
ifneq ($(ONLY),)
  TEST_RUN_ONLY = --only $(ONLY)
endif
TEST_RUN_BASE = --jobs $(J) $(TEST_RUN_FILTER) $(TEST_RUN_ONLY)
TEST_RUN_ARGS = --timeout $(TIMEOUT) $(TEST_RUN_BASE)

# Default test target (all C + Valk + stress)
.PHONY: test
test: build
	$(TEST_RUN) --build-dir build $(TEST_RUN_ARGS)

# C tests only
.PHONY: test-c
test-c: build
	$(TEST_RUN) --build-dir build --only c $(TEST_RUN_ARGS)

# Valk tests only
.PHONY: test-valk
test-valk: build
	$(TEST_RUN) --build-dir build --only valk $(TEST_RUN_ARGS)

# C tests with ASAN
.PHONY: test-c-asan
test-c-asan: build-asan
	$(TEST_RUN) --build-dir build-asan --only c --no-stress \
		--sanitizer asan --lsan-suppressions $(CURDIR)/lsan_suppressions.txt \
		$(TEST_RUN_ARGS)

# Valk tests with ASAN
.PHONY: test-valk-asan
test-valk-asan: build-asan
	$(TEST_RUN) --build-dir build-asan --only valk --no-stress \
		--sanitizer asan --lsan-suppressions $(CURDIR)/lsan_suppressions.txt \
		$(TEST_RUN_ARGS)

# C tests with TSAN
.PHONY: test-c-tsan
test-c-tsan: build-tsan
	$(TEST_RUN) --build-dir build-tsan --only c --no-stress \
		--sanitizer tsan $(TEST_RUN_ARGS)

# Valk tests with TSAN
.PHONY: test-valk-tsan
test-valk-tsan: build-tsan
	$(TEST_RUN) --build-dir build-tsan --only valk --no-stress \
		--sanitizer tsan $(TEST_RUN_ARGS)

# Example demos as tests
.PHONY: test-examples
test-examples: build
	$(TEST_RUN) --build-dir build --examples --filter "^example/" --timeout $(TIMEOUT) --jobs $(J)

# Examples with ASAN
.PHONY: test-examples-asan
test-examples-asan: build-asan
	$(TEST_RUN) --build-dir build-asan --examples --filter "^example/" \
		--sanitizer asan --lsan-suppressions $(CURDIR)/lsan_suppressions.txt \
		--timeout $(TIMEOUT) --jobs $(J)

# Comprehensive: all tests + ASAN + examples
.PHONY: test-all
test-all: build build-asan
	$(TEST_RUN) --build-dir build --examples $(TEST_RUN_ARGS)
	$(TEST_RUN) --build-dir build-asan --examples \
		--sanitizer asan --lsan-suppressions $(CURDIR)/lsan_suppressions.txt \
		$(TEST_RUN_ARGS)

# ============================================================================
# TLA+ Model Checking
# ============================================================================
# Runs all TLA+ formal models and reports pass/fail.
# Requires Java 21: /usr/lib/jvm/java-21-openjdk/bin/java
TLA_JAVA := /usr/lib/jvm/java-21-openjdk/bin/java
TLA_JAR  := tools/tla2tools.jar
TLA_CMD  := $(TLA_JAVA) -XX:+UseParallelGC -Xmx16g -cp $(TLA_JAR) tlc2.TLC -workers auto -nowarning

TLA_SPECS := \
	tla/ValkGC:tla/ValkGC.cfg \
	tla/ValkScheduler:tla/ValkScheduler.cfg \
	tla/ValkScheduler:tla/ValkSchedulerMulti.cfg \
	tla/ValkAsyncCrossPool:tla/ValkAsyncCrossPool.cfg \
	tla/ValkAsyncCrossPoolAll:tla/ValkAsyncCrossPoolAll.cfg \
	tla/ValkAsyncMultiLevel:tla/ValkAsyncMultiLevel.cfg \
	tla/ValkGCAsync:tla/ValkGCAsync.cfg \
	tla/ValkSchedAsync:tla/ValkSchedAsync.cfg \
	tla/ValkSchedAsyncDispatch:tla/ValkSchedAsyncDispatch.cfg \
	tla/AsyncHandleAll:tla/AsyncHandleAll.cfg \
	tla/AsyncHandleRace:tla/AsyncHandleRace.cfg \
	tla/AsyncHandleWithin:tla/AsyncHandleWithin.cfg \
	tla/AsyncHandleCancelTree:tla/AsyncHandleCancelTree.cfg \
	tla/AsyncTimerLifecycle:tla/AsyncTimerLifecycle.cfg

.ONESHELL:
.PHONY: tla
tla:
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running TLA+ model checker on all formal models             ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	@pass=0; fail=0; \
	for spec in $(TLA_SPECS); do \
		mod=$${spec%%:*}; cfg=$${spec#*:}; \
		printf "  %-50s " "$$cfg:"; \
		result=$$($(TLA_CMD) "$$mod" -config "$$cfg" 2>&1); \
		if echo "$$result" | grep -q "No error has been found"; then \
			states=$$(echo "$$result" | grep "distinct states found" | grep -oP '\d+ distinct' | head -1); \
			echo "PASS ($$states)"; \
			pass=$$((pass + 1)); \
		else \
			echo "FAIL"; \
			echo "$$result" | grep -A2 "Error:" | head -6; \
			fail=$$((fail + 1)); \
		fi; \
	done; \
	echo ""; \
	echo "=== $$pass passed, $$fail failed ==="; \
	if [ $$fail -gt 0 ]; then exit 1; fi

.PHONY: todo
todo:
	rg "TODO\($(shell git rev-parse --abbrev-ref HEAD)\)"

# Coverage targets
.PHONY: coverage-reset
coverage-reset:
	@echo "=== Resetting coverage data ==="
	find build-coverage -name "*.gcda" -delete 2>/dev/null || true
	rm -rf coverage-report
	rm -f build-coverage/coverage-valk.txt build-coverage/coverage-valk.info build-coverage/coverage-valk.*.info

.PHONY: coverage-tests
coverage-tests: build-coverage coverage-reset
	$(TEST_RUN) --build-dir build-coverage --timeout 60 --examples $(TEST_RUN_BASE)

.PHONY: coverage-report
coverage-report:
	@echo "=== Generating unified coverage reports ==="
	python3 bin/coverage-report.py \
		--build-dir build-coverage \
		--source-root . \
		--output coverage-report \
		--xml
	@echo ""
	@echo "Coverage reports: coverage-report/index.html, coverage-report/coverage.xml"

.PHONY: coverage
coverage: build-coverage coverage-tests coverage-report coverage-check
	@echo "=== Coverage collection complete ==="

.PHONY: coverage-check
coverage-check:
	@echo "=== Checking runtime coverage requirements ==="
	@python3 bin/check-coverage.py --build-dir build-coverage

# Stress tests
.PHONY: test-stress
test-stress: build
	$(TEST_RUN) --build-dir build --stress-only --timeout 300 $(TEST_RUN_BASE)

# Stress tests with TSAN - redirects sanitizer output to file per AGENTS.md
.ONESHELL:
.PHONY: test-stress-tsan
test-stress-tsan: build-tsan
	set -e
	export TSAN_OPTIONS="log_path=build/tsan-stress.log:halt_on_error=0:second_deadlock_stack=1"
	export VALK_TEST_NO_FORK=1
	$(TEST_RUN) --build-dir build-tsan --stress-only --timeout 300 $(TEST_RUN_BASE) 2>&1 | tee build/tsan-stress-stdout.log
	@echo ""
	@echo "=== TSAN Summary ==="
	@echo "Races found: $$(grep -c 'WARNING: ThreadSanitizer' build/tsan-stress.log* 2>/dev/null || echo 0)"
	@if [ "$$(grep -c 'WARNING: ThreadSanitizer' build/tsan-stress.log* 2>/dev/null || echo 0)" -gt 0 ]; then \
		echo "Race locations:"; \
		grep -A2 "WARNING: ThreadSanitizer" build/tsan-stress.log* 2>/dev/null | grep "#0" | sort -u | head -5; \
	fi

# Stress tests with ASAN - redirects sanitizer output to file per AGENTS.md
.ONESHELL:
.PHONY: test-stress-asan
test-stress-asan: build-asan
	set -e
	export ASAN_OPTIONS="log_path=build/asan-stress.log:detect_leaks=1:halt_on_error=0:abort_on_error=0"
	export LSAN_OPTIONS="verbosity=0:log_threads=1:suppressions=$(CURDIR)/lsan_suppressions.txt"
	$(TEST_RUN) --build-dir build-asan --stress-only --timeout 300 $(TEST_RUN_BASE) 2>&1 | tee build/asan-stress-stdout.log
	@echo ""
	@echo "=== ASAN Summary ==="
	@echo "Errors found: $$(grep -c 'ERROR: AddressSanitizer' build/asan-stress.log* 2>/dev/null || echo 0)"
	@if [ "$$(grep -c 'ERROR: AddressSanitizer' build/asan-stress.log* 2>/dev/null || echo 0)" -gt 0 ]; then \
		echo "Error types:"; \
		grep "ERROR: AddressSanitizer" build/asan-stress.log* 2>/dev/null | sort -u | head -5; \
	fi

# ============================================================================
# Time-Travel Debugging (Linux: rr, macOS: Instruments)
# ============================================================================
# Linux: rr records execution deterministically, replay with rr replay
# macOS: No rr, use Instruments Time Profiler or lldb reversible debugging
#
# Quick usage:
#   make test-rr-until-fail TEST=test_networking MAX=100

ifeq ($(UNAME), Linux)
.PHONY: test-rr-check
test-rr-check:
	@if ! command -v rr >/dev/null 2>&1; then \
		echo "ERROR: rr not installed. Install with: apt install rr"; \
		exit 1; \
	fi
	@if [ "$$(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo 99)" -gt 1 ]; then \
		echo "ERROR: perf_event_paranoid too restrictive for rr"; \
		echo "Fix with: echo 1 | sudo tee /proc/sys/kernel/perf_event_paranoid"; \
		exit 1; \
	fi
	@echo "rr is ready"

.ONESHELL:
.PHONY: test-rr-until-fail
test-rr-until-fail: test-rr-check build
	@if [ -z "$(TEST)" ]; then \
		echo "Usage: make test-rr-until-fail TEST=test_networking [MAX=100]"; \
		exit 1; \
	fi
	set -e
	max=$${MAX:-100}
	echo "Running $(TEST) under rr until failure (max $$max iterations)..."
	export VALK_TEST_NO_FORK=1
	for i in $$(seq 1 $$max); do \
		echo "[$$i/$$max] Recording..."; \
		if ! rr record --chaos build/$(TEST) 2>&1; then \
			echo ""; \
			echo "╔══════════════════════════════════════════════════════════════╗"; \
			echo "║  FAILURE on iteration $$i - recording saved!                 ║"; \
			echo "╚══════════════════════════════════════════════════════════════╝"; \
			echo ""; \
			echo "Replay with: rr replay"; \
			exit 0; \
		fi; \
		rr rm -f latest-trace 2>/dev/null || true; \
	done
	echo "No failure in $$max iterations (all recordings cleaned up)"

else
# macOS stubs - explain alternatives
.PHONY: test-rr-check
test-rr-check:
	@echo "rr is Linux-only. On macOS, use these alternatives:"
	@echo ""
	@echo "  For crashes:     lldb -- build/\$$(TEST)"
	@echo "  For profiling:   xcrun xctrace record --template 'Time Profiler' --launch -- build/\$$(TEST)"
	@echo "  For race detection: make test-c-tsan TEST=\$$(TEST)"
	@echo ""
	@exit 1

.PHONY: test-rr-until-fail
test-rr-until-fail:
	@echo "rr is Linux-only. On macOS, run tests in a loop with lldb:"
	@echo ""
	@echo "  for i in {1..100}; do build/\$$(TEST) || { echo \"Failed on \$$i\"; break; }; done"
	@echo ""
	@echo "Then debug the failure with: lldb -- build/\$$(TEST)"
	@exit 1
endif

# ============================================================================
# Core Dump Analysis
# ============================================================================
# Linux: systemd-coredump captures crashes, use coredumpctl to debug
# macOS: Core dumps go to /cores/, use lldb to debug

.PHONY: test-core
test-core: build
	ulimit -c unlimited && $(TEST_RUN) --build-dir build $(TEST_RUN_ARGS)

.PHONY: test-asan-abort
test-asan-abort: build-asan
	ulimit -c unlimited && $(TEST_RUN) --build-dir build-asan \
		--sanitizer asan --lsan-suppressions $(CURDIR)/lsan_suppressions.txt \
		$(TEST_RUN_ARGS)

.PHONY: cores
cores:
ifeq ($(UNAME), Darwin)
	@echo "Recent core dumps in /cores/:"
	@ls -lt /cores/ 2>/dev/null | head -20 || echo "No core dumps (or /cores/ not accessible)"
	@echo ""
	@echo "Debug with: lldb -c /cores/core.<pid> build/<binary>"
else
	@echo "Recent core dumps:"
	@coredumpctl list --no-pager 2>/dev/null | grep -E "(valk|test_)" | tail -20 || \
		echo "No core dumps found (or coredumpctl not available)"
endif

.PHONY: debug-core
debug-core:
ifeq ($(UNAME), Darwin)
	@core=$$(ls -t /cores/core.* 2>/dev/null | head -1); \
	if [ -z "$$core" ]; then \
		echo "No core dumps found in /cores/"; \
		echo "Enable with: sudo sysctl kern.coredump=1"; \
		exit 1; \
	fi; \
	echo "Most recent core: $$core"; \
	echo "Usage: lldb -c $$core build/<binary-that-crashed>"
else
	@exe=$$(coredumpctl list --no-pager 2>/dev/null | grep -E "(valk|test_)" | tail -1 | awk '{print $$NF}'); \
	if [ -z "$$exe" ]; then \
		echo "No core dumps found"; \
		exit 1; \
	fi; \
	echo "Debugging most recent crash: $$exe"; \
	coredumpctl debug "$$exe"
endif
