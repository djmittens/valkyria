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

# A CMake build dir is permanently bound to the source root it was
# configured against (CMAKE_HOME_DIRECTORY in CMakeCache.txt). If the tree
# is restructured, the dir cannot be migrated or reconfigured in place;
# ninja fails on paths that no longer exist and CMake refuses a different
# -S. Detect the mismatch and wipe so the configure path regenerates it.
define ensure_build_root
	if [ -f $(1)/CMakeCache.txt ] && \
	   ! grep -q '^CMAKE_HOME_DIRECTORY:INTERNAL=$(abspath runtime)$$' $(1)/CMakeCache.txt; then \
		echo "=== $(1): configured against a different source root; regenerating ==="; \
		rm -rf $(1); \
	fi
endef

# Configure a build directory: $(call cmake_configure,build-dir,asan-flag,tsan-flag)
define cmake_configure
	$(call ensure_build_root,$(1))
	$(CMAKE_BASE) -DASAN=$(2) -DTSAN=$(3) -S runtime -B $(1)
	$(call gen_ssl_certs,$(1))
	touch $(1)/.cmake
endef

# Build a directory with optional dsymutil on macOS: $(call do_build,build-dir)
define do_build
	$(call ensure_build_root,$(1))
	[ -f $(1)/.cmake ] || $(MAKE) $(1)/.cmake
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
cmake build/.cmake: runtime/CMakeLists.txt runtime/homebrew.cmake Makefile
	$(call cmake_configure,build,0,0)

.ONESHELL:
.PHONY: build
build: build/.cmake
	$(call do_build,build)

# ASAN build
.ONESHELL:
.PHONY: cmake-asan
cmake-asan build-asan/.cmake: runtime/CMakeLists.txt runtime/homebrew.cmake Makefile
	$(call cmake_configure,build-asan,1,0)

# TSAN build
.ONESHELL:
.PHONY: cmake-tsan
cmake-tsan build-tsan/.cmake: runtime/CMakeLists.txt runtime/homebrew.cmake Makefile
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
cmake-coverage build-coverage/.cmake: runtime/CMakeLists.txt runtime/homebrew.cmake Makefile
	$(call ensure_build_root,build-coverage)
	$(CMAKE_BASE) -DCOVERAGE=1 -DVALK_COVERAGE=1 -DASAN=0 -S runtime -B build-coverage
	$(call gen_ssl_certs,build-coverage)
	touch build-coverage/.cmake

.ONESHELL:
.PHONY: build-coverage
build-coverage: build-coverage/.cmake
	$(call do_build,build-coverage)

.PHONY: check
check: build
	build/valk check/valk-check.valk -- $(or $(DIR),.)
	build/valk check/check-no-globals.valk

# Homebrew's llvm formula is keg-only, so run-clang-tidy is installed but
# not linked into PATH — fall back to the formula's bin before giving up.
# run-clang-tidy resolves clang-tidy through PATH, so pass the sibling
# binary explicitly — otherwise the keg-only case fails one step later.
RUN_CLANG_TIDY := $(shell command -v run-clang-tidy 2>/dev/null || \
	ls "$$(brew --prefix llvm 2>/dev/null)/bin/run-clang-tidy" 2>/dev/null)
CLANG_TIDY_BIN := $(shell command -v clang-tidy 2>/dev/null || \
	ls "$$(brew --prefix llvm 2>/dev/null)/bin/clang-tidy" 2>/dev/null)

.PHONY: lint
lint : build/.cmake
	@if [ -z "$(RUN_CLANG_TIDY)" ]; then \
		echo "make lint: run-clang-tidy not found."; \
		echo "  macOS:  brew install llvm"; \
		echo "  Debian: apt install clang-tidy"; \
		exit 1; \
	fi
	$(RUN_CLANG_TIDY) -p build -j $(JOBS) \
		$(if $(CLANG_TIDY_BIN),-clang-tidy-binary=$(CLANG_TIDY_BIN),) \
		-extra-arg=-std=c23 \
		$(if $(filter Darwin,$(UNAME)),-extra-arg=-isysroot -extra-arg=$$(xcrun --show-sdk-path),) \
		-source-filter='$(CURDIR)/(runtime/src|runtime/test|testing/c|lsp/test)/.*\.c$$' \
		-header-filter='$(CURDIR)/runtime/src/.*\.h$$'

# Install editline (uses autotools)
# On macOS: brew install autoconf automake libtool
.PHONY: configure
configure:
	cd runtime/vendor/editline && \
	./autogen.sh && \
	./configure && \
	make install

.PHONY: clean
clean:
	rm -rf build build-asan build-tsan build-coverage

.PHONY: cppcheck
cppcheck:
	cppcheck --enable=all --inconclusive --quiet runtime/src/ runtime/test/

.PHONY: infer
infer:
	docker run -v "$(PWD):/mnt" -w "/mnt/build" --rm -it ghcr.io/facebook/infer:latest infer -- ninja

.PHONY: repl
repl: build
	build/valk --repl stdlib/prelude.valk


.PHONY: debug
debug: build
ifeq ($(UNAME), Darwin)
	lldb build/valk stdlib/prelude.valk
else
	gdb --args build/valk stdlib/prelude.valk
endif

.ONESHELL:
.PHONY: asan
asan: build-asan
	export ASAN_OPTIONS=detect_leaks=1:halt_on_error=1:abort_on_error=1
	export LSAN_OPTIONS=verbosity=1:log_threads=1
	build-asan/valk stdlib/prelude.valk stdlib/test/test_prelude.valk && echo "exit code = $$?"

# ============================================================================
# Unified Test Runner (testing/run-tests.valk)
# ============================================================================
# All test targets use the unified runner which auto-discovers tests, runs them
# in parallel, and produces JUnit XML. No hardcoded test lists needed.
#
#   Common options (pass via Makefile variables):
#   JUNIT=dir          JUnit output directory (default test-report/<timestamp>)
#   F=pattern          Substring filter for suite names
#   ONLY=c|valk|uat    Restrict to one suite kind
#   J=N                Parallel job count (0 = auto, currently ignored)
#   TEST=name          Shorthand for F=name (single test)

F ?=
ONLY ?=
J ?= 0
TIMEOUT ?= 120

TEST_RUN = build/valk testing/run-tests.valk --
TEST_RUN_FILTER =
ifdef F
  TEST_RUN_FILTER = --filter "$(F)"
else ifdef TEST
  TEST_RUN_FILTER = --filter "$(TEST)"
endif
TEST_RUN_ONLY =
ifneq ($(ONLY),)
  TEST_RUN_ONLY = --only $(ONLY)
endif
# JUNIT=dir pins the JUnit output directory (default: test-report/<timestamp>).
# CI sets it so every suite kind — C, Valk and UAT — reports into one
# collected directory.
TEST_RUN_JUNIT =
ifneq ($(JUNIT),)
  TEST_RUN_JUNIT = --junit-dir $(JUNIT)
endif
TEST_RUN_BASE = $(TEST_RUN_FILTER) $(TEST_RUN_ONLY) $(TEST_RUN_JUNIT)
TEST_RUN_ARGS = $(TEST_RUN_BASE)

# Default test target (all C + Valk + stress + UAT)
#
# UAT is discovered by the unified runner like any other suite, so it shares
# one filter, one JUnit tree and one summary with C and Valk — there is no
# second test system to invoke. `lsp` is a prerequisite because the UAT
# suites run against build/valk-lsp; without it they skip with a note.
# `check` is NOT prefixed with `-`. It used to be, so a parse error or a
# global-mutation violation printed "Error 2 (ignored)" and `make test` went
# on to exit 0 — the same way `-@$(MAKE) uat` let a red UAT sit in the tree.
# A gate that cannot fail the build is not a gate.
.PHONY: test
test: build lsp
	@$(MAKE) check
	$(TEST_RUN) --build-dir build $(TEST_RUN_ARGS)

# AOT-compile the LSP server to build/valk-lsp. Rebuilds when missing OR
# older than any LSP/stdlib source or the interpreter — a stale binary
# silently runs old code (this has burned hours of debugging). C changes
# reach the server through build/valk, so `build` is a prerequisite.
#
# Usage:
#   make lsp                          # rebuild if stale
#   make lsp FORCE=1                  # rebuild unconditionally
.PHONY: lsp
lsp: build
	@stale=0; \
	if [ -n "$(FORCE)" ]; then stale=1; \
	elif [ ! -x build/valk-lsp ]; then stale=1; \
	elif [ -n "$$(find lsp stdlib symdb -name '*.valk' -newer build/valk-lsp -print -quit 2>/dev/null)" ]; then stale=1; \
	elif [ build/valk -nt build/valk-lsp ]; then stale=1; \
	fi; \
	if [ "$$stale" = 1 ]; then \
		echo "[lsp] (re)building build/valk-lsp from lsp/build-main.valk"; \
		build/valk --build lsp/build-main.valk -o build/valk-lsp; \
	else \
		echo "[lsp] build/valk-lsp is up to date"; \
	fi

# Neovim-driven LSP user-acceptance tests, on their own. This is just the
# unified runner restricted to `--only uat`; `make test` already includes
# them. Each scenario file under lsp/test/uat/scenarios/ is one suite, run
# in its own nvim + valk-lsp + fixture workspace. Correctness scenarios are
# scheduled by the runner's pmap; scenarios flagged `_latency = true` are
# marked exclusive and run alone afterwards so their budgets stay meaningful.
#
# Skips with a note if nvim is not on PATH; VALK_UAT_STRICT=1 makes that
# fatal (CI use).
#
# Usage:
#   make uat                          # all scenarios
#   make uat F=hover                  # only suites whose name matches `hover`
.PHONY: uat
uat: lsp
	$(TEST_RUN) --build-dir build --only uat $(TEST_RUN_ARGS)

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
	$(TEST_RUN) --build-dir build --examples --filter "example/"

# Examples with ASAN
.PHONY: test-examples-asan
test-examples-asan: build-asan
	$(TEST_RUN) --build-dir build-asan --examples --filter "example/" \
		--sanitizer asan --lsan-suppressions $(CURDIR)/lsan_suppressions.txt

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
	rm -f build-coverage/coverage-valk.txt build-coverage/coverage-valk.info build-coverage/coverage-valk.*.info

.PHONY: coverage-tests
coverage-tests: build-coverage coverage-reset
	VALK_HEAP_HARD_LIMIT=8589934592 $(TEST_RUN) --build-dir build-coverage --examples --no-stress $(TEST_RUN_BASE)

.PHONY: coverage-report
coverage-report: build
	@echo "=== Generating unified coverage reports ==="
	VALK_HEAP_HARD_LIMIT=8589934592 build/valk coverage/coverage-report.valk -- \
		--build-dir build-coverage \
		--source-root . \
		--output coverage-report \
		--xml
	@echo ""
	@echo "Coverage reports: coverage-report/latest/index.html"

.PHONY: coverage
coverage: build-coverage coverage-tests coverage-report
	@echo "=== Coverage collection complete ==="

.PHONY: coverage-check
coverage-check: build
	@echo "=== Checking runtime coverage requirements ==="
	@build/valk coverage/check-coverage.valk -- --build-dir build-coverage

# Stress tests
.PHONY: test-stress
test-stress: build
	$(TEST_RUN) --build-dir build --stress-only $(TEST_RUN_BASE)

# Stress tests with TSAN - redirects sanitizer output to file per AGENTS.md
.ONESHELL:
.PHONY: test-stress-tsan
test-stress-tsan: build-tsan
	set -e
	export TSAN_OPTIONS="log_path=build/tsan-stress.log:halt_on_error=0:second_deadlock_stack=1"
	export VALK_TEST_NO_FORK=1
	$(TEST_RUN) --build-dir build-tsan --stress-only $(TEST_RUN_BASE) 2>&1 | tee build/tsan-stress-stdout.log
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
	$(TEST_RUN) --build-dir build-asan --stress-only $(TEST_RUN_BASE) 2>&1 | tee build/asan-stress-stdout.log
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
	@exe=$$(coredumpctl list --no-pager 2>/dev/null | grep -E "(valk|test_)" | tail -1 | awk '{print $$(NF-1)}'); \
	if [ -z "$$exe" ]; then \
		echo "No core dumps found"; \
		exit 1; \
	fi; \
	echo "Debugging most recent crash: $$exe"; \
	coredumpctl debug "$$exe"
endif

# One-shot batch crash report from the most recent core: signal, crash
# frame, full backtrace, registers, every thread. Non-interactive
# counterpart to debug-core.
.PHONY: core-report
core-report:
ifeq ($(UNAME), Darwin)
	@core=$$(ls -t /cores/core.* 2>/dev/null | head -1); \
	if [ -z "$$core" ]; then echo "No core dumps found in /cores/"; exit 1; fi; \
	echo "Core: $$core"; \
	lldb --batch -o "target create build/valk --core $$core" \
		-o "bt" -o "bt all" -o "register read" -o "quit"
else
	@exe=$$(coredumpctl list --no-pager 2>/dev/null | grep -E "(valk|test_)" | tail -1 | awk '{print $$(NF-1)}'); \
	if [ -z "$$exe" ]; then echo "No core dumps found"; exit 1; fi; \
	core=$$(mktemp); \
	coredumpctl dump "$$exe" -o "$$core" >/dev/null 2>&1; \
	echo "Executable: $$exe"; \
	gdb -batch "$$exe" "$$core" \
		-ex "echo \n=== Crash Location ===\n" -ex "frame" \
		-ex "echo \n=== Full Backtrace ===\n" -ex "bt full" \
		-ex "echo \n=== Registers ===\n" -ex "info registers" \
		-ex "echo \n=== All Threads ===\n" -ex "info threads" \
		-ex "thread apply all bt" 2>/dev/null; \
	rm -f "$$core"
endif
