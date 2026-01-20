UNAME := $(shell uname -s)

# Shared CMake flags
CMAKE_BASE = cmake -G Ninja -DCMAKE_BUILD_TYPE=Debug
ifeq ($(UNAME), Darwin)
	CMAKE_BASE += -DHOMEBREW_CLANG=on
endif

JOBS := $(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# Time-travel debugging support
# Linux: rr record (set RR=1 or RR=chaos)
# macOS: no rr, but we document lldb/Instruments alternatives
# Usage: RR=1 make test-c TEST=test_networking
#        RR=chaos make test-valk TEST=test/test_http_integration.valk
ifdef RR
  ifeq ($(UNAME), Darwin)
    $(error rr is Linux-only. On macOS use: lldb -- build/$(TEST) or Instruments)
  endif
  ifeq ($(RR),chaos)
    RR_PREFIX := rr record --chaos
  else
    RR_PREFIX := rr record
  endif
  export VALK_TEST_NO_FORK := 1
else
  RR_PREFIX :=
endif

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

# Run C test suite with a given build directory
# Usage: $(call run_tests_c,build-dir)
# Note: Requires set -e in calling recipe for proper error handling with ASAN
# If TEST is set, only run that test. If RR is set, prefix with rr record.
define run_tests_c
	@echo "=== Running C tests from $(1) ==="
	@if [ -n "$$ASAN_OPTIONS" ]; then echo "ASAN_OPTIONS=$$ASAN_OPTIONS"; fi
	@if [ -n "$(RR_PREFIX)" ]; then echo "Recording with rr (VALK_TEST_NO_FORK=1)"; fi
	@if [ -n "$(TEST)" ]; then \
		echo "Running single test: $(TEST)"; \
		$(RR_PREFIX) $(1)/$(TEST); \
		exit 0; \
	fi
	$(RR_PREFIX) $(1)/test_std
	$(1)/test_regression
	$(1)/test_memory
	$(1)/test_networking
	$(1)/test_large_response
	$(1)/test_per_stream_arena
	$(1)/test_debug
	$(1)/test_loop_metrics
	$(1)/test_eval_metrics
	if [ -f $(1)/test_sse_diagnostics ]; then $(1)/test_sse_diagnostics; fi
	if [ -f $(1)/test_sse ]; then $(1)/test_sse; fi
	$(1)/test_pool_metrics
	$(1)/test_metrics_delta
	$(1)/test_event_loop_metrics_unit
	$(1)/test_metrics_v2
	$(1)/test_metrics_builtins
	if [ -f $(1)/test_sse_registry_unit ]; then $(1)/test_sse_registry_unit; fi
	if [ -f $(1)/test_sse_stream_registry_unit ]; then $(1)/test_sse_stream_registry_unit; fi
	if [ -f $(1)/test_sse_builtins_unit ]; then $(1)/test_sse_builtins_unit; fi
	if [ -f $(1)/test_sse_core ]; then $(1)/test_sse_core; fi
	$(1)/test_aio_backpressure
	$(1)/test_aio_uv_coverage
	$(1)/test_aio_integration
	$(1)/test_aio_combinators
	$(1)/test_aio_load_shedding
	if [ -f $(1)/test_aio_sse_integration ]; then $(1)/test_aio_sse_integration; fi
	$(1)/test_aio_config
	$(1)/test_aio_uv_unit
	$(1)/test_aio_alloc_unit
	$(1)/test_aio_ssl_unit
	if [ -f $(1)/test_coverage_unit ]; then $(1)/test_coverage_unit; fi
	$(1)/test_gc_unit
	$(1)/test_memory_unit
	$(1)/test_log
	$(1)/test_parser_unit
	$(1)/test_parser_errors
	if [ -f $(1)/test_source_loc_unit ]; then $(1)/test_source_loc_unit; fi
	$(1)/test_pressure
	$(1)/test_conn_io
	$(1)/test_aio_timer_unit
	$(1)/test_io_timer_ops_unit
	$(1)/test_thread_posix_unit
	$(1)/test_aio_handle_diag
	$(1)/test_chase_lev_unit
	$(1)/test_task_queue_unit
	$(1)/test_request_ctx_unit
	$(1)/test_ctx_builtins_unit
	$(1)/test_http_builtins_unit
	$(1)/test_stream_body_conn_unit
	$(1)/test_backpressure_list_unit
	$(1)/test_conn_fsm_unit
	$(1)/test_stream_builtins_unit
	$(1)/test_stream_body_integration
	$(1)/test_http2_conn_unit
	$(1)/test_http2_server_unit
	$(1)/test_aio_async_unit
	$(1)/test_conn_admission_unit
	@echo "=== All C tests passed ($(1)) ==="
endef

# Run Valk/Lisp test suite with a given build directory
# Usage: $(call run_tests_valk,build-dir)
# Note: Requires set -e in calling recipe for proper error handling with ASAN
# If TEST is set, only run that test. If RR is set, prefix with rr record.
define run_tests_valk
	@echo "=== Running Valk tests from $(1) ==="
	@if [ -n "$$ASAN_OPTIONS" ]; then echo "ASAN_OPTIONS=$$ASAN_OPTIONS"; fi
	@if [ -n "$(RR_PREFIX)" ]; then echo "Recording with rr (VALK_TEST_NO_FORK=1)"; fi
	@if [ -n "$(TEST)" ]; then \
		echo "Running single test: $(TEST)"; \
		$(RR_PREFIX) $(1)/valk $(TEST); \
		exit 0; \
	fi
	$(RR_PREFIX) $(1)/valk test/test_metrics.valk
	$(1)/valk test/test_metrics_builtins_comprehensive.valk
	$(1)/valk test/test_prelude.valk
	$(1)/valk test/test_namespace.valk
	$(1)/valk test/test_varargs.valk
	$(1)/valk test/test_async_monadic_suite.valk
	$(1)/valk test/test_aio_builtins_coverage.valk
	$(1)/valk test/test_do_suite.valk
	$(1)/valk test/test_gc_suite.valk
	$(1)/valk test/test_crash_regressions.valk
	$(1)/valk test/test_http_minimal.valk
	$(1)/valk test/test_http_integration.valk
	$(1)/valk test/test_http_api_network.valk
	$(1)/valk test/test_checkpoint.valk
	$(1)/valk test/test_integration.valk
	$(1)/valk test/test_quasiquote.valk
	$(1)/valk test/test_string_builtins.valk
	$(1)/valk test/test_memory_builtins.valk
	$(1)/valk test/test_read_file.valk
	$(1)/valk test/test_aio_debug.valk
	$(1)/valk test/test_test_framework.valk
	$(1)/valk test/test_test_framework_skip.valk
	$(1)/valk test/test_test_framework_fail.valk
	$(1)/valk test/test_test_framework_empty.valk
	$(1)/valk test/test_test_framework_async_fail.valk
	$(1)/valk test/test_sse.valk
	$(1)/valk test/test_sse_builtins.valk
	$(1)/valk test/test_sse_integration.valk
	$(1)/valk test/test_sse_async_timeout.valk
	$(1)/valk test/test_sse_diagnostics_endpoint.valk
	$(1)/valk test/test_http_client_server.valk
	$(1)/valk test/test_async_http_handlers.valk
	$(1)/valk test/test_aio_config.valk
	$(1)/valk test/test_backpressure.valk
	$(1)/valk test/test_backpressure_timeout.valk
	$(1)/valk test/test_pending_streams.valk
	$(1)/valk test/test_pending_stream_headers.valk
	$(1)/valk test/test_concurrent_requests.valk
	$(1)/valk test/test_gc_async_regression.valk
	$(1)/valk test/test_arena_out_of_order.valk
	$(1)/valk test/test_client_headers.valk
	$(1)/valk test/test_http2_client_request_errors.valk
	$(1)/valk test/test_sequential_map.valk
	$(1)/valk test/test_async_handles.valk
	$(1)/valk test/test_ctx_builtins.valk
	$(1)/valk test/test_vm_metrics.valk
	$(1)/valk test/test_parser_edge_cases.valk
	$(1)/valk test/test_parser_errors.valk
	$(1)/valk test/test_parser_builtin_coverage.valk
	$(1)/valk test/test_atom_builtins.valk
	$(1)/valk test/test_error_handler_edge_cases.valk
	$(1)/valk test/test_parser_coverage_gaps.valk
	$(1)/valk test/test_parser_continuations.valk
	$(1)/valk test/test_parser_branch_coverage.valk
	$(1)/valk test/test_parser_coverage_supplement.valk
	$(1)/valk test/test_gc_and_log_builtins.valk

	$(1)/valk test/stress/test_gc_stress.valk
	$(1)/valk test/stress/test_networking_stress.valk
	$(1)/valk test/stress/test_sse_concurrency_short.valk
	@echo "=== All Valk tests passed ($(1)) ==="
endef

# Run example demos with a given build directory
# Usage: $(call run_examples,build-dir)
# Note: Requires set -e in calling recipe for proper error handling
define run_examples
	@echo "=== Running example demos from $(1) ==="
	$(1)/valk examples/gc_demo.valk
	$(1)/valk examples/checkpoint_demo.valk
	$(1)/valk examples/test_example.valk
	@echo "=== All example demos passed ($(1)) ==="
endef

# Default test target (C + Valk tests, no ASAN)
.PHONY: test
test: test-c test-valk

# C tests (no ASAN, fast)
.ONESHELL:
.PHONY: test-c
test-c: export VALK_TEST_TIMEOUT_SECONDS=5
test-c: build
	set -e
	$(call run_tests_c,build)

# Valk/Lisp tests (no ASAN)
.ONESHELL:
.PHONY: test-valk
test-valk: export VALK_TEST_TIMEOUT_SECONDS=5
test-valk: build
	set -e
	$(call run_tests_valk,build)

# C tests with ASAN enabled (catches memory errors)
.ONESHELL:
.PHONY: test-c-asan
test-c-asan: build-asan
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running C tests with AddressSanitizer (ASAN) enabled       ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	export ASAN_OPTIONS=detect_leaks=1:halt_on_error=1:abort_on_error=1
	export LSAN_OPTIONS=verbosity=0:log_threads=1
	$(call run_tests_c,build-asan)

# Valk/Lisp tests with ASAN enabled
.ONESHELL:
.PHONY: test-valk-asan
test-valk-asan: build-asan
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running Valk tests with AddressSanitizer (ASAN) enabled    ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	export ASAN_OPTIONS=detect_leaks=1:halt_on_error=1:abort_on_error=1
	export LSAN_OPTIONS=verbosity=0:log_threads=1:suppressions=$(CURDIR)/lsan_suppressions.txt
	$(call run_tests_valk,build-asan)

# C tests with TSAN enabled (catches data races)
.ONESHELL:
.PHONY: test-c-tsan
test-c-tsan: build-tsan
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running C tests with ThreadSanitizer (TSAN) enabled        ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	export TSAN_OPTIONS=halt_on_error=1:second_deadlock_stack=1
	$(call run_tests_c,build-tsan)

# Valk/Lisp tests with TSAN enabled
.ONESHELL:
.PHONY: test-valk-tsan
test-valk-tsan: build-tsan
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running Valk tests with ThreadSanitizer (TSAN) enabled     ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	export TSAN_OPTIONS=halt_on_error=1:second_deadlock_stack=1
	$(call run_tests_valk,build-tsan)

# Test example demos (gc_demo, checkpoint_demo, test_example)
.ONESHELL:
.PHONY: test-examples
test-examples: build
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running example demos as tests                             ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	$(call run_examples,build)

# Test examples with ASAN
.ONESHELL:
.PHONY: test-examples-asan
test-examples-asan: build-asan
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running example demos with ASAN                            ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	export ASAN_OPTIONS=detect_leaks=1:halt_on_error=1:abort_on_error=1
	export LSAN_OPTIONS=verbosity=0:log_threads=1
	$(call run_examples,build-asan)

# Comprehensive test suite: tests + examples, both with and without ASAN
.ONESHELL:
.PHONY: test-all
test-all:
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  COMPREHENSIVE TEST SUITE                                   ║"
	@echo "║  Running all tests with and without ASAN + examples         ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	$(MAKE) test-c
	@echo ""
	$(MAKE) test-valk
	@echo ""
	$(MAKE) test-c-asan
	@echo ""
	$(MAKE) test-valk-asan
	@echo ""
	$(MAKE) test-examples-asan
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  ALL TESTS PASSED                                           ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"

.PHONY: todo
todo:
	rg "TODO\($(shell git rev-parse --abbrev-ref HEAD)\)"

# Coverage targets
.ONESHELL:
.PHONY: coverage-reset
coverage-reset:
	@echo "=== Resetting coverage data ==="
	find build-coverage -name "*.gcda" -delete 2>/dev/null || true
	rm -rf coverage-report
	rm -f build-coverage/coverage-valk.txt build-coverage/coverage-valk.info

.ONESHELL:
.PHONY: coverage-tests
coverage-tests: build-coverage coverage-reset
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running all tests with coverage instrumentation            ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	export VALK_COVERAGE=1
	export VALK_TEST_TIMEOUT_SECONDS=30
	@echo "=== Ensuring SSL certs exist in build/ for tests ==="
	@mkdir -p build
	$(call gen_ssl_certs,build)
	$(call run_tests_c,build-coverage)
	@echo ""
	$(call run_tests_valk,build-coverage)
	@echo ""
	$(call run_examples,build-coverage)

.ONESHELL:
.PHONY: coverage-report
coverage-report:
	@echo "=== Generating unified coverage reports ==="
	python3 bin/coverage-report.py \
		--build-dir build-coverage \
		--source-root . \
		--output coverage-report \
		--xml
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════════╗"
	@echo "║  Coverage reports generated                                      ║"
	@echo "╠══════════════════════════════════════════════════════════════════╣"
	@echo "║  HTML: coverage-report/index.html                                ║"
	@echo "║  XML:  coverage-report/coverage.xml (Cobertura format)           ║"
	@echo "╚══════════════════════════════════════════════════════════════════╝"

.PHONY: coverage
coverage: export VALK_COVERAGE=1
coverage: build-coverage coverage-tests coverage-report coverage-check
	@echo "=== Coverage collection complete ==="

.PHONY: coverage-check
coverage-check:
	@echo "=== Checking runtime coverage requirements ==="
	@python3 bin/check-coverage.py --build-dir build-coverage

# Run stress tests in test/stress/ (long-running, not included in normal test suite)
# Usage: $(call run_tests_stress,build-dir)
define run_tests_stress
	@echo "=== Running stress tests from $(1) ==="
	$(1)/valk test/stress/test_sse_concurrency.valk
	$(1)/valk test/stress/test_delta_baseline_isolation.valk
	$(1)/valk test/stress/test_checkpoint_timer_stress.valk
	$(1)/valk test/stress/test_gc_stress.valk
	$(1)/valk test/stress/test_networking_stress.valk
	$(1)/valk test/stress/test_recursion_stress.valk
	$(1)/valk test/stress/test_large_download_stress.valk
	$(1)/valk test/stress/test_large_response.valk
	@echo "=== All stress tests passed ($(1)) ==="
endef

.ONESHELL:
.PHONY: test-stress
test-stress: build
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running stress tests (long-running)                         ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	$(call run_tests_stress,build)

# Stress tests with TSAN - redirects output to file per AGENTS.md
.ONESHELL:
.PHONY: test-stress-tsan
test-stress-tsan: build-tsan
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running stress tests with ThreadSanitizer (TSAN)            ║"
	@echo "║  Output: build/tsan-stress.log                               ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	export TSAN_OPTIONS="log_path=build/tsan-stress.log:halt_on_error=0:second_deadlock_stack=1"
	$(call run_tests_stress,build-tsan) 2>&1 | tee build/tsan-stress-stdout.log
	@echo ""
	@echo "=== TSAN Summary ==="
	@echo "Races found: $$(grep -c 'WARNING: ThreadSanitizer' build/tsan-stress.log* 2>/dev/null || echo 0)"
	@if [ "$$(grep -c 'WARNING: ThreadSanitizer' build/tsan-stress.log* 2>/dev/null || echo 0)" -gt 0 ]; then \
		echo "Race locations:"; \
		grep -A2 "WARNING: ThreadSanitizer" build/tsan-stress.log* 2>/dev/null | grep "#0" | sort -u | head -5; \
	fi

# Stress tests with ASAN - redirects output to file per AGENTS.md
.ONESHELL:
.PHONY: test-stress-asan
test-stress-asan: build-asan
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running stress tests with AddressSanitizer (ASAN)           ║"
	@echo "║  Output: build/asan-stress.log                               ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	export ASAN_OPTIONS="log_path=build/asan-stress.log:detect_leaks=1:halt_on_error=0:abort_on_error=0"
	export LSAN_OPTIONS="verbosity=0:log_threads=1:suppressions=$(CURDIR)/lsan_suppressions.txt"
	$(call run_tests_stress,build-asan) 2>&1 | tee build/asan-stress-stdout.log
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
#   RR=1 make test-c TEST=test_networking      # Record single test
#   RR=chaos make test-c TEST=test_networking  # Record with chaos mode
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

# Known flaky tests - run under rr to capture failures
FLAKY_C_TESTS := test_networking test_aio_integration
FLAKY_VALK_TESTS := test/test_http_integration.valk test/test_concurrent_requests.valk

# Run flaky tests under rr (Linux only)
# Uses existing RR_PREFIX mechanism, cleans up recordings on success
.ONESHELL:
.PHONY: test-flaky
test-flaky: test-rr-check build
	set -e
	export VALK_TEST_NO_FORK=1
	failed=""
	for test in $(FLAKY_C_TESTS); do \
		echo "=== $$test ==="; \
		if rr record build/$$test; then rr rm -f latest-trace 2>/dev/null || true; \
		else failed="$$failed $$test"; fi; \
	done
	for test in $(FLAKY_VALK_TESTS); do \
		echo "=== $$test ==="; \
		if rr record build/valk $$test; then rr rm -f latest-trace 2>/dev/null || true; \
		else failed="$$failed $$test"; fi; \
	done
	if [ -n "$$failed" ]; then \
		echo "FAILED (recording kept):$$failed"; \
		echo "Debug with: rr replay"; \
		exit 1; \
	fi

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

.PHONY: test-flaky
test-flaky:
	@echo "rr is Linux-only. On macOS, run flaky tests with TSAN instead:"
	@echo ""
	@echo "  make test-c-tsan"
	@echo "  make test-valk-tsan"
	@echo ""
	@exit 1
endif

# ============================================================================
# Core Dump Analysis
# ============================================================================
# Linux: systemd-coredump captures crashes, use coredumpctl to debug
# macOS: Core dumps go to /cores/, use lldb to debug

.ONESHELL:
.PHONY: test-core
test-core: build
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running tests with core dumps enabled                       ║"
ifeq ($(UNAME), Darwin)
	@echo "║  On crash: lldb -c /cores/core.<pid> build/<test>            ║"
else
	@echo "║  On crash: coredumpctl debug <test>                          ║"
endif
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	ulimit -c unlimited
	export VALK_TEST_TIMEOUT_SECONDS=30
	$(call run_tests_c,build)
	$(call run_tests_valk,build)

.ONESHELL:
.PHONY: test-asan-abort
test-asan-abort: build-asan
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running ASAN tests with abort_on_error=1                    ║"
ifeq ($(UNAME), Darwin)
	@echo "║  On failure: lldb -c /cores/core.<pid> build-asan/<test>     ║"
else
	@echo "║  On failure: coredumpctl debug <test>                        ║"
endif
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	ulimit -c unlimited
	export ASAN_OPTIONS=detect_leaks=1:halt_on_error=1:abort_on_error=1
	export LSAN_OPTIONS=verbosity=0:log_threads=1
	$(call run_tests_c,build-asan)
	$(call run_tests_valk,build-asan)

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
