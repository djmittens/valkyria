UNAME := $(shell uname -s)

# Shared CMake flags
CMAKE_BASE = cmake -G Ninja -DCMAKE_BUILD_TYPE=Debug
ifeq ($(UNAME), Darwin)
	CMAKE_BASE += -DHOMEBREW_CLANG=on
endif

JOBS := $(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# Time-travel debugging with rr (Linux only)
# - $(RR_FLAKY) prefix: always record known-flaky tests
# - RR=1 make test-c TEST=foo: record a specific test
# - RR=chaos make test-c TEST=foo: record with chaos mode
#
# macOS has no rr equivalent. Debug flaky tests on Linux.
ifeq ($(UNAME), Linux)
  RR_FLAKY := $(shell command -v rr >/dev/null 2>&1 && echo "rr record" || echo "")
  ifdef RR
    RR_PREFIX := rr record$(if $(filter chaos,$(RR)), --chaos)
    export VALK_TEST_NO_FORK := 1
  else
    RR_PREFIX :=
  endif
else
  RR_FLAKY :=
  RR_PREFIX :=
  ifdef RR
    $(error rr is Linux-only. Debug flaky tests on Linux.)
  endif
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
	$(RR_FLAKY) $(1)/test_networking
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
	$(RR_FLAKY) $(1)/test_aio_integration
	$(1)/test_aio_combinators
	$(1)/test_aio_load_shedding
	if [ -f $(1)/test_aio_sse_integration ]; then $(1)/test_aio_sse_integration; fi
	$(1)/test_aio_config
	$(1)/test_aio_uv_unit
	$(1)/test_aio_alloc_unit
	$(1)/test_aio_ssl_unit
	if [ -f $(1)/test_coverage_unit ]; then $(1)/test_coverage_unit; fi
	$(1)/test_gc_unit
	$(1)/test_gc_aio
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
	$(1)/valk test/test_aio_schedule_cancel.valk
	$(1)/valk test/test_aio_retry.valk
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
	$(1)/valk test/test_error_handler_edge_cases.valk
	$(1)/valk test/test_parser_coverage_gaps.valk
	$(1)/valk test/test_parser_continuations.valk
	$(1)/valk test/test_parser_branch_coverage.valk
	$(1)/valk test/test_parser_coverage_supplement.valk
	$(1)/valk test/test_gc_and_log_builtins.valk
	$(1)/valk test/test_large_download.valk
	$(1)/valk test/test_large_response.valk
	$(1)/valk test/test_aio_never.valk
	$(1)/valk test/test_aio_traverse.valk
	$(1)/valk test/test_interval_cancel.valk
	$(1)/valk test/test_sse_format.valk
	$(1)/valk test/test_sse_reconnect_minimal.valk
	$(1)/valk test/test_printf_closure_bug.valk
	$(1)/valk test/test_metrics_prometheus.valk
	$(1)/valk test/test_overload.valk
	$(1)/valk test/test_overload_metrics.valk
	$(1)/valk test/test_delay_error.valk
	$(1)/valk test/test_delay_continuation_error.valk
	$(1)/valk test/test_make_string.valk
	$(1)/valk test/test_coverage_integration.valk
	$(1)/valk test/test_custom_error_handler.valk
	$(1)/valk test/test_debug_handler.valk

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
# On Linux, flaky tests run under rr (requires VALK_TEST_NO_FORK=1)
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
	export LSAN_OPTIONS=verbosity=0:log_threads=1:suppressions=$(CURDIR)/lsan_suppressions.txt
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

# ============================================================================
# Parallel Test Execution (GNU Parallel)
# ============================================================================
# Runs tests in parallel for faster execution. Uses dynamic port binding so
# tests don't conflict. Requires GNU parallel to be installed.
#
# Usage:
#   make test-parallel       # Run all tests in parallel (C + Valk)
#   make test-c-parallel     # Run C tests in parallel
#   make test-valk-parallel  # Run Valk tests in parallel
#   JOBS=8 make test-parallel # Use 8 parallel jobs
#
# Note: Serial tests still available via `make test` for debugging

# Parallel job count
# C tests: can use many jobs since they're isolated
# Valk tests: use fewer jobs to avoid network/resource contention
PARALLEL_JOBS ?= $(JOBS)
PARALLEL_JOBS_VALK ?= $(shell echo $$(( ($(JOBS) + 1) / 2 )))

# C tests to run in parallel (same list as run_tests_c, minus conditionals)
C_TESTS_PARALLEL_SAFE = \
	test_std test_regression test_memory test_networking test_large_response \
	test_per_stream_arena test_debug test_loop_metrics test_eval_metrics \
	test_pool_metrics test_metrics_delta test_event_loop_metrics_unit \
	test_metrics_v2 test_metrics_builtins test_aio_backpressure \
	test_aio_uv_coverage test_aio_integration test_aio_combinators \
	test_aio_load_shedding test_aio_config test_aio_uv_unit test_aio_alloc_unit \
	test_aio_ssl_unit test_gc_aio test_memory_unit test_log \
	test_parser_unit test_parser_errors test_pressure test_conn_io \
	test_aio_timer_unit test_io_timer_ops_unit test_thread_posix_unit \
	test_aio_handle_diag test_chase_lev_unit test_gc_unit test_task_queue_unit \
	test_request_ctx_unit test_ctx_builtins_unit test_http_builtins_unit \
	test_stream_body_conn_unit test_backpressure_list_unit test_conn_fsm_unit \
	test_stream_builtins_unit test_stream_body_integration test_http2_conn_unit \
	test_http2_server_unit test_aio_async_unit test_conn_admission_unit
C_TESTS_LIST = $(C_TESTS_PARALLEL_SAFE)

# Valk tests to run in parallel (same list as run_tests_valk)
VALK_TESTS_LIST = \
	test/test_metrics.valk test/test_metrics_builtins_comprehensive.valk \
	test/test_prelude.valk test/test_namespace.valk test/test_varargs.valk \
	test/test_async_monadic_suite.valk test/test_aio_builtins_coverage.valk \
	test/test_do_suite.valk test/test_gc_suite.valk test/test_crash_regressions.valk \
	test/test_http_minimal.valk test/test_http_integration.valk \
	test/test_http_api_network.valk test/test_checkpoint.valk \
	test/test_integration.valk test/test_quasiquote.valk \
	test/test_string_builtins.valk test/test_memory_builtins.valk \
	test/test_read_file.valk test/test_aio_debug.valk test/test_test_framework.valk \
	test/test_test_framework_skip.valk test/test_test_framework_fail.valk \
	test/test_test_framework_empty.valk test/test_test_framework_async_fail.valk \
	test/test_sse.valk test/test_sse_builtins.valk test/test_sse_integration.valk \
	test/test_sse_async_timeout.valk test/test_sse_diagnostics_endpoint.valk \
	test/test_http_client_server.valk test/test_async_http_handlers.valk \
	test/test_aio_config.valk test/test_aio_schedule_cancel.valk \
	test/test_aio_retry.valk test/test_backpressure.valk \
	test/test_backpressure_timeout.valk test/test_pending_streams.valk \
	test/test_pending_stream_headers.valk test/test_concurrent_requests.valk \
	test/test_gc_async_regression.valk test/test_arena_out_of_order.valk \
	test/test_client_headers.valk test/test_http2_client_request_errors.valk \
	test/test_sequential_map.valk test/test_async_handles.valk \
	test/test_ctx_builtins.valk test/test_vm_metrics.valk \
	test/test_parser_edge_cases.valk test/test_parser_errors.valk \
	test/test_parser_builtin_coverage.valk test/test_error_handler_edge_cases.valk \
	test/test_parser_coverage_gaps.valk test/test_parser_continuations.valk \
	test/test_parser_branch_coverage.valk test/test_parser_coverage_supplement.valk \
	test/test_gc_and_log_builtins.valk test/test_large_download.valk \
	test/test_large_response.valk test/test_aio_never.valk \
	test/test_aio_traverse.valk test/test_interval_cancel.valk \
	test/test_sse_format.valk test/test_sse_reconnect_minimal.valk \
	test/test_printf_closure_bug.valk test/test_metrics_prometheus.valk \
	test/test_overload.valk test/test_overload_metrics.valk \
	test/test_delay_error.valk test/test_delay_continuation_error.valk \
	test/test_make_string.valk test/test_coverage_integration.valk \
	test/test_custom_error_handler.valk test/test_debug_handler.valk \
	test/stress/test_gc_stress.valk test/stress/test_networking_stress.valk \
	test/stress/test_sse_concurrency_short.valk

.PHONY: test-parallel
test-parallel: test-c-parallel test-valk-parallel

.ONESHELL:
.PHONY: test-c-parallel
test-c-parallel: export VALK_TEST_TIMEOUT_SECONDS=5
test-c-parallel: build
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running C tests in PARALLEL ($(PARALLEL_JOBS) jobs)                       ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	@if ! command -v parallel >/dev/null 2>&1; then \
		echo "ERROR: GNU parallel not installed. Install with: apt install parallel"; \
		exit 1; \
	fi
	@echo "Running parallel-safe tests (fork enabled)..."
	@echo "$(C_TESTS_PARALLEL_SAFE)" | tr ' ' '\n' | sed 's|^|build/|' | \
		parallel --jobs $(PARALLEL_JOBS) --halt now,fail=1 '{} >/dev/null 2>&1 && echo "PASS: {/}" || { echo "FAIL: {/}"; exit 1; }'
	@echo "=== All C tests passed (parallel) ==="

# Verbose parallel C tests (shows full output on failure)
.ONESHELL:
.PHONY: test-c-parallel-verbose
test-c-parallel-verbose: export VALK_TEST_TIMEOUT_SECONDS=30
test-c-parallel-verbose: build
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running C tests in PARALLEL (verbose, $(PARALLEL_JOBS) jobs)              ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	@if ! command -v parallel >/dev/null 2>&1; then \
		echo "ERROR: GNU parallel not installed. Install with: apt install parallel"; \
		exit 1; \
	fi
	@echo "$(C_TESTS_LIST)" | tr ' ' '\n' | sed 's|^|build/|' | \
		parallel --jobs $(PARALLEL_JOBS) --halt now,fail=1 --tag --line-buffer {}
	@echo "=== All C tests passed (parallel) ==="

.ONESHELL:
.PHONY: test-valk-parallel
test-valk-parallel: export VALK_TEST_TIMEOUT_SECONDS=5
test-valk-parallel: build
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running Valk tests in PARALLEL ($(PARALLEL_JOBS_VALK) jobs)                     ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	@if ! command -v parallel >/dev/null 2>&1; then \
		echo "ERROR: GNU parallel not installed. Install with: apt install parallel"; \
		exit 1; \
	fi
	@echo "$(VALK_TESTS_LIST)" | tr ' ' '\n' | \
		parallel --jobs $(PARALLEL_JOBS_VALK) --halt now,fail=1 'build/valk {} >/dev/null 2>&1 && echo "PASS: {/}" || { echo "FAIL: {/}"; exit 1; }'
	@echo "=== All Valk tests passed (parallel) ==="

# Verbose parallel Valk tests (shows full output on failure)
.ONESHELL:
.PHONY: test-valk-parallel-verbose
test-valk-parallel-verbose: export VALK_TEST_TIMEOUT_SECONDS=30
test-valk-parallel-verbose: build
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running Valk tests in PARALLEL (verbose, $(PARALLEL_JOBS_VALK) jobs)            ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	@if ! command -v parallel >/dev/null 2>&1; then \
		echo "ERROR: GNU parallel not installed. Install with: apt install parallel"; \
		exit 1; \
	fi
	@echo "$(VALK_TESTS_LIST)" | tr ' ' '\n' | \
		parallel --jobs $(PARALLEL_JOBS_VALK) --halt now,fail=1 --tag --line-buffer 'build/valk {}'
	@echo "=== All Valk tests passed (parallel) ==="

# Profile tests to find slowest ones
# Outputs a timing report sorted by duration
.ONESHELL:
.PHONY: test-profile
test-profile: export VALK_TEST_TIMEOUT_SECONDS=30
test-profile: build
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Profiling all tests                                         ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	@if ! command -v parallel >/dev/null 2>&1; then \
		echo "ERROR: GNU parallel not installed. Install with: apt install parallel"; \
		exit 1; \
	fi
	@mkdir -p build/test-profile
	@rm -f build/test-profile/times.txt
	@echo "Running C tests..."
	@echo "$(C_TESTS_LIST)" | tr ' ' '\n' | sed 's|^|build/|' | \
		parallel --jobs $(PARALLEL_JOBS) \
		'start=$$(date +%s%N); {} >/dev/null 2>&1; end=$$(date +%s%N); echo "$$((end - start)) {}"' \
		>> build/test-profile/times.txt
	@echo "Running Valk tests..."
	@echo "$(VALK_TESTS_LIST)" | tr ' ' '\n' | \
		parallel --jobs $(PARALLEL_JOBS_VALK) \
		'start=$$(date +%s%N); build/valk {} >/dev/null 2>&1; end=$$(date +%s%N); echo "$$((end - start)) build/valk {}"' \
		>> build/test-profile/times.txt
	@echo ""
	@echo "=== Test Profile Results ==="
	@echo ""
	@echo "Slowest 20 tests:"
	@sort -rn build/test-profile/times.txt | head -20 | \
		awk '{ns=$$1; $$1=""; ms=ns/1000000; printf "  %7.0fms %s\n", ms, $$0}'
	@echo ""
	@total=$$(awk '{sum+=$$1} END {printf "%.1f", sum/1000000000}' build/test-profile/times.txt); \
	count=$$(wc -l < build/test-profile/times.txt); \
	echo "Total: $$count tests, $${total}s combined execution time"

# C tests with TSAN enabled (catches data races)
.ONESHELL:
.PHONY: test-c-tsan
test-c-tsan: build-tsan
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running C tests with ThreadSanitizer (TSAN) enabled         ║"
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
	@echo "║  Running Valk tests with ThreadSanitizer (TSAN) enabled      ║"
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
	@echo "║  Running example demos as tests                              ║"
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
	@echo "║  Running example demos with ASAN                             ║"
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
	@echo "║  COMPREHENSIVE TEST SUITE                                    ║"
	@echo "║  Running all tests with and without ASAN + examples          ║"
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
.ONESHELL:
.PHONY: coverage-tests
coverage-tests: export VALK_TEST_TIMEOUT_SECONDS=30
coverage-tests: build-coverage coverage-reset
	set -e
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Running all tests with coverage instrumentation            ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
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
