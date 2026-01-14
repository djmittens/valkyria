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

# Configure a build directory: $(call cmake_configure,build-dir,asan-flag)
define cmake_configure
	$(CMAKE_BASE) -DASAN=$(2) -S . -B $(1)
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

# Default build (no ASAN)
.ONESHELL:
.PHONY: cmake
cmake build/.cmake: CMakeLists.txt homebrew.cmake Makefile
	$(call cmake_configure,build,0)

.ONESHELL:
.PHONY: build
build: build/.cmake
	$(call do_build,build)

# ASAN build
.ONESHELL:
.PHONY: cmake-asan
cmake-asan build-asan/.cmake: CMakeLists.txt homebrew.cmake Makefile
	$(call cmake_configure,build-asan,1)

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
	rm -rf build build-asan build-coverage

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
define run_tests_c
	@echo "=== Running C tests from $(1) ==="
	@if [ -n "$$ASAN_OPTIONS" ]; then echo "ASAN_OPTIONS=$$ASAN_OPTIONS"; fi
	$(1)/test_std
	$(1)/test_memory
	$(1)/test_networking
	$(1)/test_large_response
	$(1)/test_per_stream_arena
	$(1)/test_debug
	$(1)/test_concurrency
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
	if [ -f $(1)/test_source_loc_unit ]; then $(1)/test_source_loc_unit; fi
	$(1)/test_pressure
	$(1)/test_conn_io
	@echo "=== All C tests passed ($(1)) ==="
endef

# Run Valk/Lisp test suite with a given build directory
# Usage: $(call run_tests_valk,build-dir)
# Note: Requires set -e in calling recipe for proper error handling with ASAN
define run_tests_valk
	@echo "=== Running Valk tests from $(1) ==="
	@if [ -n "$$ASAN_OPTIONS" ]; then echo "ASAN_OPTIONS=$$ASAN_OPTIONS"; fi
	$(1)/valk test/test_metrics.valk
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
	$(1)/valk test/test_read_file.valk
	$(1)/valk test/test_aio_debug.valk
	$(1)/valk test/test_test_framework.valk
	$(1)/valk test/test_test_framework_skip.valk
	$(1)/valk test/test_test_framework_fail.valk
	$(1)/valk test/test_test_framework_empty.valk
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

	$(1)/valk test/stress/test_gc_stress.valk
	$(1)/valk test/stress/test_networking_stress.valk
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
	export LSAN_OPTIONS=verbosity=0:log_threads=1
	$(call run_tests_valk,build-asan)

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
