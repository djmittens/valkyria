UNAME := $(shell uname -s)

# Feature flags
VALK_METRICS ?= 1

# Shared CMake flags
CMAKE_BASE = cmake -G Ninja -DCMAKE_BUILD_TYPE=Debug -DVALK_METRICS=$(VALK_METRICS)
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
	$(CMAKE_BASE) -DCOVERAGE=1 -DASAN=0 -S . -B build-coverage
	$(call gen_ssl_certs,build-coverage)
	touch build-coverage/.cmake

.ONESHELL:
.PHONY: build-coverage
build-coverage: build-coverage/.cmake
	$(call do_build,build-coverage)

.PHONY: lint
lint : build/.cmake 
	run-clang-tidy -p build -j $(JOBS) -extra-arg=-std=c23

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
	if [ "$(VALK_METRICS)" = "1" ] && [ -f $(1)/test_aio_metrics ]; then $(1)/test_aio_metrics; fi
	if [ "$(VALK_METRICS)" = "1" ] && [ -f $(1)/test_loop_metrics ]; then $(1)/test_loop_metrics; fi
	if [ "$(VALK_METRICS)" = "1" ] && [ -f $(1)/test_eval_metrics ]; then $(1)/test_eval_metrics; fi
	if [ "$(VALK_METRICS)" = "1" ] && [ -f $(1)/test_sse_diagnostics ]; then $(1)/test_sse_diagnostics; fi
	if [ "$(VALK_METRICS)" = "1" ] && [ -f $(1)/test_sse ]; then $(1)/test_sse; fi
	@echo "=== All C tests passed ($(1)) ==="
endef

# Run Valk/Lisp test suite with a given build directory
# Usage: $(call run_tests_valk,build-dir)
# Note: Requires set -e in calling recipe for proper error handling with ASAN
define run_tests_valk
	@echo "=== Running Valk tests from $(1) ==="
	@if [ -n "$$ASAN_OPTIONS" ]; then echo "ASAN_OPTIONS=$$ASAN_OPTIONS"; fi
	if [ "$(VALK_METRICS)" = "1" ]; then $(1)/valk test/test_metrics.valk; fi
	$(1)/valk test/test_prelude.valk
	$(1)/valk test/test_namespace.valk
	$(1)/valk test/test_varargs.valk
	$(1)/valk test/test_continuations_suite.valk
	$(1)/valk test/test_tco_suite.valk
	$(1)/valk test/test_do_suite.valk
	$(1)/valk test/test_gc_suite.valk
	$(1)/valk test/test_crash_regressions.valk
	$(1)/valk test/test_http_minimal.valk
	$(1)/valk test/test_checkpoint.valk
	$(1)/valk test/test_integration.valk
	$(1)/valk test/test_quasiquote.valk
	$(1)/valk test/test_read_file.valk
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
test-c: build
	set -e
	$(call run_tests_c,build)

# Valk/Lisp tests (no ASAN)
.ONESHELL:
.PHONY: test-valk
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

.PHONY: build-metrics
build-metrics:
	$(MAKE) build VALK_METRICS=1

.PHONY: test-metrics
test-metrics:
	$(MAKE) test VALK_METRICS=1

# Coverage targets
.ONESHELL:
.PHONY: coverage-reset
coverage-reset:
	@echo "=== Resetting coverage data ==="
	find build-coverage -name "*.gcda" -delete 2>/dev/null || true
	rm -rf build-coverage/coverage-report
	rm -f build-coverage/coverage-c.info build-coverage/coverage-c-filtered.info build-coverage/coverage-c.txt build-coverage/coverage-valk.txt build-coverage/coverage-valk-summary.txt

.ONESHELL:
.PHONY: coverage-c
coverage-c: build-coverage coverage-reset
	set -e
	@echo "=== Running tests with C coverage ==="
	$(call run_tests_c,build-coverage)
	@echo "=== Generating C coverage report ==="
	@cd build-coverage && \
		for f in CMakeFiles/valkyria.dir/src/*.gcda; do \
			if [ -f "$$f" ]; then \
				gcov -o CMakeFiles/valkyria.dir/src/ ../src/$$(basename $$f .gcda).c 2>&1 | grep -E "^File|^Lines" || true; \
			fi; \
		done > coverage-c.txt
	@if command -v lcov >/dev/null 2>&1; then \
		lcov --capture --directory build-coverage --output-file build-coverage/coverage-c.info --rc branch_coverage=1 --ignore-errors mismatch,source,inconsistent || true; \
		if [ -f build-coverage/coverage-c.info ]; then \
			lcov --remove build-coverage/coverage-c.info '/usr/*' '*/vendor/*' '*/test/*' --output-file build-coverage/coverage-c-filtered.info --rc branch_coverage=1 --ignore-errors inconsistent || true; \
		fi; \
	fi

.ONESHELL:
.PHONY: coverage-valk
coverage-valk: build-coverage
	set -e
	@echo "=== Running tests with Valk coverage ==="
	$(call run_tests_valk,build-coverage)
	@if [ -f build-coverage/coverage-valk.txt ]; then \
		echo "=== Valk coverage data saved to build-coverage/coverage-valk.txt ==="; \
	else \
		echo "=== Warning: build-coverage/coverage-valk.txt not generated ==="; \
	fi

.ONESHELL:
.PHONY: coverage-report
coverage-report:
	@echo "=== Generating coverage reports ==="
	mkdir -p build-coverage/coverage-report
	@if [ -f build-coverage/coverage-c.txt ]; then \
		echo "C coverage (text): build-coverage/coverage-c.txt"; \
	fi
	@if command -v genhtml >/dev/null 2>&1 && [ -f build-coverage/coverage-c-filtered.info ]; then \
		genhtml build-coverage/coverage-c-filtered.info \
			--output-directory build-coverage/coverage-report/c \
			--branch-coverage \
			--title "Valkyria C Coverage" \
			--legend \
			--show-details \
			--demangle-cpp \
			--num-spaces 2 \
			--ignore-errors inconsistent,corrupt,source 2>/dev/null || true; \
		if [ -d build-coverage/coverage-report/c ]; then \
			echo "C coverage (HTML): build-coverage/coverage-report/c/index.html"; \
		fi; \
	fi
	@if [ -f build-coverage/coverage-valk.txt ]; then \
		awk -F: '{files[$$1] += $$2; total += $$2} END {print "Valkyria/Valk Coverage Report"; print "==============================\n"; print "Files executed and expression evaluation counts:\n"; for (f in files) print "  " f ": " files[f] " evaluations"; print "\n=============================="; print "TOTAL: " length(files) " files executed, " total " evaluations"}' build-coverage/coverage-valk.txt > build-coverage/coverage-valk-summary.txt; \
		echo "Valk coverage: build-coverage/coverage-valk-summary.txt"; \
	fi
	@bash -c 'set -e; \
		echo "<!DOCTYPE html><html lang=\"en\"><head><meta charset=\"UTF-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\"><title>Valkyria Coverage Report</title><style>body{font-family:-apple-system,BlinkMacSystemFont,\"Segoe UI\",Roboto,Oxygen,Ubuntu,Cantarell,sans-serif;max-width:1200px;margin:40px auto;padding:0 20px;background:#f5f5f5}h1{color:#333;border-bottom:3px solid #4CAF50;padding-bottom:10px}h2{color:#555;margin-top:30px;padding:10px;background:#fff;border-left:4px solid #2196F3}.section{background:#fff;padding:20px;margin:20px 0;border-radius:8px;box-shadow:0 2px 4px rgba(0,0,0,0.1)}.metric{display:inline-block;margin:10px 20px 10px 0;padding:15px 25px;background:#f8f9fa;border-radius:6px;border-left:4px solid #4CAF50}.metric-label{font-size:12px;color:#666;text-transform:uppercase;letter-spacing:1px;margin-bottom:5px}.metric-value{font-size:28px;font-weight:bold;color:#333}.metric-secondary{font-size:14px;color:#888;margin-top:5px}.coverage-bar{height:30px;background:#e0e0e0;border-radius:4px;overflow:hidden;margin:10px 0}.coverage-fill{height:100%;background:linear-gradient(90deg,#4CAF50,#8BC34A);display:flex;align-items:center;justify-content:center;color:#fff;font-weight:bold;font-size:14px}.coverage-low{background:linear-gradient(90deg,#f44336,#e91e63)}.coverage-med{background:linear-gradient(90deg,#ff9800,#ffc107)}.link-button{display:inline-block;padding:12px 24px;margin:10px 10px 10px 0;background:#2196F3;color:#fff;text-decoration:none;border-radius:6px;font-weight:500;transition:background 0.3s}.link-button:hover{background:#1976D2}.link-button.secondary{background:#607D8B}.link-button.secondary:hover{background:#455A64}table{width:100%;border-collapse:collapse;margin-top:15px}th,td{padding:12px;text-align:left;border-bottom:1px solid #e0e0e0}th{background:#f8f9fa;font-weight:600;color:#555}tr:hover{background:#f8f9fa}.timestamp{color:#888;font-size:14px;margin-top:20px}</style></head><body><h1>🎯 Valkyria Coverage Report</h1>" > build-coverage/coverage-report/index.html; \
		if [ -f build-coverage/coverage-c-filtered.info ]; then \
			c_lines=$$(grep -E "^LF:" build-coverage/coverage-c-filtered.info | awk -F: "{sum+=\$$2} END {print sum}"); \
			c_lines_hit=$$(grep -E "^LH:" build-coverage/coverage-c-filtered.info | awk -F: "{sum+=\$$2} END {print sum}"); \
			c_funcs=$$(grep -E "^FNF:" build-coverage/coverage-c-filtered.info | awk -F: "{sum+=\$$2} END {print sum}"); \
			c_funcs_hit=$$(grep -E "^FNH:" build-coverage/coverage-c-filtered.info | awk -F: "{sum+=\$$2} END {print sum}"); \
			c_branches=$$(grep -E "^BRF:" build-coverage/coverage-c-filtered.info | awk -F: "{sum+=\$$2} END {print sum}"); \
			c_branches_hit=$$(grep -E "^BRH:" build-coverage/coverage-c-filtered.info | awk -F: "{sum+=\$$2} END {print sum}"); \
			c_line_pct=$$(awk "BEGIN {printf \"%.1f\", ($$c_lines_hit/$$c_lines)*100}"); \
			c_func_pct=$$(awk "BEGIN {printf \"%.1f\", ($$c_funcs_hit/$$c_funcs)*100}"); \
			c_branch_pct=$$(awk "BEGIN {printf \"%.1f\", ($$c_branches_hit/$$c_branches)*100}"); \
			c_class=$$(awk "BEGIN {if($$c_line_pct<50)print \"coverage-low\";else if($$c_line_pct<80)print \"coverage-med\";else print \"\"}"); \
			echo "<div class=\"section\"><h2>📊 Overall C Coverage</h2><div class=\"metric\"><div class=\"metric-label\">Line Coverage</div><div class=\"metric-value\">$$c_line_pct%</div><div class=\"metric-secondary\">$$c_lines_hit / $$c_lines lines</div></div><div class=\"metric\"><div class=\"metric-label\">Function Coverage</div><div class=\"metric-value\">$$c_func_pct%</div><div class=\"metric-secondary\">$$c_funcs_hit / $$c_funcs functions</div></div><div class=\"metric\"><div class=\"metric-label\">Branch Coverage</div><div class=\"metric-value\">$$c_branch_pct%</div><div class=\"metric-secondary\">$$c_branches_hit / $$c_branches branches</div></div><div style=\"clear:both;margin-top:20px\"><div class=\"coverage-bar\"><div class=\"coverage-fill $$c_class\" style=\"width:$$c_line_pct%\">$$c_line_pct% lines covered</div></div></div><a href=\"c/index.html\" class=\"link-button\">View Detailed C Coverage Report</a></div>" >> build-coverage/coverage-report/index.html; \
		fi; \
		if [ -f build-coverage/coverage-valk.txt ]; then \
			valk_files=$$(wc -l < build-coverage/coverage-valk.txt | tr -d " "); \
			valk_evals=$$(awk -F: "{sum+=\$$2} END {print sum}" build-coverage/coverage-valk.txt); \
			echo "<div class=\"section\"><h2>🚀 Valk/Lisp Coverage</h2><div class=\"metric\"><div class=\"metric-label\">Files Executed</div><div class=\"metric-value\">$$valk_files</div><div class=\"metric-secondary\">.valk source files</div></div><div class=\"metric\"><div class=\"metric-label\">Total Evaluations</div><div class=\"metric-value\">$$valk_evals</div><div class=\"metric-secondary\">expression evaluations</div></div><h3 style=\"margin-top:30px;color:#666\">Files Executed:</h3><table><thead><tr><th>File</th><th>Evaluations</th></tr></thead><tbody>" >> build-coverage/coverage-report/index.html; \
			awk -F: "{printf \"<tr><td>%s</td><td>%s</td></tr>\n\", \$$1, \$$2}" build-coverage/coverage-valk.txt | sort >> build-coverage/coverage-report/index.html; \
			echo "</tbody></table></div>" >> build-coverage/coverage-report/index.html; \
		fi; \
		echo "<div class=\"timestamp\">Generated: $$(date)</div></body></html>" >> build-coverage/coverage-report/index.html'
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  Coverage reports generated                                 ║"
	@echo "╠══════════════════════════════════════════════════════════════╣"
	@echo "║  📊 Combined: open build-coverage/coverage-report/index.html║"
	@if [ -d build-coverage/coverage-report/c ]; then \
		echo "║  C (HTML):    open build-coverage/coverage-report/c/index.html║"; \
	fi
	@if [ -f build-coverage/coverage-c.txt ]; then \
		echo "║  C (text):    cat build-coverage/coverage-c.txt             ║"; \
	fi
	@if [ -f build-coverage/coverage-valk-summary.txt ]; then \
		echo "║  Valk:        cat build-coverage/coverage-valk-summary.txt  ║"; \
	fi
	@echo "╚══════════════════════════════════════════════════════════════╝"

.PHONY: coverage
coverage: export VALK_COVERAGE=1
coverage: build-coverage coverage-reset coverage-c coverage-valk coverage-report
	@echo "=== Coverage collection complete ==="
