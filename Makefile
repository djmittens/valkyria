UNAME := $(shell uname -s)
ifeq ($(UNAME), Linux)
	CMAKE= cmake -G Ninja -DASAN=0 -DCMAKE_BUILD_TYPE=Debug -S . -B build ;
endif
ifeq ($(UNAME), Darwin)
	CMAKE= cmake -G Ninja -DHOMEBREW_CLANG=on -DASAN=1 -DCMAKE_BUILD_TYPE=Debug -S . -B build;
endif

JOBS := $(shell nproc 2>/dev/null || echo 12)

.ONESHELL:
.PHONY: cmake
cmake build/.cmake: CMakeLists.txt homebrew.cmake Makefile
	$(CMAKE)
	openssl req -x509 -newkey rsa:2048 -nodes \
		-keyout build/server.key \
		-out build/server.crt \
		-sha256 \
		-days 365 \
		-subj "/C=US/ST=SomeState/L=SomeCity/O=MyOrg/CN=localhost"
	touch build/.cmake

.ONESHELL:
.PHONY: build
build : build/.cmake
	touch build/.cmake
	cmake --build build
	# Only link the symbols in like this if we are on macos
	# Also take into account which ones were actually built this run
	if [ "$(UNAME)" == "Darwin" ]; then \
		find build/ -maxdepth 1 -type f -perm -111 -newer build/.cmake -exec \
				dsymutil {} \; -print; \
	fi

.PHONY: lint
lint : build/.cmake 
	run-clang-tidy -p build -j $(JOBS) -extra-arg=-std=c23

# This will install editline and maybe other depenedencies on linux / macos
# editline particularly uses autotools, meaning its a pain to get it to work with cmakejo
# This way if this shit is installed globally, lame
# To install auto tools in homebrew do :
# `brew install autoconf automake libtool`
#
.PHONY: configure
configure:
	cd vendor/editline && \
	./autogen.sh && \
	./configure && \
	make install && \
	
.PHONY: venv
venv:
	python -m venv .venv && \
	source .venv/bin/activate && \
	pip install r Piplock

.PHONY: clean
clean:
	rm -rf build

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
debug: debug
	#lldb -o "run" build/repl src/prelude.valk
	lldb build/repl src/prelude.valk

.ONESHELL:
.PHONY: asan
asan: build
	export ASAN_OPTIONS=detect_leaks=1:halt_on_error=1:abort_on_error=1
	export LSAN_OPTIONS=verbosity=1:log_threads=1
	build/valk src/prelude.valk test/google_http2.valk && echo "exit code = $?"

.PHONY: test
test: build
	# C Test Suites
	build/test_std &&\
	build/test_memory &&\
	build/test_freeze &&\
	build/test_escape &&\
	build/test_networking &&\
	# Lisp Standard Library Tests
	build/valk test/test_prelude.valk &&\
	build/valk test/test_namespace.valk &&\
	build/valk test/test_varargs.valk &&\
	# Core Language Feature Tests
	build/valk test/test_continuations_suite.valk &&\
	build/valk test/test_tco_suite.valk &&\
	build/valk test/test_do_suite.valk &&\
	# GC Tests
	build/valk test/test_gc_suite.valk &&\
	# Crash Regressions
	build/valk test/test_crash_regressions.valk &&\
	# HTTP API Tests
	build/valk test/test_http_minimal.valk &&\
	# Stress Tests
	build/valk test/stress/test_gc_stress.valk &&\
	build/valk test/stress/test_networking_stress.valk
	# Note: test_networking_lisp disabled - requires specific server setup
	# Note: test_recursion_stress.valk disabled - hangs on deep recursion tests

.PHONY: todo
todo:
	rg "TODO\($(shell git rev-parse --abbrev-ref HEAD)\)"
