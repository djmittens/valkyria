UNAME := $(shell uname -s)
ifeq ($(UNAME), Linux)
	CMAKE= cmake -G Ninja -DASAN=0 -DCMAKE_BUILD_TYPE=Debug -S . -B build ;
endif
ifeq ($(UNAME), Darwin)
	CMAKE= cmake -G Ninja -DHOMEBREW_CLANG=on -DCMAKE_BUILD_TYPE=Debug -S . -B build;
endif


build/.stamp: CMakeLists.txt homebrew.cmake
	$(CMAKE)
	cmake --build build
	touch build/.stamp

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
repl: build/.stamp
	build/valk src/prelude.valk


.PHONY: debug
debug: debug
	#lldb -o "run" build/repl src/prelude.valk
	lldb build/repl src/prelude.valk

.PHONY: test
test: build/.stamp
	build/test_std &&\
	build/test_networking&&\
	build/test_concurrency\
