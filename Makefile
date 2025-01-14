.PHONY: build
build: 
	cmake -B build -DCMAKE_BUILD_TYPE=Debug -DASAN=on -DHOMEBREW_CLANG=on -G Ninja . && \
	cmake --build build

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
	make install

.PHONY: clean
clean:
	rm -rf build

.PHONY: repl
repl:
	build/valkyria


.PHONY: debug
debug: build
	lldb -o "run" build/valkyria
