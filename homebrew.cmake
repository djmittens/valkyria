# TODO(game_world): only llvim 17 is supported
set(HOMEBREW_PREFIX "/opt/homebrew/opt/llvm@17" CACHE PATH "Where homebrew be n stuff")

set(CMAKE_C_COMPILER "${HOMEBREW_PREFIX}/bin/clang")
set(CMAKE_CXX_COMPILER "${HOMEBREW_PREFIX}/bin/clang++")

set(CMAKE_CXX_STANDARD_INCLUDE_DIRECTORIES
  ${HOMEBREW_PREFIX}/include
  ${HOMEBREW_PREFIX}/llvm/include
)

set(CMAKE_C_STANDARD_INCLUDE_DIRECTORIES
  ${HOMEBREW_PREFIX}/include
  ${HOMEBREW_PREFIX}/llvm/include
)
