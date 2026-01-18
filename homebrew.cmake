# TODO(game_world): only llvim 17 is supported

set(CMAKE_PREFIX_PATH "/opt/homebrew/")

set(HOMEBREW_PREFIX "/opt/homebrew/" CACHE PATH "Where homebrew be n stuff")
set(HOMEBREW_LLVM "/opt/homebrew/opt/llvm" CACHE PATH "Where clang be n stuff")
set(CMAKE_C_COMPILER "${HOMEBREW_LLVM}/bin/clang")
set(CMAKE_CXX_COMPILER "${HOMEBREW_LLVM}/bin/clang++")
set(CMAKE_CXX_STANDARD_INCLUDE_DIRECTORIES
  ${HOMEBREW_PREFIX}/include
  ${HOMEBREW_LLVM}/include
  ${HOMEBREW_LLVM}/llvm/include
)
set(CMAKE_C_STANDARD_INCLUDE_DIRECTORIES
 ${HOMEBREW_PREFIX}/include
 ${HOMEBREW_LLVM}/include
 ${HOMEBREW_LLVM}/llvm/include
)
