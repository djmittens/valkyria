cmake_minimum_required(VERSION 3.26 FATAL_ERROR)


if (HOMEBREW_CLANG)
  include (${CMAKE_CURRENT_SOURCE_DIR}/homebrew.cmake)
else()
  set(CMAKE_C_COMPILER "/usr/bin/clang")
  set(CMAKE_CXX_COMPILER "/usr/bin/clang++")
endif()


project(valkyria LANGUAGES C)

set (CMAKE_EXECUTABLE_ENABLE_EXPORTS on )

if(ASAN)
  # Enable AddressSanitizer flags
  set(SANITIZE_ADDRESS_FLAGS "-fsanitize=address -fno-omit-frame-pointer -fsanitize=undefined ")
endif()

set(EXTRA_FLAGS "-fcolor-diagnostics -Wall -Wextra -Wpedantic -Wno-gnu-zero-variadic-macro-arguments -Wno-gnu-statement-expression-from-macro-expansion")


# Apply to C and C++ compile flags
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${EXTRA_FLAGS}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${EXTRA_FLAGS}")

# Apply to link flags
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${EXTRA_FLAGS}")
set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${EXTRA_FLAGS}")


find_package(PkgConfig REQUIRED)

set (ENABLE_LIB_ONLY on)
set (ENABLE_DOC off)
set (ENABLE_FAILMALLOC OFF)
set (BUILD_TESTING off)
set (ENABLE_THREADS off)
set (WITH_JEMALLOC off)
set (WITH_MRUBY off)
set (WITH_NEVERBLEED off)
set (WITH_LIBBPF off)
set (WITH_WOLFSSL off)
add_subdirectory(vendor/nghttp2)

pkg_check_modules(EDITLINE REQUIRED IMPORTED_TARGET libeditline)

set(CMAKE_C_STANDARD 23) # LOL current year - 6 is gold
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)


find_path(LIBUV_INCLUDE_DIR NAMES uv.h)
find_library(LIBUV_LIBRARIES NAMES uv libuv)

find_path(BACKTRACE_INCLUDE_DIR NAMES backtrace.h)
find_library(BACKTRACE_LIBRARIES NAMES backtrace)

find_package(OpenSSL REQUIRED)

## LIB
add_library(valkyria
  src/parser.c
  src/memory.c
  src/concurrency.c
# TODO(networking): if should detect uring and if we have it we can get it here instead of libuv.
  src/aio_uv.c
  src/debug.c
  src/aio_ssl.c
  src/vm.c
)

target_include_directories(valkyria SYSTEM PRIVATE
  ${LIBUV_INCLUDE_DIRS}
  ${PROJECT_SOURCE_DIR}/vendor
  ${BACKTRACE_INCLUDE_DIR}
)

target_link_libraries(valkyria PRIVATE
  nghttp2::nghttp2
  ${LIBUV_LIBRARIES}
  ${BACKTRACE_LIBRARIES}
  OpenSSL::SSL
  OpenSSL::Crypto)


### REPL
add_executable(valk
  "src/repl.c"
)

target_link_libraries(valk PRIVATE "-lc" PkgConfig::EDITLINE valkyria)
target_include_directories(valk SYSTEM PRIVATE
  # vendor/editline/include/
  ${EDITLINE_INCLUDE_DIRS}
  ${PROJECT_SOURCE_DIR}/vendor
  ${MACOS_SDK_PATH}
)

# TESTS

add_executable(test_std test/test_std.c test/testing.c)
target_link_libraries(test_std PRIVATE "-lc" valkyria)
include_directories(test_std src/)

add_executable(test_networking test/test_networking.c test/testing.c)
target_link_libraries(test_networking PRIVATE "-lc" valkyria)
include_directories(test_networking src/)

add_executable(test_concurrency test/test_concurrency.c test/testing.c)
target_link_libraries(test_concurrency PRIVATE "-lc" valkyria)
include_directories(test_concurrency src/)

add_executable(test_memory test/test_memory.c test/testing.c)
target_link_libraries(test_memory PRIVATE "-lc" "-lm" valkyria)
include_directories(test_memory src/)
