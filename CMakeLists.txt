cmake_minimum_required(VERSION 3.26 FATAL_ERROR)

set(CMAKE_C_COMPILER "/usr/bin/clang")
set(CMAKE_CXX_COMPILER "/usr/bin/clang++")

project(valkyria LANGUAGES C)

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
set (BUILD_TESTING off)
set (ENABLE_THREADS off)
add_subdirectory(vendor/nghttp2)

pkg_check_modules(EDITLINE REQUIRED IMPORTED_TARGET libeditline)

set(CMAKE_C_STANDARD  23) # LOL current year - 6 is gold
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if (HOMEBREW_CLANG)
  include (${CMAKE_CURRENT_SOURCE_DIR}/homebrew.cmake)
endif()

add_library(valkyria 
  src/parser.c
  src/memory.c
  src/concurrency.c
)

if(WIN32)
  message(FATAL_ERROR "Windows is not supported for networking yet")
  target_compile_definitions(valkyria PUBLIC
    PLATFORM_WINDOWS
  )
elseif(APPLE)
  message(FATAL_ERROR "OSX is not supported for networking yet")
  target_compile_definitions(valkyria PUBLIC
    PLATFORM_OSX
  )
elseif(UNIX)
  target_sources(valkyria PRIVATE
    # src/inet_epoll.c
    # TODO(networking): need to detect if the platform supports uring, otherwise we use libuv
    src/aio_uv.c
  )
  target_link_libraries(valkyria PRIVATE "-luv" )
  target_compile_definitions(valkyria PUBLIC
    PLATFORM_UNIX
  )
else()
  message(FATAL_ERROR "What the fuck is this operating system")
endif()

add_executable(valk
  "src/repl.c"
)

include_directories(valk
  # vendor/editline/include/
  ${EDITLINE_INCLUDE_DIRS}
)

target_link_libraries(valkyria PRIVATE nghttp2::nghttp2 )
# set_property(TARGET valkyria PROPERTY C_STANDARD 23)
target_link_libraries(valk PRIVATE "-lc" PkgConfig::EDITLINE valkyria)

add_executable(test_std test/test_std.c test/testing.c)
target_link_libraries(test_std PRIVATE "-lc" valkyria)
include_directories(test_std src/)

add_executable(test_networking test/test_networking.c test/testing.c)
target_link_libraries(test_networking PRIVATE "-lc" valkyria)
include_directories(test_networking src/)

add_executable(test_concurrency test/test_concurrency.c test/testing.c)
target_link_libraries(test_concurrency PRIVATE "-lc" valkyria)
include_directories(test_concurrency src/)

