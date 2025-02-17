cmake_minimum_required(VERSION 3.26 FATAL_ERROR)

set(CMAKE_C_COMPILER "/usr/bin/clang")
set(CMAKE_CXX_COMPILER "/usr/bin/clang++")

project(valkyria LANGUAGES C)

if(ASAN)
  # Enable AddressSanitizer flags
  set(SANITIZE_ADDRESS_FLAGS "-fsanitize=address -fno-omit-frame-pointer -fsanitize=undefined ")
endif()


# Apply to C and C++ compile flags
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${SANITIZE_ADDRESS_FLAGS} -fcolor-diagnostics -O3 -Wall -Wextra -Wpedantic ")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${SANITIZE_ADDRESS_FLAGS} -fcolor-diagnostics")

# Apply to link flags
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} -fcolor-diagnostics")
set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} -fcolor-diagnostics")

find_package(PkgConfig REQUIRED)

pkg_check_modules(EDITLINE REQUIRED IMPORTED_TARGET libeditline)

set(CMAKE_C_STANDARD  23) # LOL current year - 6 is gold
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if (HOMEBREW_CLANG)
  include (${CMAKE_CURRENT_SOURCE_DIR}/homebrew.cmake)
endif()

add_library(valkyria 
  src/parser.c
  src/networking.c
  src/concurrency.c
)

add_executable(valk
  "src/repl.c"
)

include_directories(valk
  # vendor/editline/include/
  ${EDITLINE_INCLUDE_DIRS}
)
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
