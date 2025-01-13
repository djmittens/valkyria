cmake_minimum_required(VERSION 3.26 FATAL_ERROR)

set(CMAKE_C_COMPILER "/usr/bin/clang")
set(CMAKE_CXX_COMPILER "/usr/bin/clang++")

project(valkyria LANGUAGES C)

if(ASAN)
  # Enable AddressSanitizer flags
  set(SANITIZE_ADDRESS_FLAGS "-fsanitize=address -fno-omit-frame-pointer")
endif()


# Apply to C and C++ compile flags
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${SANITIZE_ADDRESS_FLAGS} -fcolor-diagnostics")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${SANITIZE_ADDRESS_FLAGS} -fcolor-diagnostics")

# Apply to link flags
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} -fcolor-diagnostics")
set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} -fcolor-diagnostics")

find_package(PkgConfig REQUIRED)

pkg_check_modules(EDITLINE REQUIRED IMPORTED_TARGET libeditline)

set(CMAKE_C_STANDARD  17) # LOL current year - 6 is gold
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if (HOMEBREW_CLANG)
  include (${CMAKE_CURRENT_SOURCE_DIR}/homebrew.cmake)
endif()

file(GLOB _SRC
  src/*.c
)

# file(GLOB _HEADERS
#   src/*.h
#   vendor/editline/include/*.h
# )
add_executable(valkyria
  "src/repl.c"
  "vendor/mpc/mpc.c"
  ${_SRC}
)
include_directories(valkyria
  # vendor/editline/include/
  "vendor/mpc/"
  ${EDITLINE_INCLUDE_DIRS}
)
# set_property(TARGET valkyria PROPERTY C_STANDARD 23)
target_link_libraries(valkyria "-lc" PkgConfig::EDITLINE)
