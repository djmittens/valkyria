cmake_minimum_required(VERSION 3.26 FATAL_ERROR)

project(valkyria LANGUAGES C)

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
target_link_libraries(valkyria PkgConfig::EDITLINE)
