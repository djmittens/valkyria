cmake_minimum_required(VERSION 3.26 FATAL_ERROR)


if (HOMEBREW_CLANG)
  include (${CMAKE_CURRENT_SOURCE_DIR}/homebrew.cmake)
else()
  set(CMAKE_C_COMPILER "/usr/bin/clang")
  set(CMAKE_CXX_COMPILER "/usr/bin/clang++")
endif()


project(valkyria LANGUAGES C)

# Feature flags
option(VALK_METRICS "Enable metrics collection" OFF)
option(VALK_COVERAGE "Enable Valk line coverage instrumentation" OFF)
option(VALK_TRAMPOLINE "Use trampoline-based eval (for algebraic effects)" OFF)

set (CMAKE_EXECUTABLE_ENABLE_EXPORTS on )

set(SANITIZE_ADDRESS_FLAGS "")
set(COVERAGE_FLAGS "")

if(ASAN)
  # Enable AddressSanitizer flags
  set(SANITIZE_ADDRESS_FLAGS "-fsanitize=address -fno-omit-frame-pointer -fsanitize=undefined ")
endif()

if(COVERAGE)
  # Enable coverage flags (compatible with gcov/lcov)
  # -fprofile-arcs -ftest-coverage: basic line coverage
  # -fprofile-conditions: branch/MC-DC coverage (Clang 18+)
  set(COVERAGE_FLAGS "-fprofile-arcs -ftest-coverage -O0 -g")
endif()

set(EXTRA_FLAGS "-fcolor-diagnostics -Wall -Wextra -Wpedantic -Wno-gnu-zero-variadic-macro-arguments -Wno-gnu-statement-expression-from-macro-expansion")


# Apply to C and C++ compile flags
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${COVERAGE_FLAGS} ${EXTRA_FLAGS}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${COVERAGE_FLAGS} ${EXTRA_FLAGS}")

# Apply to link flags
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${COVERAGE_FLAGS} ${EXTRA_FLAGS}")
set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${COVERAGE_FLAGS} ${EXTRA_FLAGS}")


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

pkg_check_modules(EDITLINE REQUIRED IMPORTED_TARGET libedit)

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
set(VALKYRIA_SOURCES
  src/parser.c
  src/memory.c
  src/concurrency.c  # TODO: Remove once AIO is updated to use continuations
  src/gc.c
  src/debug.c
  src/log.c
  src/coverage.c
  src/source_loc.c
  # AIO subsystem (src/aio/)
  src/aio/aio_uv.c
  src/aio/aio_ssl.c
  src/aio/aio_alloc.c
  src/aio/aio_sse.c
  src/aio/aio_conn_io.c
  src/aio/aio_conn_admission.c
  src/aio/aio_pressure.c
  src/aio/aio_body_buffer.c
  src/aio/aio_async.c
  src/aio/aio_combinators.c
  src/aio/aio_pending_stream.c
  src/aio/aio_backpressure.c
  # HTTP/2 modular components
  src/aio/aio_http2_conn.c
  src/aio/aio_http2_server.c
  src/aio/aio_http2_client.c
  src/aio/aio_http2_session.c
  # AIO modular components
  src/aio/aio_system.c
  src/aio/aio_task.c
  src/aio/aio_maintenance.c
  src/aio/aio_sse_conn_tracking.c
)

# Conditionally add metrics sources (V2 only)
if(VALK_METRICS)
  list(APPEND VALKYRIA_SOURCES src/aio/aio_metrics.c)
  list(APPEND VALKYRIA_SOURCES src/aio/aio_timer.c)
  list(APPEND VALKYRIA_SOURCES src/aio/aio_owner.c)
  list(APPEND VALKYRIA_SOURCES src/aio/aio_handle_diag.c)
  # Metrics V2 - unified registry with delta streaming
  list(APPEND VALKYRIA_SOURCES src/metrics_v2.c)
  list(APPEND VALKYRIA_SOURCES src/metrics_delta.c)
  list(APPEND VALKYRIA_SOURCES src/metrics_builtins.c)
  # Pool metrics factory for standardized pool metrics
  list(APPEND VALKYRIA_SOURCES src/pool_metrics.c)
  # Event loop metrics for libuv loops
  list(APPEND VALKYRIA_SOURCES src/event_loop_metrics.c)
  # SSE diagnostics for memory visualization
  list(APPEND VALKYRIA_SOURCES src/aio/aio_sse_diagnostics.c)
  # SSE stream registry for global timer management
  list(APPEND VALKYRIA_SOURCES src/aio/aio_sse_stream_registry.c)
  # SSE builtins for Lisp API
  list(APPEND VALKYRIA_SOURCES src/aio/aio_sse_builtins.c)
endif()

add_library(valkyria ${VALKYRIA_SOURCES})

# Conditionally enable metrics
if(VALK_METRICS)
  target_compile_definitions(valkyria PRIVATE VALK_METRICS_ENABLED=1)
endif()

if(VALK_COVERAGE)
  add_compile_definitions(VALK_COVERAGE)
  message(STATUS "Valk line coverage: ENABLED")
endif()

if(VALK_TRAMPOLINE)
  target_compile_definitions(valkyria PRIVATE VALK_TRAMPOLINE_EVAL=1)
  message(STATUS "Trampoline eval: ENABLED")
endif()

# On glibc-based Linux, expose required pthread and POSIX interfaces
# for libuv headers (e.g. pthread_rwlock_t) without enabling non-portable APIs.
if (CMAKE_SYSTEM_NAME STREQUAL "Linux")
  target_compile_definitions(valkyria PRIVATE _XOPEN_SOURCE=700)
  # Some distros still gate rwlocks behind GNU feature selection; enable it
  # for this target only. This is a no-op on non-glibc platforms.
  target_compile_definitions(valkyria PRIVATE _GNU_SOURCE)
endif()

target_include_directories(valkyria SYSTEM PRIVATE
  ${LIBUV_INCLUDE_DIRS}
  ${PROJECT_SOURCE_DIR}/vendor
)

if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  target_include_directories(valkyria SYSTEM PRIVATE ${BACKTRACE_INCLUDE_DIR})
endif()

target_link_libraries(valkyria PRIVATE
  nghttp2::nghttp2
  ${LIBUV_LIBRARIES}
  OpenSSL::SSL
  OpenSSL::Crypto)

if(CMAKE_SYSTEM_NAME STREQUAL "Linux" AND BACKTRACE_LIBRARIES)
  target_link_libraries(valkyria PRIVATE ${BACKTRACE_LIBRARIES})
endif()


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

add_executable(test_demo_server test/test_demo_server.c test/testing.c)
target_link_libraries(test_demo_server PRIVATE "-lc" valkyria)
if(VALK_METRICS)
  target_compile_definitions(test_demo_server PRIVATE VALK_METRICS_ENABLED=1)
endif()
include_directories(test_demo_server src/)

add_executable(test_large_response test/test_large_response.c test/testing.c)
target_link_libraries(test_large_response PRIVATE "-lc" valkyria)
include_directories(test_large_response src/)

# test_networking_lisp removed - redundant tests

# REMOVED: test_concurrency - no longer using futures/ARCs
# add_executable(test_concurrency test/test_concurrency.c test/testing.c)
# target_link_libraries(test_concurrency PRIVATE "-lc" valkyria)
# include_directories(test_concurrency src/)

add_executable(test_memory test/test_memory.c test/testing.c)
target_link_libraries(test_memory PRIVATE "-lc" "-lm" valkyria)
include_directories(test_memory src/)

add_executable(test_per_stream_arena test/test_per_stream_arena.c test/testing.c)
target_link_libraries(test_per_stream_arena PRIVATE "-lc" valkyria)
include_directories(test_per_stream_arena src/)

add_executable(test_gc_metrics test/test_gc_metrics.c test/testing.c)
target_link_libraries(test_gc_metrics PRIVATE "-lc" "-lm" valkyria ${LIBUV_LIBRARIES})
include_directories(test_gc_metrics src/)

add_executable(test_aio_config test/test_aio_config.c test/testing.c)
target_link_libraries(test_aio_config PRIVATE "-lc" valkyria)
include_directories(test_aio_config src/)

add_executable(test_aio_integration test/test_aio_integration.c test/testing.c)
target_link_libraries(test_aio_integration PRIVATE "-lc" valkyria)
if(VALK_METRICS)
  target_compile_definitions(test_aio_integration PRIVATE VALK_METRICS_ENABLED=1)
endif()
include_directories(test_aio_integration src/)

add_executable(test_aio_load_shedding test/test_aio_load_shedding.c test/testing.c)
target_link_libraries(test_aio_load_shedding PRIVATE "-lc" valkyria)
if(VALK_METRICS)
  target_compile_definitions(test_aio_load_shedding PRIVATE VALK_METRICS_ENABLED=1)
endif()
include_directories(test_aio_load_shedding src/)

add_executable(test_aio_sse_integration test/test_aio_sse_integration.c test/testing.c)
target_link_libraries(test_aio_sse_integration PRIVATE "-lc" valkyria)
if(VALK_METRICS)
  target_compile_definitions(test_aio_sse_integration PRIVATE VALK_METRICS_ENABLED=1)
endif()
include_directories(test_aio_sse_integration src/)

# Metrics tests (only built when VALK_METRICS is enabled)
if(VALK_METRICS)
  add_executable(test_aio_metrics test/test_aio_metrics.c test/testing.c)
  target_link_libraries(test_aio_metrics PRIVATE "-lc" valkyria)
  target_compile_definitions(test_aio_metrics PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_aio_metrics src/)

  add_executable(test_loop_metrics test/test_loop_metrics.c test/testing.c)
  target_link_libraries(test_loop_metrics PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})
  target_compile_definitions(test_loop_metrics PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_loop_metrics src/)

  add_executable(test_eval_metrics test/test_eval_metrics.c test/testing.c)
  target_link_libraries(test_eval_metrics PRIVATE "-lc" valkyria)
  include_directories(test_eval_metrics src/)

  add_executable(test_sse_diagnostics test/test_sse_diagnostics.c test/testing.c)
  target_link_libraries(test_sse_diagnostics PRIVATE "-lc" valkyria)
  target_compile_definitions(test_sse_diagnostics PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_sse_diagnostics src/)

  add_executable(test_sse test/test_sse.c test/testing.c)
  target_link_libraries(test_sse PRIVATE "-lc" valkyria)
  include_directories(test_sse src/)

  add_executable(test_metrics_v2 test/test_metrics_v2.c test/testing.c)
  target_link_libraries(test_metrics_v2 PRIVATE "-lc" valkyria)
  target_compile_definitions(test_metrics_v2 PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_metrics_v2 src/)
endif()

if(VALK_COVERAGE)
  add_executable(test_source_loc test/test_source_loc.c test/testing.c)
  target_link_libraries(test_source_loc PRIVATE "-lc" valkyria)
  include_directories(test_source_loc src/)
endif()

add_executable(test_debug test/unit/test_debug.c test/testing.c)
target_link_libraries(test_debug PRIVATE "-lc" valkyria)
include_directories(test_debug src/)

if(VALK_METRICS)
  add_executable(test_pool_metrics test/unit/test_pool_metrics.c test/testing.c)
  target_link_libraries(test_pool_metrics PRIVATE "-lc" valkyria)
  target_compile_definitions(test_pool_metrics PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_pool_metrics src/)

  add_executable(test_metrics_delta test/unit/test_metrics_delta.c test/testing.c)
  target_link_libraries(test_metrics_delta PRIVATE "-lc" valkyria)
  target_compile_definitions(test_metrics_delta PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_metrics_delta src/)

  add_executable(test_event_loop_metrics_unit test/unit/test_event_loop_metrics.c test/testing.c)
  target_link_libraries(test_event_loop_metrics_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})
  target_compile_definitions(test_event_loop_metrics_unit PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_event_loop_metrics_unit src/)

  add_executable(test_sse_core test/unit/test_sse_core.c test/testing.c)
  target_link_libraries(test_sse_core PRIVATE "-lc" valkyria)
  target_compile_definitions(test_sse_core PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_sse_core src/)

  add_executable(test_metrics_builtins test/unit/test_metrics_builtins.c test/testing.c)
  target_link_libraries(test_metrics_builtins PRIVATE "-lc" valkyria)
  target_compile_definitions(test_metrics_builtins PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_metrics_builtins src/)

  add_executable(test_sse_registry_unit test/unit/test_sse_registry.c test/testing.c)
  target_link_libraries(test_sse_registry_unit PRIVATE "-lc" valkyria)
  target_compile_definitions(test_sse_registry_unit PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_sse_registry_unit src/)

  add_executable(test_sse_builtins_unit test/unit/test_sse_builtins.c test/testing.c)
  target_link_libraries(test_sse_builtins_unit PRIVATE "-lc" valkyria)
  target_compile_definitions(test_sse_builtins_unit PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_sse_builtins_unit src/)
endif()

add_executable(test_concurrency test/unit/test_concurrency.c test/testing.c)
target_link_libraries(test_concurrency PRIVATE "-lc" valkyria)
include_directories(test_concurrency src/)

add_executable(test_log test/unit/test_log.c test/testing.c)
target_link_libraries(test_log PRIVATE "-lc" valkyria)
include_directories(test_log src/)

add_executable(test_aio_alloc_unit test/unit/test_aio_alloc.c test/testing.c)
target_link_libraries(test_aio_alloc_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})
include_directories(test_aio_alloc_unit src/)

add_executable(test_aio_uv_unit test/unit/test_aio_uv.c test/testing.c)
target_link_libraries(test_aio_uv_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})
include_directories(test_aio_uv_unit src/)

add_executable(test_aio_uv_coverage test/test_aio_uv_coverage.c test/testing.c)
target_link_libraries(test_aio_uv_coverage PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})
if(VALK_METRICS)
  target_compile_definitions(test_aio_uv_coverage PRIVATE VALK_METRICS_ENABLED=1)
endif()
include_directories(test_aio_uv_coverage src/)

add_executable(test_aio_combinators test/test_aio_combinators.c test/testing.c)
target_link_libraries(test_aio_combinators PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})
if(VALK_METRICS)
  target_compile_definitions(test_aio_combinators PRIVATE VALK_METRICS_ENABLED=1)
endif()
include_directories(test_aio_combinators src/)

if(VALK_METRICS)
  add_executable(test_aio_backpressure test/unit/test_aio_backpressure.c test/testing.c)
  target_link_libraries(test_aio_backpressure PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})
  target_compile_definitions(test_aio_backpressure PRIVATE VALK_METRICS_ENABLED=1)
  include_directories(test_aio_backpressure src/)
endif()

add_executable(test_coverage_unit test/unit/test_coverage.c test/testing.c)
target_link_libraries(test_coverage_unit PRIVATE "-lc" valkyria)
include_directories(test_coverage_unit src/)

add_executable(test_gc_unit test/unit/test_gc.c test/testing.c)
target_link_libraries(test_gc_unit PRIVATE "-lc" valkyria)
include_directories(test_gc_unit src/)

add_executable(test_large_str test/test_large_str.c test/testing.c)
target_link_libraries(test_large_str PRIVATE "-lc" valkyria)
include_directories(test_large_str src/)

add_executable(test_parser_unit test/unit/test_parser.c test/testing.c)
target_link_libraries(test_parser_unit PRIVATE "-lc" valkyria)
include_directories(test_parser_unit src/)

add_executable(test_memory_unit test/unit/test_memory.c test/testing.c)
target_link_libraries(test_memory_unit PRIVATE "-lc" valkyria)
include_directories(test_memory_unit src/)

if(VALK_COVERAGE)
  add_executable(test_source_loc_unit test/unit/test_source_loc.c test/testing.c)
  target_link_libraries(test_source_loc_unit PRIVATE "-lc" valkyria)
  target_compile_definitions(test_source_loc_unit PRIVATE VALK_COVERAGE=1)
  include_directories(test_source_loc_unit src/)
endif()

add_executable(test_aio_ssl_unit test/unit/test_aio_ssl.c test/testing.c)
target_link_libraries(test_aio_ssl_unit PRIVATE "-lc" valkyria OpenSSL::SSL OpenSSL::Crypto)
include_directories(test_aio_ssl_unit src/)

add_executable(test_pressure test/unit/test_pressure.c test/testing.c)
target_link_libraries(test_pressure PRIVATE "-lc" valkyria)
include_directories(test_pressure src/)

add_executable(test_body_buffer test/unit/test_body_buffer.c test/testing.c)
target_link_libraries(test_body_buffer PRIVATE "-lc" valkyria)
include_directories(test_body_buffer src/)

add_executable(test_conn_io test/unit/test_conn_io.c test/testing.c)
target_link_libraries(test_conn_io PRIVATE "-lc" valkyria)
include_directories(test_conn_io src/)

add_executable(test_sse_stream_registry_unit test/unit/test_sse_stream_registry.c test/testing.c)
target_link_libraries(test_sse_stream_registry_unit PRIVATE "-lc" valkyria)
target_compile_definitions(test_sse_stream_registry_unit PRIVATE VALK_METRICS_ENABLED=1)
include_directories(test_sse_stream_registry_unit src/)
