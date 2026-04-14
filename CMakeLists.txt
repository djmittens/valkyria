cmake_minimum_required(VERSION 3.26 FATAL_ERROR)


if (HOMEBREW_CLANG)
  include (${CMAKE_CURRENT_SOURCE_DIR}/homebrew.cmake)
else()
  set(CMAKE_C_COMPILER "/usr/bin/clang")
  set(CMAKE_CXX_COMPILER "/usr/bin/clang++")
endif()


project(valkyria LANGUAGES C)

# Feature flags
option(VALK_COVERAGE "Enable Valk line coverage instrumentation" OFF)
option(VALK_TRAMPOLINE "Use trampoline-based eval (for algebraic effects)" OFF)

set (CMAKE_EXECUTABLE_ENABLE_EXPORTS on )

set(SANITIZE_ADDRESS_FLAGS "")
set(SANITIZE_THREAD_FLAGS "")
set(COVERAGE_FLAGS "")

if(ASAN)
  set(SANITIZE_ADDRESS_FLAGS "-fsanitize=address -fno-omit-frame-pointer -fsanitize=undefined ")
endif()

if(TSAN)
  set(SANITIZE_THREAD_FLAGS "-fsanitize=thread -fno-omit-frame-pointer ")
endif()

if(COVERAGE)
  # Enable coverage flags (compatible with gcov/lcov)
  # -fprofile-arcs -ftest-coverage: basic line coverage
  # -fprofile-conditions: branch/MC-DC coverage (Clang 18+)
  set(COVERAGE_FLAGS "-fprofile-arcs -ftest-coverage -O0 -g")
  add_compile_definitions(VALK_COVERAGE_BUILD=1)
endif()

set(EXTRA_FLAGS "-fcolor-diagnostics -Wall -Wextra -Wpedantic -Werror -Wno-gnu-zero-variadic-macro-arguments -Wno-gnu-statement-expression-from-macro-expansion")


# Apply to C and C++ compile flags
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${SANITIZE_THREAD_FLAGS} ${COVERAGE_FLAGS} ${EXTRA_FLAGS}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${SANITIZE_THREAD_FLAGS} ${COVERAGE_FLAGS} ${EXTRA_FLAGS}")

# Apply to link flags
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${SANITIZE_THREAD_FLAGS} ${COVERAGE_FLAGS} ${EXTRA_FLAGS}")
set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} ${SANITIZE_ADDRESS_FLAGS} ${SANITIZE_THREAD_FLAGS} ${COVERAGE_FLAGS} ${EXTRA_FLAGS}")

if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  add_compile_definitions(_XOPEN_SOURCE=700 _GNU_SOURCE)
endif()

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
pkg_check_modules(EXPAT REQUIRED IMPORTED_TARGET expat)

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)


find_path(LIBUV_INCLUDE_DIR NAMES uv.h)
find_library(LIBUV_LIBRARIES NAMES uv libuv)

find_path(BACKTRACE_INCLUDE_DIR NAMES backtrace.h)
find_library(BACKTRACE_LIBRARIES NAMES backtrace)

find_package(OpenSSL REQUIRED)

# LLVM backend (optional)
option(VALK_LLVM "Enable LLVM backend for JIT and AOT compilation" ON)
if(VALK_LLVM)
  find_package(LLVM CONFIG)
  if(LLVM_FOUND)
    message(STATUS "LLVM ${LLVM_PACKAGE_VERSION} found")
    message(STATUS "LLVM include dirs: ${LLVM_INCLUDE_DIRS}")
    add_compile_definitions(VALK_LLVM=1)
  else()
    message(STATUS "LLVM not found, disabling LLVM backend")
    set(VALK_LLVM OFF)
  endif()
endif()

## LIB
set(VALKYRIA_SOURCES
  src/parser.c
  src/lval.c
  src/eval.c
  src/lenv.c
  src/reader.c
  src/type_env.c
  src/type_transform.c
  src/type_transform_forms.c
  src/type_infer.c
  src/type_infer_scope.c
  src/builtins_math.c
  src/builtins_list.c
  src/builtins_string.c
  src/builtins_env.c
  src/builtins_io.c
  src/builtins_file.c
  src/builtins_mem.c
  src/builtins_http.c
  src/builtins_aio.c
  src/builtins_server.c
  src/builtins_test.c
  src/builtins_json.c
  src/builtins_stdio.c
  src/builtins_sqlite.c
  src/lsp_index.c
  src/ast_visit.c
  src/builtins_dict.c
  src/builtins_xml.c
  src/builtins_pipe.c
  src/memory.c
  src/slab.c
  src/memory_os.c
  src/valk_thread_posix.c

  src/gc.c
  src/gc_heap.c
  src/gc_heap_sweep.c
  src/gc_heap_lifecycle.c
  src/gc_evacuation.c
  src/gc_checkpoint.c
  src/gc_mark.c
  src/gc_region.c
  src/gc_stats.c
  src/debug.c
  src/log.c
  src/coverage.c
  src/source_loc.c
  src/diag.c
  # AIO core (src/aio/)
  src/aio/aio_uv.c
  src/aio/aio_alloc.c
  src/aio/aio_async.c
  src/aio/aio_combinators.c
  src/aio/aio_comb_timers.c
  src/aio/aio_comb_syntax.c
  src/aio/aio_comb_handle.c
  src/aio/aio_comb_propagate.c
  src/aio/aio_comb_chain.c
  src/aio/aio_comb_collection.c
  src/aio/aio_comb_all.c
  src/aio/aio_comb_pmap.c
  src/aio/aio_comb_race.c
  src/aio/aio_comb_any.c
  src/aio/aio_comb_all_settled.c
  src/aio/aio_comb_resource.c
  src/aio/aio_comb_timeout.c
  src/aio/aio_comb_util.c
  src/aio/aio_ops.c
  src/aio/aio_http_builtins.c
  # AIO system lifecycle (src/aio/system/)
  src/aio/system/aio_system.c
  src/aio/system/aio_task.c
  src/aio/system/aio_task_queue.c
  src/aio/system/aio_chase_lev.c
  src/aio/system/aio_mpmc.c
  src/aio/system/aio_maintenance.c
  # HTTP/2 protocol (src/aio/http2/)
  src/aio/http2/aio_ssl.c
  src/aio/http2/aio_conn_io.c
  src/aio/http2/aio_http2_conn.c
  src/aio/http2/aio_http2_conn_fsm.c
  src/aio/http2/aio_http2_server.c
  src/aio/http2/aio_http2_client.c
  src/aio/http2/aio_http2_session.c
  # HTTP/2 overload management (src/aio/http2/overload/)
  src/aio/http2/overload/aio_overload_admission.c
  src/aio/http2/overload/aio_overload_state.c
  src/aio/http2/overload/aio_overload_backpressure.c
  # HTTP/2 streaming responses (src/aio/http2/stream/)
  src/aio/http2/stream/aio_stream_body.c
  src/aio/http2/stream/aio_stream_body_conn.c
  src/aio/http2/stream/aio_stream_builtins.c
  # IO ops abstraction layer (src/aio/io/)
  src/aio/io/io_loop_ops_uv.c
  src/aio/io/io_tcp_ops_uv.c
  src/aio/io/io_timer_ops_uv.c
  # Metrics (always enabled)
  src/aio/aio_metrics.c
  src/aio/aio_metrics_v2.c
  src/aio/aio_timer.c
  src/aio/aio_owner.c
  src/aio/aio_handle_diag.c
  src/metrics_v2.c
  src/metrics_delta.c
  src/metrics_builtins.c
  src/macro.c
  src/module.c
  src/aio/aio_diagnostics_builtins.c
  src/aio/aio_request_ctx.c
  src/aio/aio_ctx_builtins.c
  src/pool_metrics.c
  src/event_loop_metrics.c
  src/json.c
  src/validate.c
  vendor/sqlite3/sqlite3.c
)

if(COVERAGE)
  add_library(valkyria STATIC ${VALKYRIA_SOURCES})
else()
  add_library(valkyria ${VALKYRIA_SOURCES})
endif()



# SQLite amalgamation: disable strict warnings (third-party code)
set_source_files_properties(vendor/sqlite3/sqlite3.c PROPERTIES
  COMPILE_FLAGS "-w"
)

if(VALK_COVERAGE)
  add_compile_definitions(VALK_COVERAGE)
  message(STATUS "Valk line coverage: ENABLED")
endif()

file(RELATIVE_PATH VALK_REL_BUILD_DIR "${CMAKE_SOURCE_DIR}" "${CMAKE_BINARY_DIR}")
add_compile_definitions(VALK_BUILD_DIR="${VALK_REL_BUILD_DIR}")

if(VALK_TRAMPOLINE)
  target_compile_definitions(valkyria PRIVATE VALK_TRAMPOLINE_EVAL=1)
  message(STATUS "Trampoline eval: ENABLED")
endif()



target_include_directories(valkyria PRIVATE
  ${PROJECT_SOURCE_DIR}/src
  ${PROJECT_SOURCE_DIR}/src/aio
  ${PROJECT_SOURCE_DIR}/src/aio/system
  ${PROJECT_SOURCE_DIR}/src/aio/http2
  ${PROJECT_SOURCE_DIR}/src/aio/http2/overload
  ${PROJECT_SOURCE_DIR}/src/aio/http2/stream
)
target_include_directories(valkyria SYSTEM PRIVATE
  ${LIBUV_INCLUDE_DIRS}
  ${PROJECT_SOURCE_DIR}/vendor
  ${PROJECT_SOURCE_DIR}/vendor/sqlite3
  $<$<BOOL:${VALK_LLVM}>:${LLVM_INCLUDE_DIRS}>
)

if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  target_include_directories(valkyria PRIVATE ${PROJECT_SOURCE_DIR}/vendor/backtrace)
endif()

target_link_libraries(valkyria PRIVATE
  nghttp2::nghttp2
  ${LIBUV_LIBRARIES}
  OpenSSL::SSL
  OpenSSL::Crypto
  PkgConfig::EXPAT
  m
  dl
  pthread)

if(VALK_LLVM)
  execute_process(
    COMMAND llvm-config --link-shared --libs core orcjit native support
    OUTPUT_VARIABLE LLVM_LIBS_RAW
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  string(REPLACE " " ";" LLVM_LIBS_LIST "${LLVM_LIBS_RAW}")

  add_library(valk_llvm STATIC
    src/llvm/llvm_codegen.c
    src/llvm/llvm_jit.c
    src/llvm/llvm_aot.c
    src/llvm/vir_to_llvm.c
    src/vir/vir.c
    src/vir/vir_print.c
    src/vir/ast_to_vir.c
    src/vir/vir_gc.c
  )
  target_include_directories(valk_llvm PRIVATE
    ${PROJECT_SOURCE_DIR}/src
    ${PROJECT_SOURCE_DIR}/src/aio
    ${PROJECT_SOURCE_DIR}/src/vir
  )
  target_include_directories(valk_llvm SYSTEM PRIVATE
    ${LLVM_INCLUDE_DIRS}
    ${PROJECT_SOURCE_DIR}/vendor
  )
  target_link_libraries(valk_llvm PRIVATE valkyria ${LLVM_LIBS_LIST})
  target_compile_options(valk_llvm PRIVATE -Wno-pedantic)
endif()

if(CMAKE_SYSTEM_NAME STREQUAL "Linux" AND BACKTRACE_LIBRARIES)
  target_link_libraries(valkyria PRIVATE ${BACKTRACE_LIBRARIES})
endif()

# Test fakes library (test doubles for IO ops)
# These are NOT included in coverage metrics since they're in test/
add_library(valk_test_fakes STATIC
  test/fakes/io_loop_ops_test.c
  test/fakes/io_tcp_ops_test.c
  test/fakes/io_timer_ops_test.c
  test/fakes/aio_ops_test.c
)
target_include_directories(valk_test_fakes PRIVATE
  ${PROJECT_SOURCE_DIR}/src
  ${PROJECT_SOURCE_DIR}/src/aio
  ${PROJECT_SOURCE_DIR}/src/aio/io
)
target_link_libraries(valk_test_fakes PRIVATE valkyria)

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

# Add include directories for AIO subdirectories (needed by test files)
include_directories(
  ${PROJECT_SOURCE_DIR}/src/aio
  ${PROJECT_SOURCE_DIR}/src/aio/system
  ${PROJECT_SOURCE_DIR}/src/aio/http2
  ${PROJECT_SOURCE_DIR}/src/aio/http2/overload
  ${PROJECT_SOURCE_DIR}/src/aio/http2/stream
  ${PROJECT_SOURCE_DIR}/vendor/nghttp2/lib/includes
  ${PROJECT_BINARY_DIR}/vendor/nghttp2/lib/includes
)

# All test targets need test/ for testing.h and src/ for runtime headers
include_directories(${PROJECT_SOURCE_DIR}/test ${PROJECT_SOURCE_DIR}/src)

add_executable(test_std test/lang/test_std.c test/testing.c)
target_link_libraries(test_std PRIVATE "-lc" valkyria)

add_executable(test_regression test/lang/test_regression.c test/testing.c)
target_link_libraries(test_regression PRIVATE "-lc" valkyria)

add_executable(test_networking test/http/test_networking.c test/testing.c)
target_link_libraries(test_networking PRIVATE "-lc" valkyria)

add_executable(test_demo_server test/http/test_demo_server.c test/testing.c)
target_link_libraries(test_demo_server PRIVATE "-lc" valkyria)

add_executable(test_large_response test/http/test_large_response.c test/testing.c)
target_link_libraries(test_large_response PRIVATE "-lc" valkyria)

# test_networking_lisp removed - redundant tests

# REMOVED: test_concurrency - no longer using futures/ARCs
# add_executable(test_concurrency test/test_concurrency.c test/testing.c)
# target_link_libraries(test_concurrency PRIVATE "-lc" valkyria)
# include_directories(test_concurrency src/)

add_executable(test_memory test/gc/test_memory.c test/testing.c)
target_link_libraries(test_memory PRIVATE "-lc" "-lm" valkyria)

add_executable(test_per_stream_arena test/http/test_per_stream_arena.c test/testing.c)
target_link_libraries(test_per_stream_arena PRIVATE "-lc" valkyria)

add_executable(test_gc_metrics test/gc/test_gc_metrics.c test/testing.c)
target_link_libraries(test_gc_metrics PRIVATE "-lc" "-lm" valkyria ${LIBUV_LIBRARIES})

add_executable(test_gc_aio_hang test/gc/test_gc_aio_hang.c test/testing.c)
target_link_libraries(test_gc_aio_hang PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_gc_aio test/gc/test_gc_aio.c test/testing.c)
target_link_libraries(test_gc_aio PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_system test/lang/test_system.c test/testing.c)
target_link_libraries(test_system PRIVATE "-lc" valkyria)

add_executable(test_aio_config test/aio/test_aio_config.c test/testing.c)
target_link_libraries(test_aio_config PRIVATE "-lc" valkyria)

add_executable(test_aio_integration test/aio/test_aio_integration.c test/testing.c)
target_link_libraries(test_aio_integration PRIVATE "-lc" valkyria)

add_executable(test_aio_load_shedding test/aio/test_aio_load_shedding.c test/testing.c)
target_link_libraries(test_aio_load_shedding PRIVATE "-lc" valkyria)



add_executable(test_loop_metrics test/metrics/test_loop_metrics.c test/testing.c)
target_link_libraries(test_loop_metrics PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_eval_metrics test/metrics/test_eval_metrics.c test/testing.c)
target_link_libraries(test_eval_metrics PRIVATE "-lc" valkyria)

add_executable(test_metrics_v2 test/metrics/test_metrics_v2.c test/testing.c)
target_link_libraries(test_metrics_v2 PRIVATE "-lc" valkyria)

if(VALK_COVERAGE)
  add_executable(test_source_loc test/parser/test_source_loc.c test/testing.c)
  target_link_libraries(test_source_loc PRIVATE "-lc" valkyria)
  include_directories(test_source_loc src/)
endif()

add_executable(test_debug test/unit/test_debug.c test/testing.c)
target_link_libraries(test_debug PRIVATE "-lc" valkyria)

add_executable(test_pool_metrics test/unit/test_pool_metrics.c test/testing.c)
target_link_libraries(test_pool_metrics PRIVATE "-lc" valkyria)

add_executable(test_metrics_delta test/unit/test_metrics_delta.c test/testing.c)
target_link_libraries(test_metrics_delta PRIVATE "-lc" valkyria)

add_executable(test_event_loop_metrics_unit test/unit/test_event_loop_metrics.c test/testing.c)
target_link_libraries(test_event_loop_metrics_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_metrics_builtins test/unit/test_metrics_builtins.c test/testing.c)
target_link_libraries(test_metrics_builtins PRIVATE "-lc" valkyria)

add_executable(test_log test/unit/test_log.c test/testing.c)
target_link_libraries(test_log PRIVATE "-lc" valkyria)



add_executable(test_aio_alloc_unit test/unit/test_aio_alloc.c test/testing.c)
target_link_libraries(test_aio_alloc_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_aio_uv_unit test/unit/test_aio_uv.c test/testing.c)
target_link_libraries(test_aio_uv_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_aio_uv_coverage test/aio/test_aio_uv_coverage.c test/testing.c)
target_link_libraries(test_aio_uv_coverage PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_aio_combinators test/aio/test_aio_combinators.c test/testing.c)
target_link_libraries(test_aio_combinators PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_pipe_builtins test/http/test_pipe_builtins.c test/testing.c)
target_link_libraries(test_pipe_builtins PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_lsp_integration test/lsp/test_lsp_integration.c test/testing.c)
target_link_libraries(test_lsp_integration PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_aio_backpressure test/unit/test_aio_backpressure.c test/testing.c)
target_link_libraries(test_aio_backpressure PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_coverage_unit test/unit/test_coverage.c test/testing.c)
target_link_libraries(test_coverage_unit PRIVATE "-lc" valkyria)

add_executable(test_gc_unit test/unit/test_gc.c test/testing.c)
target_link_libraries(test_gc_unit PRIVATE "-lc" valkyria)

add_executable(test_gc_parallel_unit test/unit/test_gc_parallel.c test/testing.c)
target_link_libraries(test_gc_parallel_unit PRIVATE "-lc" valkyria)

add_executable(test_large_str test/http/test_large_str.c test/testing.c)
target_link_libraries(test_large_str PRIVATE "-lc" valkyria)

add_executable(test_parser_unit test/unit/test_parser.c test/testing.c)
target_link_libraries(test_parser_unit PRIVATE "-lc" valkyria)

add_executable(test_memory_unit test/unit/test_memory.c test/testing.c)
target_link_libraries(test_memory_unit PRIVATE "-lc" valkyria)

if(VALK_COVERAGE)
  add_executable(test_source_loc_unit test/unit/test_source_loc.c test/testing.c)
  target_link_libraries(test_source_loc_unit PRIVATE "-lc" valkyria)
  target_compile_definitions(test_source_loc_unit PRIVATE VALK_COVERAGE=1)
  include_directories(test_source_loc_unit src/)
endif()

add_executable(test_aio_ssl_unit test/unit/test_aio_ssl.c test/testing.c)
target_link_libraries(test_aio_ssl_unit PRIVATE "-lc" valkyria OpenSSL::SSL OpenSSL::Crypto)

add_executable(test_pressure test/unit/test_pressure.c test/testing.c)
target_link_libraries(test_pressure PRIVATE "-lc" valkyria)

add_executable(test_conn_io test/unit/test_conn_io.c test/testing.c)
target_link_libraries(test_conn_io PRIVATE "-lc" valkyria)

add_executable(test_aio_timer_unit test/unit/test_aio_timer.c test/testing.c)
target_link_libraries(test_aio_timer_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_io_timer_ops_unit test/unit/test_io_timer_ops.c test/testing.c)
target_link_libraries(test_io_timer_ops_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_thread_posix_unit test/unit/test_thread_posix.c test/testing.c)
target_link_libraries(test_thread_posix_unit PRIVATE "-lc" valkyria)

add_executable(test_aio_async_unit test/unit/test_aio_async.c test/testing.c)
target_link_libraries(test_aio_async_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_aio_handle_diag test/aio/test_aio_handle_diag.c test/testing.c)
target_link_libraries(test_aio_handle_diag PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# HTTP2/Streaming tests
add_executable(test_http2_streaming test/http/test_http2_streaming.c test/testing.c)
target_link_libraries(test_http2_streaming PRIVATE "-lc" valkyria)

# Stream body integration tests (data flow through nghttp2)
add_executable(test_stream_body_integration test/http/test_stream_body_integration.c test/testing.c)
target_link_libraries(test_stream_body_integration PRIVATE "-lc" valkyria)

# Parser error path tests
add_executable(test_parser_errors test/parser/test_parser_errors.c test/testing.c)
target_link_libraries(test_parser_errors PRIVATE "-lc" valkyria)

# Concurrent metrics tests
add_executable(test_metrics_concurrent test/metrics/test_metrics_concurrent.c test/testing.c)
target_link_libraries(test_metrics_concurrent PRIVATE "-lc" valkyria)

# Request context tests
add_executable(test_request_ctx_unit test/unit/test_request_ctx.c test/testing.c)
target_link_libraries(test_request_ctx_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Context builtins tests (ctx/deadline, trace/id, etc.)
add_executable(test_ctx_builtins_unit test/unit/test_ctx_builtins.c test/testing.c)
target_link_libraries(test_ctx_builtins_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# HTTP request builtins tests (req/method, req/path, req/headers, etc.)
add_executable(test_http_builtins_unit test/unit/test_http_builtins.c test/testing.c)
target_link_libraries(test_http_builtins_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Chase-Lev deque tests (lock-free work-stealing data structure)
add_executable(test_chase_lev_unit test/unit/test_chase_lev.c test/testing.c)
target_link_libraries(test_chase_lev_unit PRIVATE "-lc" valkyria)

# MPMC bounded queue tests (Vyukov multi-producer multi-consumer)
add_executable(test_mpmc_unit test/unit/test_mpmc.c test/testing.c)
target_link_libraries(test_mpmc_unit PRIVATE "-lc" valkyria)

# Task queue tests (async task execution via libuv event loop)
add_executable(test_task_queue_unit test/unit/test_task_queue.c test/testing.c)
target_link_libraries(test_task_queue_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Stream body connection management tests
add_executable(test_stream_body_conn_unit test/unit/test_stream_body_conn.c test/testing.c)
target_link_libraries(test_stream_body_conn_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Backpressure list tests (linked list operations for overload protection)
add_executable(test_backpressure_list_unit test/unit/test_backpressure_list.c test/testing.c)
target_link_libraries(test_backpressure_list_unit PRIVATE "-lc" valkyria valk_test_fakes ${LIBUV_LIBRARIES})

# Connection FSM state machine tests
add_executable(test_conn_fsm_unit test/unit/test_conn_fsm.c test/testing.c)
target_link_libraries(test_conn_fsm_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Stream builtins tests (Lisp API for stream operations)
add_executable(test_stream_builtins_unit test/unit/test_stream_builtins.c test/testing.c)
target_link_libraries(test_stream_builtins_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# HTTP/2 connection tests (write buffer, backpressure, alloc callbacks)
add_executable(test_http2_conn_unit test/unit/test_http2_conn.c test/testing.c)
target_link_libraries(test_http2_conn_unit PRIVATE "-lc" valkyria valk_test_fakes ${LIBUV_LIBRARIES} nghttp2::nghttp2)

# HTTP/2 server tests (lifecycle, metrics, getters)
add_executable(test_http2_server_unit test/unit/test_http2_server.c test/testing.c)
target_link_libraries(test_http2_server_unit PRIVATE "-lc" valkyria valk_test_fakes ${LIBUV_LIBRARIES})

# HTTP/2 session tests (callbacks, stream arenas, headers)
add_executable(test_http2_session_unit test/unit/test_http2_session.c test/testing.c)
target_link_libraries(test_http2_session_unit PRIVATE "-lc" valkyria valk_test_fakes ${LIBUV_LIBRARIES} nghttp2::nghttp2 OpenSSL::SSL OpenSSL::Crypto)

# Connection admission tests (overload admission control)
add_executable(test_conn_admission_unit test/unit/test_conn_admission.c test/testing.c)
target_link_libraries(test_conn_admission_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_validate test/parser/test_validate.c test/testing.c)
target_link_libraries(test_validate PRIVATE "-lc" valkyria)

add_executable(test_type_env test/parser/test_type_env.c test/testing.c)
target_link_libraries(test_type_env PRIVATE "-lc" valkyria)

add_executable(test_type_infer test/parser/test_type_infer.c test/testing.c)
target_link_libraries(test_type_infer PRIVATE "-lc" valkyria)

# LLVM backend tests
if(VALK_LLVM)
  add_executable(test_llvm_codegen test/lang/test_llvm_codegen.c test/testing.c)
  target_link_libraries(test_llvm_codegen PRIVATE "-lc" valkyria valk_llvm ${LLVM_LIBS_LIST})
  target_include_directories(test_llvm_codegen SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
  target_compile_options(test_llvm_codegen PRIVATE -Wno-pedantic)
  include_directories(test_llvm_codegen src/)

  add_executable(test_vir test/lang/test_vir.c test/testing.c)
  target_link_libraries(test_vir PRIVATE "-lc" valkyria valk_llvm ${LLVM_LIBS_LIST})
  target_include_directories(test_vir SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
  target_compile_options(test_vir PRIVATE -Wno-pedantic)
  include_directories(test_vir src/)
endif()

