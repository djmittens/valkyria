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
  src/conc_map.c
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
  src/load.c
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
  src/lsp_index_emit.c
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
  src/gc_mark.c
  src/gc_concurrent.c
  src/gc_verify.c
  src/gc_region.c
  src/gc_stats.c
  src/debug.c
  src/log.c
  src/coverage.c
  src/source_loc.c
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
  src/aio/aio_comb_pmap_reduce.c
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
  src/aio/aio_diagnostics_builtins.c
  src/aio/aio_request_ctx.c
  src/aio/aio_ctx_builtins.c
  src/pool_metrics.c
  src/event_loop_metrics.c
  src/json.c
  src/image.c
  src/build.c
  vendor/sqlite3/sqlite3.c
)

add_library(valkyria ${VALKYRIA_SOURCES})



# SQLite amalgamation: disable strict warnings (third-party code)
set_source_files_properties(vendor/sqlite3/sqlite3.c PROPERTIES
  COMPILE_FLAGS "-w"
)

if(VALK_COVERAGE)
  add_compile_definitions(VALK_COVERAGE)
  message(STATUS "Valk line coverage: ENABLED")
endif()

# Relative to the workspace root (parent of runtime/): the binary is run from
# the workspace root, and builtins_server.c resolves TLS certs against cwd.
file(RELATIVE_PATH VALK_REL_BUILD_DIR "${CMAKE_SOURCE_DIR}/.." "${CMAKE_BINARY_DIR}")

# `valk --build` links the precompiled valk-shim.o and the instrumented
# libvalkyria; sanitizer/coverage runtimes must come from the SAME toolchain
# that built them. Bake the configured compiler in as the default (still
# overridable with $CC; falls back to `cc` if the path is gone).
add_compile_definitions(VALK_CC="${CMAKE_C_COMPILER}")
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
  # find_package(LLVM) exposes LLVM_TOOLS_BINARY_DIR; use the llvm-config that
  # ships with the detected LLVM rather than relying on one being on PATH (it
  # often is not on macOS/homebrew, which silently yielded an empty lib list and
  # undefined LLVM symbols at link time).
  find_program(LLVM_CONFIG_EXE
    NAMES llvm-config
    HINTS ${LLVM_TOOLS_BINARY_DIR}
    REQUIRED)
  execute_process(
    COMMAND ${LLVM_CONFIG_EXE} --link-shared --libs core orcjit native support
    OUTPUT_VARIABLE LLVM_LIBS_RAW
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  string(REPLACE " " ";" LLVM_LIBS_LIST "${LLVM_LIBS_RAW}")
  # llvm-config emits -lLLVM-NN but not the -L for homebrew's lib dir; add it so
  # the linker can find libLLVM.dylib.
  link_directories(${LLVM_LIBRARY_DIRS})

  add_library(valk_llvm STATIC
    src/llvm/llvm_codegen.c
    src/llvm/llvm_codegen_emit.c
    src/llvm/llvm_codegen_special.c
    src/llvm/llvm_codegen_numeric.c
    src/llvm/llvm_codegen_call.c
    src/llvm/llvm_jit.c
    src/llvm/llvm_aot.c
    src/llvm/build_aot.c
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

# Precompiled `valk --build` shim: the entry point of every --build output
# binary, compiled here with the same flags/ABI as libvalkyria and shipped as
# <build>/valk-shim.o. `valk --build` links it directly, so deployment
# machines never need the runtime headers (and can never skew the lval ABI).
add_library(valk_shim OBJECT src/build_shim.c)
target_include_directories(valk_shim PRIVATE
  ${PROJECT_SOURCE_DIR}/src
  ${PROJECT_SOURCE_DIR}/src/aio
  ${PROJECT_SOURCE_DIR}/src/aio/system
  ${PROJECT_SOURCE_DIR}/src/aio/http2
  ${PROJECT_SOURCE_DIR}/src/aio/http2/overload
  ${PROJECT_SOURCE_DIR}/src/aio/http2/stream
)
target_include_directories(valk_shim SYSTEM PRIVATE
  ${LIBUV_INCLUDE_DIRS}
  ${PROJECT_SOURCE_DIR}/vendor
)
if(VALK_COVERAGE)
  target_compile_definitions(valk_shim PRIVATE VALK_COVERAGE)
endif()
add_custom_command(
  OUTPUT ${CMAKE_BINARY_DIR}/valk-shim.o
  COMMAND ${CMAKE_COMMAND} -E copy $<TARGET_OBJECTS:valk_shim> ${CMAKE_BINARY_DIR}/valk-shim.o
  DEPENDS valk_shim $<TARGET_OBJECTS:valk_shim>
  COMMENT "Staging valk-shim.o"
)
add_custom_target(valk_shim_staged ALL DEPENDS ${CMAKE_BINARY_DIR}/valk-shim.o)

### REPL / CLI entry point (lives in the repl/ root project)
add_executable(valk
  "../repl/main.c"
)
add_dependencies(valk valk_shim_staged)
target_link_libraries(valk PRIVATE "-lc" PkgConfig::EDITLINE valkyria)
if(VALK_LLVM)
  # Link valk_llvm so --build can use LLVM AOT compilation of user lambdas.
  # src/build.c resolves valk_build_emit_aot at runtime via
  # dlsym(RTLD_DEFAULT, ...) so it degrades gracefully when the symbol is
  # absent (no LLVM) instead of crashing on a null weak reference.
  #
  # For dlsym to find it, the executable must (a) pull build_aot.o out of the
  # static archive and (b) export the symbol in its dynamic symbol table.
  if(APPLE)
    target_link_options(valk PRIVATE
      "-Wl,-u,_valk_build_emit_aot"
      "-Wl,-export_dynamic")
  else()
    target_link_options(valk PRIVATE
      "-Wl,-u,valk_build_emit_aot"
      "-rdynamic")
  endif()
  target_link_libraries(valk PRIVATE
    valk_llvm
    ${LLVM_LIBS_LIST})
endif()

target_include_directories(valk SYSTEM PRIVATE
  # vendor/editline/include/
  ${EDITLINE_INCLUDE_DIRS}
  ${PROJECT_SOURCE_DIR}/vendor
  ${MACOS_SDK_PATH}
)
target_include_directories(valk PRIVATE ${PROJECT_SOURCE_DIR}/src)

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

# All test targets need the testing harness (testing.h), test/ for the
# per-area helper headers, and src/ for runtime headers
include_directories(${PROJECT_SOURCE_DIR}/../testing/c ${PROJECT_SOURCE_DIR}/test ${PROJECT_SOURCE_DIR}/src)

add_executable(test_std test/lang/test_std.c ../testing/c/testing.c)
target_link_libraries(test_std PRIVATE "-lc" valkyria)

add_executable(test_image test/lang/test_image.c ../testing/c/testing.c)
target_link_libraries(test_image PRIVATE "-lc" valkyria)

add_executable(test_image_corrupt test/lang/test_image_corrupt.c ../testing/c/testing.c)
target_link_libraries(test_image_corrupt PRIVATE "-lc" valkyria)

add_executable(test_build test/lang/test_build.c ../testing/c/testing.c)
target_link_libraries(test_build PRIVATE "-lc" valkyria)

add_executable(test_regression test/lang/test_regression.c ../testing/c/testing.c)
target_link_libraries(test_regression PRIVATE "-lc" valkyria)

add_executable(test_networking test/http/test_networking.c ../testing/c/testing.c)
target_link_libraries(test_networking PRIVATE "-lc" valkyria)

add_executable(test_demo_server test/http/test_demo_server.c ../testing/c/testing.c)
target_link_libraries(test_demo_server PRIVATE "-lc" valkyria)

add_executable(test_large_response test/http/test_large_response.c ../testing/c/testing.c)
target_link_libraries(test_large_response PRIVATE "-lc" valkyria)

add_executable(test_memory test/gc/test_memory.c ../testing/c/testing.c)
target_link_libraries(test_memory PRIVATE "-lc" "-lm" valkyria)

add_executable(test_per_stream_arena test/http/test_per_stream_arena.c ../testing/c/testing.c)
target_link_libraries(test_per_stream_arena PRIVATE "-lc" valkyria)

add_executable(test_gc_metrics test/gc/test_gc_metrics.c ../testing/c/testing.c)
target_link_libraries(test_gc_metrics PRIVATE "-lc" "-lm" valkyria ${LIBUV_LIBRARIES})

add_executable(test_gc_aio_hang test/gc/test_gc_aio_hang.c ../testing/c/testing.c)
target_link_libraries(test_gc_aio_hang PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_gc_aio test/gc/test_gc_aio.c ../testing/c/testing.c)
target_link_libraries(test_gc_aio PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_system test/lang/test_system.c ../testing/c/testing.c)
target_link_libraries(test_system PRIVATE "-lc" valkyria)

add_executable(test_aio_config test/aio/test_aio_config.c ../testing/c/testing.c)
target_link_libraries(test_aio_config PRIVATE "-lc" valkyria)

add_executable(test_aio_integration test/aio/test_aio_integration.c ../testing/c/testing.c)
target_link_libraries(test_aio_integration PRIVATE "-lc" valkyria)

add_executable(test_aio_load_shedding test/aio/test_aio_load_shedding.c ../testing/c/testing.c)
target_link_libraries(test_aio_load_shedding PRIVATE "-lc" valkyria)



add_executable(test_loop_metrics test/metrics/test_loop_metrics.c ../testing/c/testing.c)
target_link_libraries(test_loop_metrics PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_eval_metrics test/metrics/test_eval_metrics.c ../testing/c/testing.c)
target_link_libraries(test_eval_metrics PRIVATE "-lc" valkyria)

add_executable(test_metrics_v2 test/metrics/test_metrics_v2.c ../testing/c/testing.c)
target_link_libraries(test_metrics_v2 PRIVATE "-lc" valkyria)

if(VALK_COVERAGE)
  add_executable(test_source_loc test/parser/test_source_loc.c ../testing/c/testing.c)
  target_link_libraries(test_source_loc PRIVATE "-lc" valkyria)
  include_directories(test_source_loc src/)
endif()

add_executable(test_debug test/unit/test_debug.c ../testing/c/testing.c)
target_link_libraries(test_debug PRIVATE "-lc" valkyria)

add_executable(test_pool_metrics test/unit/test_pool_metrics.c ../testing/c/testing.c)
target_link_libraries(test_pool_metrics PRIVATE "-lc" valkyria)

add_executable(test_metrics_delta test/unit/test_metrics_delta.c ../testing/c/testing.c)
target_link_libraries(test_metrics_delta PRIVATE "-lc" valkyria)

add_executable(test_event_loop_metrics_unit test/unit/test_event_loop_metrics.c ../testing/c/testing.c)
target_link_libraries(test_event_loop_metrics_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_metrics_builtins test/unit/test_metrics_builtins.c ../testing/c/testing.c)
target_link_libraries(test_metrics_builtins PRIVATE "-lc" valkyria)

add_executable(test_log test/unit/test_log.c ../testing/c/testing.c)
target_link_libraries(test_log PRIVATE "-lc" valkyria)



add_executable(test_aio_alloc_unit test/unit/test_aio_alloc.c ../testing/c/testing.c)
target_link_libraries(test_aio_alloc_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_aio_uv_unit test/unit/test_aio_uv.c ../testing/c/testing.c)
target_link_libraries(test_aio_uv_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_aio_uv_coverage test/aio/test_aio_uv_coverage.c ../testing/c/testing.c)
target_link_libraries(test_aio_uv_coverage PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_aio_combinators test/aio/test_aio_combinators.c ../testing/c/testing.c)
target_link_libraries(test_aio_combinators PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_pipe_builtins test/http/test_pipe_builtins.c ../testing/c/testing.c)
target_link_libraries(test_pipe_builtins PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_lsp_integration ../lsp/test/test_lsp_integration.c ../testing/c/testing.c)
target_link_libraries(test_lsp_integration PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_lsp_profile ../lsp/test/test_lsp_profile.c ../testing/c/testing.c)
target_link_libraries(test_lsp_profile PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(lsp_proxy ../lsp/test/lsp_proxy.c)

add_executable(test_aio_backpressure test/unit/test_aio_backpressure.c ../testing/c/testing.c)
target_link_libraries(test_aio_backpressure PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_coverage_unit test/unit/test_coverage.c ../testing/c/testing.c)
target_link_libraries(test_coverage_unit PRIVATE "-lc" valkyria)

add_executable(test_gc_unit test/unit/test_gc.c ../testing/c/testing.c)
target_link_libraries(test_gc_unit PRIVATE "-lc" valkyria)

add_executable(test_gc_parallel_unit test/unit/test_gc_parallel.c ../testing/c/testing.c)
target_link_libraries(test_gc_parallel_unit PRIVATE "-lc" valkyria)

add_executable(test_large_str test/http/test_large_str.c ../testing/c/testing.c)
target_link_libraries(test_large_str PRIVATE "-lc" valkyria)

add_executable(test_parser_unit test/unit/test_parser.c ../testing/c/testing.c)
target_link_libraries(test_parser_unit PRIVATE "-lc" valkyria)

add_executable(test_memory_unit test/unit/test_memory.c ../testing/c/testing.c)
target_link_libraries(test_memory_unit PRIVATE "-lc" valkyria)

if(VALK_COVERAGE)
  add_executable(test_source_loc_unit test/unit/test_source_loc.c ../testing/c/testing.c)
  target_link_libraries(test_source_loc_unit PRIVATE "-lc" valkyria)
  target_compile_definitions(test_source_loc_unit PRIVATE VALK_COVERAGE=1)
  include_directories(test_source_loc_unit src/)
endif()

add_executable(test_aio_ssl_unit test/unit/test_aio_ssl.c ../testing/c/testing.c)
target_link_libraries(test_aio_ssl_unit PRIVATE "-lc" valkyria OpenSSL::SSL OpenSSL::Crypto)

add_executable(test_pressure test/unit/test_pressure.c ../testing/c/testing.c)
target_link_libraries(test_pressure PRIVATE "-lc" valkyria)

add_executable(test_conn_io test/unit/test_conn_io.c ../testing/c/testing.c)
target_link_libraries(test_conn_io PRIVATE "-lc" valkyria)

add_executable(test_aio_timer_unit test/unit/test_aio_timer.c ../testing/c/testing.c)
target_link_libraries(test_aio_timer_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_io_timer_ops_unit test/unit/test_io_timer_ops.c ../testing/c/testing.c)
target_link_libraries(test_io_timer_ops_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_thread_posix_unit test/unit/test_thread_posix.c ../testing/c/testing.c)
target_link_libraries(test_thread_posix_unit PRIVATE "-lc" valkyria)

add_executable(test_aio_async_unit test/unit/test_aio_async.c ../testing/c/testing.c)
target_link_libraries(test_aio_async_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

add_executable(test_aio_handle_diag test/aio/test_aio_handle_diag.c ../testing/c/testing.c)
target_link_libraries(test_aio_handle_diag PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# HTTP2/Streaming tests
add_executable(test_http2_streaming test/http/test_http2_streaming.c ../testing/c/testing.c)
target_link_libraries(test_http2_streaming PRIVATE "-lc" valkyria)

# Stream body integration tests (data flow through nghttp2)
add_executable(test_stream_body_integration test/http/test_stream_body_integration.c ../testing/c/testing.c)
target_link_libraries(test_stream_body_integration PRIVATE "-lc" valkyria)

# Parser error path tests
add_executable(test_parser_errors test/parser/test_parser_errors.c ../testing/c/testing.c)
target_link_libraries(test_parser_errors PRIVATE "-lc" valkyria)

# Concurrent metrics tests
add_executable(test_metrics_concurrent test/metrics/test_metrics_concurrent.c ../testing/c/testing.c)
target_link_libraries(test_metrics_concurrent PRIVATE "-lc" valkyria)

# Request context tests
add_executable(test_request_ctx_unit test/unit/test_request_ctx.c ../testing/c/testing.c)
target_link_libraries(test_request_ctx_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Context builtins tests (ctx/deadline, trace/id, etc.)
add_executable(test_ctx_builtins_unit test/unit/test_ctx_builtins.c ../testing/c/testing.c)
target_link_libraries(test_ctx_builtins_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# HTTP request builtins tests (req/method, req/path, req/headers, etc.)
add_executable(test_http_builtins_unit test/unit/test_http_builtins.c ../testing/c/testing.c)
target_link_libraries(test_http_builtins_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Chase-Lev deque tests (lock-free work-stealing data structure)
add_executable(test_chase_lev_unit test/unit/test_chase_lev.c ../testing/c/testing.c)
target_link_libraries(test_chase_lev_unit PRIVATE "-lc" valkyria)

# MPMC bounded queue tests (Vyukov multi-producer multi-consumer)
add_executable(test_mpmc_unit test/unit/test_mpmc.c ../testing/c/testing.c)
target_link_libraries(test_mpmc_unit PRIVATE "-lc" valkyria)

# Concurrent map tests (striped-lock global-env hash map)
add_executable(test_conc_map_unit test/unit/test_conc_map.c ../testing/c/testing.c)
target_link_libraries(test_conc_map_unit PRIVATE "-lc" valkyria)

# Task queue tests (async task execution via libuv event loop)
add_executable(test_task_queue_unit test/unit/test_task_queue.c ../testing/c/testing.c)
target_link_libraries(test_task_queue_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Stream body connection management tests
add_executable(test_stream_body_conn_unit test/unit/test_stream_body_conn.c ../testing/c/testing.c)
target_link_libraries(test_stream_body_conn_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Backpressure list tests (linked list operations for overload protection)
add_executable(test_backpressure_list_unit test/unit/test_backpressure_list.c ../testing/c/testing.c)
target_link_libraries(test_backpressure_list_unit PRIVATE "-lc" valkyria valk_test_fakes ${LIBUV_LIBRARIES})

# Connection FSM state machine tests
add_executable(test_conn_fsm_unit test/unit/test_conn_fsm.c ../testing/c/testing.c)
target_link_libraries(test_conn_fsm_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# Stream builtins tests (Lisp API for stream operations)
add_executable(test_stream_builtins_unit test/unit/test_stream_builtins.c ../testing/c/testing.c)
target_link_libraries(test_stream_builtins_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})

# HTTP/2 connection tests (write buffer, backpressure, alloc callbacks)
add_executable(test_http2_conn_unit test/unit/test_http2_conn.c ../testing/c/testing.c)
target_link_libraries(test_http2_conn_unit PRIVATE "-lc" valkyria valk_test_fakes ${LIBUV_LIBRARIES} nghttp2::nghttp2)

# HTTP/2 server tests (lifecycle, metrics, getters)
add_executable(test_http2_server_unit test/unit/test_http2_server.c ../testing/c/testing.c)
target_link_libraries(test_http2_server_unit PRIVATE "-lc" valkyria valk_test_fakes ${LIBUV_LIBRARIES})

# HTTP/2 session tests (callbacks, stream arenas, headers)
add_executable(test_http2_session_unit test/unit/test_http2_session.c ../testing/c/testing.c)
target_link_libraries(test_http2_session_unit PRIVATE "-lc" valkyria valk_test_fakes ${LIBUV_LIBRARIES} nghttp2::nghttp2 OpenSSL::SSL OpenSSL::Crypto)

# Connection admission tests (overload admission control)
add_executable(test_conn_admission_unit test/unit/test_conn_admission.c ../testing/c/testing.c)
target_link_libraries(test_conn_admission_unit PRIVATE "-lc" valkyria ${LIBUV_LIBRARIES})


add_executable(test_type_env test/parser/test_type_env.c ../testing/c/testing.c)
target_link_libraries(test_type_env PRIVATE "-lc" valkyria)

add_executable(test_type_infer test/parser/test_type_infer.c ../testing/c/testing.c)
target_link_libraries(test_type_infer PRIVATE "-lc" valkyria)

# LLVM backend tests
if(VALK_LLVM)
  add_executable(test_llvm_codegen test/lang/test_llvm_codegen.c ../testing/c/testing.c)
  target_link_libraries(test_llvm_codegen PRIVATE "-lc" valkyria valk_llvm ${LLVM_LIBS_LIST})
  target_include_directories(test_llvm_codegen SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
  target_compile_options(test_llvm_codegen PRIVATE -Wno-pedantic)
  include_directories(test_llvm_codegen src/)

  add_executable(test_vir test/lang/test_vir.c ../testing/c/testing.c)
  target_link_libraries(test_vir PRIVATE "-lc" valkyria valk_llvm ${LLVM_LIBS_LIST})
  target_include_directories(test_vir SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
  target_compile_options(test_vir PRIVATE -Wno-pedantic)
  include_directories(test_vir src/)

  add_executable(test_image_jit test/lang/test_image_jit.c ../testing/c/testing.c)
  target_link_libraries(test_image_jit PRIVATE "-lc" valkyria valk_llvm ${LLVM_LIBS_LIST})
  target_include_directories(test_image_jit SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
  target_compile_options(test_image_jit PRIVATE -Wno-pedantic)
  include_directories(test_image_jit src/)

  add_executable(test_jit_cache test/lang/test_jit_cache.c ../testing/c/testing.c)
  target_link_libraries(test_jit_cache PRIVATE "-lc" valkyria valk_llvm ${LLVM_LIBS_LIST})
  target_include_directories(test_jit_cache SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
  target_compile_options(test_jit_cache PRIVATE -Wno-pedantic)
  include_directories(test_jit_cache src/)

  add_executable(test_jit_numeric test/lang/test_jit_numeric.c ../testing/c/testing.c)
  target_link_libraries(test_jit_numeric PRIVATE "-lc" valkyria valk_llvm ${LLVM_LIBS_LIST})
  target_include_directories(test_jit_numeric SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
  target_compile_options(test_jit_numeric PRIVATE -Wno-pedantic)
  include_directories(test_jit_numeric src/)

  add_executable(bench_jit test/lang/bench_jit.c)
  target_link_libraries(bench_jit PRIVATE "-lc" valkyria valk_llvm ${LLVM_LIBS_LIST})
  target_include_directories(bench_jit SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
  target_compile_options(bench_jit PRIVATE -Wno-pedantic -O2)
  include_directories(bench_jit src/)
endif()

# Allocation + GC pause benchmarks. No LLVM needed.
add_executable(bench_alloc test/lang/bench_alloc.c)
target_link_libraries(bench_alloc PRIVATE "-lc" valkyria)
target_compile_options(bench_alloc PRIVATE -Wno-pedantic -O2)
include_directories(bench_alloc src/)

add_executable(bench_gc test/lang/bench_gc.c)
target_link_libraries(bench_gc PRIVATE "-lc" valkyria)
target_compile_options(bench_gc PRIVATE -Wno-pedantic -O2)
include_directories(bench_gc src/)

add_executable(bench_game test/lang/bench_game.c)
target_link_libraries(bench_game PRIVATE "-lc" valkyria)
target_compile_options(bench_game PRIVATE -Wno-pedantic -O2)
include_directories(bench_game src/)

