#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/log.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_log_level_enum_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_LOG_ERROR == 0, "ERROR should be 0");
  VALK_TEST_ASSERT(VALK_LOG_WARN == 1, "WARN should be 1");
  VALK_TEST_ASSERT(VALK_LOG_INFO == 2, "INFO should be 2");
  VALK_TEST_ASSERT(VALK_LOG_DEBUG == 3, "DEBUG should be 3");
  VALK_TEST_ASSERT(VALK_LOG_TRACE == 4, "TRACE should be 4");

  VALK_PASS();
}

void test_log_init_idempotent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_init();
  valk_log_level_e level1 = valk_log_get_level();
  valk_log_init();
  valk_log_level_e level2 = valk_log_get_level();

  VALK_TEST_ASSERT(level1 == level2, "Double init should not change level");

  VALK_PASS();
}

void test_log_set_level(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_ERROR);
  VALK_TEST_ASSERT(valk_log_get_level() == VALK_LOG_ERROR, "Level should be ERROR");

  valk_log_set_level(VALK_LOG_TRACE);
  VALK_TEST_ASSERT(valk_log_get_level() == VALK_LOG_TRACE, "Level should be TRACE");

  valk_log_set_level(VALK_LOG_WARN);
  VALK_TEST_ASSERT(valk_log_get_level() == VALK_LOG_WARN, "Level should be WARN");

  VALK_PASS();
}

void test_log_would_log_at_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_ERROR);

  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_ERROR) == 1, "Should log ERROR at ERROR level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_WARN) == 0, "Should not log WARN at ERROR level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_INFO) == 0, "Should not log INFO at ERROR level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_DEBUG) == 0, "Should not log DEBUG at ERROR level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_TRACE) == 0, "Should not log TRACE at ERROR level");

  VALK_PASS();
}

void test_log_would_log_at_warn(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_WARN);

  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_ERROR) == 1, "Should log ERROR at WARN level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_WARN) == 1, "Should log WARN at WARN level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_INFO) == 0, "Should not log INFO at WARN level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_DEBUG) == 0, "Should not log DEBUG at WARN level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_TRACE) == 0, "Should not log TRACE at WARN level");

  VALK_PASS();
}

void test_log_would_log_at_info(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_INFO);

  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_ERROR) == 1, "Should log ERROR at INFO level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_WARN) == 1, "Should log WARN at INFO level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_INFO) == 1, "Should log INFO at INFO level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_DEBUG) == 0, "Should not log DEBUG at INFO level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_TRACE) == 0, "Should not log TRACE at INFO level");

  VALK_PASS();
}

void test_log_would_log_at_debug(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_DEBUG);

  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_ERROR) == 1, "Should log ERROR at DEBUG level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_WARN) == 1, "Should log WARN at DEBUG level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_INFO) == 1, "Should log INFO at DEBUG level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_DEBUG) == 1, "Should log DEBUG at DEBUG level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_TRACE) == 0, "Should not log TRACE at DEBUG level");

  VALK_PASS();
}

void test_log_would_log_at_trace(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);

  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_ERROR) == 1, "Should log ERROR at TRACE level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_WARN) == 1, "Should log WARN at TRACE level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_INFO) == 1, "Should log INFO at TRACE level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_DEBUG) == 1, "Should log DEBUG at TRACE level");
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_TRACE) == 1, "Should log TRACE at TRACE level");

  VALK_PASS();
}

void test_log_function_does_not_crash(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  valk_log(VALK_LOG_ERROR, "test.c", 1, "test_func", "error message %d", 42);
  valk_log(VALK_LOG_WARN, "test.c", 2, "test_func", "warn message");
  valk_log(VALK_LOG_INFO, "test.c", 3, "test_func", "info message");
  valk_log(VALK_LOG_DEBUG, "test.c", 4, "test_func", "debug message");
  valk_log(VALK_LOG_TRACE, "test.c", 5, "test_func", "trace message");

  VALK_PASS();
}

void test_log_macros_do_not_crash(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  VALK_ERROR("error %d", 1);
  VALK_WARN("warn %d", 2);
  VALK_INFO("info %d", 3);
  VALK_DEBUG("debug %d", 4);
  VALK_TRACE("trace %d", 5);

  VALK_PASS();
}

void test_log_suppressed_messages(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_ERROR);
  VALK_TRACE("this should be suppressed");
  VALK_DEBUG("this should be suppressed");
  VALK_INFO("this should be suppressed");
  VALK_WARN("this should be suppressed");
  VALK_ERROR("this should be logged");

  VALK_PASS();
}

void test_log_get_level_calls_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_level_e level = valk_log_get_level();
  VALK_TEST_ASSERT(level >= VALK_LOG_ERROR && level <= VALK_LOG_TRACE, 
                   "Level should be valid enum value");

  VALK_PASS();
}

void test_log_would_log_calls_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  int result = valk_log_would_log(VALK_LOG_ERROR);
  VALK_TEST_ASSERT(result == 0 || result == 1, "Result should be boolean");

  VALK_PASS();
}

void test_log_level_transitions(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_ERROR);
  VALK_TEST_ASSERT(valk_log_get_level() == VALK_LOG_ERROR, "Level should be ERROR");

  valk_log_set_level(VALK_LOG_TRACE);
  VALK_TEST_ASSERT(valk_log_get_level() == VALK_LOG_TRACE, "Level should be TRACE");

  valk_log_set_level(VALK_LOG_INFO);
  VALK_TEST_ASSERT(valk_log_get_level() == VALK_LOG_INFO, "Level should be INFO");

  valk_log_set_level(VALK_LOG_DEBUG);
  VALK_TEST_ASSERT(valk_log_get_level() == VALK_LOG_DEBUG, "Level should be DEBUG");

  valk_log_set_level(VALK_LOG_WARN);
  VALK_TEST_ASSERT(valk_log_get_level() == VALK_LOG_WARN, "Level should be WARN");

  VALK_PASS();
}

void test_log_empty_format_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "");

  VALK_PASS();
}

void test_log_long_format_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  char long_msg[1024];
  memset(long_msg, 'A', sizeof(long_msg) - 1);
  long_msg[sizeof(long_msg) - 1] = '\0';

  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "%s", long_msg);

  VALK_PASS();
}

void test_log_multiple_format_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", 
           "int=%d str=%s ptr=%p float=%f", 42, "hello", (void*)0x1234, 3.14);

  VALK_PASS();
}

void test_log_all_levels_sequential(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_level_e levels[] = {VALK_LOG_ERROR, VALK_LOG_WARN, VALK_LOG_INFO, VALK_LOG_DEBUG, VALK_LOG_TRACE};
  for (size_t i = 0; i < sizeof(levels) / sizeof(levels[0]); i++) {
    valk_log_set_level(levels[i]);
    VALK_TEST_ASSERT(valk_log_get_level() == levels[i], "Level should match after set");
  }

  VALK_PASS();
}

void test_log_error_goes_to_stderr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_ERROR);
  valk_log(VALK_LOG_ERROR, "test.c", 1, "func", "error message");

  VALK_PASS();
}

void test_log_warn_goes_to_stderr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_WARN);
  valk_log(VALK_LOG_WARN, "test.c", 1, "func", "warn message");

  VALK_PASS();
}

void test_log_info_goes_to_stdout(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_INFO);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "info message");

  VALK_PASS();
}

void test_log_debug_goes_to_stdout(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_DEBUG);
  valk_log(VALK_LOG_DEBUG, "test.c", 1, "func", "debug message");

  VALK_PASS();
}

void test_log_trace_goes_to_stdout(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  valk_log(VALK_LOG_TRACE, "test.c", 1, "func", "trace message");

  VALK_PASS();
}

void test_log_various_format_specifiers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "%%d: %d", 42);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "%%s: %s", "string");
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "%%p: %p", (void*)0x1234);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "%%x: %x", 0xABCD);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "%%f: %f", 3.14159);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "%%ld: %ld", (long)123456789);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "%%zu: %zu", (size_t)1024);

  VALK_PASS();
}

void test_log_would_log_boundary_cases(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_ERROR);
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_ERROR) == 1, "Should log at boundary");

  valk_log_set_level(VALK_LOG_WARN);
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_WARN) == 1, "Should log at boundary");

  valk_log_set_level(VALK_LOG_INFO);
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_INFO) == 1, "Should log at boundary");

  valk_log_set_level(VALK_LOG_DEBUG);
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_DEBUG) == 1, "Should log at boundary");

  valk_log_set_level(VALK_LOG_TRACE);
  VALK_TEST_ASSERT(valk_log_would_log(VALK_LOG_TRACE) == 1, "Should log at boundary");

  VALK_PASS();
}

void test_log_skips_when_level_too_low(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_ERROR);

  valk_log(VALK_LOG_WARN, "test.c", 1, "func", "should not print");
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "should not print");
  valk_log(VALK_LOG_DEBUG, "test.c", 1, "func", "should not print");
  valk_log(VALK_LOG_TRACE, "test.c", 1, "func", "should not print");

  VALK_PASS();
}

void test_log_file_and_line_info(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  valk_log(VALK_LOG_INFO, "myfile.c", 12345, "my_function", "test message");

  VALK_PASS();
}

void test_log_null_in_format_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "before\\0after");

  VALK_PASS();
}

void test_log_lvl_name_coverage(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);

  valk_log(VALK_LOG_ERROR, "test.c", 1, "func", "error");
  valk_log(VALK_LOG_WARN, "test.c", 1, "func", "warn");
  valk_log(VALK_LOG_INFO, "test.c", 1, "func", "info");
  valk_log(VALK_LOG_DEBUG, "test.c", 1, "func", "debug");
  valk_log(VALK_LOG_TRACE, "test.c", 1, "func", "trace");

  VALK_PASS();
}

void test_log_invalid_level_handling(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_log_set_level(VALK_LOG_TRACE);
  valk_log((valk_log_level_e)99, "test.c", 1, "func", "invalid level message");

  VALK_PASS();
}

void test_log_set_all_levels(VALK_TEST_ARGS()) {
  VALK_TEST();

  for (int i = VALK_LOG_ERROR; i <= VALK_LOG_TRACE; i++) {
    valk_log_set_level((valk_log_level_e)i);
    VALK_TEST_ASSERT(valk_log_get_level() == (valk_log_level_e)i,
                     "Level should match after set");
  }

  VALK_PASS();
}

void test_log_level_from_string_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_log_level_from_string(NULL) == VALK_LOG_WARN,
                   "NULL should return WARN");

  VALK_PASS();
}

void test_log_level_from_string_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_log_level_from_string("error") == VALK_LOG_ERROR,
                   "error should return ERROR");
  VALK_TEST_ASSERT(valk_log_level_from_string("ERROR") == VALK_LOG_ERROR,
                   "ERROR should return ERROR (case insensitive)");
  VALK_TEST_ASSERT(valk_log_level_from_string("Error") == VALK_LOG_ERROR,
                   "Error should return ERROR (case insensitive)");

  VALK_PASS();
}

void test_log_level_from_string_warn(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_log_level_from_string("warn") == VALK_LOG_WARN,
                   "warn should return WARN");
  VALK_TEST_ASSERT(valk_log_level_from_string("WARN") == VALK_LOG_WARN,
                   "WARN should return WARN (case insensitive)");
  VALK_TEST_ASSERT(valk_log_level_from_string("warning") == VALK_LOG_WARN,
                   "warning should return WARN");
  VALK_TEST_ASSERT(valk_log_level_from_string("WARNING") == VALK_LOG_WARN,
                   "WARNING should return WARN (case insensitive)");
  VALK_TEST_ASSERT(valk_log_level_from_string("Warning") == VALK_LOG_WARN,
                   "Warning should return WARN (case insensitive)");

  VALK_PASS();
}

void test_log_level_from_string_info(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_log_level_from_string("info") == VALK_LOG_INFO,
                   "info should return INFO");
  VALK_TEST_ASSERT(valk_log_level_from_string("INFO") == VALK_LOG_INFO,
                   "INFO should return INFO (case insensitive)");
  VALK_TEST_ASSERT(valk_log_level_from_string("Info") == VALK_LOG_INFO,
                   "Info should return INFO (case insensitive)");

  VALK_PASS();
}

void test_log_level_from_string_debug(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_log_level_from_string("debug") == VALK_LOG_DEBUG,
                   "debug should return DEBUG");
  VALK_TEST_ASSERT(valk_log_level_from_string("DEBUG") == VALK_LOG_DEBUG,
                   "DEBUG should return DEBUG (case insensitive)");
  VALK_TEST_ASSERT(valk_log_level_from_string("Debug") == VALK_LOG_DEBUG,
                   "Debug should return DEBUG (case insensitive)");

  VALK_PASS();
}

void test_log_level_from_string_trace(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_log_level_from_string("trace") == VALK_LOG_TRACE,
                   "trace should return TRACE");
  VALK_TEST_ASSERT(valk_log_level_from_string("TRACE") == VALK_LOG_TRACE,
                   "TRACE should return TRACE (case insensitive)");
  VALK_TEST_ASSERT(valk_log_level_from_string("Trace") == VALK_LOG_TRACE,
                   "Trace should return TRACE (case insensitive)");

  VALK_PASS();
}

void test_log_level_from_string_invalid(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_log_level_from_string("invalid") == VALK_LOG_WARN,
                   "invalid should return WARN (default)");
  VALK_TEST_ASSERT(valk_log_level_from_string("") == VALK_LOG_WARN,
                   "empty string should return WARN (default)");
  VALK_TEST_ASSERT(valk_log_level_from_string("err") == VALK_LOG_WARN,
                   "partial match should return WARN (default)");
  VALK_TEST_ASSERT(valk_log_level_from_string("errors") == VALK_LOG_WARN,
                   "extra chars should return WARN (default)");
  VALK_TEST_ASSERT(valk_log_level_from_string("123") == VALK_LOG_WARN,
                   "numbers should return WARN (default)");

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_log_level_enum_values", test_log_level_enum_values);
  valk_testsuite_add_test(suite, "test_log_init_idempotent", test_log_init_idempotent);
  valk_testsuite_add_test(suite, "test_log_set_level", test_log_set_level);
  valk_testsuite_add_test(suite, "test_log_would_log_at_error", test_log_would_log_at_error);
  valk_testsuite_add_test(suite, "test_log_would_log_at_warn", test_log_would_log_at_warn);
  valk_testsuite_add_test(suite, "test_log_would_log_at_info", test_log_would_log_at_info);
  valk_testsuite_add_test(suite, "test_log_would_log_at_debug", test_log_would_log_at_debug);
  valk_testsuite_add_test(suite, "test_log_would_log_at_trace", test_log_would_log_at_trace);
  valk_testsuite_add_test(suite, "test_log_function_does_not_crash", test_log_function_does_not_crash);
  valk_testsuite_add_test(suite, "test_log_macros_do_not_crash", test_log_macros_do_not_crash);
  valk_testsuite_add_test(suite, "test_log_suppressed_messages", test_log_suppressed_messages);
  valk_testsuite_add_test(suite, "test_log_get_level_calls_init", test_log_get_level_calls_init);
  valk_testsuite_add_test(suite, "test_log_would_log_calls_init", test_log_would_log_calls_init);
  valk_testsuite_add_test(suite, "test_log_level_transitions", test_log_level_transitions);
  valk_testsuite_add_test(suite, "test_log_empty_format_string", test_log_empty_format_string);
  valk_testsuite_add_test(suite, "test_log_long_format_string", test_log_long_format_string);
  valk_testsuite_add_test(suite, "test_log_multiple_format_args", test_log_multiple_format_args);
  valk_testsuite_add_test(suite, "test_log_all_levels_sequential", test_log_all_levels_sequential);
  valk_testsuite_add_test(suite, "test_log_error_goes_to_stderr", test_log_error_goes_to_stderr);
  valk_testsuite_add_test(suite, "test_log_warn_goes_to_stderr", test_log_warn_goes_to_stderr);
  valk_testsuite_add_test(suite, "test_log_info_goes_to_stdout", test_log_info_goes_to_stdout);
  valk_testsuite_add_test(suite, "test_log_debug_goes_to_stdout", test_log_debug_goes_to_stdout);
  valk_testsuite_add_test(suite, "test_log_trace_goes_to_stdout", test_log_trace_goes_to_stdout);
  valk_testsuite_add_test(suite, "test_log_various_format_specifiers", test_log_various_format_specifiers);
  valk_testsuite_add_test(suite, "test_log_would_log_boundary_cases", test_log_would_log_boundary_cases);
  valk_testsuite_add_test(suite, "test_log_skips_when_level_too_low", test_log_skips_when_level_too_low);
  valk_testsuite_add_test(suite, "test_log_file_and_line_info", test_log_file_and_line_info);
  valk_testsuite_add_test(suite, "test_log_null_in_format_string", test_log_null_in_format_string);
  valk_testsuite_add_test(suite, "test_log_lvl_name_coverage", test_log_lvl_name_coverage);
  valk_testsuite_add_test(suite, "test_log_invalid_level_handling", test_log_invalid_level_handling);
  valk_testsuite_add_test(suite, "test_log_set_all_levels", test_log_set_all_levels);
  valk_testsuite_add_test(suite, "test_log_level_from_string_null", test_log_level_from_string_null);
  valk_testsuite_add_test(suite, "test_log_level_from_string_error", test_log_level_from_string_error);
  valk_testsuite_add_test(suite, "test_log_level_from_string_warn", test_log_level_from_string_warn);
  valk_testsuite_add_test(suite, "test_log_level_from_string_info", test_log_level_from_string_info);
  valk_testsuite_add_test(suite, "test_log_level_from_string_debug", test_log_level_from_string_debug);
  valk_testsuite_add_test(suite, "test_log_level_from_string_trace", test_log_level_from_string_trace);
  valk_testsuite_add_test(suite, "test_log_level_from_string_invalid", test_log_level_from_string_invalid);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
