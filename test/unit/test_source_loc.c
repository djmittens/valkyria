#include "../testing.h"
#include "../../src/memory.h"

#ifdef VALK_COVERAGE
#include "../../src/source_loc.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_source_register_file_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  uint16_t id = valk_source_register_file(NULL);
  VALK_TEST_ASSERT(id == 0, "NULL filename should return 0");

  VALK_PASS();
}

void test_source_register_file_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id = valk_source_register_file("test_file.valk");
  VALK_TEST_ASSERT(id > 0, "Should return non-zero id");

  VALK_PASS();
}

void test_source_register_file_dedup(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id1 = valk_source_register_file("same_file.valk");
  uint16_t id2 = valk_source_register_file("same_file.valk");
  VALK_TEST_ASSERT(id1 == id2, "Same filename should return same id");

  VALK_PASS();
}

void test_source_register_file_different(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id1 = valk_source_register_file("file1.valk");
  uint16_t id2 = valk_source_register_file("file2.valk");
  VALK_TEST_ASSERT(id1 != id2, "Different filenames should return different ids");

  VALK_PASS();
}

void test_source_get_filename_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id = valk_source_register_file("lookup_test.valk");
  const char *filename = valk_source_get_filename(id);
  VALK_TEST_ASSERT(filename != NULL, "Should return non-NULL filename");
  VALK_TEST_ASSERT(strcmp(filename, "lookup_test.valk") == 0, "Filename should match");

  VALK_PASS();
}

void test_source_get_filename_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *filename = valk_source_get_filename(0);
  VALK_TEST_ASSERT(filename == NULL, "file_id 0 should return NULL");

  VALK_PASS();
}

void test_source_get_filename_invalid(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  const char *filename = valk_source_get_filename(9999);
  VALK_TEST_ASSERT(filename == NULL, "Invalid file_id should return NULL");

  VALK_PASS();
}

void test_source_registry_reset(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id1 = valk_source_register_file("reset_test.valk");
  VALK_TEST_ASSERT(id1 > 0, "First registration should succeed");

  valk_source_registry_reset();

  const char *filename = valk_source_get_filename(id1);
  VALK_TEST_ASSERT(filename == NULL, "After reset, old id should return NULL");

  uint16_t id2 = valk_source_register_file("reset_test.valk");
  VALK_TEST_ASSERT(id2 == 1, "After reset, first id should be 1 again");

  VALK_PASS();
}

void test_source_register_many_files(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t ids[100];
  for (int i = 0; i < 100; i++) {
    char filename[64];
    snprintf(filename, sizeof(filename), "file_%d.valk", i);
    ids[i] = valk_source_register_file(filename);
    VALK_TEST_ASSERT(ids[i] > 0, "Should register file %d", i);
  }

  for (int i = 0; i < 100; i++) {
    for (int j = i + 1; j < 100; j++) {
      VALK_TEST_ASSERT(ids[i] != ids[j], "IDs should be unique");
    }
  }

  VALK_PASS();
}

void test_source_register_empty_filename(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id = valk_source_register_file("");
  VALK_TEST_ASSERT(id > 0, "Empty filename should still get registered");

  const char *filename = valk_source_get_filename(id);
  VALK_TEST_ASSERT(filename != NULL, "Should be able to retrieve empty filename");
  VALK_TEST_ASSERT(strlen(filename) == 0, "Retrieved filename should be empty");

  VALK_PASS();
}

void test_source_register_long_filename(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  char long_name[512];
  memset(long_name, 'x', sizeof(long_name) - 6);
  strcpy(long_name + sizeof(long_name) - 6, ".valk");

  uint16_t id = valk_source_register_file(long_name);
  VALK_TEST_ASSERT(id > 0, "Long filename should get registered");

  const char *filename = valk_source_get_filename(id);
  VALK_TEST_ASSERT(filename != NULL, "Should be able to retrieve long filename");
  VALK_TEST_ASSERT(strcmp(filename, long_name) == 0, "Long filename should match");

  VALK_PASS();
}

void test_source_register_multiple_reset(VALK_TEST_ARGS()) {
  VALK_TEST();

  for (int i = 0; i < 5; i++) {
    valk_source_registry_reset();
    uint16_t id = valk_source_register_file("multi_reset.valk");
    VALK_TEST_ASSERT(id == 1, "After each reset, first id should be 1");
  }

  VALK_PASS();
}

void test_source_register_special_chars(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id = valk_source_register_file("/path/to/file with spaces.valk");
  VALK_TEST_ASSERT(id > 0, "Should register filename with spaces");

  const char *filename = valk_source_get_filename(id);
  VALK_TEST_ASSERT(strcmp(filename, "/path/to/file with spaces.valk") == 0,
                   "Should preserve special chars");

  VALK_PASS();
}

void test_source_ids_sequential(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id1 = valk_source_register_file("seq1.valk");
  uint16_t id2 = valk_source_register_file("seq2.valk");
  uint16_t id3 = valk_source_register_file("seq3.valk");

  VALK_TEST_ASSERT(id2 == id1 + 1, "IDs should be sequential");
  VALK_TEST_ASSERT(id3 == id2 + 1, "IDs should be sequential");

  VALK_PASS();
}

void test_source_register_dedup_interleaved(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id_a1 = valk_source_register_file("a.valk");
  uint16_t id_b = valk_source_register_file("b.valk");
  uint16_t id_a2 = valk_source_register_file("a.valk");
  uint16_t id_c = valk_source_register_file("c.valk");
  uint16_t id_b2 = valk_source_register_file("b.valk");

  VALK_TEST_ASSERT(id_a1 == id_a2, "a.valk should have same id");
  VALK_TEST_ASSERT(id_b == id_b2, "b.valk should have same id");
  VALK_TEST_ASSERT(id_a1 != id_b, "a and b should have different ids");
  VALK_TEST_ASSERT(id_b != id_c, "b and c should have different ids");

  VALK_PASS();
}

static void *concurrent_register_thread(void *arg) {
  int thread_id = *(int *)arg;
  char filename[64];
  snprintf(filename, sizeof(filename), "thread_%d.valk", thread_id);
  
  for (int i = 0; i < 100; i++) {
    valk_source_register_file(filename);
  }
  return NULL;
}

void test_source_concurrent_registration(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  pthread_t threads[4];
  int thread_ids[4] = {0, 1, 2, 3};

  for (int i = 0; i < 4; i++) {
    pthread_create(&threads[i], NULL, concurrent_register_thread, &thread_ids[i]);
  }

  for (int i = 0; i < 4; i++) {
    pthread_join(threads[i], NULL);
  }

  for (int i = 0; i < 4; i++) {
    char filename[64];
    snprintf(filename, sizeof(filename), "thread_%d.valk", i);
    uint16_t id = valk_source_register_file(filename);
    const char *retrieved = valk_source_get_filename(id);
    VALK_TEST_ASSERT(retrieved != NULL, "Should retrieve thread %d filename", i);
    VALK_TEST_ASSERT(strcmp(retrieved, filename) == 0, "Filename should match");
  }

  VALK_PASS();
}

static void *concurrent_get_thread(void *arg) {
  uint16_t *file_id = (uint16_t *)arg;
  for (int i = 0; i < 1000; i++) {
    const char *filename = valk_source_get_filename(*file_id);
    (void)filename;
  }
  return NULL;
}

void test_source_concurrent_get(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();
  uint16_t id = valk_source_register_file("concurrent_get.valk");

  pthread_t threads[4];
  for (int i = 0; i < 4; i++) {
    pthread_create(&threads[i], NULL, concurrent_get_thread, &id);
  }

  for (int i = 0; i < 4; i++) {
    pthread_join(threads[i], NULL);
  }

  const char *filename = valk_source_get_filename(id);
  VALK_TEST_ASSERT(filename != NULL, "Filename should still be retrievable");
  VALK_TEST_ASSERT(strcmp(filename, "concurrent_get.valk") == 0, "Filename should be correct");

  VALK_PASS();
}

void test_source_reset_after_concurrent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  for (int i = 0; i < 50; i++) {
    char filename[64];
    snprintf(filename, sizeof(filename), "file_%d.valk", i);
    valk_source_register_file(filename);
  }

  valk_source_registry_reset();

  for (int i = 1; i <= 50; i++) {
    const char *filename = valk_source_get_filename(i);
    VALK_TEST_ASSERT(filename == NULL, "After reset, id %d should return NULL", i);
  }

  VALK_PASS();
}

void test_source_boundary_file_id(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  const char *filename = valk_source_get_filename(65535);
  VALK_TEST_ASSERT(filename == NULL, "High file_id should return NULL");

  VALK_PASS();
}

void test_source_first_id_is_one(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id = valk_source_register_file("first.valk");
  VALK_TEST_ASSERT(id == 1, "First registered file should have id 1");

  VALK_PASS();
}

void test_source_unicode_filename(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id = valk_source_register_file("test_\xC3\xA9\xC3\xA0.valk");
  VALK_TEST_ASSERT(id > 0, "Unicode filename should register");

  const char *filename = valk_source_get_filename(id);
  VALK_TEST_ASSERT(filename != NULL, "Should retrieve unicode filename");
  VALK_TEST_ASSERT(strstr(filename, ".valk") != NULL, "Filename should end with .valk");

  VALK_PASS();
}

void test_source_path_separators(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id1 = valk_source_register_file("/usr/local/lib/test.valk");
  uint16_t id2 = valk_source_register_file("C:\\Users\\test\\test.valk");
  uint16_t id3 = valk_source_register_file("./relative/path.valk");

  VALK_TEST_ASSERT(id1 > 0, "Unix path should register");
  VALK_TEST_ASSERT(id2 > 0, "Windows path should register");
  VALK_TEST_ASSERT(id3 > 0, "Relative path should register");

  VALK_PASS();
}

void test_source_double_registration_returns_same(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id1 = valk_source_register_file("double.valk");
  uint16_t id2 = valk_source_register_file("double.valk");
  uint16_t id3 = valk_source_register_file("double.valk");

  VALK_TEST_ASSERT(id1 == id2, "Second registration should return same id");
  VALK_TEST_ASSERT(id2 == id3, "Third registration should return same id");

  VALK_PASS();
}

void test_source_get_filename_after_many_registrations(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t target_id = 0;
  for (int i = 0; i < 50; i++) {
    char filename[64];
    snprintf(filename, sizeof(filename), "file_%d.valk", i);
    uint16_t id = valk_source_register_file(filename);
    if (i == 25) target_id = id;
  }

  char expected[64];
  snprintf(expected, sizeof(expected), "file_25.valk");
  const char *actual = valk_source_get_filename(target_id);
  
  VALK_TEST_ASSERT(actual != NULL, "Should retrieve file_25.valk");
  VALK_TEST_ASSERT(strcmp(actual, expected) == 0, "Filename should match");

  VALK_PASS();
}

void test_source_register_file_dedup_returns_early(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  uint16_t id1 = valk_source_register_file("early_return_test.valk");
  uint16_t id2 = valk_source_register_file("early_return_test.valk");
  
  VALK_TEST_ASSERT(id1 == id2, "Should return same id (early return path)");
  VALK_TEST_ASSERT(id1 == 1, "First id should be 1");

  VALK_PASS();
}

void test_source_reset_frees_memory(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_source_registry_reset();

  for (int i = 0; i < 10; i++) {
    char filename[64];
    snprintf(filename, sizeof(filename), "to_free_%d.valk", i);
    valk_source_register_file(filename);
  }

  valk_source_registry_reset();

  for (int i = 1; i <= 10; i++) {
    const char *filename = valk_source_get_filename(i);
    VALK_TEST_ASSERT(filename == NULL, "After reset, id %d should be NULL", i);
  }

  uint16_t new_id = valk_source_register_file("after_reset.valk");
  VALK_TEST_ASSERT(new_id == 1, "After reset, new file should get id 1");

  VALK_PASS();
}

#else

void test_source_loc_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("source_loc tests require VALK_COVERAGE");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_COVERAGE
  valk_testsuite_add_test(suite, "test_source_register_file_null", test_source_register_file_null);
  valk_testsuite_add_test(suite, "test_source_register_file_basic", test_source_register_file_basic);
  valk_testsuite_add_test(suite, "test_source_register_file_dedup", test_source_register_file_dedup);
  valk_testsuite_add_test(suite, "test_source_register_file_different", test_source_register_file_different);
  valk_testsuite_add_test(suite, "test_source_get_filename_basic", test_source_get_filename_basic);
  valk_testsuite_add_test(suite, "test_source_get_filename_zero", test_source_get_filename_zero);
  valk_testsuite_add_test(suite, "test_source_get_filename_invalid", test_source_get_filename_invalid);
  valk_testsuite_add_test(suite, "test_source_registry_reset", test_source_registry_reset);
  valk_testsuite_add_test(suite, "test_source_register_many_files", test_source_register_many_files);
  valk_testsuite_add_test(suite, "test_source_register_empty_filename", test_source_register_empty_filename);
  valk_testsuite_add_test(suite, "test_source_register_long_filename", test_source_register_long_filename);
  valk_testsuite_add_test(suite, "test_source_register_multiple_reset", test_source_register_multiple_reset);
  valk_testsuite_add_test(suite, "test_source_register_special_chars", test_source_register_special_chars);
  valk_testsuite_add_test(suite, "test_source_ids_sequential", test_source_ids_sequential);
  valk_testsuite_add_test(suite, "test_source_register_dedup_interleaved", test_source_register_dedup_interleaved);
  valk_testsuite_add_test(suite, "test_source_concurrent_registration", test_source_concurrent_registration);
  valk_testsuite_add_test(suite, "test_source_concurrent_get", test_source_concurrent_get);
  valk_testsuite_add_test(suite, "test_source_reset_after_concurrent", test_source_reset_after_concurrent);
  valk_testsuite_add_test(suite, "test_source_boundary_file_id", test_source_boundary_file_id);
  valk_testsuite_add_test(suite, "test_source_first_id_is_one", test_source_first_id_is_one);
  valk_testsuite_add_test(suite, "test_source_unicode_filename", test_source_unicode_filename);
  valk_testsuite_add_test(suite, "test_source_path_separators", test_source_path_separators);
  valk_testsuite_add_test(suite, "test_source_double_registration_returns_same", test_source_double_registration_returns_same);
  valk_testsuite_add_test(suite, "test_source_get_filename_after_many_registrations", test_source_get_filename_after_many_registrations);
  valk_testsuite_add_test(suite, "test_source_register_file_dedup_returns_early", test_source_register_file_dedup_returns_early);
  valk_testsuite_add_test(suite, "test_source_reset_frees_memory", test_source_reset_frees_memory);
#else
  valk_testsuite_add_test(suite, "test_source_loc_disabled", test_source_loc_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
