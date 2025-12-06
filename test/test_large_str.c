// Test large string concatenation (2MB+)
// Directly tests the valk_builtin_str fix for dynamic allocation

#include "common.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

#include <string.h>

void test_2mb_string_concat(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Initialize memory and GC
  valk_gc_init();
  valk_memory_init(1024 * 1024 * 16);  // 16MB arena

  // Create a 1KB string
  char kb_buf[1025];
  for (int i = 0; i < 1024; i++) {
    kb_buf[i] = 'A' + (i % 26);
  }
  kb_buf[1024] = '\0';

  valk_lval_t* kb = valk_lval_str(kb_buf);
  VALK_TEST_ASSERT(strlen(kb->str) == 1024, "1KB string should be 1024 bytes");

  // Build 4KB by concatenating 4 x 1KB
  valk_lval_t* args4 = valk_lval_sexpr();
  for (int i = 0; i < 4; i++) {
    valk_lval_list_append(args4, valk_lval_str(kb_buf));
  }
  valk_lval_t* kb4 = valk_builtin_str(NULL, args4);
  VALK_TEST_ASSERT(LVAL_TYPE(kb4) == LVAL_STR, "Result should be string, got %s",
                   valk_ltype_name(LVAL_TYPE(kb4)));
  VALK_TEST_ASSERT(strlen(kb4->str) == 4096, "4KB string should be 4096 bytes, got %zu",
                   strlen(kb4->str));

  // Build 64KB by concatenating 16 x 4KB
  valk_lval_t* args64 = valk_lval_sexpr();
  for (int i = 0; i < 16; i++) {
    valk_lval_list_append(args64, valk_lval_str(kb4->str));
  }
  valk_lval_t* kb64 = valk_builtin_str(NULL, args64);
  VALK_TEST_ASSERT(LVAL_TYPE(kb64) == LVAL_STR, "Result should be string");
  VALK_TEST_ASSERT(strlen(kb64->str) == 65536, "64KB string should be 65536 bytes, got %zu",
                   strlen(kb64->str));

  // Build 256KB by concatenating 4 x 64KB (this would have crashed with old 64KB limit!)
  valk_lval_t* args256 = valk_lval_sexpr();
  for (int i = 0; i < 4; i++) {
    valk_lval_list_append(args256, valk_lval_str(kb64->str));
  }
  valk_lval_t* kb256 = valk_builtin_str(NULL, args256);
  VALK_TEST_ASSERT(LVAL_TYPE(kb256) == LVAL_STR, "Result should be string");
  VALK_TEST_ASSERT(strlen(kb256->str) == 262144, "256KB string should be 262144 bytes, got %zu",
                   strlen(kb256->str));

  // Build 1MB by concatenating 4 x 256KB
  valk_lval_t* args1mb = valk_lval_sexpr();
  for (int i = 0; i < 4; i++) {
    valk_lval_list_append(args1mb, valk_lval_str(kb256->str));
  }
  valk_lval_t* mb1 = valk_builtin_str(NULL, args1mb);
  VALK_TEST_ASSERT(LVAL_TYPE(mb1) == LVAL_STR, "Result should be string");
  VALK_TEST_ASSERT(strlen(mb1->str) == 1048576, "1MB string should be 1048576 bytes, got %zu",
                   strlen(mb1->str));

  // Build 2MB by concatenating 2 x 1MB
  valk_lval_t* args2mb = valk_lval_sexpr();
  valk_lval_list_append(args2mb, valk_lval_str(mb1->str));
  valk_lval_list_append(args2mb, valk_lval_str(mb1->str));
  valk_lval_t* mb2 = valk_builtin_str(NULL, args2mb);
  VALK_TEST_ASSERT(LVAL_TYPE(mb2) == LVAL_STR, "Result should be string");
  VALK_TEST_ASSERT(strlen(mb2->str) == 2097152, "2MB string should be 2097152 bytes, got %zu",
                   strlen(mb2->str));

  printf("SUCCESS: Created 2MB string (%zu bytes)\n", strlen(mb2->str));

  valk_gc_deinit();
  valk_memory_deinit();

  VALK_PASS();
}

int main(int argc, char** argv) {
  VALK_TEST_MAIN_START();

  VALK_RUN_TEST(test_2mb_string_concat);

  VALK_TEST_MAIN_END();
}
