#include "../testing.h"
#include "../../src/lsp/lsp_db.h"
#include "../../src/lsp/lsp_types.h"
#include "../../src/memory.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static const char *db_path = "/tmp/test_symdb.sqlite";

static void cleanup(void) { unlink(db_path); }

void test_symdb_open_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);
  VALK_TEST_ASSERT(db != NULL, "should open db");

  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_file_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  VALK_TEST_ASSERT(valk_symdb_file_stale(db, "/test.valk", 0, 100, "abc123"),
                   "new file should be stale");

  symdb_file_id fid = valk_symdb_upsert_file(db, "/test.valk", 0, 100, "abc123");
  VALK_TEST_ASSERT(fid >= 0, "upsert should return valid id");

  VALK_TEST_ASSERT(!valk_symdb_file_stale(db, "/test.valk", 0, 100, "abc123"),
                   "same hash should not be stale");

  VALK_TEST_ASSERT(valk_symdb_file_stale(db, "/test.valk", 0, 100, "changed"),
                   "different hash should be stale");

  symdb_file_id fid2 = valk_symdb_file_id(db, "/test.valk");
  VALK_TEST_ASSERT(fid == fid2, "file_id lookup should match");

  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_type_interning(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  valk_type_t *num = ty_num(&arena);
  symdb_type_id id1 = valk_symdb_intern_type(db, num);
  symdb_type_id id2 = valk_symdb_intern_type(db, num);
  VALK_TEST_ASSERT(id1 == id2, "same type should get same id");

  valk_type_t *str = ty_str(&arena);
  symdb_type_id id3 = valk_symdb_intern_type(db, str);
  VALK_TEST_ASSERT(id1 != id3, "different types should get different ids");

  char *display = valk_symdb_type_display(db, id1);
  VALK_TEST_ASSERT(display != NULL, "display should be non-null");
  VALK_TEST_ASSERT(strcmp(display, "Num") == 0, "display should be Num");
  free(display);

  int kind = valk_symdb_type_kind(db, id1);
  VALK_TEST_ASSERT(kind == TY_NUM, "kind should be TY_NUM");

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_compound_type_dedup(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  valk_type_t *list_str1 = ty_list(&arena, ty_str(&arena));
  valk_type_t *list_str2 = ty_list(&arena, ty_str(&arena));
  symdb_type_id a = valk_symdb_intern_type(db, list_str1);
  symdb_type_id b = valk_symdb_intern_type(db, list_str2);
  VALK_TEST_ASSERT(a == b, "List(Str) should be deduplicated");

  valk_type_t *list_num = ty_list(&arena, ty_num(&arena));
  symdb_type_id c = valk_symdb_intern_type(db, list_num);
  VALK_TEST_ASSERT(a != c, "List(Str) != List(Num)");

  valk_type_t *params[] = {ty_num(&arena), ty_str(&arena)};
  valk_type_t *fun1 = ty_fun(&arena, params, 2, ty_num(&arena), false);
  valk_type_t *fun2 = ty_fun(&arena, params, 2, ty_num(&arena), false);
  symdb_type_id d = valk_symdb_intern_type(db, fun1);
  symdb_type_id e = valk_symdb_intern_type(db, fun2);
  VALK_TEST_ASSERT(d == e, "identical function types should be deduplicated");

  char *display = valk_symdb_type_display(db, d);
  VALK_TEST_ASSERT(display != NULL, "fun display should not be null");
  VALK_TEST_ASSERT(strstr(display, "Num") != NULL, "fun display should contain Num");
  free(display);

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_symbols_and_refs(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  symdb_file_id fid = valk_symdb_upsert_file(db, "/test.valk", 0, 100, "hash1");
  symdb_type_id tid = valk_symdb_intern_type(db, ty_num(&arena));

  symdb_sym_id sid = valk_symdb_add_symbol(db, "add", fid,
                                           0, 5, 0, 8,
                                           SYMKIND_FUNCTION, tid, -1, true);
  VALK_TEST_ASSERT(sid > 0, "should create symbol");

  symdb_sym_id found = valk_symdb_find_symbol(db, "add", fid);
  VALK_TEST_ASSERT(found == sid, "should find the symbol");

  valk_symdb_add_ref(db, sid, fid, 3, 1, REF_CALL);
  valk_symdb_add_ref(db, sid, fid, 5, 1, REF_CALL);
  valk_symdb_add_ref(db, sid, fid, 7, 1, REF_CALL);

  symdb_ref_result_t *refs = NULL;
  size_t ref_count = valk_symdb_find_refs(db, sid, &refs);
  VALK_TEST_ASSERT(ref_count == 3, "should find 3 refs");
  VALK_TEST_ASSERT(refs[0].line == 3, "first ref at line 3");
  VALK_TEST_ASSERT(refs[1].line == 5, "second ref at line 5");
  VALK_TEST_ASSERT(refs[2].line == 7, "third ref at line 7");
  free(refs);

  symdb_sym_result_t *syms = NULL;
  size_t sym_count = valk_symdb_file_symbols(db, fid, &syms);
  VALK_TEST_ASSERT(sym_count == 1, "should find 1 symbol");
  VALK_TEST_ASSERT(strcmp(syms[0].name, "add") == 0, "symbol name should be 'add'");
  free(syms[0].name);
  free(syms);

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_invalidate_file(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  symdb_file_id fid = valk_symdb_upsert_file(db, "/test.valk", 0, 100, "hash1");
  symdb_type_id tid = valk_symdb_intern_type(db, ty_num(&arena));

  valk_symdb_add_symbol(db, "foo", fid, 0, 0, 0, 3,
                        SYMKIND_FUNCTION, tid, -1, true);

  symdb_sym_result_t *syms = NULL;
  size_t n = valk_symdb_file_symbols(db, fid, &syms);
  VALK_TEST_ASSERT(n == 1, "should have 1 symbol before invalidation");
  free(syms[0].name);
  free(syms);

  valk_symdb_invalidate_file(db, fid);

  n = valk_symdb_file_symbols(db, fid, &syms);
  VALK_TEST_ASSERT(n == 0, "should have 0 symbols after invalidation");
  free(syms);

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_summary(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  symdb_file_id fid = valk_symdb_upsert_file(db, "/a.valk", 0, 50, "h1");
  symdb_type_id tid = valk_symdb_intern_type(db, ty_num(&arena));
  symdb_sym_id sid = valk_symdb_add_symbol(db, "x", fid, 0, 0, 0, 1,
                                           SYMKIND_VARIABLE, tid, -1, true);
  valk_symdb_add_ref(db, sid, fid, 1, 0, REF_READ);

  symdb_summary_t sum = valk_symdb_summary(db);
  VALK_TEST_ASSERT(sum.file_count == 1, "1 file");
  VALK_TEST_ASSERT(sum.symbol_count == 1, "1 symbol");
  VALK_TEST_ASSERT(sum.type_count >= 1, "at least 1 type");
  VALK_TEST_ASSERT(sum.ref_count == 1, "1 ref");

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_hotspots(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  symdb_file_id fid = valk_symdb_upsert_file(db, "/a.valk", 0, 50, "h1");
  symdb_type_id tid = valk_symdb_intern_type(db, ty_num(&arena));

  symdb_sym_id hot = valk_symdb_add_symbol(db, "hot-fn", fid, 0, 0, 0, 6,
                                           SYMKIND_FUNCTION, tid, -1, true);
  symdb_sym_id cold = valk_symdb_add_symbol(db, "cold-fn", fid, 1, 0, 1, 7,
                                            SYMKIND_FUNCTION, tid, -1, true);

  for (int i = 0; i < 10; i++)
    valk_symdb_add_ref(db, hot, fid, i + 2, 0, REF_CALL);
  valk_symdb_add_ref(db, cold, fid, 20, 0, REF_CALL);

  symdb_stat_result_t result = valk_symdb_hotspots(db, 10);
  VALK_TEST_ASSERT(result.count >= 2, "should have at least 2 hotspot entries");
  VALK_TEST_ASSERT(strcmp(result.rows[0].name, "hot-fn") == 0,
                   "hottest symbol should be hot-fn");
  VALK_TEST_ASSERT(result.rows[0].count == 10, "hot-fn should have 10 refs");
  symdb_stat_result_free(&result);

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_dead_code(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  symdb_file_id fid = valk_symdb_upsert_file(db, "/a.valk", 0, 50, "h1");
  symdb_type_id tid = valk_symdb_intern_type(db, ty_num(&arena));

  symdb_sym_id used = valk_symdb_add_symbol(db, "used", fid, 0, 0, 0, 4,
                                            SYMKIND_FUNCTION, tid, -1, true);
  valk_symdb_add_symbol(db, "unused", fid, 1, 0, 1, 6,
                        SYMKIND_FUNCTION, tid, -1, true);

  valk_symdb_add_ref(db, used, fid, 5, 0, REF_CALL);

  symdb_stat_result_t result = valk_symdb_dead_code(db, 10);
  VALK_TEST_ASSERT(result.count == 1, "should find 1 dead code entry");
  VALK_TEST_ASSERT(strcmp(result.rows[0].name, "unused") == 0,
                   "dead code should be 'unused'");
  symdb_stat_result_free(&result);

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_type_popularity(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  symdb_file_id fid = valk_symdb_upsert_file(db, "/a.valk", 0, 50, "h1");
  symdb_type_id num_id = valk_symdb_intern_type(db, ty_num(&arena));
  symdb_type_id str_id = valk_symdb_intern_type(db, ty_str(&arena));

  valk_symdb_add_symbol(db, "a", fid, 0, 0, 0, 1,
                        SYMKIND_VARIABLE, num_id, -1, true);
  valk_symdb_add_symbol(db, "b", fid, 1, 0, 1, 1,
                        SYMKIND_VARIABLE, num_id, -1, true);
  valk_symdb_add_symbol(db, "c", fid, 2, 0, 2, 1,
                        SYMKIND_VARIABLE, str_id, -1, true);

  symdb_type_stat_result_t result = valk_symdb_type_popularity(db, 10);
  VALK_TEST_ASSERT(result.count >= 2, "should have at least 2 type entries");
  VALK_TEST_ASSERT(strcmp(result.rows[0].display, "Num") == 0,
                   "most popular should be Num");
  VALK_TEST_ASSERT(result.rows[0].count == 2, "Num should have count 2");
  symdb_type_stat_result_free(&result);

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_content_hash(VALK_TEST_ARGS()) {
  VALK_TEST();

  char h1[32], h2[32], h3[32];
  valk_symdb_content_hash("hello", 5, h1, sizeof(h1));
  valk_symdb_content_hash("hello", 5, h2, sizeof(h2));
  valk_symdb_content_hash("world", 5, h3, sizeof(h3));

  VALK_TEST_ASSERT(strcmp(h1, h2) == 0, "same content same hash");
  VALK_TEST_ASSERT(strcmp(h1, h3) != 0, "different content different hash");

  VALK_PASS();
}

void test_symdb_scopes(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  symdb_file_id fid = valk_symdb_upsert_file(db, "/test.valk", 0, 100, "h1");

  symdb_scope_id outer = valk_symdb_add_scope(db, -1, fid, 0, 0, 10, 0);
  VALK_TEST_ASSERT(outer > 0, "should create outer scope");

  symdb_scope_id inner = valk_symdb_add_scope(db, outer, fid, 2, 0, 8, 0);
  VALK_TEST_ASSERT(inner > outer, "inner scope should have different id");

  symdb_summary_t sum = valk_symdb_summary(db);
  VALK_TEST_ASSERT(sum.scope_count == 2, "should have 2 scopes");

  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_type_var_normalization(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t a1, a2;
  type_arena_init(&a1);
  type_arena_init(&a2);

  valk_type_t *v1 = ty_var(&a1);
  valk_type_t *v2 = ty_var(&a1);
  valk_type_t *p1[] = {v1};
  valk_type_t *fn1 = ty_fun(&a1, p1, 1, v2, false);

  valk_type_t *v3 = ty_var(&a2);
  valk_type_t *v4 = ty_var(&a2);
  valk_type_t *p2[] = {v3};
  valk_type_t *fn2 = ty_fun(&a2, p2, 1, v4, false);

  symdb_type_id id1 = valk_symdb_intern_type(db, fn1);
  symdb_type_id id2 = valk_symdb_intern_type(db, fn2);
  VALK_TEST_ASSERT(id1 == id2,
                   "alpha-equivalent type vars should normalize to same hash");

  type_arena_free(&a1);
  type_arena_free(&a2);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_transactions(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  valk_symdb_begin(db);
  symdb_file_id fid = valk_symdb_upsert_file(db, "/test.valk", 0, 100, "h1");
  valk_symdb_add_symbol(db, "x", fid, 0, 0, 0, 1,
                        SYMKIND_VARIABLE,
                        valk_symdb_intern_type(db, ty_num(&arena)),
                        -1, true);
  valk_symdb_rollback(db);

  symdb_summary_t sum = valk_symdb_summary(db);
  VALK_TEST_ASSERT(sum.symbol_count == 0, "rollback should undo symbol insert");

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

void test_symdb_named_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  cleanup();

  valk_symdb_t *db = valk_symdb_open(db_path);

  type_arena_t arena;
  type_arena_init(&arena);

  valk_type_t *params[] = {ty_str(&arena)};
  valk_type_t *opt1 = ty_named(&arena, "Option", params, 1);
  valk_type_t *opt2 = ty_named(&arena, "Option", params, 1);

  symdb_type_id a = valk_symdb_intern_type(db, opt1);
  symdb_type_id b = valk_symdb_intern_type(db, opt2);
  VALK_TEST_ASSERT(a == b, "Option(Str) should be deduplicated");

  char *display = valk_symdb_type_display(db, a);
  VALK_TEST_ASSERT(display != NULL, "display should not be null");
  VALK_TEST_ASSERT(strstr(display, "Option") != NULL, "should contain Option");
  VALK_TEST_ASSERT(strstr(display, "Str") != NULL, "should contain Str");
  free(display);

  type_arena_free(&arena);
  valk_symdb_close(db);
  cleanup();
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_symdb_open_close", test_symdb_open_close);
  valk_testsuite_add_test(suite, "test_symdb_file_tracking", test_symdb_file_tracking);
  valk_testsuite_add_test(suite, "test_symdb_type_interning", test_symdb_type_interning);
  valk_testsuite_add_test(suite, "test_symdb_compound_type_dedup", test_symdb_compound_type_dedup);
  valk_testsuite_add_test(suite, "test_symdb_symbols_and_refs", test_symdb_symbols_and_refs);
  valk_testsuite_add_test(suite, "test_symdb_invalidate_file", test_symdb_invalidate_file);
  valk_testsuite_add_test(suite, "test_symdb_summary", test_symdb_summary);
  valk_testsuite_add_test(suite, "test_symdb_hotspots", test_symdb_hotspots);
  valk_testsuite_add_test(suite, "test_symdb_dead_code", test_symdb_dead_code);
  valk_testsuite_add_test(suite, "test_symdb_type_popularity", test_symdb_type_popularity);
  valk_testsuite_add_test(suite, "test_symdb_content_hash", test_symdb_content_hash);
  valk_testsuite_add_test(suite, "test_symdb_scopes", test_symdb_scopes);
  valk_testsuite_add_test(suite, "test_symdb_type_var_normalization", test_symdb_type_var_normalization);
  valk_testsuite_add_test(suite, "test_symdb_transactions", test_symdb_transactions);
  valk_testsuite_add_test(suite, "test_symdb_named_type", test_symdb_named_type);

  int result = valk_testsuite_run(suite);
  valk_testsuite_free(suite);
  return result;
}
