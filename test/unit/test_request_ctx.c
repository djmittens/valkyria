#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"
#include "../../src/aio/aio_request_ctx.h"

void test_request_ctx_new(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *ctx = valk_request_ctx_new(&valk_malloc_allocator);
  VALK_TEST_ASSERT(ctx != nullptr, "ctx should not be null");
  VALK_TEST_ASSERT(ctx->trace_id != 0, "trace_id should be generated");
  VALK_TEST_ASSERT(ctx->span_id != 0, "span_id should be generated");
  VALK_TEST_ASSERT(ctx->parent_span_id == 0, "parent_span_id should be 0");
  VALK_TEST_ASSERT(ctx->deadline_us == VALK_NO_DEADLINE, "deadline should be VALK_NO_DEADLINE");
  VALK_TEST_ASSERT(ctx->locals == nullptr, "locals should be null");

  free(ctx);
  VALK_PASS();
}

void test_request_ctx_copy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *ctx = valk_request_ctx_new(&valk_malloc_allocator);
  ctx->deadline_us = 12345678;

  valk_request_ctx_t *copy = valk_request_ctx_copy(ctx, &valk_malloc_allocator);
  VALK_TEST_ASSERT(copy != nullptr, "copy should not be null");
  VALK_TEST_ASSERT(copy->trace_id == ctx->trace_id, "trace_id should be copied");
  VALK_TEST_ASSERT(copy->span_id == ctx->span_id, "span_id should be copied");
  VALK_TEST_ASSERT(copy->deadline_us == ctx->deadline_us, "deadline should be copied");

  free(ctx);
  free(copy);
  VALK_PASS();
}

void test_request_ctx_with_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *parent = valk_request_ctx_new(&valk_malloc_allocator);
  valk_request_ctx_t *ctx = valk_request_ctx_with_timeout(parent, 1000, &valk_malloc_allocator);

  VALK_TEST_ASSERT(ctx != nullptr, "ctx should not be null");
  VALK_TEST_ASSERT(ctx->deadline_us != VALK_NO_DEADLINE, "deadline should be set");
  VALK_TEST_ASSERT(ctx->trace_id == parent->trace_id, "trace_id should be inherited");

  u64 remaining = valk_request_ctx_remaining_ms(ctx);
  VALK_TEST_ASSERT(remaining > 0 && remaining <= 1000, "remaining should be between 0 and 1000");

  free(parent);
  free(ctx);
  VALK_PASS();
}

void test_request_ctx_deadline_inheritance(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *parent = valk_request_ctx_with_timeout(nullptr, 5000, &valk_malloc_allocator);
  u64 parent_deadline = parent->deadline_us;

  valk_request_ctx_t *tighter = valk_request_ctx_with_timeout(parent, 1000, &valk_malloc_allocator);
  VALK_TEST_ASSERT(tighter->deadline_us < parent_deadline, "tighter timeout should result in earlier deadline");

  valk_request_ctx_t *looser = valk_request_ctx_with_timeout(parent, 10000, &valk_malloc_allocator);
  VALK_TEST_ASSERT(looser->deadline_us == parent_deadline, "looser timeout should keep parent deadline");

  free(parent);
  free(tighter);
  free(looser);
  VALK_PASS();
}

void test_request_ctx_new_span(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *parent = valk_request_ctx_new(&valk_malloc_allocator);
  valk_request_ctx_t *child = valk_request_ctx_new_span(parent, &valk_malloc_allocator);

  VALK_TEST_ASSERT(child != nullptr, "child should not be null");
  VALK_TEST_ASSERT(child->trace_id == parent->trace_id, "trace_id should be inherited");
  VALK_TEST_ASSERT(child->parent_span_id == parent->span_id, "parent_span_id should be set");
  VALK_TEST_ASSERT(child->span_id != parent->span_id, "new span_id should be generated");

  free(parent);
  free(child);
  VALK_PASS();
}

void test_request_ctx_deadline_exceeded(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(!valk_request_ctx_deadline_exceeded(nullptr), "null ctx should not be exceeded");

  valk_request_ctx_t ctx = {0};
  ctx.deadline_us = VALK_NO_DEADLINE;
  VALK_TEST_ASSERT(!valk_request_ctx_deadline_exceeded(&ctx), "no deadline should not be exceeded");

  ctx.deadline_us = valk_time_now_us() + 1000000;
  VALK_TEST_ASSERT(!valk_request_ctx_deadline_exceeded(&ctx), "future deadline should not be exceeded");

  ctx.deadline_us = valk_time_now_us() - 1000000;
  VALK_TEST_ASSERT(valk_request_ctx_deadline_exceeded(&ctx), "past deadline should be exceeded");

  VALK_PASS();
}

void test_request_ctx_locals(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *ctx = valk_request_ctx_new(&valk_malloc_allocator);
  valk_lval_t *key = valk_lval_sym(":user-id");
  valk_lval_t *value = valk_lval_num(42);

  valk_request_ctx_t *ctx2 = valk_request_ctx_with_local(ctx, key, value, &valk_malloc_allocator);
  VALK_TEST_ASSERT(ctx2 != nullptr, "ctx with local should not be null");

  valk_lval_t *lookup_key = valk_lval_sym(":user-id");
  valk_lval_t *found = valk_request_ctx_get_local(ctx2, lookup_key);
  VALK_TEST_ASSERT(found != nullptr, "local should be found");
  VALK_TEST_ASSERT(LVAL_TYPE(found) == LVAL_NUM, "local value should be a number");
  VALK_TEST_ASSERT(found->num == 42, "local value should be 42");

  valk_lval_t *not_found_key = valk_lval_sym(":other-key");
  valk_lval_t *not_found = valk_request_ctx_get_local(ctx2, not_found_key);
  VALK_TEST_ASSERT(not_found == nullptr, "non-existent local should return null");

  free(ctx);
  free(ctx2);
  VALK_PASS();
}

void test_trace_id_generation(VALK_TEST_ARGS()) {
  VALK_TEST();

  u64 id1 = valk_trace_id_generate();
  u64 id2 = valk_trace_id_generate();
  u64 id3 = valk_trace_id_generate();

  VALK_TEST_ASSERT(id1 != 0, "trace id should not be 0");
  VALK_TEST_ASSERT(id2 != 0, "trace id should not be 0");
  VALK_TEST_ASSERT(id3 != 0, "trace id should not be 0");
  VALK_TEST_ASSERT(id1 != id2, "trace ids should be unique");
  VALK_TEST_ASSERT(id2 != id3, "trace ids should be unique");

  VALK_PASS();
}

void test_span_id_generation(VALK_TEST_ARGS()) {
  VALK_TEST();

  u64 id1 = valk_span_id_generate();
  u64 id2 = valk_span_id_generate();
  u64 id3 = valk_span_id_generate();

  VALK_TEST_ASSERT(id1 != 0, "span id should not be 0");
  VALK_TEST_ASSERT(id2 != 0, "span id should not be 0");
  VALK_TEST_ASSERT(id3 != 0, "span id should not be 0");
  VALK_TEST_ASSERT(id1 != id2, "span ids should be unique");
  VALK_TEST_ASSERT(id2 != id3, "span ids should be unique");

  VALK_PASS();
}

void test_request_ctx_copy_null_parent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *ctx = valk_request_ctx_copy(nullptr, &valk_malloc_allocator);
  VALK_TEST_ASSERT(ctx != nullptr, "copying null should create new ctx");
  VALK_TEST_ASSERT(ctx->trace_id != 0, "trace_id should be generated");
  VALK_TEST_ASSERT(ctx->span_id != 0, "span_id should be generated");
  VALK_TEST_ASSERT(ctx->deadline_us == VALK_NO_DEADLINE, "deadline should be VALK_NO_DEADLINE");

  free(ctx);
  VALK_PASS();
}

void test_request_ctx_new_span_null_parent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *ctx = valk_request_ctx_new_span(nullptr, &valk_malloc_allocator);
  VALK_TEST_ASSERT(ctx != nullptr, "new span with null parent should work");
  VALK_TEST_ASSERT(ctx->trace_id != 0, "trace_id should be generated");
  VALK_TEST_ASSERT(ctx->span_id != 0, "span_id should be generated");
  VALK_TEST_ASSERT(ctx->parent_span_id == 0, "parent_span_id should be 0");
  VALK_TEST_ASSERT(ctx->deadline_us == VALK_NO_DEADLINE, "deadline should be VALK_NO_DEADLINE");
  VALK_TEST_ASSERT(ctx->locals == nullptr, "locals should be null");

  free(ctx);
  VALK_PASS();
}

void test_request_ctx_with_deadline_direct(VALK_TEST_ARGS()) {
  VALK_TEST();

  u64 deadline = valk_time_now_us() + 5000000;
  valk_request_ctx_t *ctx = valk_request_ctx_with_deadline(nullptr, deadline, &valk_malloc_allocator);

  VALK_TEST_ASSERT(ctx != nullptr, "ctx should not be null");
  VALK_TEST_ASSERT(ctx->deadline_us == deadline, "deadline should match");

  free(ctx);
  VALK_PASS();
}

void test_request_ctx_get_local_string_key(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *ctx = valk_request_ctx_new(&valk_malloc_allocator);
  valk_lval_t *key = valk_lval_str("user-id");
  valk_lval_t *value = valk_lval_num(99);

  valk_request_ctx_t *ctx2 = valk_request_ctx_with_local(ctx, key, value, &valk_malloc_allocator);
  VALK_TEST_ASSERT(ctx2 != nullptr, "ctx with local should not be null");

  valk_lval_t *lookup_key = valk_lval_str("user-id");
  valk_lval_t *found = valk_request_ctx_get_local(ctx2, lookup_key);
  VALK_TEST_ASSERT(found != nullptr, "local should be found with string key");
  VALK_TEST_ASSERT(LVAL_TYPE(found) == LVAL_NUM, "local value should be a number");
  VALK_TEST_ASSERT(found->num == 99, "local value should be 99");

  free(ctx);
  free(ctx2);
  VALK_PASS();
}

void test_request_ctx_get_local_num_key(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *ctx = valk_request_ctx_new(&valk_malloc_allocator);
  valk_lval_t *key = valk_lval_num(123);
  valk_lval_t *value = valk_lval_str("test-value");

  valk_request_ctx_t *ctx2 = valk_request_ctx_with_local(ctx, key, value, &valk_malloc_allocator);
  VALK_TEST_ASSERT(ctx2 != nullptr, "ctx with local should not be null");

  valk_lval_t *lookup_key = valk_lval_num(123);
  valk_lval_t *found = valk_request_ctx_get_local(ctx2, lookup_key);
  VALK_TEST_ASSERT(found != nullptr, "local should be found with number key");
  VALK_TEST_ASSERT(LVAL_TYPE(found) == LVAL_STR, "local value should be a string");
  VALK_TEST_ASSERT(strcmp(found->str, "test-value") == 0, "local value should match");

  free(ctx);
  free(ctx2);
  VALK_PASS();
}

void test_request_ctx_get_local_null_cases(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *found = valk_request_ctx_get_local(nullptr, valk_lval_sym(":key"));
  VALK_TEST_ASSERT(found == nullptr, "null ctx should return null");

  valk_request_ctx_t ctx = {.locals = nullptr};
  found = valk_request_ctx_get_local(&ctx, valk_lval_sym(":key"));
  VALK_TEST_ASSERT(found == nullptr, "null locals should return null");

  found = valk_request_ctx_get_local(&ctx, nullptr);
  VALK_TEST_ASSERT(found == nullptr, "null key should return null");

  VALK_PASS();
}

void test_request_ctx_remaining_us(VALK_TEST_ARGS()) {
  VALK_TEST();

  u64 remaining = valk_request_ctx_remaining_us(nullptr);
  VALK_TEST_ASSERT(remaining == UINT64_MAX, "null ctx should return UINT64_MAX");

  valk_request_ctx_t ctx = {.deadline_us = VALK_NO_DEADLINE};
  remaining = valk_request_ctx_remaining_us(&ctx);
  VALK_TEST_ASSERT(remaining == UINT64_MAX, "no deadline should return UINT64_MAX");

  ctx.deadline_us = valk_time_now_us() + 1000000;
  remaining = valk_request_ctx_remaining_us(&ctx);
  VALK_TEST_ASSERT(remaining > 0 && remaining <= 1000000, "remaining should be reasonable");

  ctx.deadline_us = valk_time_now_us() - 1000;
  remaining = valk_request_ctx_remaining_us(&ctx);
  VALK_TEST_ASSERT(remaining == 0, "expired deadline should return 0");

  VALK_PASS();
}

void test_request_ctx_remaining_ms(VALK_TEST_ARGS()) {
  VALK_TEST();

  u64 remaining = valk_request_ctx_remaining_ms(nullptr);
  VALK_TEST_ASSERT(remaining == UINT64_MAX, "null ctx should return UINT64_MAX");

  valk_request_ctx_t ctx = {.deadline_us = VALK_NO_DEADLINE};
  remaining = valk_request_ctx_remaining_ms(&ctx);
  VALK_TEST_ASSERT(remaining == UINT64_MAX, "no deadline should return UINT64_MAX");

  ctx.deadline_us = valk_time_now_us() + 5000000;
  remaining = valk_request_ctx_remaining_ms(&ctx);
  VALK_TEST_ASSERT(remaining > 0 && remaining <= 5000, "remaining should be ~5000ms");

  VALK_PASS();
}

void test_request_ctx_has_deadline(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(!valk_request_ctx_has_deadline(nullptr), "null ctx should have no deadline");

  valk_request_ctx_t ctx = {.deadline_us = VALK_NO_DEADLINE};
  VALK_TEST_ASSERT(!valk_request_ctx_has_deadline(&ctx), "VALK_NO_DEADLINE should have no deadline");

  ctx.deadline_us = valk_time_now_us() + 1000000;
  VALK_TEST_ASSERT(valk_request_ctx_has_deadline(&ctx), "set deadline should have deadline");

  VALK_PASS();
}

void test_request_ctx_multiple_locals(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_request_ctx_t *ctx = valk_request_ctx_new(&valk_malloc_allocator);

  ctx = valk_request_ctx_with_local(ctx, valk_lval_sym(":key1"), valk_lval_num(1), &valk_malloc_allocator);
  ctx = valk_request_ctx_with_local(ctx, valk_lval_sym(":key2"), valk_lval_num(2), &valk_malloc_allocator);
  ctx = valk_request_ctx_with_local(ctx, valk_lval_sym(":key3"), valk_lval_num(3), &valk_malloc_allocator);

  valk_lval_t *found1 = valk_request_ctx_get_local(ctx, valk_lval_sym(":key1"));
  valk_lval_t *found2 = valk_request_ctx_get_local(ctx, valk_lval_sym(":key2"));
  valk_lval_t *found3 = valk_request_ctx_get_local(ctx, valk_lval_sym(":key3"));

  VALK_TEST_ASSERT(found1 != nullptr && found1->num == 1, "key1 should be 1");
  VALK_TEST_ASSERT(found2 != nullptr && found2->num == 2, "key2 should be 2");
  VALK_TEST_ASSERT(found3 != nullptr && found3->num == 3, "key3 should be 3");

  VALK_PASS();
}

void test_thread_ctx_request_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_thread_ctx.request_ctx == nullptr, "initial request_ctx should be null");

  valk_request_ctx_t ctx = {.trace_id = 123, .span_id = 456};
  VALK_WITH_REQUEST_CTX(&ctx) {
    VALK_TEST_ASSERT(valk_thread_ctx.request_ctx == &ctx, "request_ctx should be set");
    VALK_TEST_ASSERT(valk_thread_ctx.request_ctx->trace_id == 123, "trace_id should be accessible");
  }

  VALK_TEST_ASSERT(valk_thread_ctx.request_ctx == nullptr, "request_ctx should be restored to null");

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_request_ctx_new", test_request_ctx_new);
  valk_testsuite_add_test(suite, "test_request_ctx_copy", test_request_ctx_copy);
  valk_testsuite_add_test(suite, "test_request_ctx_copy_null_parent", test_request_ctx_copy_null_parent);
  valk_testsuite_add_test(suite, "test_request_ctx_with_timeout", test_request_ctx_with_timeout);
  valk_testsuite_add_test(suite, "test_request_ctx_with_deadline_direct", test_request_ctx_with_deadline_direct);
  valk_testsuite_add_test(suite, "test_request_ctx_deadline_inheritance", test_request_ctx_deadline_inheritance);
  valk_testsuite_add_test(suite, "test_request_ctx_new_span", test_request_ctx_new_span);
  valk_testsuite_add_test(suite, "test_request_ctx_new_span_null_parent", test_request_ctx_new_span_null_parent);
  valk_testsuite_add_test(suite, "test_request_ctx_deadline_exceeded", test_request_ctx_deadline_exceeded);
  valk_testsuite_add_test(suite, "test_request_ctx_has_deadline", test_request_ctx_has_deadline);
  valk_testsuite_add_test(suite, "test_request_ctx_remaining_us", test_request_ctx_remaining_us);
  valk_testsuite_add_test(suite, "test_request_ctx_remaining_ms", test_request_ctx_remaining_ms);
  valk_testsuite_add_test(suite, "test_request_ctx_locals", test_request_ctx_locals);
  valk_testsuite_add_test(suite, "test_request_ctx_get_local_string_key", test_request_ctx_get_local_string_key);
  valk_testsuite_add_test(suite, "test_request_ctx_get_local_num_key", test_request_ctx_get_local_num_key);
  valk_testsuite_add_test(suite, "test_request_ctx_get_local_null_cases", test_request_ctx_get_local_null_cases);
  valk_testsuite_add_test(suite, "test_request_ctx_multiple_locals", test_request_ctx_multiple_locals);
  valk_testsuite_add_test(suite, "test_trace_id_generation", test_trace_id_generation);
  valk_testsuite_add_test(suite, "test_span_id_generation", test_span_id_generation);
  valk_testsuite_add_test(suite, "test_thread_ctx_request_ctx", test_thread_ctx_request_ctx);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
