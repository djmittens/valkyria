#include "../testing.h"
#include "../../src/aio/http2/aio_conn_io.h"
#include "../../src/aio/aio_internal.h"
#include "../../src/memory.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void test_conn_io_init(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_conn_io_t io;
  valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
  
  ASSERT_NULL(io.read_buf);
  ASSERT_NULL(io.write_buf);
  ASSERT_EQ(io.write_pos, 0);
  ASSERT_EQ(io.buf_size, HTTP_SLAB_ITEM_SIZE);
  ASSERT_FALSE(io.write_flush_pending);
  
  VALK_PASS();
}

static void test_conn_io_read_buf_size(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_conn_io_t io;
  valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
  size_t size = valk_conn_io_read_buf_size(&io);
  ASSERT_EQ(size, HTTP_SLAB_ITEM_SIZE);
  
  VALK_PASS();
}

static void test_conn_io_write_buf_acquire_null_slab(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_conn_io_t io;
  valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
  
  bool result = valk_conn_io_write_buf_acquire(&io, nullptr);
  ASSERT_FALSE(result);
  ASSERT_NULL(io.write_buf);
  
  VALK_PASS();
}

static void test_conn_io_write_buf_available_no_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_conn_io_t io;
  valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
  
  size_t available = valk_conn_io_write_buf_available(&io);
  ASSERT_EQ(available, 0);
  
  VALK_PASS();
}

static void test_conn_io_write_buf_data_no_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_conn_io_t io;
  valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
  
  u8 *data = valk_conn_io_write_buf_data(&io);
  ASSERT_NULL(data);
  
  VALK_PASS();
}

static void test_conn_io_write_buf_append_no_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_conn_io_t io;
  valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
  
  u8 data[] = {1, 2, 3};
  size_t written = valk_conn_io_write_buf_append(&io, nullptr, data, sizeof(data));
  ASSERT_EQ(written, 0);
  
  VALK_PASS();
}

static void test_conn_io_read_buf_acquire_null_slab(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_conn_io_t io;
  valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
  
  bool result = valk_conn_io_read_buf_acquire(&io, nullptr);
  ASSERT_FALSE(result);
  ASSERT_NULL(io.read_buf);
  
  VALK_PASS();
}

static void test_conn_io_read_buf_data_no_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_conn_io_t io;
  valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
  
  u8 *data = valk_conn_io_read_buf_data(&io);
  ASSERT_NULL(data);
  
  VALK_PASS();
}

static void test_conn_io_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_conn_io_free(nullptr, nullptr);
  
  VALK_PASS();
}

static void test_conn_io_with_slab(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    valk_slab_t *slab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 4);
    
    valk_conn_io_t io;
    valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
    
    ASSERT_TRUE(valk_conn_io_write_buf_acquire(&io, slab));
    ASSERT_NOT_NULL(io.write_buf);
    ASSERT_EQ(io.write_pos, 0);
    
    size_t available = valk_conn_io_write_buf_available(&io);
    ASSERT_EQ(available, HTTP_SLAB_ITEM_SIZE);
    
    u8 *data = valk_conn_io_write_buf_data(&io);
    ASSERT_NOT_NULL(data);
    
    u8 test_data[] = {1, 2, 3, 4, 5};
    size_t written = valk_conn_io_write_buf_append(&io, slab, test_data, sizeof(test_data));
    ASSERT_EQ(written, sizeof(test_data));
    ASSERT_EQ(io.write_pos, sizeof(test_data));
    
    available = valk_conn_io_write_buf_available(&io);
    ASSERT_EQ(available, HTTP_SLAB_ITEM_SIZE - sizeof(test_data));
    
    ASSERT_TRUE(valk_conn_io_read_buf_acquire(&io, slab));
    ASSERT_NOT_NULL(io.read_buf);
    
    u8 *read_data = valk_conn_io_read_buf_data(&io);
    ASSERT_NOT_NULL(read_data);
    
    valk_conn_io_free(&io, slab);
    ASSERT_NULL(io.read_buf);
    ASSERT_NULL(io.write_buf);
    
    valk_slab_free(slab);
  }
  
  VALK_PASS();
}

static void test_conn_io_writable(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    valk_slab_t *slab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t), 4);
    
    valk_conn_io_t io;
    valk_conn_io_init(&io, HTTP_SLAB_ITEM_SIZE);
    
    ASSERT_TRUE(valk_conn_io_write_buf_writable(&io, slab, 100));
    ASSERT_NOT_NULL(io.write_buf);
    
    io.write_flush_pending = true;
    ASSERT_FALSE(valk_conn_io_write_buf_writable(&io, slab, 100));
    
    valk_conn_io_free(&io, slab);
    valk_slab_free(slab);
  }
  
  VALK_PASS();
}

int main(int argc, const char *argv[]) {
  (void)argc;
  (void)argv;

  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  
  valk_testsuite_add_test(suite, "test_conn_io_init", test_conn_io_init);
  valk_testsuite_add_test(suite, "test_conn_io_read_buf_size", test_conn_io_read_buf_size);
  valk_testsuite_add_test(suite, "test_conn_io_write_buf_acquire_null_slab", test_conn_io_write_buf_acquire_null_slab);
  valk_testsuite_add_test(suite, "test_conn_io_write_buf_available_no_buf", test_conn_io_write_buf_available_no_buf);
  valk_testsuite_add_test(suite, "test_conn_io_write_buf_data_no_buf", test_conn_io_write_buf_data_no_buf);
  valk_testsuite_add_test(suite, "test_conn_io_write_buf_append_no_buf", test_conn_io_write_buf_append_no_buf);
  valk_testsuite_add_test(suite, "test_conn_io_read_buf_acquire_null_slab", test_conn_io_read_buf_acquire_null_slab);
  valk_testsuite_add_test(suite, "test_conn_io_read_buf_data_no_buf", test_conn_io_read_buf_data_no_buf);
  valk_testsuite_add_test(suite, "test_conn_io_free_null", test_conn_io_free_null);
  valk_testsuite_add_test(suite, "test_conn_io_with_slab", test_conn_io_with_slab);
  valk_testsuite_add_test(suite, "test_conn_io_writable", test_conn_io_writable);
  
  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return result;
}
