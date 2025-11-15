// Async I/O operations using continuations instead of futures
// This replaces the complex futures/promises with simple continuations

#include "aio.h"
#include "parser.h"
#include "memory.h"
#include "log.h"

// Async connect that takes a continuation
// (http2/connect-async host port continuation)
valk_lval_t* valk_builtin_http2_connect_async(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 4);

  valk_lval_t* aio_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, aio_ref, LVAL_REF);
  LVAL_ASSERT(a, strcmp(aio_ref->ref.type, "aio_system") == 0,
              "First arg must be aio_system");

  valk_lval_t* host = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, host, LVAL_STR);

  valk_lval_t* port = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, port, LVAL_NUM);

  valk_lval_t* cont = valk_lval_list_nth(a, 3);
  LVAL_ASSERT_TYPE(a, cont, LVAL_REF);
  LVAL_ASSERT(a, strcmp(cont->ref.type, "continuation") == 0,
              "Fourth arg must be continuation");

  // For now, return a mock successful connection
  // In real implementation, would register cont with libuv callback
  valk_lval_t* mock_client = valk_lval_ref("http2_client", NULL, NULL);

  // Simulate async by immediately calling continuation
  // In real impl, libuv callback would do this
  return valk_continuation_resume(cont, mock_client);
}

// Async send that takes a continuation
// (http2/send-async request client continuation)
valk_lval_t* valk_builtin_http2_send_async(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 3);

  valk_lval_t* req = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, req, LVAL_REF);

  valk_lval_t* client = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, client, LVAL_REF);

  valk_lval_t* cont = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_TYPE(a, cont, LVAL_REF);
  LVAL_ASSERT(a, strcmp(cont->ref.type, "continuation") == 0,
              "Third arg must be continuation");

  // Mock response
  valk_lval_t* mock_response = valk_lval_ref("http2_response", NULL, NULL);

  // Simulate async completion
  return valk_continuation_resume(cont, mock_response);
}

// Register async I/O builtins
void valk_register_aio_async_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "http2/connect-async", valk_builtin_http2_connect_async);
  valk_lenv_put_builtin(env, "http2/send-async", valk_builtin_http2_send_async);
}