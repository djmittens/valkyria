#include "builtins_internal.h"

#include <stdlib.h>
#include <string.h>

#include "aio/aio.h"
#include "collections.h"
#include "gc.h"

static void __valk_http2_request_release(void* arg) {
  valk_http2_request_t* req = (valk_http2_request_t*)arg;
  valk_region_t* region = req->region;
  valk_mem_arena_t* arena = region->arena;
  free(region);
  free(arena);
}

// LCOV_EXCL_BR_START - http2/request arg validation
static valk_lval_t* valk_builtin_http2_request(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 4);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 2), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 3), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  u64 arena_bytes =
      sizeof(valk_mem_arena_t) + (8 * 1024 * 1024) + (64 * 1024);
  valk_mem_arena_t* arena = malloc(arena_bytes);
  valk_mem_arena_init(arena, arena_bytes - sizeof(*arena));

  valk_region_t* region = malloc(sizeof(valk_region_t));
  valk_region_init(region, VALK_LIFETIME_REQUEST, nullptr, arena);

  valk_http2_request_t* req =
      valk_region_alloc(region, sizeof(valk_http2_request_t));
  memset(req, 0, sizeof(*req));
  req->allocator = (valk_mem_allocator_t*)region;
  req->region = region;

  VALK_WITH_ALLOC(req->allocator) {
    u64 len;
    len = strlen(valk_lval_list_nth(a, 0)->str);
    req->method = valk_mem_alloc(len + 1);
    memcpy(req->method, valk_lval_list_nth(a, 0)->str, len + 1);

    len = strlen(valk_lval_list_nth(a, 1)->str);
    req->scheme = valk_mem_alloc(len + 1);
    memcpy(req->scheme, valk_lval_list_nth(a, 1)->str, len + 1);

    len = strlen(valk_lval_list_nth(a, 2)->str);
    req->authority = valk_mem_alloc(len + 1);
    memcpy(req->authority, valk_lval_list_nth(a, 2)->str, len + 1);

    len = strlen(valk_lval_list_nth(a, 3)->str);
    req->path = valk_mem_alloc(len + 1);
    memcpy(req->path, valk_lval_list_nth(a, 3)->str, len + 1);

    req->body = (u8*)"";
    req->bodyLen = 0;
    req->bodyCapacity = 0;
    da_init(&req->headers); // LCOV_EXCL_BR_LINE
  }

  return valk_lval_ref("http2_request", req, __valk_http2_request_release);
}

// LCOV_EXCL_BR_START - http2/request-add-header arg validation
static valk_lval_t* valk_builtin_http2_request_add_header(valk_lenv_t* e,
                                                          valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a,
              strcmp(valk_lval_list_nth(a, 0)->ref.type, "http2_request") == 0,
              "First arg must be http2_request ref, got %s",
              valk_lval_list_nth(a, 0)->ref.type);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 2), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  valk_http2_request_t* req = valk_lval_list_nth(a, 0)->ref.ptr;

  VALK_WITH_ALLOC(req->allocator) {
    struct valk_http2_header_t hdr;
    u64 nlen = strlen(valk_lval_list_nth(a, 1)->str);
    u64 vlen = strlen(valk_lval_list_nth(a, 2)->str);
    u8* n = valk_mem_alloc(nlen + 1);
    u8* v = valk_mem_alloc(vlen + 1);
    memcpy(n, valk_lval_list_nth(a, 1)->str, nlen + 1);
    memcpy(v, valk_lval_list_nth(a, 2)->str, vlen + 1);
    hdr.name = n;
    hdr.value = v;
    hdr.nameLen = nlen;
    hdr.valueLen = vlen;
    da_add(&req->headers, hdr); // LCOV_EXCL_BR_LINE
  }

  return valk_lval_nil();
}

// LCOV_EXCL_BR_START - http2/response-body arg validation
static valk_lval_t* valk_builtin_http2_response_body(valk_lenv_t* e,
                                                     valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 0)->ref.type, "success") == 0,
              "Argument must be a success ref holding a response");
  // LCOV_EXCL_BR_STOP
  valk_http2_response_t* res = valk_lval_list_nth(a, 0)->ref.ptr;
  if (!res || !res->body) { // LCOV_EXCL_BR_LINE
    return valk_lval_str("");
  }
  return valk_lval_str_n((const char*)res->body, res->bodyLen);
}

// LCOV_EXCL_BR_START - http2/response-status arg validation
static valk_lval_t* valk_builtin_http2_response_status(valk_lenv_t* e,
                                                       valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 0)->ref.type, "success") == 0,
              "Argument must be a success ref holding a response");
  // LCOV_EXCL_BR_STOP
  valk_http2_response_t* res = valk_lval_list_nth(a, 0)->ref.ptr;
  if (!res || !res->status) return valk_lval_str(""); // LCOV_EXCL_BR_LINE
  return valk_lval_str((const char*)res->status);
}

// LCOV_EXCL_BR_START - http2/response-headers arg validation
static valk_lval_t* valk_builtin_http2_response_headers(valk_lenv_t* e,
                                                        valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT(a, strcmp(valk_lval_list_nth(a, 0)->ref.type, "success") == 0,
              "Argument must be a success ref holding a response");
  // LCOV_EXCL_BR_STOP
  valk_http2_response_t* res = valk_lval_list_nth(a, 0)->ref.ptr;
  valk_lval_t* lst = valk_lval_nil();
  if (!res) return lst; // LCOV_EXCL_BR_LINE

  for (u64 i = 0; i < res->headers.count; ++i) {
    struct valk_http2_header_t* h = &res->headers.items[i];
    valk_lval_t* pair = valk_lval_nil();
    pair = valk_lval_cons(valk_lval_str((const char*)h->value), pair);
    pair = valk_lval_cons(valk_lval_str((const char*)h->name), pair);
    lst = valk_lval_cons(pair, lst);
  }
  return lst;
}

// LCOV_EXCL_START - cleanup callback only called by GC finalization
static void __valk_mock_response_free(void* ptr) {
  valk_http2_response_t* resp = (valk_http2_response_t*)ptr;
  if (resp) {
    free((void*)resp->status);
    free((void*)resp->body);
    for (u64 i = 0; i < resp->headers.count; i++) {
      free((void*)resp->headers.items[i].name);
      free((void*)resp->headers.items[i].value);
    }
    free(resp->headers.items);
    free(resp);
  }
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_http2_mock_response(valk_lenv_t* e,
                                                      valk_lval_t* a) {
  UNUSED(e);
  u64 argc = valk_lval_list_count(a);
  LVAL_ASSERT(a, argc >= 2 && argc <= 3,
              "http2/mock-response expects 2 or 3 arguments (status body [headers])");
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);

  const char* status_str = valk_lval_list_nth(a, 0)->str;
  const char* body_str = valk_lval_list_nth(a, 1)->str;
  u64 body_len = strlen(body_str);

  valk_http2_response_t* resp = malloc(sizeof(valk_http2_response_t));
  memset(resp, 0, sizeof(*resp));

  u64 status_len = strlen(status_str);
  resp->status = malloc(status_len + 1);
  memcpy((void*)resp->status, status_str, status_len + 1);

  resp->body = malloc(body_len + 1);
  memcpy(resp->body, body_str, body_len);
  resp->body[body_len] = '\0';
  resp->bodyLen = body_len;

  resp->headersReceived = true;
  resp->bodyReceived = true;

  // LCOV_EXCL_BR_START - mock response header parsing: test helper
  if (argc == 3) {
    valk_lval_t* headers = valk_lval_list_nth(a, 2);
    if (LVAL_TYPE(headers) != LVAL_NIL) {
      u64 header_count = valk_lval_list_count(headers);

      if (header_count > 0) {
        resp->headers.items = malloc(header_count * sizeof(struct valk_http2_header_t));
        resp->headers.capacity = header_count;
        resp->headers.count = 0;

        for (u64 i = 0; i < header_count; i++) {
          valk_lval_t* pair = valk_lval_list_nth(headers, i);
          u64 pair_len = valk_lval_list_count(pair);
          if (pair_len >= 2) {
            valk_lval_t* name_val = valk_lval_list_nth(pair, 0);
            valk_lval_t* value_val = valk_lval_list_nth(pair, 1);
            if (LVAL_TYPE(name_val) == LVAL_STR && LVAL_TYPE(value_val) == LVAL_STR) {
              u64 nlen = strlen(name_val->str);
              u64 vlen = strlen(value_val->str);
              u8* n = malloc(nlen + 1);
              u8* v = malloc(vlen + 1);
              memcpy(n, name_val->str, nlen + 1);
              memcpy(v, value_val->str, vlen + 1);
              resp->headers.items[resp->headers.count].name = n;
              resp->headers.items[resp->headers.count].value = v;
              resp->headers.items[resp->headers.count].nameLen = nlen;
              resp->headers.items[resp->headers.count].valueLen = vlen;
              resp->headers.count++;
            }
          }
        }
      }
    }
  }
  // LCOV_EXCL_BR_STOP

  return valk_lval_ref("success", resp, __valk_mock_response_free);
}

void valk_register_http_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "http2/request", valk_builtin_http2_request);
  valk_lenv_put_builtin(env, "http2/request-add-header",
                        valk_builtin_http2_request_add_header);
  valk_lenv_put_builtin(env, "http2/response-body",
                        valk_builtin_http2_response_body);
  valk_lenv_put_builtin(env, "http2/response-status",
                        valk_builtin_http2_response_status);
  valk_lenv_put_builtin(env, "http2/response-headers",
                        valk_builtin_http2_response_headers);
  valk_lenv_put_builtin(env, "http2/mock-response",
                        valk_builtin_http2_mock_response);
}
