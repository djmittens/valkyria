#include "aio_internal.h"
#include "common.h"
#include "log.h"
#include "memory.h"
#include "parser.h"
#include <strings.h>

static valk_http2_server_request_t *get_request(valk_lval_t *ref) {
  if (!ref || LVAL_TYPE(ref) != LVAL_REF) {
    return NULL;
  }
  if (strcmp(ref->ref.type, "http_request") != 0) {
    return NULL;
  }
  return (valk_http2_server_request_t *)ref->ref.ptr;
}

static valk_lval_t *valk_builtin_req_method(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("req/method: expected 1 argument (request), got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_http2_server_request_t *req = get_request(valk_lval_list_nth(a, 0));
  if (!req) {
    return valk_lval_err("req/method: argument must be http request");
  }

  return valk_lval_str(req->method ? req->method : "GET");
}

static valk_lval_t *valk_builtin_req_path(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("req/path: expected 1 argument (request), got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_http2_server_request_t *req = get_request(valk_lval_list_nth(a, 0));
  if (!req) {
    return valk_lval_err("req/path: argument must be http request");
  }

  return valk_lval_str(req->path ? req->path : "/");
}

static valk_lval_t *valk_builtin_req_authority(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("req/authority: expected 1 argument (request), got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_http2_server_request_t *req = get_request(valk_lval_list_nth(a, 0));
  if (!req) {
    return valk_lval_err("req/authority: argument must be http request");
  }

  if (!req->authority) {
    return valk_lval_nil();
  }
  return valk_lval_str(req->authority);
}

static valk_lval_t *valk_builtin_req_scheme(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("req/scheme: expected 1 argument (request), got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_http2_server_request_t *req = get_request(valk_lval_list_nth(a, 0));
  if (!req) {
    return valk_lval_err("req/scheme: argument must be http request");
  }

  if (!req->scheme) {
    return valk_lval_str("https");
  }
  return valk_lval_str(req->scheme);
}

static valk_lval_t *valk_builtin_req_headers(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("req/headers: expected 1 argument (request), got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_http2_server_request_t *req = get_request(valk_lval_list_nth(a, 0));
  if (!req) {
    return valk_lval_err("req/headers: argument must be http request");
  }

  valk_lval_t *headers_list = valk_lval_nil();
  for (u64 i = req->headers.count; i > 0; i--) {
    valk_lval_t *pair_items[2] = {
      valk_lval_str((char*)req->headers.items[i-1].name),
      valk_lval_str((char*)req->headers.items[i-1].value)
    };
    valk_lval_t *pair = valk_lval_qlist(pair_items, 2);
    headers_list = valk_lval_qcons(pair, headers_list);
  }
  return headers_list;
}

static valk_lval_t *valk_builtin_req_header(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("req/header: expected 2 arguments (request name), got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_http2_server_request_t *req = get_request(valk_lval_list_nth(a, 0));
  if (!req) {
    return valk_lval_err("req/header: first argument must be http request");
  }

  valk_lval_t *name_arg = valk_lval_list_nth(a, 1);
  if (LVAL_TYPE(name_arg) != LVAL_STR) {
    return valk_lval_err("req/header: second argument must be string");
  }

  const char *name = name_arg->str;
  for (u64 i = 0; i < req->headers.count; i++) {
    if (strcasecmp((const char*)req->headers.items[i].name, name) == 0) {
      return valk_lval_str((char*)req->headers.items[i].value);
    }
  }
  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_req_body(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("req/body: expected 1 argument (request), got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_http2_server_request_t *req = get_request(valk_lval_list_nth(a, 0));
  if (!req) {
    return valk_lval_err("req/body: argument must be http request");
  }

  if (!req->body || req->bodyLen == 0) {
    return valk_lval_nil();
  }

  char *body_str = valk_mem_alloc(req->bodyLen + 1);
  memcpy(body_str, req->body, req->bodyLen);
  body_str[req->bodyLen] = '\0';
  return valk_lval_str(body_str);
}

static valk_lval_t *valk_builtin_req_stream_id(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("req/stream-id: expected 1 argument (request), got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_http2_server_request_t *req = get_request(valk_lval_list_nth(a, 0));
  if (!req) {
    return valk_lval_err("req/stream-id: argument must be http request");
  }

  return valk_lval_num(req->stream_id);
}

void valk_register_http_request_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "req/method", valk_builtin_req_method);
  valk_lenv_put_builtin(env, "req/path", valk_builtin_req_path);
  valk_lenv_put_builtin(env, "req/authority", valk_builtin_req_authority);
  valk_lenv_put_builtin(env, "req/scheme", valk_builtin_req_scheme);
  valk_lenv_put_builtin(env, "req/headers", valk_builtin_req_headers);
  valk_lenv_put_builtin(env, "req/header", valk_builtin_req_header);
  valk_lenv_put_builtin(env, "req/body", valk_builtin_req_body);
  valk_lenv_put_builtin(env, "req/stream-id", valk_builtin_req_stream_id);
  VALK_DEBUG("HTTP request builtins registered");
}
