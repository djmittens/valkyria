#include "builtins_internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lsp/lsp_json.h"

static valk_lval_t *make_option_none(void) {
  valk_lval_t *items[1] = {valk_lval_sym("Option::None")};
  return valk_lval_qlist(items, 1);
}

static valk_lval_t *json_value_to_lval(json_value_t *v) {
  switch (v->type) {
    case JSON_NULL:   return make_option_none();
    case JSON_BOOL:   return valk_lval_num(v->boolean ? 1 : 0);
    case JSON_NUMBER: return valk_lval_num((long)v->number);
    case JSON_STRING: return valk_lval_str(v->string.str);
    case JSON_ARRAY: {
      valk_lval_t **items = malloc(v->array.count * sizeof(valk_lval_t *));
      for (size_t i = 0; i < v->array.count; i++)
        items[i] = json_value_to_lval(&v->array.items[i]);
      valk_lval_t *list = valk_lval_qlist(items, v->array.count);
      free(items);
      return list;
    }
    case JSON_OBJECT: {
      valk_lval_t **items = malloc(v->object.count * 2 * sizeof(valk_lval_t *));
      for (size_t i = 0; i < v->object.count; i++) {
        char kw[256];
        snprintf(kw, sizeof(kw), ":%s", v->object.keys[i]);
        items[i * 2]     = valk_lval_sym(kw);
        items[i * 2 + 1] = json_value_to_lval(&v->object.vals[i]);
      }
      valk_lval_t *plist = valk_lval_qlist(items, v->object.count * 2);
      free(items);
      return plist;
    }
  }
  return make_option_none(); // LCOV_EXCL_LINE
}

static valk_lval_t *valk_builtin_json_parse(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char *input = valk_lval_list_nth(a, 0)->str;
  json_value_t val = json_parse(input, strlen(input));
  valk_lval_t *result = json_value_to_lval(&val);
  json_free(&val);
  return result;
}

typedef struct {
  char *buf;
  size_t len;
  size_t cap;
} json_buf_t;

static void buf_init(json_buf_t *b) {
  b->cap = 256;
  b->len = 0;
  b->buf = malloc(b->cap);
}

static void buf_ensure(json_buf_t *b, size_t extra) {
  while (b->len + extra >= b->cap) {
    b->cap *= 2;
    b->buf = realloc(b->buf, b->cap);
  }
}

static void buf_append(json_buf_t *b, const char *s, size_t n) {
  buf_ensure(b, n);
  memcpy(b->buf + b->len, s, n);
  b->len += n;
}

static void buf_append_str(json_buf_t *b, const char *s) {
  buf_append(b, s, strlen(s));
}

static void buf_append_char(json_buf_t *b, char c) {
  buf_ensure(b, 1);
  b->buf[b->len++] = c;
}

static void buf_append_escaped(json_buf_t *b, const char *s) {
  char *escaped = json_escape_string(s);
  buf_append_str(b, escaped);
  free(escaped);
}

static bool is_plist(valk_lval_t *v) {
  if (LVAL_TYPE(v) == LVAL_NIL) return false;
  if (LVAL_TYPE(v) != LVAL_CONS) return false;
  valk_lval_t *first = valk_lval_list_nth(v, 0);
  return LVAL_TYPE(first) == LVAL_SYM && first->str[0] == ':';
}

static bool is_option_none(valk_lval_t *v) {
  if (LVAL_TYPE(v) != LVAL_CONS) return false;
  if (valk_lval_list_count(v) != 1) return false;
  valk_lval_t *tag = valk_lval_list_nth(v, 0);
  return LVAL_TYPE(tag) == LVAL_SYM && strcmp(tag->str, "Option::None") == 0;
}

static bool is_option_some(valk_lval_t *v) {
  if (LVAL_TYPE(v) != LVAL_CONS) return false;
  if (valk_lval_list_count(v) != 2) return false;
  valk_lval_t *tag = valk_lval_list_nth(v, 0);
  return LVAL_TYPE(tag) == LVAL_SYM && strcmp(tag->str, "Option::Some") == 0;
}

static void lval_to_json(json_buf_t *b, valk_lval_t *v) {
  switch (LVAL_TYPE(v)) {
    case LVAL_NIL:
      buf_append_str(b, "[]");
      break;
    case LVAL_NUM: {
      char tmp[32];
      snprintf(tmp, sizeof(tmp), "%ld", v->num);
      buf_append_str(b, tmp);
      break;
    }
    case LVAL_STR:
      buf_append_escaped(b, v->str);
      break;
    case LVAL_SYM:
      if (strcmp(v->str, ":true") == 0) buf_append_str(b, "true");
      else if (strcmp(v->str, ":false") == 0) buf_append_str(b, "false");
      else buf_append_escaped(b, v->str);
      break;
    case LVAL_CONS: {
      if (is_option_none(v)) {
        buf_append_str(b, "null");
      } else if (is_option_some(v)) {
        lval_to_json(b, valk_lval_list_nth(v, 1));
      } else if (is_plist(v)) {
        buf_append_char(b, '{');
        u64 count = valk_lval_list_count(v);
        for (u64 i = 0; i + 1 < count; i += 2) {
          if (i > 0) buf_append_char(b, ',');
          valk_lval_t *key = valk_lval_list_nth(v, i);
          const char *kstr = key->str + 1;
          buf_append_escaped(b, kstr);
          buf_append_char(b, ':');
          lval_to_json(b, valk_lval_list_nth(v, i + 1));
        }
        buf_append_char(b, '}');
      } else {
        buf_append_char(b, '[');
        u64 count = valk_lval_list_count(v);
        for (u64 i = 0; i < count; i++) {
          if (i > 0) buf_append_char(b, ',');
          lval_to_json(b, valk_lval_list_nth(v, i));
        }
        buf_append_char(b, ']');
      }
      break;
    }
    default:
      buf_append_str(b, "null");
      break;
  }
}

static valk_lval_t *valk_builtin_json_encode(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  json_buf_t b;
  buf_init(&b);
  lval_to_json(&b, valk_lval_list_nth(a, 0));
  buf_append_char(&b, '\0');

  valk_lval_t *result = valk_lval_str(b.buf);
  free(b.buf);
  return result;
}

void valk_register_json_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "json/parse", valk_builtin_json_parse);
  valk_lenv_put_builtin(env, "json/encode", valk_builtin_json_encode);
}
