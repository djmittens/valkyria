#include "lsp_json.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  const char *src;
  size_t len;
  size_t pos;
} json_parser_t;

static void skip_ws(json_parser_t *p) {
  while (p->pos < p->len && isspace((unsigned char)p->src[p->pos]))
    p->pos++;
}

static char peek(json_parser_t *p) {
  if (p->pos >= p->len) return '\0';
  return p->src[p->pos];
}

static char advance(json_parser_t *p) {
  if (p->pos >= p->len) return '\0';
  return p->src[p->pos++];
}

static json_value_t parse_value(json_parser_t *p);

static json_value_t parse_string(json_parser_t *p) {
  json_value_t v = {.type = JSON_STRING};
  advance(p);
  size_t start = p->pos;

  size_t cap = 64;
  char *buf = malloc(cap);
  size_t len = 0;

  while (p->pos < p->len && p->src[p->pos] != '"') {
    char c = p->src[p->pos++];
    if (c == '\\' && p->pos < p->len) {
      char esc = p->src[p->pos++];
      switch (esc) {
        case '"':  c = '"'; break;
        case '\\': c = '\\'; break;
        case '/':  c = '/'; break;
        case 'b':  c = '\b'; break;
        case 'f':  c = '\f'; break;
        case 'n':  c = '\n'; break;
        case 'r':  c = '\r'; break;
        case 't':  c = '\t'; break;
        case 'u': {
          unsigned cp = 0;
          for (int i = 0; i < 4 && p->pos < p->len; i++)
            cp = cp * 16 + (isdigit((unsigned char)p->src[p->pos]) ? p->src[p->pos++] - '0' :
                            (tolower((unsigned char)p->src[p->pos]) - 'a' + 10) + (0 * p->pos++));
          if (cp < 0x80) {
            c = (char)cp;
          } else {
            c = '?';
          }
          break;
        }
        default: c = esc; break;
      }
    }
    if (len + 1 >= cap) {
      cap *= 2;
      buf = realloc(buf, cap);
    }
    buf[len++] = c;
  }
  if (p->pos < p->len) advance(p);

  buf[len] = '\0';
  v.string.str = buf;
  v.string.len = len;
  (void)start;
  return v;
}

static json_value_t parse_number(json_parser_t *p) {
  json_value_t v = {.type = JSON_NUMBER};
  char *end = nullptr;
  v.number = strtod(p->src + p->pos, &end);
  p->pos = end - p->src;
  return v;
}

static json_value_t parse_array(json_parser_t *p) {
  json_value_t v = {.type = JSON_ARRAY};
  advance(p);

  size_t cap = 8;
  v.array.items = malloc(sizeof(json_value_t) * cap);
  v.array.count = 0;

  skip_ws(p);
  if (peek(p) == ']') { advance(p); return v; }

  for (;;) {
    skip_ws(p);
    if (v.array.count >= cap) {
      cap *= 2;
      v.array.items = realloc(v.array.items, sizeof(json_value_t) * cap);
    }
    v.array.items[v.array.count++] = parse_value(p);
    skip_ws(p);
    if (peek(p) == ',') { advance(p); continue; }
    if (peek(p) == ']') { advance(p); break; }
    break;
  }
  return v;
}

static json_value_t parse_object(json_parser_t *p) {
  json_value_t v = {.type = JSON_OBJECT};
  advance(p);

  size_t cap = 8;
  v.object.keys = malloc(sizeof(char *) * cap);
  v.object.vals = malloc(sizeof(json_value_t) * cap);
  v.object.count = 0;

  skip_ws(p);
  if (peek(p) == '}') { advance(p); return v; }

  for (;;) {
    skip_ws(p);
    if (peek(p) != '"') break;

    json_value_t key = parse_string(p);

    skip_ws(p);
    if (peek(p) == ':') advance(p);
    skip_ws(p);

    if (v.object.count >= cap) {
      cap *= 2;
      v.object.keys = realloc(v.object.keys, sizeof(char *) * cap);
      v.object.vals = realloc(v.object.vals, sizeof(json_value_t) * cap);
    }

    v.object.keys[v.object.count] = key.string.str;
    v.object.vals[v.object.count] = parse_value(p);
    v.object.count++;

    skip_ws(p);
    if (peek(p) == ',') { advance(p); continue; }
    if (peek(p) == '}') { advance(p); break; }
    break;
  }
  return v;
}

static json_value_t parse_value(json_parser_t *p) {
  skip_ws(p);
  char c = peek(p);
  if (c == '"') return parse_string(p);
  if (c == '{') return parse_object(p);
  if (c == '[') return parse_array(p);
  if (c == '-' || isdigit((unsigned char)c)) return parse_number(p);
  if (c == 't') { p->pos += 4; return (json_value_t){.type = JSON_BOOL, .boolean = true}; }
  if (c == 'f') { p->pos += 5; return (json_value_t){.type = JSON_BOOL, .boolean = false}; }
  if (c == 'n') { p->pos += 4; return (json_value_t){.type = JSON_NULL}; }
  return (json_value_t){.type = JSON_NULL};
}

json_value_t json_parse(const char *input, size_t len) {
  json_parser_t p = {.src = input, .len = len, .pos = 0};
  return parse_value(&p);
}

void json_free(json_value_t *val) {
  if (!val) return;
  switch (val->type) {
    case JSON_STRING:
      free(val->string.str);
      val->string.str = nullptr;
      break;
    case JSON_ARRAY:
      for (size_t i = 0; i < val->array.count; i++)
        json_free(&val->array.items[i]);
      free(val->array.items);
      break;
    case JSON_OBJECT:
      for (size_t i = 0; i < val->object.count; i++) {
        free(val->object.keys[i]);
        json_free(&val->object.vals[i]);
      }
      free(val->object.keys);
      free(val->object.vals);
      break;
    default:
      break;
  }
}

json_value_t *json_get(json_value_t *obj, const char *key) {
  if (!obj || obj->type != JSON_OBJECT) return nullptr;
  for (size_t i = 0; i < obj->object.count; i++) {
    if (strcmp(obj->object.keys[i], key) == 0)
      return &obj->object.vals[i];
  }
  return nullptr;
}

const char *json_get_string(json_value_t *obj, const char *key) {
  json_value_t *v = json_get(obj, key);
  if (v && v->type == JSON_STRING) return v->string.str;
  return nullptr;
}

double json_get_number(json_value_t *obj, const char *key) {
  json_value_t *v = json_get(obj, key);
  if (v && v->type == JSON_NUMBER) return v->number;
  return 0;
}

int json_get_int(json_value_t *obj, const char *key) {
  return (int)json_get_number(obj, key);
}

bool json_get_bool(json_value_t *obj, const char *key) {
  json_value_t *v = json_get(obj, key);
  if (v && v->type == JSON_BOOL) return v->boolean;
  return false;
}

char *json_escape_string(const char *input) {
  if (!input) return strdup("null");
  size_t len = strlen(input);
  size_t cap = len * 2 + 3;
  char *out = malloc(cap);
  size_t o = 0;
  out[o++] = '"';
  for (size_t i = 0; i < len; i++) {
    if (o + 8 >= cap) {
      cap *= 2;
      out = realloc(out, cap);
    }
    switch (input[i]) {
      case '"':  out[o++] = '\\'; out[o++] = '"'; break;
      case '\\': out[o++] = '\\'; out[o++] = '\\'; break;
      case '\n': out[o++] = '\\'; out[o++] = 'n'; break;
      case '\r': out[o++] = '\\'; out[o++] = 'r'; break;
      case '\t': out[o++] = '\\'; out[o++] = 't'; break;
      case '\b': out[o++] = '\\'; out[o++] = 'b'; break;
      case '\f': out[o++] = '\\'; out[o++] = 'f'; break;
      default:
        if ((unsigned char)input[i] < 0x20) {
          o += snprintf(out + o, cap - o, "\\u%04x", (unsigned char)input[i]);
        } else {
          out[o++] = input[i];
        }
        break;
    }
  }
  out[o++] = '"';
  out[o] = '\0';
  return out;
}
