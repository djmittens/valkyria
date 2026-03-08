#pragma once

#include <stdbool.h>
#include <stddef.h>

typedef enum {
  JSON_NULL,
  JSON_BOOL,
  JSON_NUMBER,
  JSON_STRING,
  JSON_ARRAY,
  JSON_OBJECT,
} json_type_e;

typedef struct json_value_t json_value_t;

struct json_value_t {
  json_type_e type;
  union {
    bool boolean;
    double number;
    struct {
      char *str;
      size_t len;
    } string;
    struct {
      json_value_t *items;
      size_t count;
    } array;
    struct {
      char **keys;
      json_value_t *vals;
      size_t count;
    } object;
  };
};

json_value_t json_parse(const char *input, size_t len);
void json_free(json_value_t *val);

char *json_escape_string(const char *input);
