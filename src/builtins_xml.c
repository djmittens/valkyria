#include "builtins_internal.h"

#include <expat.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct xml_node {
  char* tag;
  valk_lval_t* attrs;
  struct xml_node** children;
  int child_count;
  int child_cap;
  char* text;
  int text_len;
  int text_cap;
} xml_node_t;

typedef struct {
  xml_node_t** stack;
  int depth;
  int cap;
  bool error;
  char error_msg[256];
} xml_parse_ctx_t;

static xml_node_t* xml_node_new(const char* tag, const XML_Char** attr) {
  xml_node_t* node = calloc(1, sizeof(xml_node_t));
  node->tag = strdup(tag);
  node->child_cap = 8;
  node->children = malloc(node->child_cap * sizeof(xml_node_t*));
  node->text = NULL;
  node->text_len = 0;
  node->text_cap = 0;

  int attr_count = 0;
  for (int i = 0; attr[i]; i += 2) attr_count++;

  if (attr_count == 0) {
    node->attrs = valk_lval_nil();
  } else {
    valk_lval_t** items = malloc(attr_count * 2 * sizeof(valk_lval_t*));
    for (int i = 0; i < attr_count; i++) {
      char kw[256];
      snprintf(kw, sizeof(kw), ":%s", attr[i * 2]);
      items[i * 2] = valk_lval_sym(kw);
      items[i * 2 + 1] = valk_lval_str(attr[i * 2 + 1]);
    }
    node->attrs = valk_lval_qlist(items, attr_count * 2);
    free(items);
  }
  return node;
}

static void xml_node_add_child(xml_node_t* parent, xml_node_t* child) {
  if (parent->child_count >= parent->child_cap) {
    parent->child_cap *= 2;
    parent->children =
        realloc(parent->children, parent->child_cap * sizeof(xml_node_t*));
  }
  parent->children[parent->child_count++] = child;
}

static void xml_node_append_text(xml_node_t* node, const char* s, int len) {
  if (len == 0) return;
  if (node->text == NULL) {
    node->text_cap = len + 1;
    node->text = malloc(node->text_cap);
    node->text_len = 0;
  }
  while (node->text_len + len + 1 > node->text_cap) {
    node->text_cap *= 2;
    node->text = realloc(node->text, node->text_cap);
  }
  memcpy(node->text + node->text_len, s, len);
  node->text_len += len;
  node->text[node->text_len] = '\0';
}

static valk_lval_t* xml_node_to_lval(xml_node_t* node) {
  valk_lval_t* children_list = valk_lval_nil();
  for (int i = node->child_count - 1; i >= 0; i--) {
    valk_lval_t* child = xml_node_to_lval(node->children[i]);
    children_list = valk_lval_cons(child, children_list);
  }

  int item_count = 6;
  bool has_text = node->text != NULL && node->text_len > 0;
  if (has_text) item_count = 8;

  valk_lval_t** items = malloc(item_count * sizeof(valk_lval_t*));
  items[0] = valk_lval_sym(":tag");
  items[1] = valk_lval_str(node->tag);
  items[2] = valk_lval_sym(":attrs");
  items[3] = node->attrs;
  items[4] = valk_lval_sym(":children");
  items[5] = children_list;
  if (has_text) {
    items[6] = valk_lval_sym(":text");
    items[7] = valk_lval_str(node->text);
  }

  valk_lval_t* result = valk_lval_qlist(items, item_count);
  free(items);
  return result;
}

static void xml_node_free(xml_node_t* node) {
  free(node->tag);
  free(node->text);
  for (int i = 0; i < node->child_count; i++) xml_node_free(node->children[i]);
  free(node->children);
  free(node);
}

static void ctx_push(xml_parse_ctx_t* ctx, xml_node_t* node) {
  if (ctx->depth >= ctx->cap) {
    ctx->cap *= 2;
    ctx->stack = realloc(ctx->stack, ctx->cap * sizeof(xml_node_t*));
  }
  ctx->stack[ctx->depth++] = node;
}

static void XMLCALL on_start(void* data, const XML_Char* name,
                             const XML_Char** atts) {
  xml_parse_ctx_t* ctx = data;
  if (ctx->error) return;

  xml_node_t* node = xml_node_new(name, atts);
  if (ctx->depth > 0) {
    xml_node_add_child(ctx->stack[ctx->depth - 1], node);
  }
  ctx_push(ctx, node);
}

static void XMLCALL on_end(void* data, const XML_Char* name) {
  UNUSED(name);
  xml_parse_ctx_t* ctx = data;
  if (ctx->error || ctx->depth <= 0) return;
  if (ctx->depth > 1) ctx->depth--;
}

static void XMLCALL on_chardata(void* data, const XML_Char* s, int len) {
  xml_parse_ctx_t* ctx = data;
  if (ctx->error || ctx->depth <= 0) return;
  bool all_ws = true;
  for (int i = 0; i < len; i++) {
    if (s[i] != ' ' && s[i] != '\t' && s[i] != '\n' && s[i] != '\r') {
      all_ws = false;
      break;
    }
  }
  if (all_ws) return;
  xml_node_append_text(ctx->stack[ctx->depth - 1], s, len);
}

static valk_lval_t* valk_builtin_xml_parse(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char* input = valk_lval_list_nth(a, 0)->str;
  size_t input_len = strlen(input);
  if (input_len > (size_t)INT_MAX)
    return valk_lval_err("xml/parse: input too large (%zu bytes)", input_len);

  XML_Parser parser = XML_ParserCreate(NULL);
  if (!parser) // LCOV_EXCL_BR_LINE - OOM
    return valk_lval_err("xml/parse: failed to create parser"); // LCOV_EXCL_LINE

  xml_parse_ctx_t ctx = {
      .stack = malloc(32 * sizeof(xml_node_t*)),
      .depth = 0,
      .cap = 32,
      .error = false,
  };

  XML_SetUserData(parser, &ctx);
  XML_SetElementHandler(parser, on_start, on_end);
  XML_SetCharacterDataHandler(parser, on_chardata);

  enum XML_Status status = XML_Parse(parser, input, (int)input_len, XML_TRUE);

  valk_lval_t* result;
  if (status == XML_STATUS_ERROR) {
    snprintf(ctx.error_msg, sizeof(ctx.error_msg), "xml/parse: %s at line %lu",
             XML_ErrorString(XML_GetErrorCode(parser)),
             XML_GetCurrentLineNumber(parser));
    result = valk_lval_err("%s", ctx.error_msg);
  } else if (ctx.depth <= 0) {
    result = valk_lval_err("xml/parse: empty document");
  } else {
    result = xml_node_to_lval(ctx.stack[0]);
  }

  if (ctx.depth > 0) xml_node_free(ctx.stack[0]);
  free(ctx.stack);
  XML_ParserFree(parser);
  return result;
}

void valk_register_xml_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "xml/parse", valk_builtin_xml_parse);
}
