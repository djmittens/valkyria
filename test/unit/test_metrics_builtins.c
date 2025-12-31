#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"

#ifdef VALK_METRICS_ENABLED
#include "../../src/metrics_v2.h"

#include <stdio.h>
#include <string.h>

extern void valk_register_metrics_builtins(valk_lenv_t *env);

static valk_lenv_t *create_test_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_register_metrics_builtins(env);
  return env;
}

static valk_lval_t *call_builtin(valk_lenv_t *env, const char *name, valk_lval_t *args) {
  valk_lval_t *sym = valk_lval_sym(name);
  valk_lval_t *fun = valk_lval_eval(env, sym);
  if (LVAL_TYPE(fun) == LVAL_ERR) {
    return fun;
  }
  return valk_lval_eval_call(env, fun, args);
}

void test_counter_create(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("test_counter_builtin")
  }, 1);

  valk_lval_t *result = call_builtin(env, "metrics/counter", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should return a ref");
  VALK_TEST_ASSERT(strcmp(result->ref.type, "metrics_counter") == 0, "Ref type should be metrics_counter");

  VALK_PASS();
}

void test_counter_create_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/counter", args);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error for no args");
  VALK_TEST_ASSERT(strstr(result->str, "expected at least 1 argument") != nullptr,
                   "Error should mention expected arguments");

  VALK_PASS();
}

void test_counter_create_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_num(42)
  }, 1);

  valk_lval_t *result = call_builtin(env, "metrics/counter", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error for wrong type");
  VALK_TEST_ASSERT(strstr(result->str, "name must be a string") != nullptr,
                   "Error should mention name must be string");

  VALK_PASS();
}

void test_counter_create_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("http_requests_labeled"),
    valk_lval_str("method"),
    valk_lval_str("GET"),
    valk_lval_str("path"),
    valk_lval_str("/api")
  }, 5);

  valk_lval_t *result = call_builtin(env, "metrics/counter", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should return a ref");
  VALK_TEST_ASSERT(strcmp(result->ref.type, "metrics_counter") == 0, "Ref type should be metrics_counter");

  VALK_PASS();
}

void test_counter_create_invalid_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("counter_invalid_labels"),
    valk_lval_str("key"),
    valk_lval_num(123)
  }, 3);

  valk_lval_t *result = call_builtin(env, "metrics/counter", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error for invalid label value");

  VALK_PASS();
}

void test_counter_inc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("inc_test_counter")
  }, 1);

  valk_lval_t *counter = call_builtin(env, "metrics/counter", create_args);
  VALK_TEST_ASSERT(LVAL_TYPE(counter) == LVAL_REF, "Should create counter");

  valk_lval_t *inc_args = valk_lval_list((valk_lval_t*[]){counter}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/counter-inc", inc_args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL, "Should return nil");

  VALK_PASS();
}

void test_counter_inc_with_value(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("inc_value_test_counter")
  }, 1);

  valk_lval_t *counter = call_builtin(env, "metrics/counter", create_args);
  VALK_TEST_ASSERT(LVAL_TYPE(counter) == LVAL_REF, "Should create counter");

  valk_lval_t *inc_args = valk_lval_list((valk_lval_t*[]){
    counter,
    valk_lval_num(10)
  }, 2);
  valk_lval_t *result = call_builtin(env, "metrics/counter-inc", inc_args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL, "Should return nil");

  VALK_PASS();
}

void test_counter_inc_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/counter-inc", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_counter_inc_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", nullptr, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){fake_ref}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/counter-inc", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");
  VALK_TEST_ASSERT(strstr(result->str, "counter handle") != nullptr,
                   "Error should mention counter handle");

  VALK_PASS();
}

void test_counter_inc_not_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_str("not a ref")}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/counter-inc", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_counter_inc_wrong_n_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("counter_wrong_n")
  }, 1);
  valk_lval_t *counter = call_builtin(env, "metrics/counter", create_args);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    counter,
    valk_lval_str("not a number")
  }, 2);
  valk_lval_t *result = call_builtin(env, "metrics/counter-inc", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_create(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("test_gauge_builtin")
  }, 1);

  valk_lval_t *result = call_builtin(env, "metrics/gauge", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should return a ref");
  VALK_TEST_ASSERT(strcmp(result->ref.type, "metrics_gauge") == 0, "Ref type should be metrics_gauge");

  VALK_PASS();
}

void test_gauge_create_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/gauge", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_create_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/gauge", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_create_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("gauge_labeled"),
    valk_lval_str("region"),
    valk_lval_str("us-east")
  }, 3);

  valk_lval_t *result = call_builtin(env, "metrics/gauge", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should return a ref");

  VALK_PASS();
}

void test_gauge_create_invalid_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("gauge_invalid_labels"),
    valk_lval_num(123),
    valk_lval_str("value")
  }, 3);

  valk_lval_t *result = call_builtin(env, "metrics/gauge", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_set(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("set_test_gauge")
  }, 1);
  valk_lval_t *gauge = call_builtin(env, "metrics/gauge", create_args);
  VALK_TEST_ASSERT(LVAL_TYPE(gauge) == LVAL_REF, "Should create gauge");

  valk_lval_t *set_args = valk_lval_list((valk_lval_t*[]){
    gauge,
    valk_lval_num(100)
  }, 2);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-set", set_args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL, "Should return nil");

  VALK_PASS();
}

void test_gauge_set_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-set", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_set_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", nullptr, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){fake_ref, valk_lval_num(100)}, 2);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-set", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_set_not_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_str("not ref"), valk_lval_num(100)}, 2);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-set", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_set_wrong_value_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("gauge_wrong_value")
  }, 1);
  valk_lval_t *gauge = call_builtin(env, "metrics/gauge", create_args);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){gauge, valk_lval_str("not a number")}, 2);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-set", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_inc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("inc_test_gauge")
  }, 1);
  valk_lval_t *gauge = call_builtin(env, "metrics/gauge", create_args);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){gauge}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-inc", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL, "Should return nil");

  VALK_PASS();
}

void test_gauge_inc_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/gauge-inc", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_inc_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", nullptr, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){fake_ref}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-inc", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_inc_not_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_str("not ref")}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-inc", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_dec(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("dec_test_gauge")
  }, 1);
  valk_lval_t *gauge = call_builtin(env, "metrics/gauge", create_args);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){gauge}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-dec", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL, "Should return nil");

  VALK_PASS();
}

void test_gauge_dec_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/gauge-dec", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_dec_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", nullptr, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){fake_ref}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-dec", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_gauge_dec_not_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_str("not ref")}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/gauge-dec", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_histogram_create(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("test_histogram_builtin")
  }, 1);

  valk_lval_t *result = call_builtin(env, "metrics/histogram", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should return a ref");
  VALK_TEST_ASSERT(strcmp(result->ref.type, "metrics_histogram") == 0, "Ref type should be metrics_histogram");

  VALK_PASS();
}

void test_histogram_create_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/histogram", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_histogram_create_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/histogram", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_histogram_create_with_buckets(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *buckets = valk_lval_qlist((valk_lval_t*[]){
    valk_lval_num(1),
    valk_lval_num(5),
    valk_lval_num(10),
    valk_lval_num(50),
    valk_lval_num(100)
  }, 5);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("histogram_with_buckets"),
    valk_lval_sym(":buckets"),
    buckets
  }, 3);

  valk_lval_t *result = call_builtin(env, "metrics/histogram", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should return a ref");

  VALK_PASS();
}

void test_histogram_create_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("histogram_labeled"),
    valk_lval_str("method"),
    valk_lval_str("GET")
  }, 3);

  valk_lval_t *result = call_builtin(env, "metrics/histogram", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should return a ref");

  VALK_PASS();
}

void test_histogram_create_invalid_label_value(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("histogram_invalid_label"),
    valk_lval_str("method"),
    valk_lval_num(123)
  }, 3);

  valk_lval_t *result = call_builtin(env, "metrics/histogram", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_histogram_create_invalid_buckets_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("histogram_invalid_buckets"),
    valk_lval_sym(":buckets"),
    valk_lval_str("not a list")
  }, 3);

  valk_lval_t *result = call_builtin(env, "metrics/histogram", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_histogram_observe(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("observe_test_histogram")
  }, 1);
  valk_lval_t *histogram = call_builtin(env, "metrics/histogram", create_args);
  VALK_TEST_ASSERT(LVAL_TYPE(histogram) == LVAL_REF, "Should create histogram");

  valk_lval_t *observe_args = valk_lval_list((valk_lval_t*[]){
    histogram,
    valk_lval_num(1000)
  }, 2);
  valk_lval_t *result = call_builtin(env, "metrics/histogram-observe", observe_args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL, "Should return nil");

  VALK_PASS();
}

void test_histogram_observe_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/histogram-observe", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_histogram_observe_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", nullptr, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){fake_ref, valk_lval_num(1000)}, 2);
  valk_lval_t *result = call_builtin(env, "metrics/histogram-observe", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_histogram_observe_not_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_str("not ref"), valk_lval_num(1000)}, 2);
  valk_lval_t *result = call_builtin(env, "metrics/histogram-observe", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_histogram_observe_wrong_value_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("histogram_wrong_value")
  }, 1);
  valk_lval_t *histogram = call_builtin(env, "metrics/histogram", create_args);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){histogram, valk_lval_str("not a number")}, 2);
  valk_lval_t *result = call_builtin(env, "metrics/histogram-observe", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_collect_delta(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/collect-delta", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should return a ref");
  VALK_TEST_ASSERT(strcmp(result->ref.type, "metrics_delta") == 0, "Ref type should be metrics_delta");

  VALK_PASS();
}

void test_collect_delta_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/collect-delta", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_delta_json(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *collect_args = valk_lval_nil();
  valk_lval_t *delta = call_builtin(env, "metrics/collect-delta", collect_args);
  VALK_TEST_ASSERT(LVAL_TYPE(delta) == LVAL_REF, "Should create delta");

  valk_lval_t *json_args = valk_lval_list((valk_lval_t*[]){delta}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/delta-json", json_args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_STR, "Should return string");
  VALK_TEST_ASSERT(strstr(result->str, "ts") != nullptr, "JSON should contain ts");

  VALK_PASS();
}

void test_delta_json_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/delta-json", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_delta_json_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *fake_ref = valk_lval_ref("wrong_type", nullptr, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){fake_ref}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/delta-json", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_delta_json_not_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_str("not ref")}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/delta-json", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_prometheus(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/prometheus", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_STR, "Should return string");

  VALK_PASS();
}

void test_prometheus_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/prometheus", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_metrics_json(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = call_builtin(env, "metrics/json", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_STR, "Should return string");
  VALK_TEST_ASSERT(result->str[0] == '{', "Should start with {");

  VALK_PASS();
}

void test_metrics_json_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){valk_lval_num(42)}, 1);
  valk_lval_t *result = call_builtin(env, "metrics/json", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error");

  VALK_PASS();
}

void test_delta_snapshot_cleanup(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *delta = call_builtin(env, "metrics/collect-delta", args);
  VALK_TEST_ASSERT(LVAL_TYPE(delta) == LVAL_REF, "Should create delta");

  if (delta->ref.free) {
    delta->ref.free(delta->ref.ptr);
    delta->ref.ptr = nullptr;
    delta->ref.free = nullptr;
  }

  VALK_PASS();
}

void test_delta_snapshot_cleanup_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *delta = call_builtin(env, "metrics/collect-delta", args);
  VALK_TEST_ASSERT(LVAL_TYPE(delta) == LVAL_REF, "Should create delta");

  if (delta->ref.free) {
    delta->ref.free(nullptr);
  }

  VALK_PASS();
}

void test_counter_create_max_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("counter_max_labels"),
    valk_lval_str("l1"), valk_lval_str("v1"),
    valk_lval_str("l2"), valk_lval_str("v2"),
    valk_lval_str("l3"), valk_lval_str("v3"),
    valk_lval_str("l4"), valk_lval_str("v4"),
    valk_lval_str("l5"), valk_lval_str("v5"),
    valk_lval_str("l6"), valk_lval_str("v6"),
    valk_lval_str("l7"), valk_lval_str("v7"),
    valk_lval_str("l8"), valk_lval_str("v8"),
    valk_lval_str("l9"), valk_lval_str("v9"),
    valk_lval_str("l10"), valk_lval_str("v10")
  }, 21);

  valk_lval_t *result = call_builtin(env, "metrics/counter", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should succeed even with overflow labels");

  VALK_PASS();
}

void test_gauge_create_max_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("gauge_max_labels"),
    valk_lval_str("l1"), valk_lval_str("v1"),
    valk_lval_str("l2"), valk_lval_str("v2"),
    valk_lval_str("l3"), valk_lval_str("v3"),
    valk_lval_str("l4"), valk_lval_str("v4"),
    valk_lval_str("l5"), valk_lval_str("v5"),
    valk_lval_str("l6"), valk_lval_str("v6"),
    valk_lval_str("l7"), valk_lval_str("v7"),
    valk_lval_str("l8"), valk_lval_str("v8"),
    valk_lval_str("l9"), valk_lval_str("v9")
  }, 19);

  valk_lval_t *result = call_builtin(env, "metrics/gauge", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should succeed with max labels overflow");

  VALK_PASS();
}

void test_histogram_create_max_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("histogram_max_labels"),
    valk_lval_str("l1"), valk_lval_str("v1"),
    valk_lval_str("l2"), valk_lval_str("v2"),
    valk_lval_str("l3"), valk_lval_str("v3"),
    valk_lval_str("l4"), valk_lval_str("v4"),
    valk_lval_str("l5"), valk_lval_str("v5"),
    valk_lval_str("l6"), valk_lval_str("v6"),
    valk_lval_str("l7"), valk_lval_str("v7"),
    valk_lval_str("l8"), valk_lval_str("v8"),
    valk_lval_str("l9"), valk_lval_str("v9")
  }, 19);

  valk_lval_t *result = call_builtin(env, "metrics/histogram", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should succeed with max labels overflow");

  VALK_PASS();
}

void test_histogram_create_max_buckets(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *buckets = valk_lval_qlist((valk_lval_t*[]){
    valk_lval_num(1), valk_lval_num(2), valk_lval_num(3), valk_lval_num(4),
    valk_lval_num(5), valk_lval_num(6), valk_lval_num(7), valk_lval_num(8),
    valk_lval_num(9), valk_lval_num(10), valk_lval_num(11), valk_lval_num(12),
    valk_lval_num(13), valk_lval_num(14), valk_lval_num(15), valk_lval_num(16),
    valk_lval_num(17), valk_lval_num(18), valk_lval_num(19), valk_lval_num(20),
    valk_lval_num(21), valk_lval_num(22), valk_lval_num(23), valk_lval_num(24),
    valk_lval_num(25), valk_lval_num(26), valk_lval_num(27), valk_lval_num(28),
    valk_lval_num(29), valk_lval_num(30), valk_lval_num(31), valk_lval_num(32),
    valk_lval_num(33), valk_lval_num(34), valk_lval_num(35), valk_lval_num(36)
  }, 36);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("histogram_max_buckets"),
    valk_lval_sym(":buckets"),
    buckets
  }, 3);

  valk_lval_t *result = call_builtin(env, "metrics/histogram", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_REF, "Should succeed with max buckets overflow");

  VALK_PASS();
}

void test_counter_inc_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  valk_lenv_t *env = create_test_env();

  valk_lval_t *create_args = valk_lval_list((valk_lval_t*[]){
    valk_lval_str("counter_too_many_args")
  }, 1);
  valk_lval_t *counter = call_builtin(env, "metrics/counter", create_args);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    counter,
    valk_lval_num(10),
    valk_lval_num(20)
  }, 3);
  valk_lval_t *result = call_builtin(env, "metrics/counter-inc", args);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Should return error for too many args");

  VALK_PASS();
}

#else

void test_metrics_builtins_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("Metrics builtins tests require VALK_METRICS_ENABLED");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_counter_create", test_counter_create);
  valk_testsuite_add_test(suite, "test_counter_create_no_args", test_counter_create_no_args);
  valk_testsuite_add_test(suite, "test_counter_create_wrong_type", test_counter_create_wrong_type);
  valk_testsuite_add_test(suite, "test_counter_create_with_labels", test_counter_create_with_labels);
  valk_testsuite_add_test(suite, "test_counter_create_invalid_labels", test_counter_create_invalid_labels);
  valk_testsuite_add_test(suite, "test_counter_inc", test_counter_inc);
  valk_testsuite_add_test(suite, "test_counter_inc_with_value", test_counter_inc_with_value);
  valk_testsuite_add_test(suite, "test_counter_inc_no_args", test_counter_inc_no_args);
  valk_testsuite_add_test(suite, "test_counter_inc_wrong_ref_type", test_counter_inc_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_counter_inc_not_ref", test_counter_inc_not_ref);
  valk_testsuite_add_test(suite, "test_counter_inc_wrong_n_type", test_counter_inc_wrong_n_type);
  valk_testsuite_add_test(suite, "test_counter_inc_too_many_args", test_counter_inc_too_many_args);
  valk_testsuite_add_test(suite, "test_gauge_create", test_gauge_create);
  valk_testsuite_add_test(suite, "test_gauge_create_no_args", test_gauge_create_no_args);
  valk_testsuite_add_test(suite, "test_gauge_create_wrong_type", test_gauge_create_wrong_type);
  valk_testsuite_add_test(suite, "test_gauge_create_with_labels", test_gauge_create_with_labels);
  valk_testsuite_add_test(suite, "test_gauge_create_invalid_labels", test_gauge_create_invalid_labels);
  valk_testsuite_add_test(suite, "test_gauge_set", test_gauge_set);
  valk_testsuite_add_test(suite, "test_gauge_set_wrong_args", test_gauge_set_wrong_args);
  valk_testsuite_add_test(suite, "test_gauge_set_wrong_ref_type", test_gauge_set_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_gauge_set_not_ref", test_gauge_set_not_ref);
  valk_testsuite_add_test(suite, "test_gauge_set_wrong_value_type", test_gauge_set_wrong_value_type);
  valk_testsuite_add_test(suite, "test_gauge_inc", test_gauge_inc);
  valk_testsuite_add_test(suite, "test_gauge_inc_wrong_args", test_gauge_inc_wrong_args);
  valk_testsuite_add_test(suite, "test_gauge_inc_wrong_ref_type", test_gauge_inc_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_gauge_inc_not_ref", test_gauge_inc_not_ref);
  valk_testsuite_add_test(suite, "test_gauge_dec", test_gauge_dec);
  valk_testsuite_add_test(suite, "test_gauge_dec_wrong_args", test_gauge_dec_wrong_args);
  valk_testsuite_add_test(suite, "test_gauge_dec_wrong_ref_type", test_gauge_dec_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_gauge_dec_not_ref", test_gauge_dec_not_ref);
  valk_testsuite_add_test(suite, "test_histogram_create", test_histogram_create);
  valk_testsuite_add_test(suite, "test_histogram_create_no_args", test_histogram_create_no_args);
  valk_testsuite_add_test(suite, "test_histogram_create_wrong_type", test_histogram_create_wrong_type);
  valk_testsuite_add_test(suite, "test_histogram_create_with_buckets", test_histogram_create_with_buckets);
  valk_testsuite_add_test(suite, "test_histogram_create_with_labels", test_histogram_create_with_labels);
  valk_testsuite_add_test(suite, "test_histogram_create_invalid_label_value", test_histogram_create_invalid_label_value);
  valk_testsuite_add_test(suite, "test_histogram_create_invalid_buckets_type", test_histogram_create_invalid_buckets_type);
  valk_testsuite_add_test(suite, "test_histogram_observe", test_histogram_observe);
  valk_testsuite_add_test(suite, "test_histogram_observe_wrong_args", test_histogram_observe_wrong_args);
  valk_testsuite_add_test(suite, "test_histogram_observe_wrong_ref_type", test_histogram_observe_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_histogram_observe_not_ref", test_histogram_observe_not_ref);
  valk_testsuite_add_test(suite, "test_histogram_observe_wrong_value_type", test_histogram_observe_wrong_value_type);
  valk_testsuite_add_test(suite, "test_collect_delta", test_collect_delta);
  valk_testsuite_add_test(suite, "test_collect_delta_wrong_args", test_collect_delta_wrong_args);
  valk_testsuite_add_test(suite, "test_delta_json", test_delta_json);
  valk_testsuite_add_test(suite, "test_delta_json_wrong_args", test_delta_json_wrong_args);
  valk_testsuite_add_test(suite, "test_delta_json_wrong_ref_type", test_delta_json_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_delta_json_not_ref", test_delta_json_not_ref);
  valk_testsuite_add_test(suite, "test_prometheus", test_prometheus);
  valk_testsuite_add_test(suite, "test_prometheus_wrong_args", test_prometheus_wrong_args);
  valk_testsuite_add_test(suite, "test_metrics_json", test_metrics_json);
  valk_testsuite_add_test(suite, "test_metrics_json_wrong_args", test_metrics_json_wrong_args);
  valk_testsuite_add_test(suite, "test_delta_snapshot_cleanup", test_delta_snapshot_cleanup);
  valk_testsuite_add_test(suite, "test_delta_snapshot_cleanup_null", test_delta_snapshot_cleanup_null);
  valk_testsuite_add_test(suite, "test_counter_create_max_labels", test_counter_create_max_labels);
  valk_testsuite_add_test(suite, "test_gauge_create_max_labels", test_gauge_create_max_labels);
  valk_testsuite_add_test(suite, "test_histogram_create_max_labels", test_histogram_create_max_labels);
  valk_testsuite_add_test(suite, "test_histogram_create_max_buckets", test_histogram_create_max_buckets);
#else
  valk_testsuite_add_test(suite, "test_metrics_builtins_disabled", test_metrics_builtins_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
