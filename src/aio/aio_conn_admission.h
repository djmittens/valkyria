#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#include "aio_pressure.h"

struct valk_aio_system;

typedef struct valk_conn_admission_ctx {
  valk_pressure_config_t config;
  uint32_t random_state;
} valk_conn_admission_ctx_t;

void valk_conn_admission_init(valk_conn_admission_ctx_t *ctx, const valk_pressure_config_t *config);

void valk_conn_admission_init_from_config(valk_conn_admission_ctx_t *ctx,
                                           float high_watermark,
                                           float critical_watermark,
                                           uint32_t backpressure_timeout_ms);

valk_pressure_state_t valk_conn_admission_snapshot(struct valk_aio_system *sys, uint64_t now_ms);

typedef struct valk_conn_admission_result {
  bool accept;
  valk_pressure_level_e level;
  const char *reason;
} valk_conn_admission_result_t;

valk_conn_admission_result_t valk_conn_admission_check(
    valk_conn_admission_ctx_t *ctx,
    const valk_pressure_state_t *state);

float valk_conn_admission_random(valk_conn_admission_ctx_t *ctx);

void valk_conn_admission_seed(valk_conn_admission_ctx_t *ctx, uint32_t seed);
