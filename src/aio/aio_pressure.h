#pragma once
#include "types.h"

#include <stdbool.h>

typedef struct valk_pressure_state {
  float tcp_write_slab_usage;
  float arena_slab_usage;
  float pending_stream_usage;
  float handle_slab_usage;

  u32 active_connections;
  u32 backpressure_queue_len;
  u32 pending_stream_count;

  u64 oldest_backpressure_age_ms;
  u64 oldest_pending_stream_age_ms;
} valk_pressure_state_t;

typedef struct valk_pressure_config {
  float high_watermark;
  float critical_watermark;

  u32 backpressure_max;
  u32 backpressure_timeout_ms;

  u32 pending_stream_max;
  u32 pending_stream_timeout_ms;
} valk_pressure_config_t;

typedef enum {
  VALK_PRESSURE_NORMAL,
  VALK_PRESSURE_ELEVATED,
  VALK_PRESSURE_HIGH,
  VALK_PRESSURE_CRITICAL,
} valk_pressure_level_e;

typedef struct valk_pressure_decision {
  valk_pressure_level_e level;

  bool accept_connection;
  float connection_shed_probability;

  bool accept_stream;
  bool use_pending_queue;

  bool drop_oldest_backpressure;
  bool drop_oldest_pending_stream;
  u32 connections_to_timeout;
} valk_pressure_decision_t;

valk_pressure_decision_t valk_pressure_evaluate(
    const valk_pressure_state_t *state,
    const valk_pressure_config_t *config
);

valk_pressure_config_t valk_pressure_config_default(void);

const char *valk_pressure_level_str(valk_pressure_level_e level);
