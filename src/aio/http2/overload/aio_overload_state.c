#include "aio_overload_state.h"

valk_pressure_config_t valk_pressure_config_default(void) {
  return (valk_pressure_config_t){
    .high_watermark = 0.85f,
    .critical_watermark = 0.95f,
    .backpressure_max = 1000,
    .backpressure_timeout_ms = 30000,
  };
}

valk_pressure_decision_t valk_pressure_evaluate(
    const valk_pressure_state_t *state,
    const valk_pressure_config_t *config
) {
  valk_pressure_decision_t decision = {0};

  float tcp_usage = state->tcp_write_slab_usage;

  if (tcp_usage >= config->critical_watermark) {
    decision.level = VALK_PRESSURE_CRITICAL;
  } else if (tcp_usage >= config->high_watermark) {
    decision.level = VALK_PRESSURE_HIGH;
  } else if (tcp_usage >= config->high_watermark * 0.7f) {
    decision.level = VALK_PRESSURE_ELEVATED;
  } else {
    decision.level = VALK_PRESSURE_NORMAL;
  }

  switch (decision.level) {
    case VALK_PRESSURE_NORMAL:
      decision.accept_connection = true;
      decision.connection_shed_probability = 0.0f;
      break;

    case VALK_PRESSURE_ELEVATED: {
      decision.accept_connection = true;
      float elevated_threshold = config->high_watermark * 0.7f;
      float range = config->high_watermark - elevated_threshold;
      if (range > 0.0f) {
        decision.connection_shed_probability =
          (tcp_usage - elevated_threshold) / range * 0.3f;
      } else {
        decision.connection_shed_probability = 0.0f;
      }
      break;
    }

    case VALK_PRESSURE_HIGH:
      decision.accept_connection = false;
      decision.connection_shed_probability = 1.0f;
      break;

    case VALK_PRESSURE_CRITICAL:
      decision.accept_connection = false;
      decision.connection_shed_probability = 1.0f;
      decision.drop_oldest_backpressure = true;
      break;
  }

  decision.accept_stream = state->arena_slab_usage < config->critical_watermark;

  if (state->oldest_backpressure_age_ms > config->backpressure_timeout_ms) {
    decision.drop_oldest_backpressure = true;
  }

  return decision;
}

const char *valk_pressure_level_str(valk_pressure_level_e level) {
  switch (level) {
    case VALK_PRESSURE_NORMAL:   return "NORMAL";
    case VALK_PRESSURE_ELEVATED: return "ELEVATED";
    case VALK_PRESSURE_HIGH:     return "HIGH";
    case VALK_PRESSURE_CRITICAL: return "CRITICAL";
    default:                     return "UNKNOWN";
  }
}
