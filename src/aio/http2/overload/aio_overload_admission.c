#include "aio_overload_admission.h"
#include "aio_internal.h"

void valk_conn_admission_init(valk_conn_admission_ctx_t *ctx, const valk_pressure_config_t *config) {
  if (!ctx) return;
  if (config) {
    ctx->config = *config;
  } else {
    ctx->config = valk_pressure_config_default();
  }
  ctx->random_state = 12345;
}

void valk_conn_admission_init_from_config(valk_conn_admission_ctx_t *ctx,
                                           float high_watermark,
                                           float critical_watermark,
                                           u32 backpressure_timeout_ms) {
  if (!ctx) return;
  ctx->config = valk_pressure_config_default();
  if (high_watermark > 0.0f) ctx->config.high_watermark = high_watermark;
  if (critical_watermark > 0.0f) ctx->config.critical_watermark = critical_watermark;
  if (backpressure_timeout_ms > 0) ctx->config.backpressure_timeout_ms = backpressure_timeout_ms;
  ctx->random_state = 12345;
}

static float slab_usage(valk_slab_t *slab) {
  if (!slab || slab->numItems == 0) return 0.0f;
  u64 available = valk_slab_available(slab);
  return 1.0f - ((float)available / (float)slab->numItems);
}

static u64 oldest_backpressure_age(valk_backpressure_list_t *list, u64 now_ms) {
  if (!list || !list->head) return 0;
  
  u64 oldest = 0;
  for (valk_aio_handle_t *h = list->head; h; h = h->http.backpressure_next) {
    if (h->http.backpressure_start_time > 0 && h->http.backpressure_start_time <= now_ms) {
      u64 age = now_ms - h->http.backpressure_start_time;
      if (age > oldest) oldest = age;
    }
  }
  return oldest;
}

static u64 oldest_pending_stream_age(valk_pending_stream_queue_t *queue, u64 now_ms) {
  if (!queue || !queue->head) return 0;
  
  u64 oldest = 0;
  for (valk_pending_stream_t *ps = queue->head; ps; ps = ps->next) {
    if (ps->queued_time_ms > 0 && ps->queued_time_ms <= now_ms) {
      u64 age = now_ms - ps->queued_time_ms;
      if (age > oldest) oldest = age;
    }
  }
  return oldest;
}

valk_pressure_state_t valk_conn_admission_snapshot(valk_aio_system_t *sys, u64 now_ms) {
  valk_pressure_state_t state = {0};
  if (!sys) return state;

  state.tcp_write_slab_usage = slab_usage(sys->tcpBufferSlab);
  state.arena_slab_usage = slab_usage(sys->httpStreamArenas);
  state.handle_slab_usage = slab_usage(sys->handleSlab);

  if (sys->pending_streams.pool.capacity > 0) {
    state.pending_stream_usage = (float)sys->pending_streams.count /
                                  (float)sys->pending_streams.pool.capacity;
    state.pending_stream_count = (u32)sys->pending_streams.count;
  }

  state.backpressure_queue_len = (u32)sys->backpressure.size;
  state.oldest_backpressure_age_ms = oldest_backpressure_age(&sys->backpressure, now_ms);
  state.oldest_pending_stream_age_ms = oldest_pending_stream_age(&sys->pending_streams, now_ms);

  return state;
}

float valk_conn_admission_random(valk_conn_admission_ctx_t *ctx) {
  ctx->random_state = ctx->random_state * 1103515245 + 12345;
  return (float)(ctx->random_state >> 16) / 32768.0f;
}

void valk_conn_admission_seed(valk_conn_admission_ctx_t *ctx, u32 seed) {
  if (ctx) ctx->random_state = seed;
}

valk_conn_admission_result_t valk_conn_admission_check(
    valk_conn_admission_ctx_t *ctx,
    const valk_pressure_state_t *state) {
  
  valk_conn_admission_result_t result = {.accept = true, .level = VALK_PRESSURE_NORMAL, .reason = nullptr};
  
  if (!ctx || !state) {
    result.accept = true;
    return result;
  }

  valk_pressure_decision_t decision = valk_pressure_evaluate(state, &ctx->config);
  result.level = decision.level;

  if (!decision.accept_connection) {
    result.accept = false;
    result.reason = decision.level == VALK_PRESSURE_CRITICAL 
                    ? "critical pressure" 
                    : "high pressure";
    return result;
  }

  if (decision.connection_shed_probability > 0.0f) {
    float r = valk_conn_admission_random(ctx);
    if (r < decision.connection_shed_probability) {
      result.accept = false;
      result.reason = "probabilistic shed";
      return result;
    }
  }

  result.accept = true;
  return result;
}
