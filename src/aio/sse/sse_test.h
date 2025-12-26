#ifndef VALK_SSE_TEST_H
#define VALK_SSE_TEST_H

#include "../aio_sse.h"
#include <stdbool.h>
#include <stddef.h>

typedef struct valk_test_sse_ctx valk_test_sse_ctx_t;

valk_sse_stream_t *valk_test_sse_create(void);

void valk_test_sse_free(valk_sse_stream_t *stream);

size_t valk_test_sse_bytes_written(valk_sse_stream_t *stream);

size_t valk_test_sse_events_count(valk_sse_stream_t *stream);

char *valk_test_sse_capture_output(valk_sse_stream_t *stream);

void valk_test_sse_reset_capture(valk_sse_stream_t *stream);

bool valk_test_sse_has_event(valk_sse_stream_t *stream, const char *event_type, const char *data);

void valk_test_sse_simulate_drain(valk_sse_stream_t *stream);

void valk_test_sse_simulate_close(valk_sse_stream_t *stream);

int valk_test_sse_send_event(valk_sse_stream_t *stream, const char *event_type,
                              const char *data, size_t len, uint64_t id);

#endif // VALK_SSE_TEST_H
