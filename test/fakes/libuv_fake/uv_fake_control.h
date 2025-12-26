#pragma once

#include "uv_fake.h"

void uv_fake_time_set(uv_loop_t *loop, uint64_t time_ms);
void uv_fake_time_advance(uv_loop_t *loop, uint64_t delta_ms);
uint64_t uv_fake_time_get(uv_loop_t *loop);

int uv_fake_run_pending(uv_loop_t *loop);

size_t uv_fake_timer_count(uv_loop_t *loop);
size_t uv_fake_active_handles(uv_loop_t *loop);

void uv_fake_reset(uv_loop_t *loop);

void uv_fake_inject_connection(uv_tcp_t *server, uv_tcp_t *client);

void uv_fake_inject_read_data(uv_tcp_t *tcp, const void *data, size_t len);

void uv_fake_inject_read_eof(uv_tcp_t *tcp);

void uv_fake_inject_read_error(uv_tcp_t *tcp, int error);

size_t uv_fake_get_written_data(uv_tcp_t *tcp, void *buf, size_t max_len);

void uv_fake_clear_written_data(uv_tcp_t *tcp);

void uv_fake_process_io(uv_loop_t *loop);
