#pragma once

#include <stddef.h>
#define VALK_TRACE_MAX 50
#define VALK_TRACE_DEPTH 10

size_t valk_trace_capture(void** stack, size_t n);

void valk_trace_print(void** stack, size_t num);
