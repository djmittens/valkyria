#pragma once

#include "types.h"
#include <stddef.h>
#define VALK_TRACE_MAX 50
#define VALK_TRACE_DEPTH 10

u64 valk_trace_capture(void** stack, u64 n);

void valk_trace_print(void** stack, u64 num);
