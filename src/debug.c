#include "debug.h"
#include "common.h"

#ifdef __linux__
#include <backtrace.h>
#endif
#include <dlfcn.h>
#include <execinfo.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

size_t valk_trace_capture(void** stack, size_t n) {
  return backtrace(stack, n);
}

#ifdef __linux__
static int __valk_trace_info_cb(void* data, uintptr_t pc, const char* filename,
                                int lineno, const char* function) {
  UNUSED(data);
  UNUSED(pc);
  fprintf(stderr, "  → %s() %s:%d\n", function, filename ? filename : "??",
          lineno);
  return 0;
}
static void __valk_trace_error_cb(void* data, const char* msg, int errnum) {
  UNUSED(data);
  fprintf(stderr, "   [symbol resolution error: %s (%d)]\n", msg, errnum);
}
#endif

void valk_trace_print(void** stack, size_t num) {
  char** strings;

#ifdef __linux__
  static struct backtrace_state* valkBtState = nullptr;
  if (!valkBtState) {
    valkBtState = backtrace_create_state(nullptr, 0, nullptr, nullptr);
  }
#endif

  strings = backtrace_symbols(stack, num);

  for (size_t j = 0; j < num; ++j) {
    printf("- [#%ld] %s\n", j, strings[j]);

#ifdef __linux__
    backtrace_pcinfo(valkBtState, (uintptr_t)stack[j], __valk_trace_info_cb,
                     __valk_trace_error_cb, nullptr);
#else
    void *addr = stack[j];
    Dl_info info;

    if (dladdr(addr, &info) && info.dli_sname) {
      uintptr_t offset_in_sym =
          info.dli_saddr ? (uintptr_t)addr - (uintptr_t)info.dli_saddr : 0;
      fprintf(stderr, "  → %s+0x%lx\n", info.dli_sname, offset_in_sym);
    }
#endif
  }
  free(strings);
}
