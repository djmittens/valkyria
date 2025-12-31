#include "debug.h"
#include "common.h"

#ifdef __linux__
#include <backtrace.h>
#endif
#include <dlfcn.h>
#include <execinfo.h>
#include <stdio.h>
#include <stdlib.h>

u64 valk_trace_capture(void** stack, u64 n) {
  return backtrace(stack, n);
}

#ifdef __linux__
static int __valk_trace_info_cb(void* data, uptr pc, const char* filename,
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

void valk_trace_print(void** stack, u64 num) {
  char** strings;

#ifdef __linux__
  static struct backtrace_state* valkBtState = nullptr;
  if (!valkBtState) {
    valkBtState = backtrace_create_state(nullptr, 0, nullptr, nullptr);
  }
#endif

  strings = backtrace_symbols(stack, num);

  for (u64 j = 0; j < num; ++j) {
    printf("- [#%llu] %s\n", (unsigned long long)j, strings[j]);

#ifdef __linux__
    backtrace_pcinfo(valkBtState, (uptr)stack[j], __valk_trace_info_cb,
                     __valk_trace_error_cb, nullptr);
#else
    void *addr = stack[j];
    Dl_info info;

    // COVERAGE_EXEMPT: Platform-dependent dladdr behavior - can't control symbol resolution
    if (dladdr(addr, &info) && info.dli_sname) {
      uptr offset_in_sym =
          info.dli_saddr ? (uptr)addr - (uptr)info.dli_saddr : 0;  // COVERAGE_EXEMPT: dli_saddr nullptr depends on linker
      fprintf(stderr, "  → %s+0x%llx\n", info.dli_sname, (unsigned long long)offset_in_sym);
    }
#endif
  }
  free(strings);
}
