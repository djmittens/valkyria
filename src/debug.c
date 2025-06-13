#include "debug.h"

#include <backtrace.h>
#include <dlfcn.h>
#include <execinfo.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

size_t valk_trace_capture(void** stack, size_t n) {
  return backtrace(stack, n);
}

static int __valk_trace_info_cb(void* data, uintptr_t pc, const char* filename,
                                int lineno, const char* function) {
  fprintf(stderr, "  → %s() %s:%d\n", function, filename ? filename : "??",
          lineno);
  return 0;
}
static void __valk_trace_error_cb(void* data, const char* msg, int errnum) {
  fprintf(stderr, "   [symbol resolution error: %s (%d)]\n", msg, errnum);
}

void valk_trace_print(void** stack, size_t num) {
  char** strings;

  static struct backtrace_state* valkBtState = nullptr;
  if (!valkBtState) {
    valkBtState = backtrace_create_state(nullptr, 0, nullptr, nullptr);
  }

  strings = backtrace_symbols(stack, num);

  for (size_t j = 0; j < num; ++j) {
    printf("- [#%ld] %s\n", j, strings[j]);

    backtrace_pcinfo(valkBtState, (uintptr_t)stack[j], __valk_trace_info_cb,
                     __valk_trace_error_cb, nullptr);
    // void *addr = stack[j];
    // Dl_info info;
    //
    // if (dladdr(addr, &info) && info.dli_fname) {
    //   // Offset within the shared object or binary
    //   uintptr_t offset_in_obj = (uintptr_t)addr - (uintptr_t)info.dli_fbase;
    //   uintptr_t offset_in_sym =
    //       info.dli_saddr ? (uintptr_t)addr - (uintptr_t)info.dli_saddr : 0;
    //
    //   fprintf(stderr, "   #%zu %s(%s+0x%lx) [%p]  ; offset in image:
    //   0x%lx\n",
    //           j, info.dli_fname, info.dli_sname ? info.dli_sname : "??",
    //           offset_in_sym, addr, offset_in_obj);
    // } else {
    //   fprintf(stderr, "   #%zu [address %p, symbol resolution failed]\n", j,
    //           addr);
    // }
  }
  free(strings);
}
