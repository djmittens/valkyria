#include "lsp_types.h"

// All builtin type schemes are now declared in src/builtins.valk via (sig ...)
// forms and loaded transitively through prelude.valk. This function is kept
// as a no-op for call-site compatibility.

void lsp_builtin_schemes_init(type_arena_t *a, typed_scope_t *scope) {
  (void)a;
  (void)scope;
}
