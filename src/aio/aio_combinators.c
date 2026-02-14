#include "aio_combinators_internal.h"

void valk_register_async_handle_builtins(valk_lenv_t *env) {
  valk_register_comb_handle(env);
  valk_register_comb_chain(env);
  valk_register_comb_collection(env);
  valk_register_comb_resource(env);
  valk_register_comb_timeout(env);
  valk_register_comb_timers(env);
  valk_register_comb_syntax(env);
  valk_register_comb_util(env);
}
