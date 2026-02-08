#include "aio_combinators_internal.h"

void valk_register_comb_collection(valk_lenv_t *env) {
  valk_register_comb_all(env);
  valk_register_comb_race(env);
  valk_register_comb_any(env);
  valk_register_comb_all_settled(env);
}
