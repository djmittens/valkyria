#include "aio_internal.h"
#include "common.h"
#include "log.h"
#include "memory.h"
#include "parser.h"
#include "metrics_v2.h"

#include <string.h>
#include <stdlib.h>

#ifdef VALK_METRICS_ENABLED
static valk_lval_t *valk_builtin_aio_slab_buckets(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  u64 argc = valk_lval_list_count(a);
  if (argc < 5) {
    return valk_lval_err("aio/slab-buckets: expected (sys slab-name start end num-buckets)");
  }

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(sys_arg) != LVAL_REF || strcmp(sys_arg->ref.type, "aio_system") != 0) {
    return valk_lval_err("aio/slab-buckets: first argument must be an aio_system");
  }
  valk_aio_system_t *sys = (valk_aio_system_t *)sys_arg->ref.ptr;

  valk_lval_t *name_arg = valk_lval_list_nth(a, 1);
  valk_lval_t *start_arg = valk_lval_list_nth(a, 2);
  valk_lval_t *end_arg = valk_lval_list_nth(a, 3);
  valk_lval_t *buckets_arg = valk_lval_list_nth(a, 4);

  if (LVAL_TYPE(name_arg) != LVAL_STR ||
      LVAL_TYPE(start_arg) != LVAL_NUM ||
      LVAL_TYPE(end_arg) != LVAL_NUM ||
      LVAL_TYPE(buckets_arg) != LVAL_NUM) {
    return valk_lval_err("aio/slab-buckets: invalid argument types");
  }

  const char *slab_name = name_arg->str;
  u64 start = (u64)start_arg->num;
  u64 end = (u64)end_arg->num;
  u64 num_buckets = (u64)buckets_arg->num;

  if (num_buckets == 0 || num_buckets > 4096) {
    return valk_lval_err("aio/slab-buckets: num-buckets must be 1-4096");
  }

  valk_slab_t *slab = nullptr;
  if (strcmp(slab_name, "tcp_buffers") == 0) {
    slab = valk_aio_get_tcp_buffer_slab(sys);
  } else if (strcmp(slab_name, "handles") == 0) {
    slab = valk_aio_get_handle_slab(sys);
  } else if (strcmp(slab_name, "stream_arenas") == 0) {
    slab = valk_aio_get_stream_arenas_slab(sys);
  } else if (strcmp(slab_name, "http_servers") == 0) {
    slab = valk_aio_get_http_servers_slab(sys);
  } else if (strcmp(slab_name, "http_clients") == 0) {
    slab = valk_aio_get_http_clients_slab(sys);
  } else if (strcmp(slab_name, "lval") == 0 || strcmp(slab_name, "lenv") == 0) {
    return valk_lval_err("aio/slab-buckets: lval/lenv slabs no longer exist in heap2");
  }

  if (!slab) {
    return valk_lval_err("aio/slab-buckets: unknown slab name");
  }

  if (!slab->usage_bitmap) {
    return valk_lval_err("aio/slab-buckets: slab has no maintained bitmap");
  }

  valk_bitmap_bucket_t *buckets = malloc(num_buckets * sizeof(valk_bitmap_bucket_t));
  if (!buckets) {
    return valk_lval_err("aio/slab-buckets: allocation failed");
  }

  u64 actual_buckets = valk_slab_bitmap_buckets(slab, start, end, num_buckets, buckets);

  u64 buf_size = 32 + actual_buckets * 32;
  char *buf = malloc(buf_size);
  if (!buf) {
    free(buckets);
    return valk_lval_err("aio/slab-buckets: allocation failed");
  }

  char *p = buf;
  char *buf_end = buf + buf_size;
  int n = snprintf(p, buf_end - p, "{\"buckets\":[");
  p += n;

  for (u64 i = 0; i < actual_buckets && p < buf_end - 30; i++) {
    if (i > 0) *p++ = ',';
    n = snprintf(p, buf_end - p, "{\"u\":%llu,\"f\":%llu}",
                 (unsigned long long)buckets[i].used, (unsigned long long)buckets[i].free);
    if (n > 0) p += n;
  }

  snprintf(p, buf_end - p, "],\"total\":%llu}", (unsigned long long)slab->numItems);

  valk_lval_t *result = valk_lval_str(buf);
  free(buf);
  free(buckets);

  return result;
}
#endif

static void write_slab_json(char **p, char *end, const char *name, valk_slab_t *slab) {
  if (!slab || *p >= end - 100) return;

  u64 used = slab->numItems - slab->numFree;
  u64 total = slab->numItems;
  u64 hwm = slab->peakUsed;
  u64 overflow = slab->overflowCount;

  int n = snprintf(*p, end - *p,
    "{\"name\":\"%s\",\"used\":%llu,\"total\":%llu,\"hwm\":%llu,\"overflow\":%llu}",
    name,
    (unsigned long long)used,
    (unsigned long long)total,
    (unsigned long long)hwm,
    (unsigned long long)overflow);
  if (n > 0 && *p + n < end) *p += n;
}

static valk_lval_t *valk_builtin_aio_diagnostics_state_json(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/diagnostics-state-json: expected 1 argument (sys)");
  }

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(sys_arg) != LVAL_REF || strcmp(sys_arg->ref.type, "aio_system") != 0) {
    return valk_lval_err("aio/diagnostics-state-json: argument must be an aio_system");
  }

#ifdef VALK_METRICS_ENABLED
  valk_aio_system_t *sys = (valk_aio_system_t *)sys_arg->ref.ptr;

  valk_slab_t *tcp_slab = valk_aio_get_tcp_buffer_slab(sys);
  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  valk_slab_t *arena_slab = valk_aio_get_stream_arenas_slab(sys);
  valk_slab_t *server_slab = valk_aio_get_http_servers_slab(sys);
  valk_slab_t *client_slab = valk_aio_get_http_clients_slab(sys);

  valk_process_memory_t pm = {0};
  valk_process_memory_collect(&pm);

  valk_gc_malloc_heap_t *heap = valk_aio_get_gc_heap(sys);
  u64 gc_used = 0, gc_total = 0;
  if (heap) {
    gc_used = valk_gc_heap2_used_bytes(heap);
    gc_total = heap->hard_limit;
  }

  u64 buf_size = 8192;
  char *buf = malloc(buf_size);
  if (!buf) {
    return valk_lval_err("aio/diagnostics-state-json: allocation failed");
  }

  char *p = buf;
  char *end = buf + buf_size;

  int n = snprintf(p, end - p, "{\"slabs\":[");
  if (n > 0) p += n;

  int first = 1;
  if (tcp_slab) {
    if (!first) { *p++ = ','; } first = 0;
    write_slab_json(&p, end, "tcp_buffers", tcp_slab);
  }
  if (handle_slab) {
    if (!first) { *p++ = ','; } first = 0;
    write_slab_json(&p, end, "handles", handle_slab);
  }
  if (arena_slab) {
    if (!first) { *p++ = ','; } first = 0;
    write_slab_json(&p, end, "stream_arenas", arena_slab);
  }
  if (server_slab) {
    if (!first) { *p++ = ','; } first = 0;
    write_slab_json(&p, end, "http_servers", server_slab);
  }
  if (client_slab) {
    if (!first) { *p++ = ','; }
    write_slab_json(&p, end, "http_clients", client_slab);
  }

  n = snprintf(p, end - p, "],\"arenas\":[");
  if (n > 0) p += n;

  n = snprintf(p, end - p,
    "{\"name\":\"stream_arenas\",\"used\":%llu,\"capacity\":%llu}",
    arena_slab ? (unsigned long long)(arena_slab->numItems - arena_slab->numFree) : 0ULL,
    arena_slab ? (unsigned long long)arena_slab->numItems : 0ULL);
  if (n > 0) p += n;

  n = snprintf(p, end - p,
    "],\"gc\":{\"heap_used_bytes\":%llu,\"heap_total_bytes\":%llu}",
    (unsigned long long)gc_used,
    (unsigned long long)gc_total);
  if (n > 0) p += n;

  n = snprintf(p, end - p,
    ",\"process\":{\"rss\":%llu,\"vms\":%llu,\"system_total\":%llu}",
    (unsigned long long)pm.rss_bytes,
    (unsigned long long)pm.vms_bytes,
    (unsigned long long)pm.system_total_bytes);
  if (n > 0) p += n;

  u64 aio_used = 0, aio_cap = 0;
  if (tcp_slab) {
    aio_used += (tcp_slab->numItems - tcp_slab->numFree) * tcp_slab->itemSize;
    aio_cap += tcp_slab->numItems * tcp_slab->itemSize;
  }
  if (handle_slab) {
    aio_used += (handle_slab->numItems - handle_slab->numFree) * handle_slab->itemSize;
    aio_cap += handle_slab->numItems * handle_slab->itemSize;
  }
  if (arena_slab) {
    aio_used += (arena_slab->numItems - arena_slab->numFree) * arena_slab->itemSize;
    aio_cap += arena_slab->numItems * arena_slab->itemSize;
  }

  n = snprintf(p, end - p,
    ",\"breakdown\":{\"gc_used\":%llu,\"gc_cap\":%llu,"
    "\"aio_used\":%llu,\"aio_cap\":%llu,"
    "\"scratch_used\":0,\"scratch_cap\":0,"
    "\"metrics_used\":0,\"metrics_cap\":0}}",
    (unsigned long long)gc_used,
    (unsigned long long)gc_total,
    (unsigned long long)aio_used,
    (unsigned long long)aio_cap);
  if (n > 0) p += n;

  valk_lval_t *result = valk_lval_str(buf);
  free(buf);
  return result;
#else
  UNUSED(sys_arg);
  return valk_lval_str("{}");
#endif
}

void valk_register_aio_diagnostics_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/diagnostics-state-json",
                        valk_builtin_aio_diagnostics_state_json);

#ifdef VALK_METRICS_ENABLED
  valk_lenv_put_builtin(env, "aio/slab-buckets",
                        valk_builtin_aio_slab_buckets);
#endif
}
