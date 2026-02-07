#include "aio_internal.h"
#include "builtins_internal.h"
#include "common.h"
#include "log.h"
#include "memory.h"
#include "parser.h"
#include "metrics_v2.h"
#include "aio/aio_alloc.h"

#include <string.h>
#include <stdlib.h>

// LCOV_EXCL_BR_START - diagnostic builtins have many defensive type checks
static valk_lval_t *valk_builtin_aio_slab_buckets(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  u64 argc = valk_lval_list_count(a);
  if (argc < 5) {
    return valk_lval_err("aio/slab-buckets: expected (sys slab-name start end num-buckets)");
  }

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);
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
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - internal JSON formatting with defensive buffer bounds
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
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - internal handle state enum dispatch
static char get_handle_state_char(valk_aio_system_t *sys, u64 slot_idx) {
  valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(sys, slot_idx);
  switch (kind) {
    case VALK_DIAG_HNDL_EMPTY:
      return 'F';
    case VALK_DIAG_HNDL_TCP:
      return 'T';
    case VALK_DIAG_HNDL_TASK:
      return 'K';
    case VALK_DIAG_HNDL_TIMER:
      return 'M';
    case VALK_DIAG_HNDL_HTTP_CONN: {
      valk_handle_diag_t diag;
      if (valk_aio_get_handle_diag(sys, slot_idx, &diag)) {
        switch (diag.state) {
          case VALK_DIAG_CONN_CONNECTING: return 'N';
          case VALK_DIAG_CONN_ACTIVE:     return 'A';
          case VALK_DIAG_CONN_IDLE:       return 'I';
          case VALK_DIAG_CONN_CLOSING:    return 'C';
          default:                        return 'A';
        }
      }
      return 'A';
    }
    default:
      return 'F';
  }
}

static void write_handle_slab_json(char **p, char *end, valk_aio_system_t *sys, valk_slab_t *slab) {
  if (!slab || *p >= end - 200) return;

  u64 used = slab->numItems - slab->numFree;
  u64 total = slab->numItems;
  u64 hwm = slab->peakUsed;
  u64 overflow = slab->overflowCount;

  int n = snprintf(*p, end - *p,
    "{\"name\":\"handles\",\"used\":%llu,\"total\":%llu,\"hwm\":%llu,\"overflow\":%llu,\"states\":\"",
    (unsigned long long)used,
    (unsigned long long)total,
    (unsigned long long)hwm,
    (unsigned long long)overflow);
  if (n < 0 || *p + n >= end) return;
  *p += n;

  u64 owner_active[VALK_MAX_OWNERS] = {0};
  u64 owner_idle[VALK_MAX_OWNERS] = {0};
  u64 owner_closing[VALK_MAX_OWNERS] = {0};

  if (total > 0 && *p < end - total * 6) {
    char prev_char = get_handle_state_char(sys, 0);
    u64 run_count = 1;

    valk_handle_diag_t diag;
    if (valk_aio_get_handle_kind(sys, 0) == VALK_DIAG_HNDL_HTTP_CONN) {
      if (valk_aio_get_handle_diag(sys, 0, &diag) && diag.owner_idx < VALK_MAX_OWNERS) {
        switch (diag.state) {
          case VALK_DIAG_CONN_ACTIVE:  owner_active[diag.owner_idx]++; break;
          case VALK_DIAG_CONN_IDLE:    owner_idle[diag.owner_idx]++; break;
          case VALK_DIAG_CONN_CLOSING: owner_closing[diag.owner_idx]++; break;
          default: owner_active[diag.owner_idx]++; break;
        }
      }
    }

    for (u64 i = 1; i < total; i++) {
      char cur_char = get_handle_state_char(sys, i);

      if (valk_aio_get_handle_kind(sys, i) == VALK_DIAG_HNDL_HTTP_CONN) {
        if (valk_aio_get_handle_diag(sys, i, &diag) && diag.owner_idx < VALK_MAX_OWNERS) {
          switch (diag.state) {
            case VALK_DIAG_CONN_ACTIVE:  owner_active[diag.owner_idx]++; break;
            case VALK_DIAG_CONN_IDLE:    owner_idle[diag.owner_idx]++; break;
            case VALK_DIAG_CONN_CLOSING: owner_closing[diag.owner_idx]++; break;
            default: owner_active[diag.owner_idx]++; break;
          }
        }
      }

      if (cur_char == prev_char) {
        run_count++;
      } else {
        n = snprintf(*p, end - *p, "%c%llu", prev_char, (unsigned long long)run_count);
        if (n > 0 && *p + n < end) *p += n;
        prev_char = cur_char;
        run_count = 1;
      }
    }
    n = snprintf(*p, end - *p, "%c%llu", prev_char, (unsigned long long)run_count);
    if (n > 0 && *p + n < end) *p += n;
  }

  n = snprintf(*p, end - *p, "\",\"summary\":{\"by_owner\":{");
  if (n > 0 && *p + n < end) *p += n;

  int first_owner = 1;
  for (u16 oi = 0; oi < VALK_MAX_OWNERS; oi++) {
    u64 a = owner_active[oi];
    u64 i = owner_idle[oi];
    u64 c = owner_closing[oi];
    if (a > 0 || i > 0 || c > 0) {
      if (!first_owner) {
        if (*p < end) *(*p)++ = ',';
      }
      first_owner = 0;
      n = snprintf(*p, end - *p, "\"%u\":{\"A\":%llu,\"I\":%llu,\"C\":%llu}",
        (unsigned)oi, (unsigned long long)a, (unsigned long long)i, (unsigned long long)c);
      if (n > 0 && *p + n < end) *p += n;
    }
  }

  n = snprintf(*p, end - *p, "}}}");
  if (n > 0 && *p + n < end) *p += n;
}

// LCOV_EXCL_BR_START - diagnostics JSON has many defensive checks and buffer bounds
static valk_lval_t *valk_builtin_aio_diagnostics_state_json(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/diagnostics-state-json: expected 1 argument (sys)");
  }

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);

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

  u64 buf_size = 65536;
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
    write_handle_slab_json(&p, end, sys, handle_slab);
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
    "\"metrics_used\":0,\"metrics_cap\":0,"
    "\"ssl_used\":%llu,\"nghttp2_used\":%llu,\"libuv_used\":%llu}",
    (unsigned long long)gc_used,
    (unsigned long long)gc_total,
    (unsigned long long)aio_used,
    (unsigned long long)aio_cap,
    (unsigned long long)valk_aio_ssl_bytes_used(),
    (unsigned long long)valk_aio_nghttp2_bytes_used(),
    (unsigned long long)valk_aio_libuv_bytes_used());
  if (n > 0) p += n;

  n = snprintf(p, end - p, ",\"owner_map\":[");
  if (n > 0) p += n;

  u64 owner_count = valk_owner_get_count(sys);
  for (u64 oi = 0; oi < owner_count; oi++) {
    const char *name = valk_owner_get_name(sys, (u16)oi);
    if (oi > 0 && p < end) *p++ = ',';
    if (name) {
      n = snprintf(p, end - p, "\"%s\"", name);
    } else {
      n = snprintf(p, end - p, "null");
    }
    if (n > 0 && p + n < end) p += n;
  }

  n = snprintf(p, end - p, "]}");
  if (n > 0) p += n;

  valk_lval_t *result = valk_lval_str(buf);
  free(buf);
  return result;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - defensive type/buffer checks in diagnostic builtin
static valk_lval_t *valk_builtin_aio_diagnostics_state_json_compact(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/diagnostics-state-json-compact: expected 1 argument");
  }

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);

  valk_aio_system_t *sys = (valk_aio_system_t *)sys_arg->ref.ptr;

  valk_process_memory_t pm = {0};
  valk_process_memory_collect(&pm);

  valk_gc_malloc_heap_t *heap = valk_aio_get_gc_heap(sys);
  u64 gc_used = heap ? valk_gc_heap2_used_bytes(heap) : 0;

  char buf[128];
  int n = snprintf(buf, sizeof(buf),
    "{\"gc\":%llu,\"rss\":%llu}",
    (unsigned long long)gc_used,
    (unsigned long long)pm.rss_bytes);

  if (n < 0 || (size_t)n >= sizeof(buf)) {
    return valk_lval_str("{}");
  }

  return valk_lval_str(buf);
}
// LCOV_EXCL_BR_STOP

void valk_register_aio_diagnostics_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/diagnostics-state-json",
                        valk_builtin_aio_diagnostics_state_json);
  valk_lenv_put_builtin(env, "aio/diagnostics-state-json-compact",
                        valk_builtin_aio_diagnostics_state_json_compact);
  valk_lenv_put_builtin(env, "aio/slab-buckets",
                        valk_builtin_aio_slab_buckets);
}
