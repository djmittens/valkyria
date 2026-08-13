#include "image.h"
#include "conc_map.h"
#include "dict.h"
#include "gc.h"
#include "log.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ============================================================================
// Wire format
//
//   [header][object_buffer][fixup_table][stub_table][sym_table]
//
// Pointers in the object buffer are stored as byte offsets into the buffer
// (nullptr stays as literal 0). On load:
//   1. Apply fixups: *(uintptr_t*)(buf+fx) += (uintptr_t)buf
//   2. For each stub offset, look up fun.name in the caller's registry to get
//      the live builtin lval; build stub_addr -> live_addr map.
//   3. Walk the fixup table again; rewrite any slot whose value is a stub
//      address to the mapped live address. This transparently replaces every
//      dumped reference to a builtin with the live registry lval.
//   4. Walk sym offsets; re-intern fun.str through sym_intern_str so the
//      global intern table owns the string.
// ============================================================================

#define VALK_IMAGE_MAGIC "VALKIMG\0"
#define VALK_IMAGE_VERSION 5u

#define VALK_IMAGE_ROOT_LVAL 0u
#define VALK_IMAGE_ROOT_ENV  1u

#define VALK_IMAGE_ENDIAN_TAG 0x0123456789ABCDEFULL

typedef struct {
  char magic[8];
  u32 version;
  u32 root_kind;
  u64 endian_tag;
  u32 lval_size;
  u32 lenv_size;
  u32 ptr_size;
  u32 reserved;
  u64 buf_size;
  u64 root_offset;
  u64 fixup_count;
  u64 stub_count;
  u64 sym_count;
  u64 env_count;
} valk_image_header_t;

#define IMG_MAX_TABLE_BYTES (((size_t)1) << 30)

// ============================================================================
// Builder
// ============================================================================

typedef struct {
  u8 *buf;
  u64 len;
  u64 cap;

  u64 *fixups;
  u64 fx_len;
  u64 fx_cap;

  u64 *stubs;
  u64 st_len;
  u64 st_cap;

  u64 *syms;
  u64 sy_len;
  u64 sy_cap;

  // Offsets of every dumped env. Load re-interns each env's key strings so
  // symbol identity stays pointer identity across a dump/load round trip.
  u64 *envs;
  u64 en_len;
  u64 en_cap;

  // src pointer -> (offset + 1) so a valid offset of 0 survives ptr_map's
  // nullptr-means-absent convention.
  valk_ptr_map_t pm;

  bool error;
} valk_image_builder_t;

static bool img_builder_init(valk_image_builder_t *b) {
  memset(b, 0, sizeof(*b));
  b->cap = 1024;
  b->buf = malloc(b->cap);
  b->fx_cap = 64;
  b->fixups = malloc(b->fx_cap * sizeof(u64));
  b->st_cap = 16;
  b->stubs = malloc(b->st_cap * sizeof(u64));
  b->sy_cap = 64;
  b->syms = malloc(b->sy_cap * sizeof(u64));
  b->en_cap = 64;
  b->en_len = 0;
  b->envs = malloc(b->en_cap * sizeof(u64));
  if (!b->buf || !b->fixups || !b->stubs || !b->syms || !b->envs) {
    free(b->buf); free(b->fixups); free(b->stubs); free(b->syms); free(b->envs);
    memset(b, 0, sizeof(*b));
    return false;
  }
  valk_ptr_map_init(&b->pm);
  return true;
}

static void img_builder_free(valk_image_builder_t *b) {
  free(b->buf);
  free(b->fixups);
  free(b->stubs);
  free(b->syms);
  free(b->envs);
  valk_ptr_map_free(&b->pm);
}

static u64 img_reserve(valk_image_builder_t *b, u64 size) {
  while (b->len + size > b->cap) {
    u64 ncap = b->cap * 2;
    u8 *nbuf = realloc(b->buf, ncap);
    if (!nbuf) { b->error = true; return 0; }
    b->buf = nbuf;
    b->cap = ncap;
  }
  u64 off = b->len;
  b->len += size;
  return off;
}

static u64 img_copy_bytes(valk_image_builder_t *b, const void *src, u64 size) {
  u64 off = img_reserve(b, size);
  memcpy(b->buf + off, src, size);
  return off;
}

static void img_add_fixup(valk_image_builder_t *b, u64 field_offset) {
  if (b->fx_len >= b->fx_cap) {
    u64 ncap = b->fx_cap * 2;
    u64 *na = realloc(b->fixups, ncap * sizeof(u64));
    if (!na) { b->error = true; return; }
    b->fixups = na; b->fx_cap = ncap;
  }
  b->fixups[b->fx_len++] = field_offset;
}

static void img_add_stub(valk_image_builder_t *b, u64 stub_offset) {
  if (b->st_len >= b->st_cap) {
    u64 ncap = b->st_cap * 2;
    u64 *na = realloc(b->stubs, ncap * sizeof(u64));
    if (!na) { b->error = true; return; }
    b->stubs = na; b->st_cap = ncap;
  }
  b->stubs[b->st_len++] = stub_offset;
}

static void img_add_sym(valk_image_builder_t *b, u64 sym_offset) {
  if (b->sy_len >= b->sy_cap) {
    u64 ncap = b->sy_cap * 2;
    u64 *na = realloc(b->syms, ncap * sizeof(u64));
    if (!na) { b->error = true; return; }
    b->syms = na; b->sy_cap = ncap;
  }
  b->syms[b->sy_len++] = sym_offset;
}

static void img_add_env(valk_image_builder_t *b, u64 env_offset) {
  if (b->en_len >= b->en_cap) {
    u64 ncap = b->en_cap * 2;
    u64 *na = realloc(b->envs, ncap * sizeof(u64));
    if (!na) { b->error = true; return; }
    b->envs = na; b->en_cap = ncap;
  }
  b->envs[b->en_len++] = env_offset;
}

// Copy a null-terminated C string into the buffer. Dedupes via pm.
// Returns byte offset of the copy. If `s` is NULL, returns 0 and records
// nothing.
static u64 img_dump_cstr(valk_image_builder_t *b, const char *s) {
  if (!s) return 0;
  void *existing = valk_ptr_map_get(&b->pm, (void*)s);
  if (existing) return (u64)(uintptr_t)existing - 1;

  u64 len = strlen(s) + 1;
  u64 off = img_copy_bytes(b, s, len);
  valk_ptr_map_put(&b->pm, (void*)s, (void*)(uintptr_t)(off + 1));
  return off;
}

static u64 img_dump_lval(valk_image_builder_t *b, valk_lval_t *v);
static u64 img_dump_lenv(valk_image_builder_t *b, valk_lenv_t *env);
static void img_store_ptr(valk_image_builder_t *b, u64 field_off, u64 dst_off);

// Round the build buffer to `align`, zero-padding the gap. Required
// before reserving a dict block: dict cells contain u64 hash fields and
// the dict header has u64 strings_* fields, both of which require
// 8-byte alignment on stricter ISAs.
static void img_align(valk_image_builder_t *b, u64 align) {
  u64 next = (b->len + align - 1) & ~(align - 1);
  if (next > b->len) {
    u64 pad = next - b->len;
    u64 off = img_reserve(b, pad);
    memset(b->buf + off, 0, pad);
  }
}

// Dump a valk_dict_t block as a single contiguous blob.
//
// The dict layout is self-contained: keys live inside the dict's own
// `strings` buffer at u32 offsets (see dict.h), so there are no raw
// pointers to char keys to relocate. The only intra-buffer pointers are
// the per-cell `value` field (valk_lval_t*), which is registered with
// img_store_ptr so load-time fixups relocate them.
static u64 img_dump_dict(valk_image_builder_t *b, valk_dict_t *d) {
  if (!d) return 0;
  void *existing = valk_ptr_map_get(&b->pm, d);
  if (existing) return (u64)(uintptr_t)existing - 1;

  u64 total = dict_block_size(d->num_buckets, d->capacity, d->strings_cap);
  img_align(b, 8);
  u64 off = img_reserve(b, total);
  valk_ptr_map_put(&b->pm, d, (void*)(uintptr_t)(off + 1));
  memcpy(b->buf + off, d, total);

  u64 cells_off_rel = dict_cells_offset(d->num_buckets);
  valk_dict_cell_t *src_cells = dict_cells(d);
  u32 *src_buckets = dict_buckets(d);
  for (u32 bkt = 0; bkt < d->num_buckets; bkt++) {
    u32 ci = src_buckets[bkt];
    while (ci != DICT_EMPTY) {
      valk_lval_t *val = src_cells[ci].value;
      u64 val_off = img_dump_lval(b, val);
      u64 cell_off = off + cells_off_rel + (u64)ci * sizeof(valk_dict_cell_t);
      img_store_ptr(b,
        cell_off + offsetof(valk_dict_cell_t, value), val_off);
      ci = src_cells[ci].next;
    }
  }
  return off;
}

// Record a pointer field: at buf offset `field_off`, store the destination
// offset, and register this slot for load-time fixup.
static void img_store_ptr(valk_image_builder_t *b, u64 field_off, u64 dst_off) {
  if (dst_off == 0) {
    *(u64*)(b->buf + field_off) = 0;
    return;
  }
  *(u64*)(b->buf + field_off) = dst_off;
  img_add_fixup(b, field_off);
}

static u64 img_dump_lval(valk_image_builder_t *b, valk_lval_t *v) {
  if (!v) return 0;
  void *existing = valk_ptr_map_get(&b->pm, v);
  if (existing) return (u64)(uintptr_t)existing - 1;

  // valk_lval_t has u64/pointer fields written via raw *(u64*) stores below;
  // they must land on 8-byte boundaries or arm64 faults (EXC_ARM_DA_ALIGN).
  // img_reserve doesn't align, and a preceding odd-length cstr dump (e.g. a
  // lambda's native_name) can leave b->len unaligned, so align first.
  img_align(b, alignof(valk_lval_t));
  u64 off = img_reserve(b, sizeof(valk_lval_t));
  valk_ptr_map_put(&b->pm, v, (void*)(uintptr_t)(off + 1));

  memcpy(b->buf + off, v, sizeof(valk_lval_t));
  valk_lval_t *dst = (valk_lval_t*)(b->buf + off);
  dst->flags = v->flags | LVAL_FLAG_IMMORTAL;

  valk_ltype_e type = LVAL_TYPE(v);
  switch (type) {
    case LVAL_NUM:
    case LVAL_NIL:
      break;

    case LVAL_STR:
    case LVAL_ERR: {
      u64 str_off = img_dump_cstr(b, v->str);
      img_store_ptr(b, off + offsetof(valk_lval_t, str), str_off);
      break;
    }

    case LVAL_SYM: {
      u64 str_off = img_dump_cstr(b, v->str);
      img_store_ptr(b, off + offsetof(valk_lval_t, str), str_off);
      img_add_sym(b, off);
      break;
    }

    case LVAL_CONS: {
      u64 head_off = img_dump_lval(b, v->cons.head);
      u64 tail_off = img_dump_lval(b, v->cons.tail);
      img_store_ptr(b, off + offsetof(valk_lval_t, cons.head), head_off);
      img_store_ptr(b, off + offsetof(valk_lval_t, cons.tail), tail_off);
      break;
    }

    case LVAL_DICT: {
      u64 dict_off = img_dump_dict(b, v->dict.data);
      img_store_ptr(b, off + offsetof(valk_lval_t, dict.data), dict_off);
      break;
    }

    case LVAL_FUN: {
      u64 name_off = img_dump_cstr(b, v->fun.name);
      img_store_ptr(b, off + offsetof(valk_lval_t, fun.name), name_off);
      // native_fn is a live function pointer — never portable across process
      // loads. Zero it out in both builtin and lambda branches; the lambda
      // branch below serializes native_name so it can be re-resolved at load.
      *(u64*)(b->buf + off + offsetof(valk_lval_t, fun.native_fn)) = 0;
      if (v->fun.builtin != nullptr) {
        // Builtin stub: zero the function pointer and lambda-only fields.
        valk_lval_t *dst2 = (valk_lval_t*)(b->buf + off);
        dst2->fun.builtin = nullptr;
        *(u64*)(b->buf + off + offsetof(valk_lval_t, fun.env)) = 0;
        *(u64*)(b->buf + off + offsetof(valk_lval_t, fun.formals)) = 0;
        *(u64*)(b->buf + off + offsetof(valk_lval_t, fun.body)) = 0;
        *(u64*)(b->buf + off + offsetof(valk_lval_t, fun.native_name)) = 0;
        if (!v->fun.name) {
          VALK_ERROR("valk_image_dump: builtin has no fun.name");
          b->error = true;
          break;
        }
        img_add_stub(b, off);
      } else {
        // Lambda: serialize closure env, formals, body, native_name.
        u64 env_off = v->fun.env ? img_dump_lenv(b, v->fun.env) : 0;
        u64 formals_off = img_dump_lval(b, v->fun.formals);
        u64 body_off = img_dump_lval(b, v->fun.body);
        u64 nname_off = img_dump_cstr(b, v->fun.native_name);
        img_store_ptr(b, off + offsetof(valk_lval_t, fun.env), env_off);
        img_store_ptr(b, off + offsetof(valk_lval_t, fun.formals), formals_off);
        img_store_ptr(b, off + offsetof(valk_lval_t, fun.body), body_off);
        img_store_ptr(b, off + offsetof(valk_lval_t, fun.native_name), nname_off);
      }
      break;
    }

    default:
      VALK_ERROR("valk_image_dump: unsupported lval type %d", (int)type);
      b->error = true;
      break;
  }

  return off;
}

// Collect a cmap env's live {key,val} pairs into flat arrays so the env can
// be serialized in the same linear form as a non-concurrent env. The loaded
// image env is frozen (read-only), so it never needs the concurrent map.
typedef struct {
  char **keys;
  valk_lval_t **vals;
  u64 count;
  u64 cap;
} img_cmap_collect_t;

static void img_cmap_collect_cb(char *key, _Atomic(valk_lval_t *) *slot,
                                void *ctx) {
  img_cmap_collect_t *c = ctx;
  if (c->count >= c->cap) return;  // LCOV_EXCL_LINE - sized to count up front
  c->keys[c->count] = key;
  c->vals[c->count] = atomic_load(slot);
  c->count++;
}

static u64 img_dump_lenv(valk_image_builder_t *b, valk_lenv_t *env) {
  if (!env) return 0;
  void *existing = valk_ptr_map_get(&b->pm, env);
  if (existing) return (u64)(uintptr_t)existing - 1;

  img_align(b, alignof(valk_lenv_t));
  u64 off = img_reserve(b, sizeof(valk_lenv_t));
  valk_ptr_map_put(&b->pm, env, (void*)(uintptr_t)(off + 1));
  img_add_env(b, off);

  memcpy(b->buf + off, env, sizeof(valk_lenv_t));

  // Source bindings from the concurrent map when present, else linear arrays.
  char **keys = env->symbols.items;
  valk_lval_t **vals = env->vals.items;
  u64 n = env->symbols.count;
  img_cmap_collect_t collected = {0};
  if (env->cmap) {
    u64 cnt = valk_cmap_count((valk_cmap_t *)env->cmap);
    collected.keys = malloc(sizeof(char *) * (cnt ? cnt : 1));
    collected.vals = malloc(sizeof(valk_lval_t *) * (cnt ? cnt : 1));
    collected.cap = cnt;
    valk_cmap_foreach((valk_cmap_t *)env->cmap, img_cmap_collect_cb, &collected);
    keys = collected.keys;
    vals = collected.vals;
    n = collected.count;
  }

  // Dump symbol name strings array: char*[n].
  u64 sym_arr_off = 0;
  if (n > 0 && keys) {
    img_align(b, alignof(char*));
    sym_arr_off = img_reserve(b, n * sizeof(char*));
    for (u64 i = 0; i < n; i++) {
      u64 s_off = img_dump_cstr(b, keys[i]);
      u64 slot_off = sym_arr_off + i * sizeof(char*);
      img_store_ptr(b, slot_off, s_off);
    }
  }

  // Dump value pointer array: valk_lval_t*[n].
  u64 val_arr_off = 0;
  if (n > 0 && vals) {
    img_align(b, alignof(valk_lval_t*));
    val_arr_off = img_reserve(b, n * sizeof(valk_lval_t*));
    for (u64 i = 0; i < n; i++) {
      u64 v_off = img_dump_lval(b, vals[i]);
      u64 slot_off = val_arr_off + i * sizeof(valk_lval_t*);
      img_store_ptr(b, slot_off, v_off);
    }
  }

  if (collected.keys) free(collected.keys);
  if (collected.vals) free(collected.vals);

  u64 parent_off = env->parent ? img_dump_lenv(b, env->parent) : 0;

  // Write the env header fields (count, pointers) after all reserves so we
  // don't hold stale buf pointers across realloc. The dumped env is a frozen,
  // linear-array env (no concurrent map needed: it is read-only after load).
  valk_lenv_t *dst = (valk_lenv_t*)(b->buf + off);
  atomic_store(&dst->flags, LENV_FLAG_FROZEN);
  dst->allocator = nullptr;
  dst->cmap = nullptr;
  dst->symbols.count = n;
  dst->symbols.capacity = n;
  dst->vals.count = n;
  dst->vals.capacity = n;
  img_store_ptr(b, off + offsetof(valk_lenv_t, symbols.items), sym_arr_off);
  img_store_ptr(b, off + offsetof(valk_lenv_t, vals.items), val_arr_off);
  img_store_ptr(b, off + offsetof(valk_lenv_t, parent), parent_off);
  img_store_ptr(b, off + offsetof(valk_lenv_t, cmap), 0);

  return off;
}

// ============================================================================
// Write helpers
// ============================================================================

static int img_write_file(valk_image_builder_t *b, u64 root_off, u32 root_kind,
                          const char *path) {
  FILE *f = fopen(path, "wb");
  if (!f) return -2;

  valk_image_header_t hdr = {
    .version = VALK_IMAGE_VERSION,
    .root_kind = root_kind,
    .endian_tag = VALK_IMAGE_ENDIAN_TAG,
    .lval_size = (u32)sizeof(valk_lval_t),
    .lenv_size = (u32)sizeof(valk_lenv_t),
    .ptr_size = (u32)sizeof(void *),
    .reserved = 0,
    .buf_size = b->len,
    .root_offset = root_off,
    .fixup_count = b->fx_len,
    .stub_count = b->st_len,
    .sym_count = b->sy_len,
    .env_count = b->en_len,
  };
  memcpy(hdr.magic, VALK_IMAGE_MAGIC, 8);

  int rc = 0;
  if (fwrite(&hdr, sizeof(hdr), 1, f) != 1) rc = -3;
  if (!rc && b->len && fwrite(b->buf, 1, b->len, f) != b->len) rc = -3;
  if (!rc && b->fx_len &&
      fwrite(b->fixups, sizeof(u64), b->fx_len, f) != b->fx_len) rc = -3;
  if (!rc && b->st_len &&
      fwrite(b->stubs, sizeof(u64), b->st_len, f) != b->st_len) rc = -3;
  if (!rc && b->sy_len &&
      fwrite(b->syms, sizeof(u64), b->sy_len, f) != b->sy_len) rc = -3;
  if (!rc && b->en_len &&
      fwrite(b->envs, sizeof(u64), b->en_len, f) != b->en_len) rc = -3;

  fclose(f);
  return rc;
}

// ============================================================================
// Public: dump
// ============================================================================

int valk_image_dump(valk_lval_t *val, const char *path) {
  valk_image_builder_t b;
  if (!img_builder_init(&b)) return -1;

  u64 root_off = img_dump_lval(&b, val);
  if (b.error) {
    img_builder_free(&b);
    return -1;
  }

  int rc = img_write_file(&b, root_off, VALK_IMAGE_ROOT_LVAL, path);
  img_builder_free(&b);
  return rc;
}

int valk_image_dump_env(valk_lenv_t *env, const char *path) {
  valk_image_builder_t b;
  if (!img_builder_init(&b)) return -1;

  u64 root_off = img_dump_lenv(&b, env);
  if (b.error) {
    img_builder_free(&b);
    return -1;
  }

  int rc = img_write_file(&b, root_off, VALK_IMAGE_ROOT_ENV, path);
  img_builder_free(&b);
  return rc;
}

// ============================================================================
// Load
// ============================================================================

typedef struct {
  u8 *buf;
  u64 buf_size;
  u64 root_offset;
  u32 root_kind;
  u64 *fixups;
  u64 fixup_count;
  u64 *stubs;
  u64 stub_count;
  u64 *syms;
  u64 sym_count;
  u64 *envs;
  u64 env_count;
} valk_image_loaded_t;

// Copy `n` bytes from a memory cursor into `dst`, bounds-checked. Returns
// false if the image buffer is truncated.
static bool img_mem_read(const u8 **cur, const u8 *end, void *dst, size_t n) {
  if ((size_t)(end - *cur) < n) return false;
  memcpy(dst, *cur, n);
  *cur += n;
  return true;
}

static bool img_check_table_size(u64 count, size_t elem) {
  if (count == 0) return true;
  if (count > IMG_MAX_TABLE_BYTES / elem) return false;
  return true;
}

static bool img_alloc_and_read(const u8 **cur, const u8 *end,
                               void **out, u64 count, size_t elem) {
  if (count == 0) { *out = nullptr; return true; }
  if (!img_check_table_size(count, elem)) return false;
  size_t bytes = (size_t)count * elem;
  void *p = malloc(bytes);
  if (!p) return false;
  if (!img_mem_read(cur, end, p, bytes)) { free(p); return false; }
  *out = p;
  return true;
}

static bool img_read_bytes(const u8 *bytes, size_t len,
                           valk_image_loaded_t *out) {
  memset(out, 0, sizeof(*out));
  const u8 *cur = bytes;
  const u8 *end = bytes + len;

  valk_image_header_t hdr;
  if (!img_mem_read(&cur, end, &hdr, sizeof(hdr))) return false;
  if (memcmp(hdr.magic, VALK_IMAGE_MAGIC, 8) != 0) {
    VALK_ERROR("valk_image_load: bad magic");
    return false;
  }
  if (hdr.version != VALK_IMAGE_VERSION) {
    VALK_ERROR("valk_image_load: version mismatch (file=%u expected=%u)",
               hdr.version, VALK_IMAGE_VERSION);
    return false;
  }
  if (hdr.endian_tag != VALK_IMAGE_ENDIAN_TAG) {
    VALK_ERROR("valk_image_load: endian or word-size mismatch");
    return false;
  }
  if (hdr.lval_size != sizeof(valk_lval_t) ||
      hdr.lenv_size != sizeof(valk_lenv_t) ||
      hdr.ptr_size != sizeof(void *)) {
    VALK_ERROR("valk_image_load: struct layout mismatch "
               "(lval=%u/%zu lenv=%u/%zu ptr=%u/%zu)",
               hdr.lval_size, sizeof(valk_lval_t),
               hdr.lenv_size, sizeof(valk_lenv_t),
               hdr.ptr_size, sizeof(void *));
    return false;
  }
  if (hdr.buf_size > IMG_MAX_TABLE_BYTES) {
    VALK_ERROR("valk_image_load: buffer too large (%llu)",
               (unsigned long long)hdr.buf_size);
    return false;
  }
  if (hdr.root_offset > hdr.buf_size) {
    VALK_ERROR("valk_image_load: root_offset out of range");
    return false;
  }

  out->buf_size = hdr.buf_size;
  out->root_offset = hdr.root_offset;
  out->root_kind = hdr.root_kind;
  out->fixup_count = hdr.fixup_count;
  out->stub_count = hdr.stub_count;
  out->sym_count = hdr.sym_count;
  out->env_count = hdr.env_count;

  if (hdr.buf_size > 0) {
    out->buf = malloc(hdr.buf_size);
    if (!out->buf) goto fail;
    if (!img_mem_read(&cur, end, out->buf, hdr.buf_size)) goto fail;
  }

  if (!img_alloc_and_read(&cur, end, (void **)&out->fixups,
                          hdr.fixup_count, sizeof(u64))) goto fail;
  if (!img_alloc_and_read(&cur, end, (void **)&out->stubs,
                          hdr.stub_count, sizeof(u64))) goto fail;
  if (!img_alloc_and_read(&cur, end, (void **)&out->syms,
                          hdr.sym_count, sizeof(u64))) goto fail;
  if (!img_alloc_and_read(&cur, end, (void **)&out->envs,
                          hdr.env_count, sizeof(u64))) goto fail;

  for (u64 i = 0; i < out->fixup_count; i++) {
    if (out->fixups[i] > out->buf_size ||
        out->fixups[i] + sizeof(u64) > out->buf_size) {
      VALK_ERROR("valk_image_load: fixup[%llu]=%llu out of range",
                 (unsigned long long)i,
                 (unsigned long long)out->fixups[i]);
      goto fail;
    }
  }
  for (u64 i = 0; i < out->stub_count; i++) {
    if (out->stubs[i] > out->buf_size ||
        out->stubs[i] + sizeof(valk_lval_t) > out->buf_size) {
      VALK_ERROR("valk_image_load: stub[%llu] out of range", (unsigned long long)i);
      goto fail;
    }
  }
  for (u64 i = 0; i < out->sym_count; i++) {
    if (out->syms[i] > out->buf_size ||
        out->syms[i] + sizeof(valk_lval_t) > out->buf_size) {
      VALK_ERROR("valk_image_load: sym[%llu] out of range", (unsigned long long)i);
      goto fail;
    }
  }
  for (u64 i = 0; i < out->env_count; i++) {
    if (out->envs[i] > out->buf_size ||
        out->envs[i] + sizeof(valk_lenv_t) > out->buf_size) {
      VALK_ERROR("valk_image_load: env[%llu] out of range", (unsigned long long)i);
      goto fail;
    }
  }

  return true;

fail:
  free(out->buf);
  free(out->fixups);
  free(out->stubs);
  free(out->syms);
  memset(out, 0, sizeof(*out));
  return false;
}

static bool img_read_all(const char *path, valk_image_loaded_t *out) {
  memset(out, 0, sizeof(*out));
  FILE *f = fopen(path, "rb");
  if (!f) return false;
  if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return false; }
  long sz = ftell(f);
  if (sz < 0 || (size_t)sz > IMG_MAX_TABLE_BYTES) {
    fclose(f); return false;
  }
  rewind(f);
  u8 *buf = (sz > 0) ? malloc((size_t)sz) : nullptr;
  if (sz > 0 && !buf) { fclose(f); return false; }
  if (sz > 0 && fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
    free(buf); fclose(f); return false;
  }
  fclose(f);
  bool ok = img_read_bytes(buf, (size_t)sz, out);
  free(buf);
  return ok;
}

// Resolve each builtin stub against `registry` and fill rep[i] with the
// replacement pointer. Returns false on any unresolved name.
static bool img_resolve_stubs(valk_image_loaded_t *ld, valk_lenv_t *registry,
                              valk_lval_t **rep) {
  if (ld->stub_count == 0) return true;
  if (!registry) {
    VALK_ERROR("valk_image_load: image contains %llu builtin stubs but no "
               "registry was provided",
               (unsigned long long)ld->stub_count);
    return false;
  }
  for (u64 i = 0; i < ld->stub_count; i++) {
    valk_lval_t *stub = (valk_lval_t*)(ld->buf + ld->stubs[i]);
    if (!stub->fun.name) {
      VALK_ERROR("valk_image_load: stub missing fun.name");
      return false;
    }
    valk_lval_t key = {0};
    key.flags = LVAL_SYM;
    key.str = stub->fun.name;
    valk_lval_t *live = valk_lenv_get(registry, &key);
    if (!live || LVAL_TYPE(live) == LVAL_ERR) {
      VALK_ERROR("valk_image_load: builtin `%s` not found in registry",
                 stub->fun.name);
      return false;
    }
    rep[i] = live;
  }
  return true;
}

typedef struct { uintptr_t addr; valk_lval_t *rep; } img_stub_pair_t;

static int img_stub_pair_cmp(const void *a, const void *b) {
  uintptr_t aa = ((const img_stub_pair_t *)a)->addr;
  uintptr_t bb = ((const img_stub_pair_t *)b)->addr;
  return (aa < bb) ? -1 : (aa > bb) ? 1 : 0;
}

// Rewrite any fixup slot whose value equals a stub address with the
// corresponding live pointer. Sorted bsearch is O(F log S) instead of
// O(F * S) — meaningful once a prelude image has hundreds of builtins.
static void img_apply_stub_map(valk_image_loaded_t *ld, valk_lval_t **rep) {
  if (ld->stub_count == 0) return;
  img_stub_pair_t *pairs = malloc(ld->stub_count * sizeof(*pairs));
  if (!pairs) return;
  for (u64 s = 0; s < ld->stub_count; s++) {
    pairs[s].addr = (uintptr_t)(ld->buf + ld->stubs[s]);
    pairs[s].rep = rep[s];
  }
  qsort(pairs, ld->stub_count, sizeof(*pairs), img_stub_pair_cmp);
  for (u64 i = 0; i < ld->fixup_count; i++) {
    void **slot = (void**)(ld->buf + ld->fixups[i]);
    img_stub_pair_t key = { .addr = (uintptr_t)*slot, .rep = nullptr };
    img_stub_pair_t *m = bsearch(&key, pairs, ld->stub_count,
                                 sizeof(*pairs), img_stub_pair_cmp);
    if (m) *slot = m->rep;
  }
  free(pairs);
}

// Symbol identity is pointer identity everywhere at runtime (env key arrays,
// the global concurrent map). A dumped image stores key STRINGS inline, so on
// load those pointers address the image buffer, not the intern table — two
// spellings of the same symbol would compare unequal. Re-intern every env key
// here, at load, and mark the env so lookups can pointer-compare.
//
// Without this the AOT server took ~6.8M strcmp-scanning lookups per document
// walk: every stdlib/LSP closure env came from the image and was therefore
// excluded from the fast path.
static void img_reintern_envs(valk_image_loaded_t *ld) {
  for (u64 i = 0; i < ld->env_count; i++) {
    valk_lenv_t *env = (valk_lenv_t *)(ld->buf + ld->envs[i]);
    if (env->symbols.items != nullptr) {
      for (u64 k = 0; k < env->symbols.count; k++) {
        if (env->symbols.items[k] == nullptr) continue;
        env->symbols.items[k] = (char *)valk_sym_intern(env->symbols.items[k]);
      }
    }
    atomic_fetch_or(&env->flags, LENV_FLAG_KEYS_INTERNED);
  }
}

static void img_reintern_syms(valk_image_loaded_t *ld) {
  for (u64 i = 0; i < ld->sym_count; i++) {
    valk_lval_t *sym = (valk_lval_t*)(ld->buf + ld->syms[i]);
    if (!sym->str) continue;
    const char *interned = valk_sym_intern(sym->str);
    sym->str = (char*)interned;
    sym->flags |= LVAL_FLAG_INTERNED;
  }
}

// Shared prologue: apply fixups, resolve stubs, re-intern syms.
// On failure frees internal allocations and returns false.
//
// Requires the root to live at buffer offset 0 (the dumper always dumps the
// root first). That lets the caller free the whole image by calling free()
// on the returned pointer.
static bool img_finalize(valk_image_loaded_t *ld, valk_lenv_t *registry,
                         void **root_out) {
  if (ld->root_offset != 0) {
    VALK_ERROR("valk_image_load: unexpected non-zero root_offset");
    return false;
  }

  uintptr_t base = (uintptr_t)ld->buf;
  for (u64 i = 0; i < ld->fixup_count; i++) {
    u64 fx = ld->fixups[i];
    *(uintptr_t*)(ld->buf + fx) += base;
  }

  valk_lval_t **rep = nullptr;
  if (ld->stub_count > 0) {
    rep = malloc(ld->stub_count * sizeof(valk_lval_t*));
    if (!rep) return false;
    if (!img_resolve_stubs(ld, registry, rep)) {
      free(rep);
      return false;
    }
  }
  img_apply_stub_map(ld, rep);
  free(rep);

  img_reintern_syms(ld);
  // After fixups: symbols.items is a real pointer only once fixups are applied.
  img_reintern_envs(ld);

  *root_out = ld->buf;
  return true;
}

static void img_loaded_free_tables(valk_image_loaded_t *ld) {
  free(ld->fixups); free(ld->stubs); free(ld->syms); free(ld->envs);
  ld->fixups = nullptr; ld->stubs = nullptr; ld->syms = nullptr;
  ld->envs = nullptr;
}

static void img_loaded_free_all(valk_image_loaded_t *ld) {
  free(ld->buf);
  img_loaded_free_tables(ld);
  ld->buf = nullptr;
}

static void *img_finalize_root(valk_image_loaded_t *ld, valk_lenv_t *registry,
                               u32 expect_kind) {
  if (ld->root_kind != expect_kind) {
    img_loaded_free_all(ld);
    return nullptr;
  }
  void *root = nullptr;
  if (!img_finalize(ld, registry, &root)) {
    img_loaded_free_all(ld);
    return nullptr;
  }
  img_loaded_free_tables(ld);
  return root;
}

// ============================================================================
// Public: load
// ============================================================================

valk_lval_t *valk_image_load_ex(const char *path, valk_lenv_t *registry) {
  valk_image_loaded_t ld;
  if (!img_read_all(path, &ld)) return nullptr;
  return (valk_lval_t *)img_finalize_root(&ld, registry, VALK_IMAGE_ROOT_LVAL);
}

valk_lval_t *valk_image_load(const char *path) {
  return valk_image_load_ex(path, nullptr);
}

valk_lenv_t *valk_image_load_env(const char *path, valk_lenv_t *registry) {
  valk_image_loaded_t ld;
  if (!img_read_all(path, &ld)) return nullptr;
  return (valk_lenv_t *)img_finalize_root(&ld, registry, VALK_IMAGE_ROOT_ENV);
}

void valk_image_load_free(valk_lval_t *root) {
  if (!root) return;
  free(root);
}

void valk_image_load_free_env(valk_lenv_t *root) {
  if (!root) return;
  free(root);
}

valk_lenv_t *valk_image_load_overlay(const char *path, valk_lenv_t *registry) {
  valk_lenv_t *dumped = valk_image_load_env(path, registry);
  if (!dumped) return nullptr;

  valk_lenv_t *overlay = valk_lenv_empty();
  overlay->parent = dumped;
  return overlay;
}

valk_lenv_t *valk_image_load_env_bytes(const unsigned char *bytes, size_t len,
                                      valk_lenv_t *registry) {
  valk_image_loaded_t ld;
  if (!img_read_bytes(bytes, len, &ld)) return nullptr;
  return (valk_lenv_t *)img_finalize_root(&ld, registry, VALK_IMAGE_ROOT_ENV);
}

valk_lenv_t *valk_image_load_overlay_bytes(const unsigned char *bytes,
                                           size_t len,
                                           valk_lenv_t *registry) {
  valk_lenv_t *dumped = valk_image_load_env_bytes(bytes, len, registry);
  if (!dumped) return nullptr;

  valk_lenv_t *overlay = valk_lenv_empty();
  overlay->parent = dumped;
  // The overlay is the mutable global env in image-backed runtimes (the AOT
  // LSP). It is read on every lookup and written/read by worker threads, so
  // back it with the concurrent map. The frozen `dumped` parent is read-only
  // after load and needs no synchronization.
  valk_lenv_make_concurrent(overlay);
  return overlay;
}

void valk_image_load_free_overlay(valk_lenv_t *overlay) {
  if (!overlay) return;
  valk_lenv_t *parent = overlay->parent;
  overlay->parent = nullptr;
  valk_lenv_free(overlay);
  valk_image_load_free_env(parent);
}

// ============================================================================
// AOT dispatch resolution
// ============================================================================

static valk_lval_t *(*aot_lookup(const valk_aot_entry_t *table, size_t count,
                                 const char *name))(valk_lenv_t *) {
  if (!table || !name) return nullptr;
  for (size_t i = 0; i < count; i++) {
    if (table[i].name && strcmp(table[i].name, name) == 0) return table[i].fn;
  }
  return nullptr;
}

valk_lenv_t *valk_aot_root_env = nullptr;

void valk_image_resolve_aot(valk_lenv_t *env,
                            const valk_aot_entry_t *table,
                            size_t count) {
  if (!env || !table || count == 0) return;
  for (valk_lenv_t *e = env; e != nullptr; e = e->parent) {
    if (!e->vals.items) continue;
    for (u64 i = 0; i < e->vals.count; i++) {
      valk_lval_t *v = e->vals.items[i];
      if (!v || LVAL_TYPE(v) != LVAL_FUN) continue;
      if (!v->fun.native_name) continue;
      valk_lval_t *(*fn)(valk_lenv_t *) =
          aot_lookup(table, count, v->fun.native_name);
      if (fn) v->fun.native_fn = fn;
    }
  }
}
