#include "image.h"
#include "gc.h"

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
#define VALK_IMAGE_VERSION 2u

#define VALK_IMAGE_ROOT_LVAL 0u
#define VALK_IMAGE_ROOT_ENV  1u

typedef struct {
  char magic[8];
  u32 version;
  u32 root_kind;         // 0 = lval, 1 = env
  u64 buf_size;
  u64 root_offset;
  u64 fixup_count;
  u64 stub_count;
  u64 sym_count;
} valk_image_header_t;

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

  // src pointer -> (offset + 1) so a valid offset of 0 survives ptr_map's
  // nullptr-means-absent convention.
  valk_ptr_map_t pm;

  bool error;
} valk_image_builder_t;

static void img_builder_init(valk_image_builder_t *b) {
  memset(b, 0, sizeof(*b));
  b->cap = 1024;
  b->buf = malloc(b->cap);
  b->fx_cap = 64;
  b->fixups = malloc(b->fx_cap * sizeof(u64));
  b->st_cap = 16;
  b->stubs = malloc(b->st_cap * sizeof(u64));
  b->sy_cap = 64;
  b->syms = malloc(b->sy_cap * sizeof(u64));
  valk_ptr_map_init(&b->pm);
}

static void img_builder_free(valk_image_builder_t *b) {
  free(b->buf);
  free(b->fixups);
  free(b->stubs);
  free(b->syms);
  valk_ptr_map_free(&b->pm);
}

static u64 img_reserve(valk_image_builder_t *b, u64 size) {
  while (b->len + size > b->cap) {
    b->cap *= 2;
    b->buf = realloc(b->buf, b->cap);
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
    b->fx_cap *= 2;
    b->fixups = realloc(b->fixups, b->fx_cap * sizeof(u64));
  }
  b->fixups[b->fx_len++] = field_offset;
}

static void img_add_stub(valk_image_builder_t *b, u64 stub_offset) {
  if (b->st_len >= b->st_cap) {
    b->st_cap *= 2;
    b->stubs = realloc(b->stubs, b->st_cap * sizeof(u64));
  }
  b->stubs[b->st_len++] = stub_offset;
}

static void img_add_sym(valk_image_builder_t *b, u64 sym_offset) {
  if (b->sy_len >= b->sy_cap) {
    b->sy_cap *= 2;
    b->syms = realloc(b->syms, b->sy_cap * sizeof(u64));
  }
  b->syms[b->sy_len++] = sym_offset;
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

    case LVAL_FUN: {
      u64 name_off = img_dump_cstr(b, v->fun.name);
      img_store_ptr(b, off + offsetof(valk_lval_t, fun.name), name_off);
      if (v->fun.builtin != nullptr) {
        // Builtin stub: zero the function pointer and lambda-only fields.
        valk_lval_t *dst2 = (valk_lval_t*)(b->buf + off);
        dst2->fun.builtin = nullptr;
        *(u64*)(b->buf + off + offsetof(valk_lval_t, fun.env)) = 0;
        *(u64*)(b->buf + off + offsetof(valk_lval_t, fun.formals)) = 0;
        *(u64*)(b->buf + off + offsetof(valk_lval_t, fun.body)) = 0;
        if (!v->fun.name) {
          fprintf(stderr, "valk_image_dump: builtin has no fun.name\n");
          b->error = true;
          break;
        }
        img_add_stub(b, off);
      } else {
        // Lambda: serialize closure env, formals, body.
        u64 env_off = v->fun.env ? img_dump_lenv(b, v->fun.env) : 0;
        u64 formals_off = img_dump_lval(b, v->fun.formals);
        u64 body_off = img_dump_lval(b, v->fun.body);
        img_store_ptr(b, off + offsetof(valk_lval_t, fun.env), env_off);
        img_store_ptr(b, off + offsetof(valk_lval_t, fun.formals), formals_off);
        img_store_ptr(b, off + offsetof(valk_lval_t, fun.body), body_off);
      }
      break;
    }

    default:
      fprintf(stderr, "valk_image_dump: unsupported lval type %d\n", type);
      b->error = true;
      break;
  }

  return off;
}

static u64 img_dump_lenv(valk_image_builder_t *b, valk_lenv_t *env) {
  if (!env) return 0;
  void *existing = valk_ptr_map_get(&b->pm, env);
  if (existing) return (u64)(uintptr_t)existing - 1;

  u64 off = img_reserve(b, sizeof(valk_lenv_t));
  valk_ptr_map_put(&b->pm, env, (void*)(uintptr_t)(off + 1));

  memcpy(b->buf + off, env, sizeof(valk_lenv_t));

  u64 n = env->symbols.count;

  // Dump symbol name strings array: char*[n].
  u64 sym_arr_off = 0;
  if (n > 0 && env->symbols.items) {
    sym_arr_off = img_reserve(b, n * sizeof(char*));
    for (u64 i = 0; i < n; i++) {
      u64 s_off = img_dump_cstr(b, env->symbols.items[i]);
      u64 slot_off = sym_arr_off + i * sizeof(char*);
      img_store_ptr(b, slot_off, s_off);
    }
  }

  // Dump value pointer array: valk_lval_t*[n].
  u64 val_arr_off = 0;
  if (n > 0 && env->vals.items) {
    val_arr_off = img_reserve(b, n * sizeof(valk_lval_t*));
    for (u64 i = 0; i < n; i++) {
      u64 v_off = img_dump_lval(b, env->vals.items[i]);
      u64 slot_off = val_arr_off + i * sizeof(valk_lval_t*);
      img_store_ptr(b, slot_off, v_off);
    }
  }

  u64 parent_off = env->parent ? img_dump_lenv(b, env->parent) : 0;

  // Write the env header fields (count, pointers) after all reserves so we
  // don't hold stale buf pointers across realloc.
  valk_lenv_t *dst = (valk_lenv_t*)(b->buf + off);
  atomic_store(&dst->flags, LENV_FLAG_FROZEN);
  dst->allocator = nullptr;
  dst->symbols.count = n;
  dst->symbols.capacity = n;
  dst->vals.count = n;
  dst->vals.capacity = n;
  img_store_ptr(b, off + offsetof(valk_lenv_t, symbols.items), sym_arr_off);
  img_store_ptr(b, off + offsetof(valk_lenv_t, vals.items), val_arr_off);
  img_store_ptr(b, off + offsetof(valk_lenv_t, parent), parent_off);

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
    .buf_size = b->len,
    .root_offset = root_off,
    .fixup_count = b->fx_len,
    .stub_count = b->st_len,
    .sym_count = b->sy_len,
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

  fclose(f);
  return rc;
}

// ============================================================================
// Public: dump
// ============================================================================

int valk_image_dump(valk_lval_t *val, const char *path) {
  valk_image_builder_t b;
  img_builder_init(&b);

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
  img_builder_init(&b);

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
} valk_image_loaded_t;

static bool img_read_all(const char *path, valk_image_loaded_t *out) {
  memset(out, 0, sizeof(*out));
  FILE *f = fopen(path, "rb");
  if (!f) return false;

  valk_image_header_t hdr;
  if (fread(&hdr, sizeof(hdr), 1, f) != 1) goto fail;
  if (memcmp(hdr.magic, VALK_IMAGE_MAGIC, 8) != 0 ||
      hdr.version != VALK_IMAGE_VERSION) goto fail;

  out->buf_size = hdr.buf_size;
  out->root_offset = hdr.root_offset;
  out->root_kind = hdr.root_kind;
  out->fixup_count = hdr.fixup_count;
  out->stub_count = hdr.stub_count;
  out->sym_count = hdr.sym_count;

  out->buf = malloc(hdr.buf_size);
  if (hdr.buf_size && fread(out->buf, 1, hdr.buf_size, f) != hdr.buf_size)
    goto fail;

  out->fixups = malloc(hdr.fixup_count * sizeof(u64));
  if (hdr.fixup_count &&
      fread(out->fixups, sizeof(u64), hdr.fixup_count, f) != hdr.fixup_count)
    goto fail;

  out->stubs = malloc(hdr.stub_count * sizeof(u64));
  if (hdr.stub_count &&
      fread(out->stubs, sizeof(u64), hdr.stub_count, f) != hdr.stub_count)
    goto fail;

  out->syms = malloc(hdr.sym_count * sizeof(u64));
  if (hdr.sym_count &&
      fread(out->syms, sizeof(u64), hdr.sym_count, f) != hdr.sym_count)
    goto fail;

  fclose(f);
  return true;

fail:
  fclose(f);
  free(out->buf);
  free(out->fixups);
  free(out->stubs);
  free(out->syms);
  memset(out, 0, sizeof(*out));
  return false;
}

// Resolve each builtin stub against `registry` and fill rep[i] with the
// replacement pointer. Returns false on any unresolved name.
static bool img_resolve_stubs(valk_image_loaded_t *ld, valk_lenv_t *registry,
                              valk_lval_t **rep) {
  if (ld->stub_count == 0) return true;
  if (!registry) {
    fprintf(stderr,
            "valk_image_load: image contains %llu builtin stubs but no "
            "registry was provided\n",
            (unsigned long long)ld->stub_count);
    return false;
  }
  for (u64 i = 0; i < ld->stub_count; i++) {
    valk_lval_t *stub = (valk_lval_t*)(ld->buf + ld->stubs[i]);
    if (!stub->fun.name) {
      fprintf(stderr, "valk_image_load: stub missing fun.name\n");
      return false;
    }
    valk_lval_t key = {0};
    key.flags = LVAL_SYM;
    key.str = stub->fun.name;
    valk_lval_t *live = valk_lenv_get(registry, &key);
    if (!live || LVAL_TYPE(live) == LVAL_ERR) {
      fprintf(stderr,
              "valk_image_load: builtin `%s` not found in registry\n",
              stub->fun.name);
      return false;
    }
    rep[i] = live;
  }
  return true;
}

// Rewrite any fixup slot whose value equals a stub address with the
// corresponding live pointer from `rep`.
static void img_apply_stub_map(valk_image_loaded_t *ld, valk_lval_t **rep) {
  if (ld->stub_count == 0) return;
  for (u64 i = 0; i < ld->fixup_count; i++) {
    void **slot = (void**)(ld->buf + ld->fixups[i]);
    void *p = *slot;
    for (u64 s = 0; s < ld->stub_count; s++) {
      if (p == (void*)(ld->buf + ld->stubs[s])) {
        *slot = rep[s];
        break;
      }
    }
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
    fprintf(stderr, "valk_image_load: unexpected non-zero root_offset\n");
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
    if (!img_resolve_stubs(ld, registry, rep)) {
      free(rep);
      return false;
    }
  }
  img_apply_stub_map(ld, rep);
  free(rep);

  img_reintern_syms(ld);

  *root_out = ld->buf;
  return true;
}

// ============================================================================
// Public: load
// ============================================================================

valk_lval_t *valk_image_load_ex(const char *path, valk_lenv_t *registry) {
  valk_image_loaded_t ld;
  if (!img_read_all(path, &ld)) return nullptr;
  if (ld.root_kind != VALK_IMAGE_ROOT_LVAL) {
    free(ld.buf); free(ld.fixups); free(ld.stubs); free(ld.syms);
    return nullptr;
  }
  void *root = nullptr;
  if (!img_finalize(&ld, registry, &root)) {
    free(ld.buf); free(ld.fixups); free(ld.stubs); free(ld.syms);
    return nullptr;
  }
  free(ld.fixups); free(ld.stubs); free(ld.syms);
  // Keep ld.buf alive; root points into it (or into registry for stub-root).
  return (valk_lval_t*)root;
}

valk_lval_t *valk_image_load(const char *path) {
  return valk_image_load_ex(path, nullptr);
}

valk_lenv_t *valk_image_load_env(const char *path, valk_lenv_t *registry) {
  valk_image_loaded_t ld;
  if (!img_read_all(path, &ld)) return nullptr;
  if (ld.root_kind != VALK_IMAGE_ROOT_ENV) {
    free(ld.buf); free(ld.fixups); free(ld.stubs); free(ld.syms);
    return nullptr;
  }
  void *root = nullptr;
  if (!img_finalize(&ld, registry, &root)) {
    free(ld.buf); free(ld.fixups); free(ld.stubs); free(ld.syms);
    return nullptr;
  }
  free(ld.fixups); free(ld.stubs); free(ld.syms);
  return (valk_lenv_t*)root;
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

void valk_image_load_free_overlay(valk_lenv_t *overlay) {
  if (!overlay) return;
  valk_lenv_t *parent = overlay->parent;
  overlay->parent = nullptr;
  valk_lenv_free(overlay);
  valk_image_load_free_env(parent);
}
