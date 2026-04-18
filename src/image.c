#include "image.h"
#include "gc.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ============================================================================
// Wire format
//
//   [header][object_buffer][fixup_table]
//
// Pointers in the object buffer are stored as byte offsets into the buffer
// (nullptr stays as a literal 0). The fixup table lists every pointer-slot
// offset that needs relocation on load: `*(void**)(buf+fx) += (uintptr_t)buf`.
// ============================================================================

#define VALK_IMAGE_MAGIC "VALKIMG\0"
#define VALK_IMAGE_VERSION 1u

typedef struct {
  char magic[8];
  u32 version;
  u32 _pad;
  u64 buf_size;
  u64 root_offset;
  u64 fixup_count;
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
  valk_ptr_map_init(&b->pm);
}

static void img_builder_free(valk_image_builder_t *b) {
  free(b->buf);
  free(b->fixups);
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

  // Reserve space for the lval up front and register the mapping immediately,
  // so cycles (and shared subtrees) terminate.
  u64 off = img_reserve(b, sizeof(valk_lval_t));
  valk_ptr_map_put(&b->pm, v, (void*)(uintptr_t)(off + 1));

  // Copy raw bytes, then overwrite pointer fields with offsets.
  memcpy(b->buf + off, v, sizeof(valk_lval_t));
  valk_lval_t *dst = (valk_lval_t*)(b->buf + off);
  dst->flags = v->flags | LVAL_FLAG_IMMORTAL;

  valk_ltype_e type = LVAL_TYPE(v);
  switch (type) {
    case LVAL_NUM:
    case LVAL_NIL:
      // No pointer fields.
      break;

    case LVAL_STR:
    case LVAL_SYM:
    case LVAL_ERR: {
      u64 str_off = img_dump_cstr(b, v->str);
      // `str` lives at offsetof(valk_lval_t, str) in the dumped copy.
      u64 field_off = off + offsetof(valk_lval_t, str);
      img_store_ptr(b, field_off, str_off);
      break;
    }

    case LVAL_CONS: {
      u64 head_off = img_dump_lval(b, v->cons.head);
      u64 tail_off = img_dump_lval(b, v->cons.tail);
      img_store_ptr(b, off + offsetof(valk_lval_t, cons.head), head_off);
      img_store_ptr(b, off + offsetof(valk_lval_t, cons.tail), tail_off);
      break;
    }

    default:
      fprintf(stderr, "valk_image_dump: unsupported lval type %d\n", type);
      b->error = true;
      break;
  }

  return off;
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

  FILE *f = fopen(path, "wb");
  if (!f) {
    img_builder_free(&b);
    return -2;
  }

  valk_image_header_t hdr = {
    .version = VALK_IMAGE_VERSION,
    ._pad = 0,
    .buf_size = b.len,
    .root_offset = root_off,
    .fixup_count = b.fx_len,
  };
  memcpy(hdr.magic, VALK_IMAGE_MAGIC, 8);

  int rc = 0;
  if (fwrite(&hdr, sizeof(hdr), 1, f) != 1) rc = -3;
  if (!rc && b.len && fwrite(b.buf, 1, b.len, f) != b.len) rc = -3;
  if (!rc && b.fx_len &&
      fwrite(b.fixups, sizeof(u64), b.fx_len, f) != b.fx_len) rc = -3;

  fclose(f);
  img_builder_free(&b);
  return rc;
}

// ============================================================================
// Public: load
// ============================================================================

valk_lval_t *valk_image_load(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) return nullptr;

  valk_image_header_t hdr;
  if (fread(&hdr, sizeof(hdr), 1, f) != 1) {
    fclose(f);
    return nullptr;
  }
  if (memcmp(hdr.magic, VALK_IMAGE_MAGIC, 8) != 0 ||
      hdr.version != VALK_IMAGE_VERSION) {
    fclose(f);
    return nullptr;
  }

  u8 *buf = malloc(hdr.buf_size);
  if (hdr.buf_size && fread(buf, 1, hdr.buf_size, f) != hdr.buf_size) {
    free(buf);
    fclose(f);
    return nullptr;
  }

  u64 *fixups = malloc(hdr.fixup_count * sizeof(u64));
  if (hdr.fixup_count &&
      fread(fixups, sizeof(u64), hdr.fixup_count, f) != hdr.fixup_count) {
    free(fixups);
    free(buf);
    fclose(f);
    return nullptr;
  }
  fclose(f);

  // Apply fixups: each stored offset becomes an absolute pointer.
  uintptr_t base = (uintptr_t)buf;
  for (u64 i = 0; i < hdr.fixup_count; i++) {
    u64 fx = fixups[i];
    *(uintptr_t*)(buf + fx) += base;
  }
  free(fixups);

  return (valk_lval_t*)(buf + hdr.root_offset);
}

void valk_image_load_free(valk_lval_t *root) {
  if (!root) return;
  // The root points into the buffer that was returned by malloc in load().
  // The buffer was laid out with the first object at offset 0 OR at the
  // same offset as root — the allocated base is the buffer, and the
  // buffer's first byte was the start of the object region. Walk back.
  //
  // Since we always call valk_image_dump starting with the root (offset 0),
  // root points at the start of the buffer.
  free(root);
}
