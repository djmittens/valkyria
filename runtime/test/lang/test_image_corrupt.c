#include "testing.h"
#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/image.h"
#include "../src/gc.h"
#include "../src/builtins_internal.h"

#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>

static const char *tmp_path = "/tmp/valk_image_corrupt_test.img";

#define IMG_HDR_SIZE 88u
#define IMG_OFF_ENDIAN 16u
#define IMG_OFF_LVAL_SIZE 24u
#define IMG_OFF_BUF_SIZE 40u
#define IMG_OFF_ROOT_OFFSET 48u
#define IMG_OFF_FIXUP_COUNT 56u
#define IMG_OFF_STUB_COUNT 64u
#define IMG_OFF_SYM_COUNT 72u
#define IMG_OFF_ENV_COUNT 80u

static uint8_t *read_file(const char *path, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (!f) return NULL;
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  rewind(f);
  uint8_t *buf = malloc((size_t)sz);
  size_t got = fread(buf, 1, (size_t)sz, f);
  fclose(f);
  if (got != (size_t)sz) { free(buf); return NULL; }
  *out_len = (size_t)sz;
  return buf;
}

static int write_whole_file(const char *path, const uint8_t *buf, size_t len) {
  FILE *f = fopen(path, "wb");
  if (!f) return -1;
  size_t put = fwrite(buf, 1, len, f);
  fclose(f);
  return put == len ? 0 : -1;
}

static uint64_t file_u64(const uint8_t *buf, size_t off) {
  uint64_t v;
  memcpy(&v, buf + off, sizeof(v));
  return v;
}

static void file_set_u64(uint8_t *buf, size_t off, uint64_t v) {
  memcpy(buf + off, &v, sizeof(v));
}

static int patch_u64(const char *path, size_t off, uint64_t v) {
  size_t len = 0;
  uint8_t *buf = read_file(path, &len);
  if (!buf || off + 8 > len) { free(buf); return -1; }
  file_set_u64(buf, off, v);
  int rc = write_whole_file(path, buf, len);
  free(buf);
  return rc;
}

static int patch_u32(const char *path, size_t off, uint32_t v) {
  size_t len = 0;
  uint8_t *buf = read_file(path, &len);
  if (!buf || off + 4 > len) { free(buf); return -1; }
  memcpy(buf + off, &v, sizeof(v));
  int rc = write_whole_file(path, buf, len);
  free(buf);
  return rc;
}

static void dump_num_image(void) {
  valk_lval_t *v = valk_lval_num(7);
  valk_image_dump(v, tmp_path);
}

void test_corrupt_endian_tag(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  VALK_TEST_ASSERT(patch_u64(tmp_path, IMG_OFF_ENDIAN, 0xFEEDFACEFEEDFACEull) == 0,
                   "patch ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "endian mismatch → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_struct_layout(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  VALK_TEST_ASSERT(patch_u32(tmp_path, IMG_OFF_LVAL_SIZE, 12) == 0, "patch ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "layout mismatch → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_buf_size_too_large(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  VALK_TEST_ASSERT(patch_u64(tmp_path, IMG_OFF_BUF_SIZE,
                             (1ull << 30) + 1) == 0, "patch ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "huge buf_size → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_root_offset_beyond_buf(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  size_t len = 0;
  uint8_t *buf = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(buf != NULL, "read ok");
  uint64_t buf_size = file_u64(buf, IMG_OFF_BUF_SIZE);
  free(buf);
  VALK_TEST_ASSERT(patch_u64(tmp_path, IMG_OFF_ROOT_OFFSET, buf_size + 1) == 0,
                   "patch ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "root beyond buf → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_root_offset_nonzero(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  VALK_TEST_ASSERT(patch_u64(tmp_path, IMG_OFF_ROOT_OFFSET, 8) == 0, "patch ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "nonzero root → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_buf_size_overclaims(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  size_t len = 0;
  uint8_t *buf = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(buf != NULL, "read ok");
  uint64_t buf_size = file_u64(buf, IMG_OFF_BUF_SIZE);
  free(buf);
  VALK_TEST_ASSERT(patch_u64(tmp_path, IMG_OFF_BUF_SIZE, buf_size + 4096) == 0,
                   "patch ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "short buf read → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_fixup_count_overflows_limit(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  VALK_TEST_ASSERT(patch_u64(tmp_path, IMG_OFF_FIXUP_COUNT, 1ull << 40) == 0,
                   "patch ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "giant table → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_fixup_count_overclaims(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  VALK_TEST_ASSERT(patch_u64(tmp_path, IMG_OFF_FIXUP_COUNT, 100000) == 0,
                   "patch ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "short table → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_fixup_entry_out_of_range(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *items[] = { valk_lval_num(1), valk_lval_num(2) };
  valk_lval_t *v = valk_lval_list(items, 2);
  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");

  size_t len = 0;
  uint8_t *buf = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(buf != NULL, "read ok");
  uint64_t buf_size = file_u64(buf, IMG_OFF_BUF_SIZE);
  uint64_t fx_count = file_u64(buf, IMG_OFF_FIXUP_COUNT);
  VALK_TEST_ASSERT(fx_count > 0, "cons image has fixups");
  size_t fx_off = IMG_HDR_SIZE + buf_size;
  file_set_u64(buf, fx_off, buf_size - 4);
  VALK_TEST_ASSERT(write_whole_file(tmp_path, buf, len) == 0, "write ok");
  free(buf);

  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "bad fixup → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

static valk_lval_t *corrupt_test_builtin(valk_lenv_t *env, valk_lval_t *args) {
  (void)env; (void)args;
  return valk_lval_num(1);
}

void test_corrupt_stub_entry_out_of_range(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *src = valk_lenv_empty();
  valk_lenv_put_builtin(src, "corrupt-bi", corrupt_test_builtin);
  VALK_TEST_ASSERT(valk_image_dump_env(src, tmp_path) == 0, "dump ok");

  size_t len = 0;
  uint8_t *buf = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(buf != NULL, "read ok");
  uint64_t buf_size = file_u64(buf, IMG_OFF_BUF_SIZE);
  uint64_t fx_count = file_u64(buf, IMG_OFF_FIXUP_COUNT);
  uint64_t st_count = file_u64(buf, IMG_OFF_STUB_COUNT);
  VALK_TEST_ASSERT(st_count > 0, "builtin env image has stubs");
  size_t st_off = IMG_HDR_SIZE + buf_size + fx_count * 8;
  file_set_u64(buf, st_off, buf_size - 4);
  VALK_TEST_ASSERT(write_whole_file(tmp_path, buf, len) == 0, "write ok");
  free(buf);

  valk_lenv_t *reg = valk_lenv_empty();
  valk_lenv_put_builtin(reg, "corrupt-bi", corrupt_test_builtin);
  VALK_TEST_ASSERT(valk_image_load_env(tmp_path, reg) == NULL,
                   "bad stub → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_sym_entry_out_of_range(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *v = valk_lval_sym("corrupt-sym");
  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");

  size_t len = 0;
  uint8_t *buf = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(buf != NULL, "read ok");
  uint64_t buf_size = file_u64(buf, IMG_OFF_BUF_SIZE);
  uint64_t fx_count = file_u64(buf, IMG_OFF_FIXUP_COUNT);
  uint64_t st_count = file_u64(buf, IMG_OFF_STUB_COUNT);
  uint64_t sy_count = file_u64(buf, IMG_OFF_SYM_COUNT);
  VALK_TEST_ASSERT(sy_count > 0, "sym image has sym entries");
  size_t sy_off = IMG_HDR_SIZE + buf_size + (fx_count + st_count) * 8;
  file_set_u64(buf, sy_off, buf_size - 4);
  VALK_TEST_ASSERT(write_whole_file(tmp_path, buf, len) == 0, "write ok");
  free(buf);

  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "bad sym → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_env_entry_out_of_range(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *src = valk_lenv_empty();
  valk_lenv_put(src, valk_lval_sym("a"), valk_lval_num(1));
  VALK_TEST_ASSERT(valk_image_dump_env(src, tmp_path) == 0, "dump ok");

  size_t len = 0;
  uint8_t *buf = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(buf != NULL, "read ok");
  uint64_t buf_size = file_u64(buf, IMG_OFF_BUF_SIZE);
  uint64_t fx_count = file_u64(buf, IMG_OFF_FIXUP_COUNT);
  uint64_t st_count = file_u64(buf, IMG_OFF_STUB_COUNT);
  uint64_t sy_count = file_u64(buf, IMG_OFF_SYM_COUNT);
  uint64_t en_count = file_u64(buf, IMG_OFF_ENV_COUNT);
  VALK_TEST_ASSERT(en_count > 0, "env image has env entries");
  size_t en_off =
      IMG_HDR_SIZE + buf_size + (fx_count + st_count + sy_count) * 8;
  file_set_u64(buf, en_off, buf_size - 4);
  VALK_TEST_ASSERT(write_whole_file(tmp_path, buf, len) == 0, "write ok");
  free(buf);

  VALK_TEST_ASSERT(valk_image_load_env(tmp_path, NULL) == NULL,
                   "bad env → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_table_entry_first_condition(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *items[] = { valk_lval_sym("s1"), valk_lval_num(2) };
  valk_lval_t *v = valk_lval_list(items, 2);

  for (int table = 0; table < 3; table++) {
    VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");
    size_t len = 0;
    uint8_t *buf = read_file(tmp_path, &len);
    VALK_TEST_ASSERT(buf != NULL, "read ok");
    uint64_t buf_size = file_u64(buf, IMG_OFF_BUF_SIZE);
    uint64_t fx_count = file_u64(buf, IMG_OFF_FIXUP_COUNT);
    uint64_t st_count = file_u64(buf, IMG_OFF_STUB_COUNT);
    size_t off = IMG_HDR_SIZE + buf_size;
    if (table == 1) off += fx_count * 8;
    if (table == 2) off += (fx_count + st_count) * 8;
    file_set_u64(buf, off, buf_size + 100);
    VALK_TEST_ASSERT(write_whole_file(tmp_path, buf, len) == 0, "write ok");
    free(buf);
    if (table == 1) {
      VALK_TEST_ASSERT(st_count == 0, "no stubs in sym image");
    } else {
      VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL,
                       "way-out-of-range entry → NULL");
    }
  }

  valk_lenv_t *src = valk_lenv_empty();
  valk_lenv_put_builtin(src, "far-bi", corrupt_test_builtin);
  VALK_TEST_ASSERT(valk_image_dump_env(src, tmp_path) == 0, "dump env ok");
  size_t len = 0;
  uint8_t *buf = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(buf != NULL, "read ok");
  uint64_t buf_size = file_u64(buf, IMG_OFF_BUF_SIZE);
  uint64_t fx_count = file_u64(buf, IMG_OFF_FIXUP_COUNT);
  file_set_u64(buf, IMG_HDR_SIZE + buf_size + fx_count * 8, buf_size + 100);
  VALK_TEST_ASSERT(write_whole_file(tmp_path, buf, len) == 0, "write ok");
  free(buf);
  VALK_TEST_ASSERT(valk_image_load_env(tmp_path, src) == NULL,
                   "way-out-of-range stub → NULL");

  VALK_TEST_ASSERT(valk_image_dump_env(src, tmp_path) == 0, "dump env2 ok");
  len = 0;
  buf = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(buf != NULL, "read ok");
  buf_size = file_u64(buf, IMG_OFF_BUF_SIZE);
  fx_count = file_u64(buf, IMG_OFF_FIXUP_COUNT);
  uint64_t st_count = file_u64(buf, IMG_OFF_STUB_COUNT);
  uint64_t sy_count = file_u64(buf, IMG_OFF_SYM_COUNT);
  file_set_u64(buf,
      IMG_HDR_SIZE + buf_size + (fx_count + st_count + sy_count) * 8,
      buf_size + 100);
  VALK_TEST_ASSERT(write_whole_file(tmp_path, buf, len) == 0, "write ok");
  free(buf);
  VALK_TEST_ASSERT(valk_image_load_env(tmp_path, src) == NULL,
                   "way-out-of-range env → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_other_table_counts_overclaim(VALK_TEST_ARGS()) {
  VALK_TEST();
  const size_t offs[] = { IMG_OFF_STUB_COUNT, IMG_OFF_SYM_COUNT,
                          IMG_OFF_ENV_COUNT };
  for (int i = 0; i < 3; i++) {
    dump_num_image();
    VALK_TEST_ASSERT(patch_u64(tmp_path, offs[i], 100000) == 0, "patch ok");
    VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL,
                     "overclaimed table → NULL");
  }
  unlink(tmp_path);
  VALK_PASS();
}

void test_corrupt_layout_lenv_and_ptr_size(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  VALK_TEST_ASSERT(patch_u32(tmp_path, 28, 12) == 0, "patch lenv ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "lenv mismatch → NULL");

  dump_num_image();
  VALK_TEST_ASSERT(patch_u32(tmp_path, 32, 2) == 0, "patch ptr ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "ptr mismatch → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_empty_and_zero_buf_images(VALK_TEST_ARGS()) {
  VALK_TEST();
  FILE *f = fopen(tmp_path, "wb");
  VALK_TEST_ASSERT(f != NULL, "create empty");
  fclose(f);
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "empty file → NULL");

  dump_num_image();
  size_t len = 0;
  uint8_t *buf = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(buf != NULL, "read ok");
  file_set_u64(buf, IMG_OFF_BUF_SIZE, 0);
  file_set_u64(buf, IMG_OFF_ROOT_OFFSET, 0);
  file_set_u64(buf, IMG_OFF_FIXUP_COUNT, 0);
  file_set_u64(buf, IMG_OFF_STUB_COUNT, 0);
  file_set_u64(buf, IMG_OFF_SYM_COUNT, 0);
  file_set_u64(buf, IMG_OFF_ENV_COUNT, 0);
  VALK_TEST_ASSERT(write_whole_file(tmp_path, buf, IMG_HDR_SIZE) == 0,
                   "write header-only ok");
  free(buf);
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "zero buf → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_sparse_giant_file_rejected(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  VALK_TEST_ASSERT(truncate(tmp_path, (off_t)2 * 1024 * 1024 * 1024) == 0,
                   "sparse grow ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL, "2GB file → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_null_frees_and_bytes_failures(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_image_load_free(NULL);
  valk_image_load_free_env(NULL);
  valk_image_load_free_overlay(NULL);

  VALK_TEST_ASSERT(valk_image_load_overlay("/tmp/valk_no_such_image.img",
                                           NULL) == NULL,
                   "overlay of missing file → NULL");

  unsigned char junk[64];
  memset(junk, 0xAB, sizeof(junk));
  VALK_TEST_ASSERT(valk_image_load_env_bytes(junk, sizeof(junk), NULL) == NULL,
                   "junk env bytes → NULL");
  VALK_TEST_ASSERT(valk_image_load_overlay_bytes(junk, sizeof(junk),
                                                 NULL) == NULL,
                   "junk overlay bytes → NULL");
  VALK_PASS();
}

void test_dump_dict_edge_shapes(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *no_data = valk_lval_dict(NULL);
  VALK_TEST_ASSERT(valk_image_dump(no_data, tmp_path) == 0,
                   "NULL-data dict dumps");
  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL && r->dict.data == NULL,
                   "NULL-data dict reloads");
  valk_image_load_free(r);

  valk_lval_t *d = valk_dict_lval_new(4);
  valk_dict_lval_set(d, "k", valk_lval_num(1));
  valk_lval_t *alias = valk_lval_dict(d->dict.data);
  valk_lval_t *items[] = { d, alias };
  valk_lval_t *v = valk_lval_list(items, 2);
  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "aliased dict dumps");
  valk_lval_t *r2 = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r2 != NULL, "aliased dict reloads");
  valk_lval_t *d1 = r2->cons.head;
  valk_lval_t *d2 = r2->cons.tail->cons.head;
  VALK_TEST_ASSERT(d1 != d2 && d1->dict.data == d2->dict.data,
                   "dict block deduped across lvals");
  valk_image_load_free(r2);
  unlink(tmp_path);
  VALK_PASS();
}

void test_dump_lambda_without_env(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = valk_lenv_empty();
  valk_lval_t *formals = valk_lval_qcons(valk_lval_sym("x"), valk_lval_nil());
  valk_lval_t *lambda = valk_lval_lambda(env, formals, valk_lval_sym("x"));
  lambda->fun.env = NULL;
  VALK_TEST_ASSERT(valk_image_dump(lambda, tmp_path) == 0,
                   "envless lambda dumps");
  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL && r->fun.env == NULL, "envless lambda reloads");
  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

void test_dump_empty_concurrent_env(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_make_concurrent(env);
  VALK_TEST_ASSERT(valk_image_dump_env(env, tmp_path) == 0,
                   "empty cmap env dumps");
  valk_lenv_t *loaded = valk_image_load_env(tmp_path, NULL);
  VALK_TEST_ASSERT(loaded != NULL, "empty cmap env reloads");
  VALK_TEST_ASSERT(loaded->symbols.count == 0, "no symbols");
  valk_image_load_free_env(loaded);
  unlink(tmp_path);
  VALK_PASS();
}

void test_stub_missing_name(VALK_TEST_ARGS()) {
  VALK_TEST();
  dump_num_image();
  size_t len = 0;
  uint8_t *tmpl = read_file(tmp_path, &len);
  VALK_TEST_ASSERT(tmpl != NULL && len >= IMG_HDR_SIZE, "template ok");

  size_t total = IMG_HDR_SIZE + sizeof(valk_lval_t) + 8;
  uint8_t *img = calloc(1, total);
  memcpy(img, tmpl, IMG_HDR_SIZE);
  free(tmpl);
  file_set_u64(img, IMG_OFF_BUF_SIZE, sizeof(valk_lval_t));
  file_set_u64(img, IMG_OFF_ROOT_OFFSET, 0);
  file_set_u64(img, IMG_OFF_FIXUP_COUNT, 0);
  file_set_u64(img, IMG_OFF_STUB_COUNT, 1);
  file_set_u64(img, IMG_OFF_SYM_COUNT, 0);
  file_set_u64(img, IMG_OFF_ENV_COUNT, 0);

  valk_lval_t stub = {0};
  stub.flags = LVAL_FUN;
  stub.fun.builtin = NULL;
  stub.fun.name = NULL;
  memcpy(img + IMG_HDR_SIZE, &stub, sizeof(stub));
  file_set_u64(img, IMG_HDR_SIZE + sizeof(valk_lval_t), 0);

  VALK_TEST_ASSERT(write_whole_file(tmp_path, img, total) == 0, "write ok");
  free(img);

  valk_lenv_t *reg = valk_lenv_empty();
  valk_lenv_put_builtin(reg, "some-bi", corrupt_test_builtin);
  VALK_TEST_ASSERT(valk_image_load_ex(tmp_path, reg) == NULL,
                   "nameless stub → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_root_kind_mismatch(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *src = valk_lenv_empty();
  valk_lenv_put(src, valk_lval_sym("a"), valk_lval_num(1));
  VALK_TEST_ASSERT(valk_image_dump_env(src, tmp_path) == 0, "dump env ok");
  VALK_TEST_ASSERT(valk_image_load(tmp_path) == NULL,
                   "env image via lval load → NULL");

  valk_lval_t *v = valk_lval_num(3);
  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump lval ok");
  VALK_TEST_ASSERT(valk_image_load_env(tmp_path, NULL) == NULL,
                   "lval image via env load → NULL");
  unlink(tmp_path);
  VALK_PASS();
}

void test_dump_builtin_without_name_fails(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_put_builtin(env, "named-bi", corrupt_test_builtin);
  valk_lval_t *bi = valk_lenv_get(env, valk_lval_sym("named-bi"));
  VALK_TEST_ASSERT(LVAL_TYPE(bi) == LVAL_FUN, "got builtin");

  valk_lval_t copy = *bi;
  copy.fun.name = NULL;
  VALK_TEST_ASSERT(valk_image_dump(&copy, tmp_path) == -1,
                   "nameless builtin dump fails");
  unlink(tmp_path);
  VALK_PASS();
}

void test_dump_unsupported_type_fails(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *r = valk_lval_ref("test-ref", NULL, NULL);
  VALK_TEST_ASSERT(valk_image_dump(r, tmp_path) == -1,
                   "ref dump fails");

  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_put(env, valk_lval_sym("r"), valk_lval_ref("test-ref", NULL, NULL));
  VALK_TEST_ASSERT(valk_image_dump_env(env, tmp_path) == -1,
                   "env with ref dump fails");
  unlink(tmp_path);
  VALK_PASS();
}

static void remembered_counter(valk_lval_t *v, void *ctx) {
  (void)v;
  (*(int *)ctx)++;
}

void test_dict_roundtrip_and_remembered(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *d = valk_dict_lval_new(4);
  valk_dict_lval_set(d, "alpha", valk_lval_num(1));
  valk_dict_lval_set(d, "beta", valk_lval_num(2));

  valk_lval_t *items[] = { d, d, valk_lval_num(9) };
  valk_lval_t *v = valk_lval_list(items, 3);
  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");

  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");
  valk_lval_t *d1 = r->cons.head;
  valk_lval_t *d2 = r->cons.tail->cons.head;
  ASSERT_LVAL_TYPE(d1, LVAL_DICT);
  VALK_TEST_ASSERT(d1 == d2, "shared dict deduped");
  VALK_TEST_ASSERT(d1->dict.data != NULL, "dict block present");
  VALK_TEST_ASSERT(d1->flags & LVAL_FLAG_IMMORTAL, "loaded dict is immortal");

  valk_dict_lval_set(d1, "gamma", valk_lval_num(3));
  valk_dict_lval_set(d1, "gamma", valk_lval_num(4));

  valk_lval_t *e = valk_dict_lval_new(4);
  valk_dict_lval_set(e, "solo", valk_lval_num(5));
  VALK_TEST_ASSERT(valk_image_dump(e, tmp_path) == 0, "dump second dict ok");
  valk_lval_t *e1 = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(e1 != NULL, "load second dict ok");
  valk_dict_lval_set(e1, "solo2", valk_lval_num(6));

  int count = 0;
  valk_gc_visit_remembered(remembered_counter, &count);
  VALK_TEST_ASSERT(count >= 2, "both mutated immortal dicts remembered");

  valk_gc_remember_immortal(NULL);
  int count2 = 0;
  valk_gc_visit_remembered(remembered_counter, &count2);
  VALK_TEST_ASSERT(count2 == count, "NULL is never remembered");

  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

void test_env_table_growth(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *leaf = valk_lenv_empty();
  valk_lenv_put(leaf, valk_lval_sym("leaf"), valk_lval_num(0));
  valk_lenv_t *cur = leaf;
  char name[32];
  for (int i = 0; i < 70; i++) {
    valk_lenv_t *parent = valk_lenv_empty();
    snprintf(name, sizeof(name), "chain-%d", i);
    valk_lenv_put(parent, valk_lval_sym(name), valk_lval_num(i));
    cur->parent = parent;
    cur = parent;
  }

  VALK_TEST_ASSERT(valk_image_dump_env(leaf, tmp_path) == 0, "dump ok");
  valk_lenv_t *loaded = valk_image_load_env(tmp_path, NULL);
  VALK_TEST_ASSERT(loaded != NULL, "load ok");

  valk_lval_t *vv = valk_lenv_get(loaded, valk_lval_sym("chain-69"));
  ASSERT_LVAL_TYPE(vv, LVAL_NUM);
  ASSERT_LVAL_NUM(vv, 69);

  valk_image_load_free_env(loaded);
  unlink(tmp_path);
  VALK_PASS();
}

static valk_lval_t *aot_native_stub(valk_lenv_t *env) {
  (void)env;
  return NULL;
}

void test_resolve_aot_dispatch(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *parent = valk_lenv_empty();
  valk_lenv_t *env = valk_lenv_empty();
  env->parent = parent;

  valk_lval_t *formals = valk_lval_qcons(valk_lval_sym("x"), valk_lval_nil());
  valk_lval_t *hit = valk_lval_lambda(env, formals, valk_lval_sym("x"));
  hit->fun.native_name = "aot_hit_fn";
  valk_lval_t *miss = valk_lval_lambda(env, formals, valk_lval_sym("x"));
  miss->fun.native_name = "aot_missing_fn";
  valk_lval_t *anon = valk_lval_lambda(env, formals, valk_lval_sym("x"));

  valk_lenv_put(env, valk_lval_sym("hit"), hit);
  valk_lenv_put(env, valk_lval_sym("miss"), miss);
  valk_lenv_put(env, valk_lval_sym("anon"), anon);
  valk_lenv_put(env, valk_lval_sym("num"), valk_lval_num(1));

  valk_lval_t *parent_hit = valk_lval_lambda(parent, formals, valk_lval_sym("x"));
  parent_hit->fun.native_name = "aot_hit_fn";
  valk_lenv_put(parent, valk_lval_sym("parent-hit"), parent_hit);

  valk_aot_entry_t table[] = {
    { .name = "aot_other_fn", .fn = NULL },
    { .name = "aot_hit_fn", .fn = aot_native_stub },
    { .name = NULL, .fn = NULL },
  };

  valk_image_resolve_aot(NULL, table, 3);
  valk_image_resolve_aot(env, NULL, 3);
  valk_image_resolve_aot(env, table, 0);
  VALK_TEST_ASSERT(hit->fun.native_fn == NULL, "no-op calls resolve nothing");

  valk_image_resolve_aot(env, table, 3);
  VALK_TEST_ASSERT(hit->fun.native_fn == aot_native_stub, "hit resolved");
  VALK_TEST_ASSERT(parent_hit->fun.native_fn == aot_native_stub,
                   "parent chain resolved");
  VALK_TEST_ASSERT(miss->fun.native_fn == NULL, "missing name unresolved");
  VALK_TEST_ASSERT(anon->fun.native_fn == NULL, "no native_name untouched");
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_lval_init_singletons();

  setenv("VALK_TEST_NO_FORK", "1", 1);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "corrupt_endian_tag", test_corrupt_endian_tag);
  valk_testsuite_add_test(suite, "corrupt_struct_layout", test_corrupt_struct_layout);
  valk_testsuite_add_test(suite, "corrupt_buf_size_too_large", test_corrupt_buf_size_too_large);
  valk_testsuite_add_test(suite, "corrupt_root_offset_beyond_buf", test_corrupt_root_offset_beyond_buf);
  valk_testsuite_add_test(suite, "corrupt_root_offset_nonzero", test_corrupt_root_offset_nonzero);
  valk_testsuite_add_test(suite, "corrupt_buf_size_overclaims", test_corrupt_buf_size_overclaims);
  valk_testsuite_add_test(suite, "corrupt_fixup_count_overflows_limit", test_corrupt_fixup_count_overflows_limit);
  valk_testsuite_add_test(suite, "corrupt_fixup_count_overclaims", test_corrupt_fixup_count_overclaims);
  valk_testsuite_add_test(suite, "corrupt_fixup_entry_out_of_range", test_corrupt_fixup_entry_out_of_range);
  valk_testsuite_add_test(suite, "corrupt_stub_entry_out_of_range", test_corrupt_stub_entry_out_of_range);
  valk_testsuite_add_test(suite, "corrupt_sym_entry_out_of_range", test_corrupt_sym_entry_out_of_range);
  valk_testsuite_add_test(suite, "corrupt_env_entry_out_of_range", test_corrupt_env_entry_out_of_range);
  valk_testsuite_add_test(suite, "corrupt_table_entry_first_condition", test_corrupt_table_entry_first_condition);
  valk_testsuite_add_test(suite, "corrupt_other_table_counts_overclaim", test_corrupt_other_table_counts_overclaim);
  valk_testsuite_add_test(suite, "corrupt_layout_lenv_and_ptr_size", test_corrupt_layout_lenv_and_ptr_size);
  valk_testsuite_add_test(suite, "empty_and_zero_buf_images", test_empty_and_zero_buf_images);
  valk_testsuite_add_test(suite, "sparse_giant_file_rejected", test_sparse_giant_file_rejected);
  valk_testsuite_add_test(suite, "null_frees_and_bytes_failures", test_null_frees_and_bytes_failures);
  valk_testsuite_add_test(suite, "dump_dict_edge_shapes", test_dump_dict_edge_shapes);
  valk_testsuite_add_test(suite, "dump_lambda_without_env", test_dump_lambda_without_env);
  valk_testsuite_add_test(suite, "dump_empty_concurrent_env", test_dump_empty_concurrent_env);
  valk_testsuite_add_test(suite, "stub_missing_name", test_stub_missing_name);
  valk_testsuite_add_test(suite, "root_kind_mismatch", test_root_kind_mismatch);
  valk_testsuite_add_test(suite, "dump_builtin_without_name_fails", test_dump_builtin_without_name_fails);
  valk_testsuite_add_test(suite, "dump_unsupported_type_fails", test_dump_unsupported_type_fails);
  valk_testsuite_add_test(suite, "dict_roundtrip_and_remembered", test_dict_roundtrip_and_remembered);
  valk_testsuite_add_test(suite, "env_table_growth", test_env_table_growth);
  valk_testsuite_add_test(suite, "resolve_aot_dispatch", test_resolve_aot_dispatch);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return result;
}
