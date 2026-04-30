#include "builtins_internal.h"
#include "type_infer.h"
extern valk_lval_t *valk_builtin_lsp_index_file(valk_lenv_t *e, valk_lval_t *a);

#include <dirent.h>
#include <errno.h>
#include <limits.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>
#ifdef __linux__
#include <sys/prctl.h>
#endif
#include <uv.h>

#include "gc.h"
#include "type_env.h"
#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/aio_internal.h"

static valk_lval_t* valk_builtin_list_dir(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* path = valk_lval_list_nth(a, 0)->str;
  DIR* d = opendir(path);
  if (!d) LVAL_RAISE(a, "Could not open directory (%s)", path);

  size_t count = 0;
  size_t cap = 64;
  valk_lval_t** items = malloc(cap * sizeof(valk_lval_t*));

  struct dirent* ent;
  while ((ent = readdir(d))) {
    if (ent->d_name[0] == '.') continue;

    char full[4096];
    snprintf(full, sizeof(full), "%s/%s", path, ent->d_name);
    struct stat st;
    const char* type_str = "file";
    if (stat(full, &st) == 0 && S_ISDIR(st.st_mode))
      type_str = "dir";

    valk_lval_t* fields[4] = {
      valk_lval_sym(":name"), valk_lval_str(ent->d_name),
      valk_lval_sym(":type"), valk_lval_str(type_str),
    };
    if (count >= cap) {
      cap *= 2;
      items = realloc(items, cap * sizeof(valk_lval_t*));
    }
    items[count++] = valk_lval_qlist(fields, 4);
  }
  closedir(d);

  valk_lval_t* result = valk_lval_qlist(items, count);
  free(items);
  return result;
}

static valk_lval_t* valk_builtin_file_fingerprint(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* path = valk_lval_list_nth(a, 0)->str;
  struct stat st;
  if (stat(path, &st) != 0)
    LVAL_RAISE(a, "file/fingerprint: cannot stat (%s)", path);
  char buf[64];
  snprintf(buf, sizeof(buf), "%lld:%lld", (long long)st.st_mtime, (long long)st.st_size);
  return valk_lval_str(buf);
}

static valk_lval_t* valk_builtin_file_size(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* path = valk_lval_list_nth(a, 0)->str;
  struct stat st;
  if (stat(path, &st) != 0)
    LVAL_RAISE(a, "file/size: cannot stat (%s)", path);
  return valk_lval_num((long)st.st_size);
}

// LSP semantic-tokens delta encoder.
//
// Input:  text plus a list of 4-tuples (offset length type mods).
// Output: flat list of 5-tuples (deltaLine deltaCol length type mods)
//         in LSP wire order: tokens sorted by absolute (line, col) with
//         non-negative deltas.
//
// We sort by offset before encoding because the AST walker emits in
// AST-traversal order, not source order — a `(do (fn) (fn))` that
// recurses into the second `(fn)` before classifying the head produces
// out-of-order tokens. Sorting decouples walker correctness from
// encoding correctness; otherwise the encoder produces negative
// deltaLine values, which violate the LSP spec and make every editor
// downstream of the bad token misalign all subsequent highlighting.
typedef struct {
  int off;
  int len;
  int type;
  int mods;
} sem_tok_t;

static int sem_tok_cmp(const void *a, const void *b) {
  const sem_tok_t *x = a;
  const sem_tok_t *y = b;
  if (x->off != y->off) return x->off - y->off;
  // Stable order for equal offsets keeps the encoder happy: within one
  // position, longer tokens first so a containing token doesn't end up
  // emitted with negative deltaCol.
  return y->len - x->len;
}

static valk_lval_t *valk_builtin_sem_encode_deltas(valk_lenv_t *e,
                                                    valk_lval_t *a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char *text = valk_lval_list_nth(a, 0)->str;
  valk_lval_t *tokens = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, tokens, LVAL_CONS, LVAL_NIL); // LCOV_EXCL_BR_LINE

  int text_len = (int)strlen(text);

  // Phase 1: collect tokens into a flat array we can sort.
  u64 capacity = 64;
  u64 count = 0;
  sem_tok_t *toks = valk_mem_alloc(sizeof(sem_tok_t) * capacity);
  valk_lval_t *cur = tokens;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    valk_lval_t *tok = cur->cons.head;
    if (!tok || LVAL_TYPE(tok) != LVAL_CONS) break;

    valk_lval_t *off_v = tok->cons.head;
    valk_lval_t *r1 = tok->cons.tail;
    if (!r1 || LVAL_TYPE(r1) != LVAL_CONS) break;
    valk_lval_t *len_v = r1->cons.head;
    valk_lval_t *r2 = r1->cons.tail;
    if (!r2 || LVAL_TYPE(r2) != LVAL_CONS) break;
    valk_lval_t *type_v = r2->cons.head;
    valk_lval_t *r3 = r2->cons.tail;
    if (!r3 || LVAL_TYPE(r3) != LVAL_CONS) break;
    valk_lval_t *mods_v = r3->cons.head;

    if (count >= capacity) {
      capacity *= 2;
      sem_tok_t *new_toks = valk_mem_alloc(sizeof(sem_tok_t) * capacity);
      memcpy(new_toks, toks, sizeof(sem_tok_t) * count);
      toks = new_toks;
    }
    int off = (int)off_v->num;
    // Skip tokens with negative offsets (they're invalid in any text).
    // Don't filter on `off >= text_len` here — the encoder loop below
    // already bounds its scan by text_len, so a token past EOF will
    // simply land at end-of-text in the encoded output. Filtering here
    // dropped legitimate tokens whose end-position equals text_len
    // exactly, which is a common case for tokens at EOF.
    if (off < 0) { cur = cur->cons.tail; continue; }
    toks[count].off = off;
    toks[count].len = (int)len_v->num;
    toks[count].type = (int)type_v->num;
    toks[count].mods = (int)mods_v->num;
    count++;
    cur = cur->cons.tail;
  }

  // Phase 2: sort by offset so deltas are non-negative by construction.
  qsort(toks, count, sizeof(sem_tok_t), sem_tok_cmp);

  // Phase 3: encode deltas. Single forward pass over text computes the
  // (line, col) of each token's offset; since tokens are now sorted,
  // the scan never has to rewind.
  int prev_line = 0, prev_col = 0, scan_pos = 0, line = 0, col = 0;
  valk_lval_t *result = valk_lval_nil();
  int bad_dl = 0, bad_dc = 0, total = 0;
  int first_bad_line = -1, first_bad_col = -1;
  for (u64 i = 0; i < count; i++) {
    int off = toks[i].off;
    while (scan_pos < off && scan_pos < text_len) {
      if (text[scan_pos] == '\n') { line++; col = 0; }
      else col++;
      scan_pos++;
    }

    int dl = line - prev_line;
    int dc = (dl == 0) ? col - prev_col : col;
    total++;
    if (dl < 0) {
      if (first_bad_line < 0) first_bad_line = (int)i;
      bad_dl++;
    }
    if (dl == 0 && dc < 0) {
      if (first_bad_col < 0) first_bad_col = (int)i;
      bad_dc++;
    }

    result = valk_lval_qcons(valk_lval_num(dl), result);
    result = valk_lval_qcons(valk_lval_num(dc), result);
    result = valk_lval_qcons(valk_lval_num(toks[i].len), result);
    result = valk_lval_qcons(valk_lval_num(toks[i].type), result);
    result = valk_lval_qcons(valk_lval_num(toks[i].mods), result);
    prev_line = line;
    prev_col = col;
  }
  if (bad_dl > 0 || bad_dc > 0) {
    fprintf(stderr,
      "[sem-encode] BAD tokens: %d/%d had dl<0 (first idx=%d), %d had dc<0 (first idx=%d)\n",
      bad_dl, total, first_bad_line, bad_dc, first_bad_col);
  }

  valk_lval_t *reversed = valk_lval_nil();
  valk_lval_t *p = result;
  while (p && LVAL_TYPE(p) == LVAL_CONS) {
    reversed = valk_lval_qcons(p->cons.head, reversed);
    p = p->cons.tail;
  }
  return reversed;
}

static valk_lval_t *valk_builtin_offsets_to_lines(valk_lenv_t *e,
                                                    valk_lval_t *a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char *text = valk_lval_list_nth(a, 0)->str;
  valk_lval_t *offsets = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_TYPE(a, offsets, LVAL_CONS, LVAL_NIL); // LCOV_EXCL_BR_LINE
  int text_len = (int)strlen(text);

  int scan_pos = 0, line = 0, col = 0;
  valk_lval_t *result = valk_lval_nil();

  valk_lval_t *cur = offsets;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    int off = (int)cur->cons.head->num;
    if (off >= scan_pos) {
      for (int i = scan_pos; i < off && i < text_len; i++) {
        if (text[i] == '\n') { line++; col = 0; }
        else col++;
      }
    }
    scan_pos = off;
    valk_lval_t *pair[2] = {valk_lval_num(line), valk_lval_num(col)};
    result = valk_lval_qcons(valk_lval_qlist(pair, 2), result);
    cur = cur->cons.tail;
  }

  valk_lval_t *reversed = valk_lval_nil();
  valk_lval_t *p = result;
  while (p && LVAL_TYPE(p) == LVAL_CONS) {
    reversed = valk_lval_qcons(p->cons.head, reversed);
    p = p->cons.tail;
  }
  return reversed;
}

static valk_lval_t* valk_builtin_write_file(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* path = valk_lval_list_nth(a, 0)->str;
  const char* content = valk_lval_list_nth(a, 1)->str;
  u64 len = strlen(content);

  FILE* f = fopen(path, "wb");
  if (!f)
    LVAL_RAISE(a, "write-file: could not open (%s): %s", path, strerror(errno));

  if (len > 0) {
    u64 written = fwrite(content, 1, len, f);
    if (written != len) { // LCOV_EXCL_START
      fclose(f);
      LVAL_RAISE(a, "write-file: partial write (%s)", path);
    } // LCOV_EXCL_STOP
  }
  fclose(f);
  return valk_lval_num((long)len);
}

static valk_lval_t* valk_builtin_file_exists(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  struct stat st;
  return valk_lval_num(stat(valk_lval_list_nth(a, 0)->str, &st) == 0 ? 1 : 0);
}

static valk_lval_t* valk_builtin_mkdir_p(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char* path = valk_lval_list_nth(a, 0)->str;
  char tmp[4096];
  snprintf(tmp, sizeof(tmp), "%s", path);

  for (char* p = tmp + 1; *p; p++) {
    if (*p == '/') {
      *p = '\0';
      if (mkdir(tmp, 0755) != 0 && errno != EEXIST)
        LVAL_RAISE(a, "mkdir-p: failed at (%s): %s", tmp, strerror(errno));
      *p = '/';
    }
  }
  if (mkdir(tmp, 0755) != 0 && errno != EEXIST)
    LVAL_RAISE(a, "mkdir-p: failed (%s): %s", tmp, strerror(errno));

  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_file_delete(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* path = valk_lval_list_nth(a, 0)->str;
  if (unlink(path) != 0)
    LVAL_RAISE(a, "file/delete: failed (%s): %s", path, strerror(errno));
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_rmdir(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* path = valk_lval_list_nth(a, 0)->str;
  if (rmdir(path) != 0)
    LVAL_RAISE(a, "rmdir: failed (%s): %s", path, strerror(errno));
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_symlink(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* target = valk_lval_list_nth(a, 0)->str;
  const char* link_path = valk_lval_list_nth(a, 1)->str;
  unlink(link_path);
  if (symlink(target, link_path) != 0)
    LVAL_RAISE(a, "symlink: failed (%s -> %s): %s", link_path, target, strerror(errno));
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_env_get(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  const char* val = getenv(valk_lval_list_nth(a, 0)->str);
  if (!val) return valk_lval_nil();
  return valk_lval_str(val);
}

static valk_lval_t* valk_builtin_env_set(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  setenv(valk_lval_list_nth(a, 0)->str, valk_lval_list_nth(a, 1)->str, 1);
  return valk_lval_nil();
}

static valk_lval_t* valk_builtin_realpath(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP
  char resolved[PATH_MAX];
  if (!realpath(valk_lval_list_nth(a, 0)->str, resolved))
    LVAL_RAISE(a, "realpath: failed (%s): %s",
               valk_lval_list_nth(a, 0)->str, strerror(errno));
  return valk_lval_str(resolved);
}

static valk_lval_t* valk_builtin_exec(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_GE(a, a, 1);

  u64 nargs = valk_lval_list_count(a);
  for (u64 i = 0; i < nargs; i++) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, i), LVAL_STR);
  }
  // LCOV_EXCL_BR_STOP

  char** argv_exec = calloc(nargs + 1, sizeof(char*));
  for (u64 i = 0; i < nargs; i++) {
    argv_exec[i] = (char*)valk_lval_list_nth(a, i)->str;
  }
  argv_exec[nargs] = nullptr;

  int stdout_pipe[2], stderr_pipe[2];
  if (pipe(stdout_pipe) != 0 || pipe(stderr_pipe) != 0) { // LCOV_EXCL_START
    free(argv_exec);
    LVAL_RAISE(a, "exec: pipe() failed: %s", strerror(errno));
  } // LCOV_EXCL_STOP

  pid_t pid = fork();
  if (pid < 0) { // LCOV_EXCL_START
    free(argv_exec);
    close(stdout_pipe[0]); close(stdout_pipe[1]);
    close(stderr_pipe[0]); close(stderr_pipe[1]);
    LVAL_RAISE(a, "exec: fork() failed: %s", strerror(errno));
  } // LCOV_EXCL_STOP

  // LCOV_EXCL_START - runs in forked child process, unreachable by coverage instrumentation
  if (pid == 0) {
#ifdef __linux__
    // If parent dies (crashes, killed, etc.), receive SIGTERM and exit.
    // Prevents zombie subprocesses reparenting to init and burning CPU.
    prctl(PR_SET_PDEATHSIG, SIGTERM);
    // Race: parent may have already died between fork() and prctl().
    if (getppid() == 1) _exit(143);
#endif
    close(stdout_pipe[0]);
    close(stderr_pipe[0]);
    dup2(stdout_pipe[1], STDOUT_FILENO);
    dup2(stderr_pipe[1], STDERR_FILENO);
    close(stdout_pipe[1]);
    close(stderr_pipe[1]);
    execvp(argv_exec[0], argv_exec);
    _exit(127);
  }
  // LCOV_EXCL_STOP

  free(argv_exec);
  close(stdout_pipe[1]);
  close(stderr_pipe[1]);

  size_t out_cap = 4096, out_len = 0;
  char* out_buf = malloc(out_cap);
  size_t err_cap = 4096, err_len = 0;
  char* err_buf = malloc(err_cap);

  struct pollfd fds[2] = {
    {.fd = stdout_pipe[0], .events = POLLIN},
    {.fd = stderr_pipe[0], .events = POLLIN},
  };
  // LCOV_EXCL_BR_START - poll/read loop: branch edges depend on pipe timing and buffer state
  int open_fds = 2;
  while (open_fds > 0) {
    int ret = poll(fds, 2, -1);
    if (ret < 0) {
      if (errno == EINTR) continue;
      break; // LCOV_EXCL_LINE
    }
    for (int fi = 0; fi < 2; fi++) {
      if (fds[fi].fd < 0) continue;
      if (!(fds[fi].revents & (POLLIN | POLLHUP))) continue;
      char **buf = fi == 0 ? &out_buf : &err_buf;
      size_t *len = fi == 0 ? &out_len : &err_len;
      size_t *cap = fi == 0 ? &out_cap : &err_cap;
      if (*len >= *cap) { *cap *= 2; *buf = realloc(*buf, *cap); }
      ssize_t n = read(fds[fi].fd, *buf + *len, *cap - *len);
      if (n > 0) {
        *len += n;
      } else if (n == 0 || (n < 0 && errno != EINTR)) {
        close(fds[fi].fd);
        fds[fi].fd = -1;
        open_fds--;
      }
    }
  }
  if (fds[0].fd >= 0) close(fds[0].fd);
  if (fds[1].fd >= 0) close(fds[1].fd);
  // LCOV_EXCL_BR_STOP

  int status = 0;
  waitpid(pid, &status, 0);

  // LCOV_EXCL_BR_START - process exit status: WIFEXITED/WIFSIGNALED macro branches
  long exit_code;
  if (WIFEXITED(status)) {
    exit_code = WEXITSTATUS(status);
  } else if (WIFSIGNALED(status)) {
    exit_code = -(long)WTERMSIG(status);
  } else {
    exit_code = -1; // LCOV_EXCL_LINE
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t* result;
  valk_mem_arena_t* scratch = valk_thread_ctx.scratch;
  if (scratch) {
    VALK_WITH_ALLOC((void*)scratch) {
      valk_lval_t* fields[6] = {
        valk_lval_sym(":exit-code"), valk_lval_num(exit_code),
        valk_lval_sym(":stdout"),    valk_lval_str_n(out_buf, out_len),
        valk_lval_sym(":stderr"),    valk_lval_str_n(err_buf, err_len),
      };
      result = valk_lval_qlist(fields, 6);
    }
    result = valk_evacuate_to_heap(result);
  } else { // LCOV_EXCL_START - scratch always present in aio/REPL contexts
    valk_lval_t* fields[6] = {
      valk_lval_sym(":exit-code"), valk_lval_num(exit_code),
      valk_lval_sym(":stdout"),    valk_lval_str_n(out_buf, out_len),
      valk_lval_sym(":stderr"),    valk_lval_str_n(err_buf, err_len),
    };
    result = valk_lval_qlist(fields, 6);
  } // LCOV_EXCL_STOP
  free(out_buf);
  free(err_buf);
  return result;
}

// --- async exec via uv_spawn --------------------------------------------
// aio/exec dispatches the subprocess through libuv on loop 0. Output is
// accumulated by uv_read_start callbacks until both pipes hit EOF and the
// process exits. Result qlist is built in the close callback of the last
// handle to close; handle transitions to COMPLETED at that point.
// LCOV_EXCL_START - aio/exec: test coverage via Valk-level tests
typedef struct valk_aio_exec_ctx {
  valk_async_handle_t *handle;
  uv_process_t process;
  uv_pipe_t stdout_pipe;
  uv_pipe_t stderr_pipe;
  char *out_buf; size_t out_len, out_cap;
  char *err_buf; size_t err_len, err_cap;
  bool process_exited;
  bool stdout_closed;
  bool stderr_closed;
  bool spawn_failed;
  int close_pending;
  int64_t exit_status;
  int term_signal;
  char *spawn_err_msg;
  char **argv;
  int argc;
} valk_aio_exec_ctx_t;

static void __aio_exec_free_ctx(valk_aio_exec_ctx_t *ctx) {
  if (!ctx) return;
  free(ctx->out_buf);
  free(ctx->err_buf);
  if (ctx->argv) {
    for (int i = 0; i < ctx->argc; i++) free(ctx->argv[i]);
    free(ctx->argv);
  }
  free(ctx->spawn_err_msg);
  free(ctx);
}

static void __aio_exec_try_finalize(valk_aio_exec_ctx_t *ctx) {
  if (ctx->close_pending > 0) return;
  if (!ctx->spawn_failed &&
      (!ctx->process_exited || !ctx->stdout_closed || !ctx->stderr_closed)) return;

  if (ctx->spawn_failed) {
    valk_lval_t *err;
    VALK_WITH_ALLOC((void*)valk_thread_ctx.heap) {
      err = valk_lval_err("aio/exec: uv_spawn failed: %s",
                          ctx->spawn_err_msg ? ctx->spawn_err_msg : "unknown");
    }
    valk_async_handle_fail(ctx->handle, err);
    __aio_exec_free_ctx(ctx);
    return;
  }

  long exit_code = (ctx->term_signal != 0) ? -(long)ctx->term_signal
                                           : (long)ctx->exit_status;
  valk_lval_t *result;
  VALK_WITH_ALLOC((void*)valk_thread_ctx.heap) {
    valk_lval_t *fields[6] = {
      valk_lval_sym(":exit-code"), valk_lval_num(exit_code),
      valk_lval_sym(":stdout"),    valk_lval_str_n(ctx->out_buf ? ctx->out_buf : "", ctx->out_len),
      valk_lval_sym(":stderr"),    valk_lval_str_n(ctx->err_buf ? ctx->err_buf : "", ctx->err_len),
    };
    result = valk_lval_qlist(fields, 6);
  }
  valk_async_handle_complete(ctx->handle, result);
  __aio_exec_free_ctx(ctx);
}

static void __aio_exec_uv_close_cb(uv_handle_t *h) {
  valk_aio_exec_ctx_t *ctx = h->data;
  ctx->close_pending--;
  __aio_exec_try_finalize(ctx);
}

static void __aio_exec_alloc_cb(uv_handle_t *h, size_t suggested, uv_buf_t *buf) {
  (void)h; (void)suggested;
  buf->base = malloc(4096);
  buf->len = 4096;
}

static void __aio_exec_read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
  VALK_GC_SAFE_POINT();
  valk_aio_exec_ctx_t *ctx = stream->data;
  bool is_stdout = (stream == (uv_stream_t*)&ctx->stdout_pipe);
  char **dst = is_stdout ? &ctx->out_buf : &ctx->err_buf;
  size_t *len = is_stdout ? &ctx->out_len : &ctx->err_len;
  size_t *cap = is_stdout ? &ctx->out_cap : &ctx->err_cap;

  if (nread > 0) {
    if (*len + (size_t)nread > *cap) {
      *cap = (*len + (size_t)nread) * 2;
      *dst = realloc(*dst, *cap);
    }
    memcpy(*dst + *len, buf->base, (size_t)nread);
    *len += (size_t)nread;
    free(buf->base);
    return;
  }
  free(buf->base);
  bool *closed_flag = is_stdout ? &ctx->stdout_closed : &ctx->stderr_closed;
  if (*closed_flag) return;
  *closed_flag = true;
  uv_close((uv_handle_t*)stream, __aio_exec_uv_close_cb);
}

static void __aio_exec_exit_cb(uv_process_t *proc, int64_t exit_status, int term_signal) {
  valk_aio_exec_ctx_t *ctx = proc->data;
  ctx->process_exited = true;
  ctx->exit_status = exit_status;
  ctx->term_signal = term_signal;
  uv_close((uv_handle_t*)&ctx->process, __aio_exec_uv_close_cb);
}

static void __aio_exec_spawn_on_loop(void *arg) {
  VALK_GC_SAFE_POINT();
  valk_aio_exec_ctx_t *ctx = arg;
  valk_aio_system_t *sys = ctx->handle->sys;
  uv_loop_t *loop = sys->loops[0].uv_loop;

  uv_pipe_init(loop, &ctx->stdout_pipe, 0);
  uv_pipe_init(loop, &ctx->stderr_pipe, 0);
  ctx->stdout_pipe.data = ctx;
  ctx->stderr_pipe.data = ctx;
  ctx->process.data = ctx;

  uv_stdio_container_t stdio[3] = {
    { .flags = UV_IGNORE },
    { .flags = UV_CREATE_PIPE | UV_WRITABLE_PIPE, .data.stream = (uv_stream_t*)&ctx->stdout_pipe },
    { .flags = UV_CREATE_PIPE | UV_WRITABLE_PIPE, .data.stream = (uv_stream_t*)&ctx->stderr_pipe },
  };
  uv_process_options_t options = {
    .file = ctx->argv[0],
    .args = ctx->argv,
    .stdio_count = 3,
    .stdio = stdio,
    .exit_cb = __aio_exec_exit_cb,
  };

  int r = uv_spawn(loop, &ctx->process, &options);
  if (r != 0) {
    ctx->spawn_failed = true;
    ctx->spawn_err_msg = strdup(uv_strerror(r));
    ctx->close_pending = 3;
    uv_close((uv_handle_t*)&ctx->process, __aio_exec_uv_close_cb);
    uv_close((uv_handle_t*)&ctx->stdout_pipe, __aio_exec_uv_close_cb);
    uv_close((uv_handle_t*)&ctx->stderr_pipe, __aio_exec_uv_close_cb);
    return;
  }

  ctx->close_pending = 3;
  uv_read_start((uv_stream_t*)&ctx->stdout_pipe, __aio_exec_alloc_cb, __aio_exec_read_cb);
  uv_read_start((uv_stream_t*)&ctx->stderr_pipe, __aio_exec_alloc_cb, __aio_exec_read_cb);
}

static valk_lval_t* valk_builtin_aio_exec(valk_lenv_t *e, valk_lval_t *a) {
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_GE(a, a, 2);
  LVAL_ASSERT_AIO_SYSTEM(a, valk_lval_list_nth(a, 0));
  u64 nargs = valk_lval_list_count(a);
  for (u64 i = 1; i < nargs; i++) {
    valk_lval_t *arg_i = valk_lval_list_nth(a, i);
    LVAL_ASSERT_TYPE(a, arg_i, LVAL_STR);
  }
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t *sys = valk_lval_list_nth(a, 0)->ref.ptr;
  int argc = (int)(nargs - 1);

  valk_aio_exec_ctx_t *ctx = calloc(1, sizeof(valk_aio_exec_ctx_t));
  ctx->argc = argc;
  ctx->argv = calloc((size_t)argc + 1, sizeof(char*));
  for (int i = 0; i < argc; i++) {
    ctx->argv[i] = strdup(valk_lval_list_nth(a, i + 1)->str);
  }
  ctx->argv[argc] = NULL;

  ctx->handle = valk_async_handle_new(sys, e);
  if (!ctx->handle) {
    __aio_exec_free_ctx(ctx);
    LVAL_RAISE(a, "aio/exec: handle alloc failed");
  }
  atomic_store_explicit(&ctx->handle->status, VALK_ASYNC_RUNNING, memory_order_release);

  valk_aio_enqueue_task(sys, __aio_exec_spawn_on_loop, ctx);
  return valk_lval_handle(ctx->handle);
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START - GC destructor: called non-deterministically during garbage collection
static void file_handle_free(void *ptr) {
  FILE *f = ptr;
  if (f) fclose(f);
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_file_open(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  const char *path = valk_lval_list_nth(a, 0)->str;
  const char *mode = valk_lval_list_nth(a, 1)->str;
  FILE *f = fopen(path, mode);
  if (f == nullptr) {
    LVAL_RAISE(a, "file/open: could not open '%s' with mode '%s'", path, mode);
  }
  return valk_lval_ref("file_handle", f, file_handle_free);
}

static valk_lval_t* valk_builtin_file_write_str(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  LVAL_ASSERT_COUNT_EQ(a, a, 2); // LCOV_EXCL_BR_LINE - arg validation
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  // LCOV_EXCL_BR_START - type validation: ref type + null check
  if (LVAL_TYPE(ref) != LVAL_REF || ref->ref.ptr == nullptr) {
    LVAL_RAISE(a, "file/write: first argument must be a file handle");
  }
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  FILE *f = ref->ref.ptr;
  const char *s = valk_lval_list_nth(a, 1)->str;
  u64 len = strlen(s);
  if (len > 0) {
    u64 written = fwrite(s, 1, len, f);
    if (written != len) // LCOV_EXCL_BR_LINE
      LVAL_RAISE(a, "file/write: partial write (%zu of %zu bytes)", written, len); // LCOV_EXCL_LINE
  }
  return valk_lval_num((long)len);
}

static valk_lval_t* valk_builtin_file_close(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(ref) != LVAL_REF || ref->ref.ptr == nullptr) {
    LVAL_RAISE(a, "file/close: argument must be a file handle");
  }
  // LCOV_EXCL_BR_STOP
  FILE *f = ref->ref.ptr;
  ref->ref.ptr = nullptr;
  ref->ref.free = nullptr;
  fclose(f);
  return valk_lval_num(0);
}

static valk_lval_t* valk_builtin_for_each_line(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);
  // LCOV_EXCL_BR_STOP

  valk_lval_t* fn = valk_lval_list_nth(a, 1);
  // LCOV_EXCL_BR_START - type validation
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    LVAL_RAISE(a, "for-each-line: second argument must be a function");
  }
  // LCOV_EXCL_BR_STOP
  VALK_GC_ROOT(fn);

  const char* filename = valk_lval_list_nth(a, 0)->str;
  FILE* f = fopen(filename, "r");
  if (f == nullptr) {
    LVAL_RAISE(a, "for-each-line: could not open file (%s)", filename);
  }

  char *buf = nullptr;
  size_t buf_cap = 0;
  ssize_t len;
  u64 lines_read = 0;

  while ((len = getline(&buf, &buf_cap, f)) != -1) {
    if (len > 0 && buf[len - 1] == '\n') buf[len - 1] = '\0';
    valk_lval_t *line_str = valk_lval_str(buf);
    valk_lval_t *call_args[] = {fn, line_str};
    valk_lval_t *call_expr = valk_lval_list(call_args, 2);
    valk_lval_t *result = valk_lval_eval(e, call_expr);
    if (LVAL_TYPE(result) == LVAL_ERR) { // LCOV_EXCL_BR_LINE - callback error propagation
      free(buf); // LCOV_EXCL_LINE
      fclose(f); // LCOV_EXCL_LINE
      return result; // LCOV_EXCL_LINE
    }
    lines_read++;
    VALK_GC_SAFE_POINT();
  }

  free(buf);
  fclose(f);
  return valk_lval_num((long)lines_read);
}

static valk_lval_t *valk_builtin_type_infer_file(valk_lenv_t *e,
                                                   valk_lval_t *a) {
  UNUSED(e);
  u64 argc = valk_lval_list_count(a);
  if (argc < 1)
    LVAL_RAISE(a, "type/infer-file: expected at least 1 argument (ast)");
  valk_lval_t *ast = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, ast, LVAL_CONS, LVAL_NIL);

  valk_ti_ctx_t *ctx = valk_ti_create(valk_type_env_global());
  valk_ti_import_new(ctx);
  
  valk_ti_infer_file(ctx, ast);

  valk_lval_t *errors = valk_lval_nil();
  for (u32 i = ctx->error_count; i > 0; i--) {
    valk_ti_error_t *err = &ctx->errors[i - 1];
    valk_lval_t *entry = valk_lval_nil();
    entry = valk_lval_cons(valk_lval_str(err->message), entry);
    entry = valk_lval_cons(valk_lval_sym(":message"), entry);
    entry = valk_lval_cons(valk_lval_num(err->col), entry);
    entry = valk_lval_cons(valk_lval_sym(":col"), entry);
    entry = valk_lval_cons(valk_lval_num(err->line), entry);
    entry = valk_lval_cons(valk_lval_sym(":line"), entry);
    errors = valk_lval_cons(entry, errors);
  }

  valk_lval_t *types = valk_lval_nil();
  char tbuf[512];
  for (valk_ti_scope_t *s = ctx->scope; s; s = s->parent) {
    for (u32 i = 0; i < s->count; i++) {
      const char *name = s->entries[i].name;
      valk_type_t *t = valk_type_find(s->entries[i].scheme.type);
      if (!t || t->kind == VALK_TY_VAR) continue;
      valk_type_to_str(t, tbuf, sizeof(tbuf));
      valk_lval_t *entry = valk_lval_nil();
      entry = valk_lval_cons(valk_lval_str(tbuf), entry);
      entry = valk_lval_cons(valk_lval_sym(":type"), entry);
      entry = valk_lval_cons(valk_lval_str(name), entry);
      entry = valk_lval_cons(valk_lval_sym(":var"), entry);
      types = valk_lval_cons(entry, types);
    }
  }

  valk_lval_t *result = valk_lval_nil();
  result = valk_lval_cons(types, result);
  result = valk_lval_cons(valk_lval_sym(":types"), result);
  result = valk_lval_cons(errors, result);
  result = valk_lval_cons(valk_lval_sym(":errors"), result);

  valk_ti_destroy(ctx);
  return result;
}

void valk_register_file_builtins(valk_lenv_t* env) {
  valk_lenv_put_builtin(env, "list-dir", valk_builtin_list_dir);
  valk_lenv_put_builtin(env, "file/size", valk_builtin_file_size);
  valk_lenv_put_builtin(env, "file/fingerprint", valk_builtin_file_fingerprint);
  valk_lenv_put_builtin(env, "sem/encode-deltas", valk_builtin_sem_encode_deltas);
  valk_lenv_put_builtin(env, "lsp/index-ast", valk_builtin_lsp_index_file);
  extern valk_lval_t *valk_builtin_ast_visit(valk_lenv_t *, valk_lval_t *);
  valk_lenv_put_builtin(env, "ast/visit", valk_builtin_ast_visit);
  valk_lenv_put_builtin(env, "offsets->line-cols", valk_builtin_offsets_to_lines);
  valk_lenv_put_builtin(env, "write-file", valk_builtin_write_file);
  valk_lenv_put_builtin(env, "file/exists?", valk_builtin_file_exists);
  valk_lenv_put_builtin(env, "file/delete", valk_builtin_file_delete);
  valk_lenv_put_builtin(env, "mkdir-p", valk_builtin_mkdir_p);
  valk_lenv_put_builtin(env, "rmdir", valk_builtin_rmdir);
  valk_lenv_put_builtin(env, "symlink", valk_builtin_symlink);
  valk_lenv_put_builtin(env, "env/get", valk_builtin_env_get);
  valk_lenv_put_builtin(env, "env/set", valk_builtin_env_set);
  valk_lenv_put_builtin(env, "realpath", valk_builtin_realpath);
  valk_lenv_put_builtin(env, "exec", valk_builtin_exec);
  valk_lenv_put_builtin(env, "aio/exec", valk_builtin_aio_exec);
  valk_lenv_put_builtin(env, "for-each-line", valk_builtin_for_each_line);
  valk_lenv_put_builtin(env, "file/open", valk_builtin_file_open);
  valk_lenv_put_builtin(env, "file/write", valk_builtin_file_write_str);
  valk_lenv_put_builtin(env, "file/close", valk_builtin_file_close);
  valk_lenv_put_builtin(env, "type/infer-file", valk_builtin_type_infer_file);
}
