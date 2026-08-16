// Profile test: spawn the LSP binary, replay the neovim file-open sequence,
// print per-phase wall-clock latency (microseconds).
//
// The goal is to pinpoint where time is lost between process spawn and the
// first semanticTokens response — the moment the editor can paint colors.
//
// Which binary gets profiled is controlled by two env vars:
//   VALK_LSP_BIN  — path to binary (default: build/valk-lsp, the AOT build)
//   VALK_LSP_ARGS — if set to "main.valk", run valk + lsp/main.valk
//                   (default is no args, meaning the binary is self-contained)
// VALK_LSP_ROOT   — rootUri path sent in initialize (default: repo root).
//                   Set to "" to skip workspace indexing.
// VALK_LSP_OPEN   — path to file sent via didOpen (default: a small fixture).
//
// Phases reported:
//   spawn->init_req    wall time from fork/exec to sending initialize
//   init_req->init_resp time LSP takes to respond to initialize
//   init_resp->didopen  time spent sending initialized + didOpen
//   didopen->sem_req    idle gap before we ask for semanticTokens
//   sem_req->sem_resp   time LSP takes to respond to semanticTokens/full
//   TOTAL spawn->sem_resp  what the user perceives as "file loaded"
//
// The numbers print to stderr so you can pipe-filter them out.

#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include "memory.h"
#include "testing.h"

#define MSG_TIMEOUT_MS 15000
#define TEST_TIMEOUT_SEC 60

typedef struct {
  int fd;
  char buf[65536];
  int len;
} lsp_reader_t;

static void lsp_reader_init(lsp_reader_t *r, int fd) { r->fd = fd; r->len = 0; }

static char *lsp_reader_next(lsp_reader_t *r, int timeout_ms) {
  long start = valk_get_millis();
  while (1) {
    char *header_end = memmem(r->buf, r->len, "\r\n\r\n", 4);
    if (header_end) {
      char *cl = memmem(r->buf, header_end - r->buf, "Content-Length: ", 16);
      if (!cl) return NULL;
      int content_length = atoi(cl + 16);
      if (content_length <= 0) return NULL;
      int header_size = (int)((header_end + 4) - r->buf);
      int total_needed = header_size + content_length;
      if (r->len >= total_needed) {
        char *body = malloc(content_length + 1);
        memcpy(body, r->buf + header_size, content_length);
        body[content_length] = '\0';
        r->len -= total_needed;
        memmove(r->buf, r->buf + total_needed, r->len);
        return body;
      }
    }
    long elapsed = valk_get_millis() - start;
    if (elapsed >= timeout_ms) return NULL;
    struct pollfd pfd = {.fd = r->fd, .events = POLLIN};
    int ret = poll(&pfd, 1, timeout_ms - (int)elapsed);
    if (ret <= 0) return NULL;
    int n = read(r->fd, r->buf + r->len, (int)sizeof(r->buf) - r->len);
    if (n <= 0) return NULL;
    r->len += n;
  }
}

static int lsp_write(int fd, const char *json) {
  int len = strlen(json);
  char header[128];
  int hlen = snprintf(header, sizeof(header), "Content-Length: %d\r\n\r\n", len);
  if (write(fd, header, hlen) != hlen) return -1;
  if (write(fd, json, len) != len) return -1;
  return 0;
}

// Read messages until we find one with "id":<id> in the body, or timeout.
static char *lsp_read_response(lsp_reader_t *r, int id, int timeout_ms) {
  char id_str[32];
  snprintf(id_str, sizeof(id_str), "\"id\":%d", id);
  long start = valk_get_millis();
  while (valk_get_millis() - start < timeout_ms) {
    int remaining = timeout_ms - (int)(valk_get_millis() - start);
    char *msg = lsp_reader_next(r, remaining);
    if (!msg) return NULL;
    if (strstr(msg, id_str)) return msg;
    free(msg);
  }
  return NULL;
}

typedef struct {
  pid_t pid;
  int write_fd;
  int read_fd;
  lsp_reader_t reader;
} lsp_t;

static volatile sig_atomic_t profile_timed_out = 0;
static pid_t profile_child_pid = 0;

static void profile_alarm_handler(int sig) {
  (void)sig;
  profile_timed_out = 1;
  if (profile_child_pid > 0) kill(profile_child_pid, SIGKILL);
}

static void profile_timeout_start(int seconds) {
  profile_timed_out = 0;
  profile_child_pid = 0;
  struct sigaction sa = {.sa_handler = profile_alarm_handler, .sa_flags = 0};
  sigemptyset(&sa.sa_mask);
  sigaction(SIGALRM, &sa, NULL);
  alarm(seconds);
}

static void profile_timeout_stop(void) {
  alarm(0);
  signal(SIGALRM, SIG_DFL);
}

// Spawn the LSP. `bin_path` is the executable. If `run_main_valk` is non-zero,
// exec as `<bin_path> lsp/main.valk` (for when bin is the interpreter).
// Otherwise exec as `<bin_path>` with no args (AOT binary case).
// Child stderr goes to stderr_path if non-NULL, else /dev/null.
static lsp_t lsp_spawn(const char *bin_path, int run_main_valk,
                       const char *stderr_path) {
  int stdin_pipe[2], stdout_pipe[2];
  pipe(stdin_pipe);
  pipe(stdout_pipe);
  pid_t pid = fork();
  if (pid == 0) {
    for (int fd = 3; fd < 256; fd++) {
      if (fd != stdin_pipe[0] && fd != stdout_pipe[1]) close(fd);
    }
    dup2(stdin_pipe[0], 0);
    dup2(stdout_pipe[1], 1);
    close(stdin_pipe[0]);
    close(stdout_pipe[1]);
    int errfd = stderr_path ? open(stderr_path, O_WRONLY | O_CREAT | O_TRUNC, 0644)
                            : open("/dev/null", O_WRONLY);
    if (errfd >= 0) { dup2(errfd, 2); close(errfd); }
    if (run_main_valk)
      execlp(bin_path, bin_path, "lsp/main.valk", NULL);
    else
      execlp(bin_path, bin_path, NULL);
    _exit(1);
  }
  close(stdin_pipe[0]);
  close(stdout_pipe[1]);
  lsp_t lsp = {.pid = pid, .write_fd = stdin_pipe[1], .read_fd = stdout_pipe[0]};
  lsp_reader_init(&lsp.reader, lsp.read_fd);
  return lsp;
}

static void lsp_kill(lsp_t *lsp) {
  if (lsp->write_fd >= 0) close(lsp->write_fd);
  close(lsp->read_fd);
  kill(lsp->pid, SIGTERM);
  int status;
  waitpid(lsp->pid, &status, 0);
}

static void lsp_shutdown(lsp_t *lsp) {
  lsp_write(lsp->write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":999,\"method\":\"shutdown\",\"params\":{}}");
  char *resp = lsp_read_response(&lsp->reader, 999, MSG_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp->write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");
  close(lsp->write_fd);
  lsp->write_fd = -1;
  int status;
  waitpid(lsp->pid, &status, 0);
  close(lsp->read_fd);
}

// Slurp a file to a malloc'd buffer. On failure returns NULL and leaves *out_size
// at 0. Caller frees.
static char *slurp(const char *path, long *out_size) {
  FILE *f = fopen(path, "rb");
  if (!f) return NULL;
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  rewind(f);
  char *buf = malloc(sz + 1);
  if (!buf) { fclose(f); return NULL; }
  if (fread(buf, 1, sz, f) != (size_t)sz) { free(buf); fclose(f); return NULL; }
  buf[sz] = '\0';
  fclose(f);
  if (out_size) *out_size = sz;
  return buf;
}

// Escape a string for JSON (just backslash, quote, newline, carriage return, tab).
// Output is malloc'd.
static char *json_escape(const char *s, long len) {
  size_t cap = len * 2 + 16;
  char *out = malloc(cap);
  size_t j = 0;
  for (long i = 0; i < len; i++) {
    if (j + 8 >= cap) { cap *= 2; out = realloc(out, cap); }
    unsigned char c = (unsigned char)s[i];
    switch (c) {
      case '"':  out[j++] = '\\'; out[j++] = '"'; break;
      case '\\': out[j++] = '\\'; out[j++] = '\\'; break;
      case '\n': out[j++] = '\\'; out[j++] = 'n'; break;
      case '\r': out[j++] = '\\'; out[j++] = 'r'; break;
      case '\t': out[j++] = '\\'; out[j++] = 't'; break;
      default:
        if (c < 0x20) { j += snprintf(out + j, cap - j, "\\u%04x", c); }
        else out[j++] = (char)c;
    }
  }
  out[j] = '\0';
  return out;
}

static void print_phase(const char *label, long t0, long t1) {
  long us = t1 - t0;
  fprintf(stderr, "  %-28s  %8ld us  (%ld ms)\n", label, us, us / 1000);
}

// Run one end-to-end profile. Writes phase breakdown to stderr.
// root_path: absolute path used as rootUri in initialize. NULL = no rootUri.
// open_uri:  URI string sent in didOpen.
// open_text: text body of the file being opened.
static void run_profile(const char *label, const char *bin_path,
                        int run_main_valk, const char *root_path,
                        const char *open_uri, const char *open_text) {
  fprintf(stderr, "\n=== %s ===\n", label);
  fprintf(stderr, "  bin:        %s%s\n", bin_path,
          run_main_valk ? " lsp/main.valk" : "");
  fprintf(stderr, "  root:       %s\n", root_path ? root_path : "(none)");
  fprintf(stderr, "  open:       %s\n", open_uri);

  long t_spawn = valk_get_micros();
  lsp_t lsp = lsp_spawn(bin_path, run_main_valk, NULL);
  profile_child_pid = lsp.pid;

  // 1) initialize
  char init_msg[2048];
  if (root_path) {
    snprintf(init_msg, sizeof(init_msg),
      "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
      "\"params\":{\"rootUri\":\"file://%s\",\"processId\":null,\"capabilities\":{"
      "\"general\":{\"positionEncodings\":[\"utf-8\"]},"
      "\"window\":{\"workDoneProgress\":true}}}}", root_path);
  } else {
    snprintf(init_msg, sizeof(init_msg),
      "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
      "\"params\":{\"processId\":null,\"capabilities\":{\"general\":{\"positionEncodings\":[\"utf-8\"]}}}}");
  }
  long t_init_send = valk_get_micros();
  lsp_write(lsp.write_fd, init_msg);
  char *init_resp = lsp_read_response(&lsp.reader, 1, MSG_TIMEOUT_MS);
  long t_init_resp = valk_get_micros();
  if (!init_resp) {
    fprintf(stderr, "  FAILED: no initialize response\n");
    lsp_kill(&lsp);
    return;
  }
  free(init_resp);

  // 2) initialized + didOpen
  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  // Build didOpen — text is JSON-escaped
  char *esc = json_escape(open_text, strlen(open_text));
  size_t didopen_cap = strlen(esc) + strlen(open_uri) + 256;
  char *didopen_msg = malloc(didopen_cap);
  snprintf(didopen_msg, didopen_cap,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"%s\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"%s\"}}}", open_uri, esc);
  free(esc);
  long t_didopen_send = valk_get_micros();
  lsp_write(lsp.write_fd, didopen_msg);
  free(didopen_msg);

  // 3) Request semanticTokens/full immediately (same burst neovim would send)
  char sem_msg[1024];
  snprintf(sem_msg, sizeof(sem_msg),
    "{\"jsonrpc\":\"2.0\",\"id\":100,\"method\":\"textDocument/semanticTokens/full\","
    "\"params\":{\"textDocument\":{\"uri\":\"%s\"}}}", open_uri);
  long t_sem_send = valk_get_micros();
  lsp_write(lsp.write_fd, sem_msg);

  // 4) Read until we see the semanticTokens response (id=100).
  char *sem_resp = lsp_read_response(&lsp.reader, 100, MSG_TIMEOUT_MS);
  long t_sem_resp = valk_get_micros();
  if (!sem_resp) {
    fprintf(stderr, "  FAILED: no semanticTokens response within %d ms\n",
            MSG_TIMEOUT_MS);
    lsp_kill(&lsp);
    return;
  }
  int data_count = 0;
  char *p = strstr(sem_resp, "\"data\":[");
  if (p) {
    p += 8;
    while (*p && *p != ']') { if (*p == ',') data_count++; p++; }
    if (p != strstr(sem_resp, "\"data\":[") + 8) data_count++;
  }
  free(sem_resp);

  print_phase("spawn  -> init_req",   t_spawn,        t_init_send);
  print_phase("init_req -> init_resp", t_init_send,    t_init_resp);
  print_phase("init_resp -> didopen",  t_init_resp,    t_didopen_send);
  print_phase("didopen -> sem_req",    t_didopen_send, t_sem_send);
  print_phase("sem_req -> sem_resp",   t_sem_send,     t_sem_resp);
  print_phase("TOTAL spawn -> sem_resp", t_spawn,      t_sem_resp);
  fprintf(stderr, "  tokens returned: ~%d values (flat array)\n", data_count);

  lsp_shutdown(&lsp);
}

static void test_profile(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);
  profile_timeout_start(TEST_TIMEOUT_SEC);

  const char *bin = getenv("VALK_LSP_BIN");
  if (!bin || !*bin) bin = "build/valk-lsp";

  const char *args = getenv("VALK_LSP_ARGS");
  int run_main_valk = (args && strcmp(args, "main.valk") == 0);

  const char *override_root = getenv("VALK_LSP_ROOT");
  const char *open_path_env = getenv("VALK_LSP_OPEN");

  // Default: use repo CWD as root and a representative workspace file
  char cwd_buf[1024];
  if (!getcwd(cwd_buf, sizeof(cwd_buf))) {
    VALK_TEST_ASSERT(0, "getcwd failed");
    profile_timeout_stop();
    return;
  }

  const char *root_for_indexed = (override_root && *override_root) ? override_root : cwd_buf;
  const char *open_path = (open_path_env && *open_path_env)
                              ? open_path_env
                              : "lsp/workspace.valk";

  // Absolutize open_path relative to cwd unless already absolute
  char open_abs[1200];
  if (open_path[0] == '/') {
    snprintf(open_abs, sizeof(open_abs), "%s", open_path);
  } else {
    snprintf(open_abs, sizeof(open_abs), "%s/%s", cwd_buf, open_path);
  }

  long sz = 0;
  char *body = slurp(open_abs, &sz);
  if (!body) {
    fprintf(stderr, "cannot read %s; skipping profile\n", open_abs);
    VALK_TEST_ASSERT(0, "fixture file missing");
    profile_timeout_stop();
    return;
  }
  fprintf(stderr, "fixture %s (%ld bytes)\n", open_abs, sz);

  char open_uri[1300];
  snprintf(open_uri, sizeof(open_uri), "file://%s", open_abs);

  // Run 1: no rootUri (skips workspace scan) — baseline
  run_profile("NO rootUri (skip indexing)", bin, run_main_valk,
              NULL, open_uri, body);

  // Run 2: with rootUri (triggers workspace scan)
  run_profile("WITH rootUri (indexes workspace)", bin, run_main_valk,
              root_for_indexed, open_uri, body);

  // Run 3: small synthetic file (rules out parse-time of the opened file)
  const char *small = "(fun {add a b} {+ a b})\n(add 1 2)\n";
  run_profile("small file + rootUri", bin, run_main_valk,
              root_for_indexed, "file:///tmp/prof-small.valk", small);

  free(body);
  profile_timeout_stop();
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  setenv("VALK_TEST_TIMEOUT_SECONDS", "90", 1);
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  valk_testsuite_add_test(suite, "lsp_profile", test_profile);
  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  return result;
}
