#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "memory.h"
#include "testing.h"

// Per-message read timeout
#define MSG_TIMEOUT_MS 5000

// Per-test hard timeout via alarm()
#define TEST_TIMEOUT_SEC 10

// ---------------------------------------------------------------------------
// LSP framed message reader
// ---------------------------------------------------------------------------

typedef struct {
  int fd;
  char buf[65536];
  int len;
} lsp_reader_t;

static void lsp_reader_init(lsp_reader_t *r, int fd) {
  r->fd = fd;
  r->len = 0;
}

// Read one Content-Length framed message. Returns malloc'd body or NULL on timeout.
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

// ---------------------------------------------------------------------------
// Write a Content-Length framed message
// ---------------------------------------------------------------------------

static int lsp_write(int fd, const char *json) {
  int len = strlen(json);
  char header[128];
  int hlen = snprintf(header, sizeof(header), "Content-Length: %d\r\n\r\n", len);
  if (write(fd, header, hlen) != hlen) return -1;
  if (write(fd, json, len) != len) return -1;
  return 0;
}

// ---------------------------------------------------------------------------
// Message helpers
// ---------------------------------------------------------------------------

// Read next response matching a specific id (skips notifications)
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

// Wait for a notification containing a substring
static char *lsp_wait_notification(lsp_reader_t *r, const char *match, int timeout_ms) {
  long start = valk_get_millis();
  while (valk_get_millis() - start < timeout_ms) {
    int remaining = timeout_ms - (int)(valk_get_millis() - start);
    char *msg = lsp_reader_next(r, remaining);
    if (!msg) return NULL;
    if (strstr(msg, match)) return msg;
    free(msg);
  }
  return NULL;
}

// Drain all pending messages
static void lsp_drain(lsp_reader_t *r) {
  char *msg;
  while ((msg = lsp_reader_next(r, 100)) != NULL) free(msg);
}

// ---------------------------------------------------------------------------
// LSP process lifecycle
// ---------------------------------------------------------------------------

typedef struct {
  pid_t pid;
  int write_fd;
  int read_fd;
  lsp_reader_t reader;
} lsp_t;

static volatile sig_atomic_t test_timed_out = 0;
static pid_t alarm_child_pid = 0;

static void alarm_handler(int sig) {
  (void)sig;
  test_timed_out = 1;
  if (alarm_child_pid > 0) kill(alarm_child_pid, SIGKILL);
}

static void test_timeout_start(int seconds) {
  test_timed_out = 0;
  alarm_child_pid = 0;
  struct sigaction sa = {.sa_handler = alarm_handler, .sa_flags = 0};
  sigemptyset(&sa.sa_mask);
  sigaction(SIGALRM, &sa, NULL);
  alarm(seconds);
}

static void test_timeout_stop(void) {
  alarm(0);
  signal(SIGALRM, SIG_DFL);
}

// Fork LSP process. Closes inherited fds to prevent framework pipe leaks.
static lsp_t lsp_spawn(void) {
  int stdin_pipe[2], stdout_pipe[2];
  pipe(stdin_pipe);
  pipe(stdout_pipe);

  pid_t pid = fork();
  if (pid == 0) {
    // Close inherited fds (framework capture pipes) to prevent hangs
    for (int fd = 3; fd < 256; fd++) {
      if (fd != stdin_pipe[0] && fd != stdout_pipe[1])
        close(fd);
    }
    dup2(stdin_pipe[0], 0);
    dup2(stdout_pipe[1], 1);
    close(stdin_pipe[0]);
    close(stdout_pipe[1]);

    int devnull = open("/dev/null", O_WRONLY);
    if (devnull >= 0) { dup2(devnull, 2); close(devnull); }

    char valk_path[256];
    snprintf(valk_path, sizeof(valk_path), "%s/valk", VALK_BUILD_DIR);
    execlp(valk_path, valk_path, "scripts/lsp/main.valk", NULL);
    _exit(1);
  }

  close(stdin_pipe[0]);
  close(stdout_pipe[1]);

  lsp_t lsp = {.pid = pid, .write_fd = stdin_pipe[1], .read_fd = stdout_pipe[0]};
  lsp_reader_init(&lsp.reader, lsp.read_fd);
  return lsp;
}

// Initialize + send initialized. Returns init response (caller frees) or NULL.
static char *lsp_initialize(lsp_t *lsp) {
  lsp_write(lsp->write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  char *resp = lsp_read_response(&lsp->reader, 1, MSG_TIMEOUT_MS);
  if (!resp) return NULL;
  lsp_write(lsp->write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");
  return resp;
}

// Graceful shutdown + exit + waitpid
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

static void lsp_kill(lsp_t *lsp) {
  if (lsp->write_fd >= 0) close(lsp->write_fd);
  close(lsp->read_fd);
  kill(lsp->pid, SIGTERM);
  int status;
  waitpid(lsp->pid, &status, 0);
}

// Send didOpen, wait briefly for publishDiagnostics as a completion signal.
// May return NULL if diagnostics don't arrive — doc is still stored synchronously.
static char *lsp_did_open(lsp_t *lsp, const char *did_open_json) {
  lsp_write(lsp->write_fd, did_open_json);
  return lsp_wait_notification(&lsp->reader, "publishDiagnostics", MSG_TIMEOUT_MS);
}

// Send didChange, wait briefly for publishDiagnostics.
static char *lsp_did_change(lsp_t *lsp, const char *did_change_json) {
  lsp_write(lsp->write_fd, did_change_json);
  return lsp_wait_notification(&lsp->reader, "publishDiagnostics", MSG_TIMEOUT_MS);
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#define BEGIN_TEST() \
  VALK_TEST(); \
  signal(SIGPIPE, SIG_IGN); \
  test_timeout_start(TEST_TIMEOUT_SEC); \
  lsp_t lsp = lsp_spawn(); \
  alarm_child_pid = lsp.pid;

#define INIT_OR_BAIL() \
  char *_init = lsp_initialize(&lsp); \
  VALK_TEST_ASSERT(_init != NULL, "initialize"); \
  if (!_init) { lsp_kill(&lsp); test_timeout_stop(); return; } \
  free(_init);

#define END_TEST() \
  lsp_shutdown(&lsp); \
  test_timeout_stop(); \
  VALK_PASS();

static void test_initialize_shutdown(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);
  test_timeout_start(TEST_TIMEOUT_SEC);

  lsp_t lsp = lsp_spawn();
  alarm_child_pid = lsp.pid;

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  char *resp = lsp_read_response(&lsp.reader, 1, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get initialize response");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  VALK_TEST_ASSERT(strstr(resp, "capabilities") != NULL, "should have capabilities");
  VALK_TEST_ASSERT(strstr(resp, "hoverProvider") != NULL, "should have hoverProvider");
  VALK_TEST_ASSERT(strstr(resp, "valk-lsp") != NULL, "serverInfo should say valk-lsp");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");
  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&lsp.reader, 2, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get shutdown response");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"id\":2") != NULL, "shutdown response id=2");
  free(resp);

  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");
  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  VALK_TEST_ASSERT(WIFEXITED(status), "child should exit normally");
  close(lsp.read_fd);
  test_timeout_stop();
  VALK_PASS();
}

static void test_didopen_hover(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/test.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {add a b} {+ a b})\\n(add 1 2)\"}}}");
  free(diag);  // may be NULL if diagnostics didn't arrive, hover still works

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/hover\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/test.valk\"},"
    "\"position\":{\"line\":0,\"character\":6}}}");
  char *resp = lsp_read_response(&lsp.reader, 3, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get hover response");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "hover should have result");
  VALK_TEST_ASSERT(strstr(resp, "contents") != NULL, "hover should have contents");
  free(resp);
  END_TEST();
}

static void test_didopen_completion(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/test.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fu\"}}}");
  free(diag);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/completion\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/test.valk\"},"
    "\"position\":{\"line\":0,\"character\":3}}}");
  char *resp = lsp_read_response(&lsp.reader, 4, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get completion response");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "completion should have result");
  VALK_TEST_ASSERT(strstr(resp, "items") != NULL, "completion should have items");
  VALK_TEST_ASSERT(strstr(resp, "fun") != NULL, "should suggest 'fun' snippet");
  free(resp);
  END_TEST();
}

static void test_not_initialized_error(VALK_TEST_ARGS()) {
  BEGIN_TEST();

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/hover\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/test.valk\"},"
    "\"position\":{\"line\":0,\"character\":0}}}");
  char *resp = lsp_read_response(&lsp.reader, 5, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get error response");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"error\"") != NULL, "should have error field");
  VALK_TEST_ASSERT(strstr(resp, "-32002") != NULL, "error code -32002");
  free(resp);
  INIT_OR_BAIL();
  END_TEST();
}

static void test_unknown_method_error(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"bogus/method\","
    "\"params\":{}}");
  char *resp = lsp_read_response(&lsp.reader, 6, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get error for unknown method");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"error\"") != NULL, "should have error");
  VALK_TEST_ASSERT(strstr(resp, "-32601") != NULL, "error code -32601");
  free(resp);
  END_TEST();
}

static void test_semantic_tokens(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/tok.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {f x} {+ x 1})\"}}}");
  free(diag);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/semanticTokens/full\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/tok.valk\"}}}");
  char *resp = lsp_read_response(&lsp.reader, 7, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get semantic tokens response");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  VALK_TEST_ASSERT(strstr(resp, "data") != NULL, "should have data field");
  free(resp);
  END_TEST();
}

static void test_didchange_diagnostics(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/diag.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(+ 1 2)\"}}}");
  VALK_TEST_ASSERT(diag != NULL, "should get diagnostics after didOpen");
  if (!diag) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(diag, "diag.valk") != NULL, "should reference our file");
  free(diag);

  char *notif = lsp_did_change(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/diag.valk\","
    "\"version\":2},"
    "\"contentChanges\":[{\"text\":\"(+ 1\"}]}}");
  VALK_TEST_ASSERT(notif != NULL, "should get diagnostics after didChange");
  if (notif) {
    VALK_TEST_ASSERT(strstr(notif, "publishDiagnostics") != NULL,
      "publishDiagnostics after change");
    free(notif);
  }
  END_TEST();
}

static void test_signature_help(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/sig.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {add a b} {+ a b})\\n(add 1 2)\"}}}");
  free(diag);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/signatureHelp\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/sig.valk\"},"
    "\"position\":{\"line\":1,\"character\":5}}}");
  char *resp = lsp_read_response(&lsp.reader, 5, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get signature help response");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  free(resp);
  END_TEST();
}

static void test_semantic_tokens_range(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/tokr.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {f x} {+ x 1})\\n(def {y} 42)\"}}}");
  free(diag);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"textDocument/semanticTokens/range\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/tokr.valk\"},"
    "\"range\":{\"start\":{\"line\":0,\"character\":0},"
    "\"end\":{\"line\":1,\"character\":99}}}}");
  char *resp = lsp_read_response(&lsp.reader, 8, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get semantic tokens range response");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  VALK_TEST_ASSERT(strstr(resp, "data") != NULL, "should have data field");
  free(resp);
  END_TEST();
}

static void test_inlay_hints(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/hint.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {add a b} {+ a b})\\n(def {x} 42)\\n(add 1 2)\"}}}");
  free(diag);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/inlayHint\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/hint.valk\"},"
    "\"range\":{\"start\":{\"line\":0,\"character\":0},"
    "\"end\":{\"line\":2,\"character\":99}}}}");
  char *resp = lsp_read_response(&lsp.reader, 9, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get inlay hints response");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  free(resp);
  END_TEST();
}

static void test_incremental_didchange(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/inc.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(+ 1 2)\"}}}");
  free(diag);

  char *notif = lsp_did_change(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/inc.valk\","
    "\"version\":2},"
    "\"contentChanges\":[{\"range\":{"
    "\"start\":{\"line\":0,\"character\":3},"
    "\"end\":{\"line\":0,\"character\":4}},"
    "\"text\":\"10\"}]}}");
  free(notif);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"textDocument/hover\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/inc.valk\"},"
    "\"position\":{\"line\":0,\"character\":3}}}");
  char *resp = lsp_read_response(&lsp.reader, 10, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "hover after incremental edit");
  if (resp) {
    VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "hover result exists");
    free(resp);
  }

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"textDocument/semanticTokens/full\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/inc.valk\"}}}");
  resp = lsp_read_response(&lsp.reader, 11, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "semantic tokens after incremental edit");
  if (resp) {
    VALK_TEST_ASSERT(strstr(resp, "data") != NULL, "should have token data");
    free(resp);
  }
  END_TEST();
}

static void test_rapid_incremental_edits(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/rapid.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(+ 1 2)\"}}}");
  free(diag);

  const char *edits[] = {
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/rapid.valk\",\"version\":2},"
    "\"contentChanges\":[{\"range\":{\"start\":{\"line\":0,\"character\":7},"
    "\"end\":{\"line\":0,\"character\":7}},\"text\":\"\\n\"}]}}",

    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/rapid.valk\",\"version\":3},"
    "\"contentChanges\":[{\"range\":{\"start\":{\"line\":1,\"character\":0},"
    "\"end\":{\"line\":1,\"character\":0}},\"text\":\"(\"}]}}",

    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/rapid.valk\",\"version\":4},"
    "\"contentChanges\":[{\"range\":{\"start\":{\"line\":1,\"character\":1},"
    "\"end\":{\"line\":1,\"character\":1}},\"text\":\"+ 3 4\"}]}}",

    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/rapid.valk\",\"version\":5},"
    "\"contentChanges\":[{\"range\":{\"start\":{\"line\":1,\"character\":6},"
    "\"end\":{\"line\":1,\"character\":6}},\"text\":\")\"}]}}",
  };

  for (int i = 0; i < 4; i++) lsp_write(lsp.write_fd, edits[i]);

  // Wait for at least one diagnostics notification then drain
  char *last = lsp_wait_notification(&lsp.reader, "publishDiagnostics", MSG_TIMEOUT_MS);
  lsp_drain(&lsp.reader);
  free(last);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":20,\"method\":\"textDocument/semanticTokens/full\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/rapid.valk\"}}}");
  char *resp = lsp_read_response(&lsp.reader, 20, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "semantic tokens after rapid edits");
  if (resp) {
    VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "result present");
    VALK_TEST_ASSERT(strstr(resp, "data") != NULL, "data present");
    free(resp);
  }

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":21,\"method\":\"textDocument/completion\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/rapid.valk\"},"
    "\"position\":{\"line\":1,\"character\":1}}}");
  resp = lsp_read_response(&lsp.reader, 21, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "completion after rapid edits");
  if (resp) {
    VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "completion result");
    free(resp);
  }
  END_TEST();
}

static void test_startup_race(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);
  test_timeout_start(TEST_TIMEOUT_SEC * 3);

  for (int attempt = 0; attempt < 5; attempt++) {
    lsp_t lsp = lsp_spawn();
    alarm_child_pid = lsp.pid;

    char *init = lsp_initialize(&lsp);
    VALK_TEST_ASSERT(init != NULL, "initialize on immediate send");
    if (!init) { lsp_kill(&lsp); test_timeout_stop(); return; }
    VALK_TEST_ASSERT(strstr(init, "\"result\"") != NULL, "should have result");
    free(init);

    lsp_shutdown(&lsp);
  }
  test_timeout_stop();
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  // Set per-test framework timeout to match our alarm-based timeout
  if (!getenv("VALK_TEST_TIMEOUT_SECONDS"))
    setenv("VALK_TEST_TIMEOUT_SECONDS", "15", 0);
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  valk_testsuite_add_test(suite, "lsp_initialize_shutdown", test_initialize_shutdown);
  valk_testsuite_add_test(suite, "lsp_didopen_hover", test_didopen_hover);
  valk_testsuite_add_test(suite, "lsp_didopen_completion", test_didopen_completion);
  valk_testsuite_add_test(suite, "lsp_not_initialized_error", test_not_initialized_error);
  valk_testsuite_add_test(suite, "lsp_unknown_method_error", test_unknown_method_error);
  valk_testsuite_add_test(suite, "lsp_semantic_tokens", test_semantic_tokens);
  valk_testsuite_add_test(suite, "lsp_didchange_diagnostics", test_didchange_diagnostics);
  valk_testsuite_add_test(suite, "lsp_signature_help", test_signature_help);
  valk_testsuite_add_test(suite, "lsp_semantic_tokens_range", test_semantic_tokens_range);
  valk_testsuite_add_test(suite, "lsp_inlay_hints", test_inlay_hints);
  valk_testsuite_add_test(suite, "lsp_incremental_didchange", test_incremental_didchange);
  valk_testsuite_add_test(suite, "lsp_rapid_incremental_edits", test_rapid_incremental_edits);
  valk_testsuite_add_test(suite, "lsp_startup_race", test_startup_race);
  return valk_testsuite_run(suite);
}
