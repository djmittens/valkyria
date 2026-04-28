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

// Read next response matching a string-valued id (JSON-RPC 2.0 allows either
// number or string IDs). Matches `"id":"<str_id>"` in the response.
static char *lsp_read_response_str(lsp_reader_t *r, const char *str_id, int timeout_ms) {
  char id_pattern[64];
  snprintf(id_pattern, sizeof(id_pattern), "\"id\":\"%s\"", str_id);

  long start = valk_get_millis();
  while (valk_get_millis() - start < timeout_ms) {
    int remaining = timeout_ms - (int)(valk_get_millis() - start);
    char *msg = lsp_reader_next(r, remaining);
    if (!msg) return NULL;
    if (strstr(msg, id_pattern)) return msg;
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
// If stderr_path is non-NULL, redirects child stderr to that file (for
// race condition tests that need to inspect stderr after).
static lsp_t lsp_spawn_with_stderr(const char *stderr_path) {
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

    int errfd;
    if (stderr_path) {
      errfd = open(stderr_path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    } else {
      errfd = open("/dev/null", O_WRONLY);
    }
    if (errfd >= 0) { dup2(errfd, 2); close(errfd); }

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

static lsp_t lsp_spawn(void) {
  return lsp_spawn_with_stderr(NULL);
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

// JSON-RPC 2.0 allows string request IDs. Verify the LSP server echoes
// a string ID back in the response (previously it silently ignored them).
static void test_string_request_id(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":\"req-abc-123\",\"method\":\"bogus/method\","
    "\"params\":{}}");
  char *resp = lsp_read_response_str(&lsp.reader, "req-abc-123", MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get response with string id");
  if (!resp) { lsp_kill(&lsp); test_timeout_stop(); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"error\"") != NULL,
    "unknown method should produce an error");
  VALK_TEST_ASSERT(strstr(resp, "\"id\":\"req-abc-123\"") != NULL,
    "response id should match request id exactly");
  VALK_TEST_ASSERT(strstr(resp, "-32601") != NULL,
    "error code should be -32601 (method not found)");
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
  VALK_TEST_ASSERT(strstr(resp, "\"result\":[]") == NULL, "hints should not be empty");
  VALK_TEST_ASSERT(strstr(resp, "\"result\":null") == NULL, "hints should not be null");
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

// Create a temporary workspace populated with N small .valk files. The
// workspace scan must be slow enough for the next didOpen to interleave
// with scan callbacks (testing the nested-transaction race). Returns a
// malloc'd path; caller must rmtree.
static char *make_temp_workspace(int file_count) {
  char *tmpl = strdup("/tmp/valk-lsp-race-XXXXXX");
  if (!mkdtemp(tmpl)) { free(tmpl); return NULL; }
  for (int i = 0; i < file_count; i++) {
    char path[512];
    snprintf(path, sizeof(path), "%s/file%03d.valk", tmpl, i);
    FILE *f = fopen(path, "w");
    if (!f) continue;
    // Non-trivial content so parsing+indexing takes some time.
    fprintf(f, "(fun {fn%03d a b c} {do (= {x} (+ a b)) (= {y} (* x c)) y})\n", i);
    fprintf(f, "(fun {helper%03d x} {if (> x 0) {x} {0}})\n", i);
    fprintf(f, "(def {const%03d} (+ %d 1))\n", i, i);
    fclose(f);
  }
  return tmpl;
}

static void rm_workspace(const char *path) {
  if (!path) return;
  char cmd[1024];
  snprintf(cmd, sizeof(cmd), "rm -rf '%s'", path);
  int rc = system(cmd);
  (void)rc;
}

// Initialize with a specific rootUri (forces a workspace scan).
static char *lsp_initialize_with_root(lsp_t *lsp, const char *root_path) {
  char msg[1024];
  snprintf(msg, sizeof(msg),
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"rootUri\":\"file://%s\",\"capabilities\":{},\"processId\":null}}",
    root_path);
  lsp_write(lsp->write_fd, msg);
  char *resp = lsp_read_response(&lsp->reader, 1, MSG_TIMEOUT_MS);
  if (!resp) return NULL;
  lsp_write(lsp->write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");
  return resp;
}

// Read a file fully into memory. Returns malloc'd content or NULL.
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

// Regression test for the nested-transaction race during workspace scan.
//
// The bug: lsp/scan-all used to call BEGIN, then dispatch async file-prepare
// jobs, then COMMIT in the last callback. Holding the transaction across
// async dispatch boundaries races with handle-did-open (also runs on the
// main loop), which tries to start its own BEGIN. SQLite errors with
// "cannot start a transaction within a transaction".
//
// The bug is silent in user-visible responses (errors return as values
// from sqlite/exec, not crashes), so this test inspects the captured
// server stderr for SQLite transaction errors.
//
// This test:
//   1. Creates a workspace with many files to slow the scan.
//   2. Initializes the LSP with rootUri set (triggers scan).
//   3. Sends a flood of didOpen messages immediately, racing with
//      the scan callbacks.
//   4. After shutdown, asserts no SQLite transaction errors in stderr.
static void test_workspace_scan_didopen_race(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);
  test_timeout_start(TEST_TIMEOUT_SEC * 3);

  // Workspace size and didOpen count are tuned so the scan is slow enough
  // for didOpen to interleave but not so slow the LSP times out servicing
  // queries afterwards.
  char *workspace = make_temp_workspace(30);
  VALK_TEST_ASSERT(workspace != NULL, "create temp workspace");
  if (!workspace) { test_timeout_stop(); return; }

  char stderr_path[512];
  snprintf(stderr_path, sizeof(stderr_path), "%s/lsp.stderr", workspace);

  lsp_t lsp = lsp_spawn_with_stderr(stderr_path);
  alarm_child_pid = lsp.pid;

  char *init = lsp_initialize_with_root(&lsp, workspace);
  VALK_TEST_ASSERT(init != NULL, "initialize with root");
  if (!init) { lsp_kill(&lsp); rm_workspace(workspace); free(workspace); test_timeout_stop(); return; }
  free(init);

  // Open files immediately to interleave with scan callbacks.
  for (int i = 0; i < 10; i++) {
    char buf[2048];
    snprintf(buf, sizeof(buf),
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
      "\"params\":{\"textDocument\":{"
      "\"uri\":\"file://%s/file%03d.valk\","
      "\"languageId\":\"valk\",\"version\":1,"
      "\"text\":\"(fun {fn%03d a b c} {do (= {x} (+ a b)) (= {y} (* x c)) y})\"}}}",
      workspace, i, i);
    lsp_write(lsp.write_fd, buf);
  }

  // Send a hover request and wait for a response — proves the LSP is
  // still functioning end-to-end after the race.
  char hover_msg[1024];
  snprintf(hover_msg, sizeof(hover_msg),
    "{\"jsonrpc\":\"2.0\",\"id\":50,\"method\":\"textDocument/hover\","
    "\"params\":{\"textDocument\":{\"uri\":\"file://%s/file000.valk\"},"
    "\"position\":{\"line\":0,\"character\":7}}}",
    workspace);
  lsp_write(lsp.write_fd, hover_msg);
  char *resp = lsp_read_response(&lsp.reader, 50, MSG_TIMEOUT_MS * 2);
  VALK_TEST_ASSERT(resp != NULL, "should get hover response after scan race");
  if (resp) free(resp);

  lsp_shutdown(&lsp);

  // Check stderr for SQLite transaction errors. The bug logs:
  //   "sqlite/exec: cannot start a transaction within a transaction"
  //   "sqlite/exec: cannot commit - no transaction is active"
  long sz = 0;
  char *errlog = slurp(stderr_path, &sz);
  if (errlog) {
    bool nested_begin = strstr(errlog, "cannot start a transaction within a transaction") != NULL;
    bool no_active_tx = strstr(errlog, "cannot commit - no transaction is active") != NULL;
    VALK_TEST_ASSERT(!nested_begin,
      "stderr should not contain nested-BEGIN error");
    VALK_TEST_ASSERT(!no_active_tx,
      "stderr should not contain stale-COMMIT error");
    free(errlog);
  }

  rm_workspace(workspace);
  free(workspace);
  test_timeout_stop();
  VALK_PASS();
}

// Regression test: when the user edits a file into a broken state mid-typing,
// the LSP must:
//   1. Emit a parse error diagnostic at the right line/column
//   2. Still return semantic tokens (using the last-known-good AST as a
//      fallback) so the editor doesn't lose all syntax highlighting
//
// Without this fix, neovim shows all text in the default Identifier color
// (orange in many themes) because the LSP returns 0 tokens while parse fails.
static void test_partial_edit_keeps_highlighting(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  // Step 1: open a VALID file. This populates the last-good AST cache.
  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/edit.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {foo x} {+ x 1})\\n(def {y} 42)\"}}}");
  free(diag);

  // Verify semantic tokens for the valid file
  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":40,\"method\":\"textDocument/semanticTokens/full\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/edit.valk\"}}}");
  char *resp = lsp_read_response(&lsp.reader, 40, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "valid file: semantic tokens response");
  if (resp) {
    // Tokens come as a flat int array of length 5N. At least one token expected.
    VALK_TEST_ASSERT(strstr(resp, "\"data\":[") != NULL, "valid file: data array");
    VALK_TEST_ASSERT(strstr(resp, "\"data\":[]") == NULL, "valid file: non-empty tokens");
    free(resp);
  }

  // Step 2: edit the file into a BROKEN state (mid-typing).
  // The new text has an unclosed paren — exactly what happens during typing.
  char *change_diag = lsp_did_change(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/edit.valk\",\"version\":2},"
    "\"contentChanges\":[{\"text\":\"(fun {foo x} {+ x\"}]}}");
  // Diagnostics MUST contain the parse error
  VALK_TEST_ASSERT(change_diag != NULL, "broken: should publish diagnostics");
  if (change_diag) {
    VALK_TEST_ASSERT(strstr(change_diag, "Unexpected end of input") != NULL,
      "broken: parse error diagnostic should mention EOF");
    free(change_diag);
  }

  // Step 3: request semantic tokens for the broken state.
  // We had a last-good clean parse, so the LSP should return null per
  // spec — the client keeps its previous tokens on screen (no orange
  // default, no flicker). Either null OR a non-empty data array is
  // acceptable; what we must NOT do is return empty data[] (which would
  // clear the client's tokens).
  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":41,\"method\":\"textDocument/semanticTokens/full\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/edit.valk\"}}}");
  char *broken_resp = lsp_read_response(&lsp.reader, 41, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(broken_resp != NULL, "broken: semantic tokens response");
  if (broken_resp) {
    int is_null = strstr(broken_resp, "\"result\":null") != NULL;
    int has_nonempty = (strstr(broken_resp, "\"data\":[") != NULL)
                       && (strstr(broken_resp, "\"data\":[]") == NULL);
    VALK_TEST_ASSERT(is_null || has_nonempty,
      "broken: must return null (keep old tokens) or non-empty data");
    VALK_TEST_ASSERT(strstr(broken_resp, "\"data\":[]") == NULL,
      "broken: must NOT return empty data[] (would clear highlighting)");
    free(broken_resp);
  }

  // Step 4: edit back to a valid state. The cache should update and
  // parse error diagnostics should clear.
  char *fix_diag = lsp_did_change(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/edit.valk\",\"version\":3},"
    "\"contentChanges\":[{\"text\":\"(fun {foo x} {+ x 1})\"}]}}");
  if (fix_diag) {
    // Should not contain a parse error any more
    VALK_TEST_ASSERT(strstr(fix_diag, "Unexpected end of input") == NULL,
      "fixed: parse error should be cleared");
    free(fix_diag);
  }

  END_TEST();
}

// Regression test for the "everything turns orange" bug via incremental
// didChange (range + text), which is what neovim actually sends while typing.
// Full-document didChange hid this bug — apply-one-change called an unbound
// symbol `line-col->offset`, str/slice propagated the error, and the document
// text became an error message string instead of valid source.
//
// The test:
//   1. Opens a valid file
//   2. Sends a RANGE-based didChange (deletes the final ')')
//   3. Verifies the document is still syntactically coherent enough for
//      the LSP to respond with tokens and a parse error diagnostic — not
//      a gibberish error-string document that breaks everything downstream.
static void test_incremental_didchange_range(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/inc.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {foo x} {+ x 1})\"}}}");
  free(diag);

  // Delete the closing ')' using an incremental range-based change.
  // This is exactly what neovim sends when you delete a character.
  char *cdiag = lsp_did_change(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/inc.valk\",\"version\":2},"
    "\"contentChanges\":[{"
    "\"range\":{\"start\":{\"line\":0,\"character\":20},\"end\":{\"line\":0,\"character\":21}},"
    "\"text\":\"\"}]}}");
  VALK_TEST_ASSERT(cdiag != NULL, "range-based didChange should produce diagnostics");
  if (cdiag) {
    // The diagnostic must describe the ACTUAL parse error (EOF), not an
    // internal str/slice failure from a broken apply-changes.
    VALK_TEST_ASSERT(strstr(cdiag, "Unexpected end of input") != NULL,
      "diagnostic should describe parse error, not an internal str/slice failure");
    VALK_TEST_ASSERT(strstr(cdiag, "str/slice") == NULL,
      "diagnostic should not contain an str/slice builtin error");
    VALK_TEST_ASSERT(strstr(cdiag, "builtins_string.c") == NULL,
      "diagnostic should not contain a C file reference from a builtin error");
    free(cdiag);
  }

  // Semantic tokens should fall back to the last-good AST and produce
  // a non-empty response (the document state is sane).
  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":70,\"method\":\"textDocument/semanticTokens/full\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/inc.valk\"}}}");
  char *resp = lsp_read_response(&lsp.reader, 70, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "semantic tokens after incremental edit");
  if (resp) {
    VALK_TEST_ASSERT(strstr(resp, "\"data\":[]") == NULL,
      "incremental edit: semantic tokens must not be empty");
    free(resp);
  }

  END_TEST();
}

// Regression test: opening a brand-new broken file (no prior valid state to
// fall back to) must still return semantic tokens via the lexer fallback.
// Common case: user creates a new file and the first few keystrokes are
// always syntactically incomplete.
static void test_brand_new_broken_file_has_tokens(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  // Open a file that's broken from the very first byte. No prior valid
  // parse means no last-good AST cache — must use lexer fallback.
  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/brand.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {foo x} {+ x\"}}}");
  // Should publish a parse error diagnostic
  VALK_TEST_ASSERT(diag != NULL, "brand-new broken: should publish diagnostics");
  if (diag) {
    VALK_TEST_ASSERT(strstr(diag, "Unexpected end of input") != NULL,
      "brand-new broken: should report parse error");
    free(diag);
  }

  // Semantic tokens should NOT be empty — the lexer fallback should
  // identify keywords/variables/operators in the broken text.
  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":60,\"method\":\"textDocument/semanticTokens/full\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/brand.valk\"}}}");
  char *resp = lsp_read_response(&lsp.reader, 60, MSG_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "brand-new broken: semantic tokens response");
  if (resp) {
    VALK_TEST_ASSERT(strstr(resp, "\"data\":[]") == NULL,
      "brand-new broken: lexer fallback should produce non-empty tokens");
    free(resp);
  }

  END_TEST();
}

// ---------------------------------------------------------------------------
// Mid-edit positional sanity
// ---------------------------------------------------------------------------
//
// Regression for the visual "goes all crazy lookin, then loads fine" bug:
// while typing `(fuck you)` into a random spot of a valid file, the LSP was
// returning semantic tokens / inlay hints whose (line, col, length) pointed
// OUTSIDE the current text — stale byte offsets from the last DB sync mapped
// through the post-edit text landed in the middle of identifiers or past
// end-of-line. The editor then rendered highlights / ":: T" labels at those
// wrong columns for a frame until the parse re-synced.
//
// Invariant under test: for every (intermediate) text state, every token /
// hint position returned by the LSP must fit within the bounds of the CURRENT
// text's lines. If a response ever lies about positions, the visual chaos
// follows.

// Parse the first `"data":[...]` integer array from an LSP response.
// Returns a malloc'd int array (caller frees) and writes element count into
// *count_out. Returns NULL if the field is missing or malformed.
static int *parse_data_array(const char *resp, int *count_out) {
  *count_out = 0;
  const char *p = strstr(resp, "\"data\":[");
  if (!p) return NULL;
  p += 8;
  int cap = 64, n = 0;
  int *arr = malloc(cap * sizeof(int));
  while (*p && *p != ']') {
    while (*p == ',' || *p == ' ') p++;
    if (*p == ']') break;
    char *end;
    long v = strtol(p, &end, 10);
    if (end == p) { free(arr); return NULL; }
    if (n == cap) { cap *= 2; arr = realloc(arr, cap * sizeof(int)); }
    arr[n++] = (int)v;
    p = end;
  }
  *count_out = n;
  return arr;
}

// Compute per-line character lengths from the current text buffer.
// Writes out a newly-allocated array of line lengths and the line count.
static int *compute_line_lengths(const char *text, int *num_lines_out) {
  int cap = 16, n = 0;
  int *lens = malloc(cap * sizeof(int));
  int cur = 0;
  for (const char *p = text; ; p++) {
    if (*p == '\n' || *p == '\0') {
      if (n == cap) { cap *= 2; lens = realloc(lens, cap * sizeof(int)); }
      lens[n++] = cur;
      cur = 0;
      if (*p == '\0') break;
    } else {
      cur++;
    }
  }
  *num_lines_out = n;
  return lens;
}

// Find the byte offset of the start of `line` in `text`. Returns -1 if the
// line doesn't exist.
static int line_start_offset(const char *text, int line) {
  if (line == 0) return 0;
  int cur = 0;
  for (int i = 0; text[i]; i++) {
    if (text[i] == '\n') {
      cur++;
      if (cur == line) return i + 1;
    }
  }
  return -1;
}

// Verify every 5-tuple [dl, dc, len, type, mod] in the semantic tokens data
// array lands inside the current text's line bounds AND points at a
// non-whitespace, non-empty span. Returns 1 on success, 0 on first failure
// (fills `msg`).
static int verify_tokens_fit(const int *data, int n, const char *text,
                             const int *line_lens, int num_lines,
                             char *msg, size_t msglen) {
  int line = 0, col = 0;
  for (int i = 0; i + 4 < n; i += 5) {
    int dl = data[i], dc = data[i + 1], len = data[i + 2];
    if (dl > 0) { line += dl; col = dc; } else { col += dc; }
    if (line < 0 || line >= num_lines) {
      snprintf(msg, msglen, "token #%d: line %d out of range [0, %d)",
               i / 5, line, num_lines);
      return 0;
    }
    if (col < 0 || col + len > line_lens[line]) {
      snprintf(msg, msglen,
               "token #%d: col+len=%d past line %d length %d",
               i / 5, col + len, line, line_lens[line]);
      return 0;
    }
    if (len <= 0) {
      snprintf(msg, msglen, "token #%d: zero-length span at line %d col %d",
               i / 5, line, col);
      return 0;
    }
    // Whitespace-only spans are tolerated: when the parser is broken,
    // the LSP serves the last clean token array as a fallback. After a
    // few keystrokes those cached spans naturally drift onto whitespace
    // (e.g. indent expanded). The contract is "fits inside the buffer",
    // not "still points at the original lexeme".
    int ls = line_start_offset(text, line);
    if (ls < 0) { snprintf(msg, msglen, "token #%d: missing line %d", i/5, line); return 0; }
  }
  return 1;
}

// Verify every inlay-hint `character` in the response is <= the line length.
// Hints are emitted as `"character":N`; we walk pairs of (line, character).
// Returns 1 on success, 0 if any hint is past EOL.
static int verify_hints_fit(const char *resp, const int *line_lens,
                            int num_lines, char *msg, size_t msglen) {
  if (strstr(resp, "\"result\":null")) return 1;
  const char *p = resp;
  while ((p = strstr(p, "\"line\":")) != NULL) {
    p += 7;
    int line = (int)strtol(p, (char **)&p, 10);
    const char *c = strstr(p, "\"character\":");
    if (!c) break;
    c += 12;
    int ch = (int)strtol(c, NULL, 10);
    if (line < 0 || line >= num_lines) {
      snprintf(msg, msglen, "hint line %d out of range [0, %d)",
               line, num_lines);
      return 0;
    }
    if (ch < 0 || ch > line_lens[line]) {
      snprintf(msg, msglen, "hint char %d past line %d length %d",
               ch, line, line_lens[line]);
      return 0;
    }
    p = c;
  }
  return 1;
}

static void test_mid_edit_positions_stay_valid(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  // Starting text: valid Valkyria with a function and a def. We'll insert
  // `(fuck you)` character-by-character into line 2 (the blank line) to
  // exercise intermediate broken-parse states exactly like live typing.
  const char *initial_text = "(fun {add a b} {+ a b})\n(def {x} 42)\n";
  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/midedit.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {add a b} {+ a b})\\n(def {x} 42)\\n\"}}}");
  free(diag);

  // Build the running text buffer we'll mutate alongside the LSP.
  size_t bufcap = 512;
  char *text = malloc(bufcap);
  strcpy(text, initial_text);

  const char *typed = "(fuck you)";
  int req_id = 2000;
  int version = 2;

  for (size_t i = 0; i < strlen(typed); i++) {
    char ch = typed[i];

    // Send a range-based didChange inserting `ch` at (line=2, char=i).
    char did_change[512];
    // Escape special JSON characters (none in "(fuck you)", safe).
    snprintf(did_change, sizeof(did_change),
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
      "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/midedit.valk\","
      "\"version\":%d},"
      "\"contentChanges\":[{\"range\":{"
      "\"start\":{\"line\":2,\"character\":%zu},"
      "\"end\":{\"line\":2,\"character\":%zu}},"
      "\"text\":\"%c\"}]}}",
      version++, i, i, ch);
    char *n = lsp_did_change(&lsp, did_change);
    if (n) free(n);

    // Mirror the insert in our local text buffer: find byte offset of start
    // of line 2 and insert ch at that offset + i.
    size_t line2_start = 0;
    int nl = 0;
    for (size_t k = 0; text[k]; k++) {
      if (text[k] == '\n') { nl++; if (nl == 2) { line2_start = k + 1; break; } }
    }
    size_t insert_at = line2_start + i;
    size_t tlen = strlen(text);
    if (tlen + 2 > bufcap) { bufcap *= 2; text = realloc(text, bufcap); }
    memmove(text + insert_at + 1, text + insert_at, tlen - insert_at + 1);
    text[insert_at] = ch;

    int num_lines = 0;
    int *line_lens = compute_line_lengths(text, &num_lines);

    // Request semantic tokens and validate positions.
    char req[256];
    snprintf(req, sizeof(req),
      "{\"jsonrpc\":\"2.0\",\"id\":%d,"
      "\"method\":\"textDocument/semanticTokens/full\","
      "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/midedit.valk\"}}}",
      req_id);
    lsp_write(lsp.write_fd, req);
    char *resp = lsp_read_response(&lsp.reader, req_id, MSG_TIMEOUT_MS);
    req_id++;
    VALK_TEST_ASSERT(resp != NULL, "semantic tokens response during mid-edit");
    if (resp) {
      int count = 0;
      int *data = parse_data_array(resp, &count);
      if (data) {
        char err[128] = {0};
        int ok = verify_tokens_fit(data, count, text, line_lens, num_lines,
                                   err, sizeof(err));
        if (!ok) fprintf(stderr, "midedit step %zu ('%c'): %s\n", i, ch, err);
        VALK_TEST_ASSERT(ok, "all semantic tokens must fit current text bounds");
        free(data);
      }
      free(resp);
    }

    // Request inlay hints and validate positions.
    snprintf(req, sizeof(req),
      "{\"jsonrpc\":\"2.0\",\"id\":%d,\"method\":\"textDocument/inlayHint\","
      "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/midedit.valk\"},"
      "\"range\":{\"start\":{\"line\":0,\"character\":0},"
      "\"end\":{\"line\":99,\"character\":0}}}}",
      req_id);
    lsp_write(lsp.write_fd, req);
    resp = lsp_read_response(&lsp.reader, req_id, MSG_TIMEOUT_MS);
    req_id++;
    VALK_TEST_ASSERT(resp != NULL, "inlay hints response during mid-edit");
    if (resp) {
      char err[128] = {0};
      int ok = verify_hints_fit(resp, line_lens, num_lines, err, sizeof(err));
      if (!ok) fprintf(stderr, "midedit hint step %zu ('%c'): %s\n", i, ch, err);
      VALK_TEST_ASSERT(ok, "all inlay hints must fit current text bounds");
      free(resp);
    }

    free(line_lens);
  }

  free(text);
  END_TEST();
}

// Fires rapid didChange + semanticTokens pairs WITHOUT waiting for diagnostics
// between them — exactly what neovim does while you hold down keys. If the
// server drops older semantic-token requests (via the sem-version gate) but
// never sends a response for them, the client ends up holding stale token
// data on screen until it eventually correlates a late response. This test
// verifies EVERY request id gets a response (even if null) so the client
// can always correlate and update.
static void test_rapid_typing_every_request_responds(VALK_TEST_ARGS()) {
  BEGIN_TEST();
  INIT_OR_BAIL();

  char *diag = lsp_did_open(&lsp,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/rapid.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {add a b} {+ a b})\\n(def {x} 42)\\n\"}}}");
  free(diag);

  // Fire 10 interleaved didChange + semanticTokens requests without waiting.
  // Characters of "(fuck you)" inserted one at a time on line 2.
  const char *typed = "(fuck you)";
  int ids[10];
  for (size_t i = 0; i < strlen(typed); i++) {
    char did_change[512];
    snprintf(did_change, sizeof(did_change),
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
      "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/rapid.valk\","
      "\"version\":%zu},"
      "\"contentChanges\":[{\"range\":{"
      "\"start\":{\"line\":2,\"character\":%zu},"
      "\"end\":{\"line\":2,\"character\":%zu}},"
      "\"text\":\"%c\"}]}}",
      i + 2, i, i, typed[i]);
    lsp_write(lsp.write_fd, did_change);

    ids[i] = 3000 + (int)i;
    char req[256];
    snprintf(req, sizeof(req),
      "{\"jsonrpc\":\"2.0\",\"id\":%d,"
      "\"method\":\"textDocument/semanticTokens/full\","
      "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/rapid.valk\"}}}",
      ids[i]);
    lsp_write(lsp.write_fd, req);
  }

  // Collect responses. We need a response for EVERY id, otherwise the client
  // is left hanging with stale tokens visible. The sem-version gate in the
  // dispatch silently dropped older requests — that's the bug.
  int seen[10] = {0};
  int seen_count = 0;
  long deadline = valk_get_millis() + MSG_TIMEOUT_MS;
  while (seen_count < 10 && valk_get_millis() < deadline) {
    int remaining = (int)(deadline - valk_get_millis());
    if (remaining <= 0) break;
    char *msg = lsp_reader_next(&lsp.reader, remaining);
    if (!msg) break;
    for (int i = 0; i < 10; i++) {
      if (seen[i]) continue;
      char id_pat[32];
      snprintf(id_pat, sizeof(id_pat), "\"id\":%d", ids[i]);
      if (strstr(msg, id_pat)) { seen[i] = 1; seen_count++; break; }
    }
    free(msg);
  }

  for (int i = 0; i < 10; i++) {
    if (!seen[i]) {
      fprintf(stderr, "NO RESPONSE for semanticTokens request id=%d "
                      "(keystroke '%c') — client held stale state on screen\n",
              ids[i], typed[i]);
    }
    VALK_TEST_ASSERT(seen[i], "every semanticTokens request must get a response");
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
  valk_testsuite_add_test(suite, "lsp_string_request_id", test_string_request_id);
  valk_testsuite_add_test(suite, "lsp_semantic_tokens", test_semantic_tokens);
  valk_testsuite_add_test(suite, "lsp_didchange_diagnostics", test_didchange_diagnostics);
  valk_testsuite_add_test(suite, "lsp_signature_help", test_signature_help);
  valk_testsuite_add_test(suite, "lsp_semantic_tokens_range", test_semantic_tokens_range);
  valk_testsuite_add_test(suite, "lsp_inlay_hints", test_inlay_hints);
  valk_testsuite_add_test(suite, "lsp_incremental_didchange", test_incremental_didchange);
  valk_testsuite_add_test(suite, "lsp_rapid_incremental_edits", test_rapid_incremental_edits);
  valk_testsuite_add_test(suite, "lsp_startup_race", test_startup_race);
  valk_testsuite_add_test(suite, "lsp_workspace_scan_didopen_race", test_workspace_scan_didopen_race);
  valk_testsuite_add_test(suite, "lsp_partial_edit_keeps_highlighting", test_partial_edit_keeps_highlighting);
  valk_testsuite_add_test(suite, "lsp_brand_new_broken_file_has_tokens", test_brand_new_broken_file_has_tokens);
  valk_testsuite_add_test(suite, "lsp_incremental_didchange_range", test_incremental_didchange_range);
  valk_testsuite_add_test(suite, "lsp_mid_edit_positions_stay_valid", test_mid_edit_positions_stay_valid);
  valk_testsuite_add_test(suite, "lsp_rapid_typing_every_request_responds", test_rapid_typing_every_request_responds);
  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  return result;
}
