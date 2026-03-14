#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "memory.h"
#include "testing.h"

#define LSP_TIMEOUT_MS 15000

typedef struct {
  int fd;
  char buf[65536];
  int len;
} lsp_reader_t;

static void lsp_reader_init(lsp_reader_t *r, int fd) {
  r->fd = fd;
  r->len = 0;
}

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
} lsp_proc_t;

static lsp_proc_t start_lsp(void) {
  int stdin_pipe[2], stdout_pipe[2];
  pipe(stdin_pipe);
  pipe(stdout_pipe);

  pid_t pid = fork();
  if (pid == 0) {
    dup2(stdin_pipe[0], 0);
    dup2(stdout_pipe[1], 1);
    close(stdin_pipe[1]);
    close(stdout_pipe[0]);
    close(stdin_pipe[0]);
    close(stdout_pipe[1]);

    int devnull = open("/dev/null", O_WRONLY);
    if (devnull >= 0) {
      dup2(devnull, 2);
      close(devnull);
    }

    execlp("build/valk", "build/valk", "src/lsp-main.valk", NULL);
    _exit(1);
  }

  close(stdin_pipe[0]);
  close(stdout_pipe[1]);

  usleep(1000000);

  return (lsp_proc_t){.pid = pid, .write_fd = stdin_pipe[1], .read_fd = stdout_pipe[0]};
}

static void stop_lsp(lsp_proc_t *lsp) {
  close(lsp->write_fd);
  close(lsp->read_fd);
  kill(lsp->pid, SIGTERM);
  int status;
  waitpid(lsp->pid, &status, 0);
}

static void test_initialize_shutdown(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  int rc = lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  VALK_TEST_ASSERT(rc == 0, "write initialize");

  char *resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get initialize response");
  if (!resp) { stop_lsp(&lsp); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  VALK_TEST_ASSERT(strstr(resp, "capabilities") != NULL, "should have capabilities");
  VALK_TEST_ASSERT(strstr(resp, "hoverProvider") != NULL, "should have hoverProvider");
  VALK_TEST_ASSERT(strstr(resp, "completionProvider") != NULL, "should have completionProvider");
  VALK_TEST_ASSERT(strstr(resp, "valk-lsp") != NULL, "serverInfo should say valk-lsp");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  rc = lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"shutdown\",\"params\":{}}");
  VALK_TEST_ASSERT(rc == 0, "write shutdown");

  resp = lsp_read_response(&reader, 2, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get shutdown response");
  if (!resp) { stop_lsp(&lsp); return; }
  VALK_TEST_ASSERT(strstr(resp, "\"id\":2") != NULL, "shutdown response id=2");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;

  int status;
  int w = waitpid(lsp.pid, &status, 0);
  VALK_TEST_ASSERT(w > 0, "waitpid should succeed");
  VALK_TEST_ASSERT(WIFEXITED(status), "child should exit normally");

  close(lsp.read_fd);
  VALK_PASS();
}

static void test_didopen_hover(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");

  char *resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "initialize response");
  if (!resp) { stop_lsp(&lsp); return; }
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/test.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {add a b} {+ a b})\\n(add 1 2)\"}}}");

  usleep(200000);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/hover\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/test.valk\"},"
    "\"position\":{\"line\":0,\"character\":6}}}");

  resp = lsp_read_response(&reader, 3, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get hover response");
  if (!resp) { stop_lsp(&lsp); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "hover should have result");
  VALK_TEST_ASSERT(strstr(resp, "contents") != NULL, "hover should have contents");
  VALK_TEST_ASSERT(strstr(resp, "add") != NULL, "hover should mention 'add'");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&reader, 99, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  close(lsp.read_fd);
  VALK_PASS();
}

static void test_didopen_completion(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  char *resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "initialize response");
  if (!resp) { stop_lsp(&lsp); return; }
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/test.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fu\"}}}");

  usleep(200000);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/completion\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/test.valk\"},"
    "\"position\":{\"line\":0,\"character\":3}}}");

  resp = lsp_read_response(&reader, 4, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get completion response");
  if (!resp) { stop_lsp(&lsp); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "completion should have result");
  VALK_TEST_ASSERT(strstr(resp, "items") != NULL, "completion should have items");
  VALK_TEST_ASSERT(strstr(resp, "fun") != NULL, "should suggest 'fun' snippet");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&reader, 99, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  close(lsp.read_fd);
  VALK_PASS();
}

static void test_not_initialized_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/hover\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/test.valk\"},"
    "\"position\":{\"line\":0,\"character\":0}}}");

  char *resp = lsp_read_response(&reader, 5, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get error response");
  if (!resp) { stop_lsp(&lsp); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"error\"") != NULL, "should have error field");
  VALK_TEST_ASSERT(strstr(resp, "-32002") != NULL, "error code should be -32002");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");
  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&reader, 99, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  close(lsp.read_fd);
  VALK_PASS();
}

static void test_unknown_method_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  char *resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "initialize response");
  if (!resp) { stop_lsp(&lsp); return; }
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  usleep(100000);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"bogus/method\","
    "\"params\":{}}");

  resp = lsp_read_response(&reader, 6, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get error for unknown method");
  if (!resp) { stop_lsp(&lsp); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"error\"") != NULL, "should have error");
  VALK_TEST_ASSERT(strstr(resp, "-32601") != NULL, "error code -32601");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&reader, 99, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  close(lsp.read_fd);
  VALK_PASS();
}

static void test_semantic_tokens(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  char *resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "initialize response");
  if (!resp) { stop_lsp(&lsp); return; }
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/tok.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {f x} {+ x 1})\"}}}");

  usleep(200000);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/semanticTokens/full\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/tok.valk\"}}}");

  resp = lsp_read_response(&reader, 7, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get semantic tokens response");
  if (!resp) { stop_lsp(&lsp); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  VALK_TEST_ASSERT(strstr(resp, "data") != NULL, "should have data field");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&reader, 99, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  close(lsp.read_fd);
  VALK_PASS();
}

static void test_didchange_diagnostics(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  char *resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "initialize response");
  if (!resp) { stop_lsp(&lsp); return; }
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/diag.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(+ 1 2)\"}}}");

  usleep(300000);

  char *notif = lsp_reader_next(&reader, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(notif != NULL, "should get diagnostics notification after didOpen");
  if (!notif) { stop_lsp(&lsp); return; }
  VALK_TEST_ASSERT(strstr(notif, "publishDiagnostics") != NULL, "should be publishDiagnostics");
  VALK_TEST_ASSERT(strstr(notif, "diag.valk") != NULL, "should reference our file");
  free(notif);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/diag.valk\","
    "\"version\":2},"
    "\"contentChanges\":[{\"text\":\"(+ 1\"}]}}");

  usleep(300000);

  notif = lsp_reader_next(&reader, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(notif != NULL, "should get diagnostics after didChange");
  if (!notif) { stop_lsp(&lsp); return; }
  VALK_TEST_ASSERT(strstr(notif, "publishDiagnostics") != NULL, "publishDiagnostics after change");
  free(notif);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&reader, 99, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  close(lsp.read_fd);
  VALK_PASS();
}

static void test_signature_help(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  char *resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "initialize response");
  if (!resp) { stop_lsp(&lsp); return; }
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/sig.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {add a b} {+ a b})\\n(add 1 2)\"}}}");

  usleep(200000);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/signatureHelp\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/sig.valk\"},"
    "\"position\":{\"line\":1,\"character\":5}}}");

  resp = lsp_read_response(&reader, 5, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get signature help response");
  if (!resp) { stop_lsp(&lsp); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&reader, 99, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  close(lsp.read_fd);
  VALK_PASS();
}

static void test_semantic_tokens_range(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  char *resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "initialize response");
  if (!resp) { stop_lsp(&lsp); return; }
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/tokr.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {f x} {+ x 1})\\n(def {y} 42)\"}}}");

  usleep(200000);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"textDocument/semanticTokens/range\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/tokr.valk\"},"
    "\"range\":{\"start\":{\"line\":0,\"character\":0},"
    "\"end\":{\"line\":1,\"character\":99}}}}");

  resp = lsp_read_response(&reader, 8, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get semantic tokens range response");
  if (!resp) { stop_lsp(&lsp); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  VALK_TEST_ASSERT(strstr(resp, "data") != NULL, "should have data field");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&reader, 99, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  close(lsp.read_fd);
  VALK_PASS();
}

static void test_inlay_hints(VALK_TEST_ARGS()) {
  VALK_TEST();
  signal(SIGPIPE, SIG_IGN);

  lsp_proc_t lsp = start_lsp();
  lsp_reader_t reader;
  lsp_reader_init(&reader, lsp.read_fd);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\","
    "\"params\":{\"capabilities\":{}}}");
  char *resp = lsp_read_response(&reader, 1, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "initialize response");
  if (!resp) { stop_lsp(&lsp); return; }
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\","
    "\"params\":{\"textDocument\":{"
    "\"uri\":\"file:///tmp/hint.valk\","
    "\"languageId\":\"valk\","
    "\"version\":1,"
    "\"text\":\"(fun {add a b} {+ a b})\\n(def {x} 42)\\n(add 1 2)\"}}}");

  usleep(200000);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/inlayHint\","
    "\"params\":{\"textDocument\":{\"uri\":\"file:///tmp/hint.valk\"},"
    "\"range\":{\"start\":{\"line\":0,\"character\":0},"
    "\"end\":{\"line\":2,\"character\":99}}}}");

  resp = lsp_read_response(&reader, 9, LSP_TIMEOUT_MS);
  VALK_TEST_ASSERT(resp != NULL, "should get inlay hints response");
  if (!resp) { stop_lsp(&lsp); return; }

  VALK_TEST_ASSERT(strstr(resp, "\"result\"") != NULL, "should have result");
  VALK_TEST_ASSERT(strstr(resp, "\"a:\"") != NULL, "should have param hint for a");
  VALK_TEST_ASSERT(strstr(resp, "\"b:\"") != NULL, "should have param hint for b");
  VALK_TEST_ASSERT(strstr(resp, "\":: Num\"") != NULL, "should have type hint for x binding");
  free(resp);

  lsp_write(lsp.write_fd,
    "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":{}}");
  resp = lsp_read_response(&reader, 99, LSP_TIMEOUT_MS);
  free(resp);
  lsp_write(lsp.write_fd, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");

  close(lsp.write_fd);
  lsp.write_fd = -1;
  int status;
  waitpid(lsp.pid, &status, 0);
  close(lsp.read_fd);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
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
  return valk_testsuite_run(suite);
}
