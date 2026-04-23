// LSP logging proxy — drop between neovim and valk-lsp to time real traffic.
//
// Usage (neovim):
//   :lua vim.lsp.start({ name = "valk-lsp", cmd = {
//     "/home/nik/src/valkyria/build/lsp_proxy",
//     "/home/nik/src/valkyria/build/valk-lsp"
//   }, ... })
// Or wrap whatever cmd your nvim config uses with this proxy out front.
//
// The proxy:
//   1) Fork/execs argv[1..] as the real LSP server (pipes stdin/stdout).
//   2) Forwards client→server bytes verbatim (stdin → child).
//   3) Forwards server→client bytes verbatim (child stdout → our stdout).
//   4) On every framed LSP message, appends one line to the log file:
//        <elapsed_us>\t<direction>\t<bytes>\t<method-or-id>\t<snippet>
//      direction is C2S (client→server) or S2C (server→client).
//   5) Log path from $VALK_LSP_PROXY_LOG (default /tmp/valk-lsp-proxy.log).
//
// Build: CMake target `lsp_proxy`. Binary at build/lsp_proxy.

#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define BUFSZ 65536

static long t0_us;
static FILE *logf;

static long now_us(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000000L + ts.tv_nsec / 1000L;
}

// Extract "method":"..." or "id":N from a JSON body. Caller-provided buffer.
static void extract_summary(const char *body, int body_len, char *out, int out_cap) {
  out[0] = '\0';
  const char *mkey = "\"method\":\"";
  const char *m = memmem(body, body_len, mkey, 10);
  if (m) {
    m += 10;
    const char *end = memchr(m, '"', body + body_len - m);
    if (end) {
      int n = end - m;
      if (n > out_cap - 1) n = out_cap - 1;
      memcpy(out, m, n);
      out[n] = '\0';
      return;
    }
  }
  const char *ikey = "\"id\":";
  const char *i = memmem(body, body_len, ikey, 5);
  if (i) {
    i += 5;
    const char *end = i;
    while (end < body + body_len && *end != ',' && *end != '}' && *end != '\n') end++;
    int n = end - i;
    if (n > out_cap - 1) n = out_cap - 1;
    snprintf(out, out_cap, "id=%.*s", n, i);
  }
}

// Scan buffered bytes for complete LSP messages. For each one found, write
// a log line. Returns the number of bytes consumed (0 if no complete msg).
static int log_and_consume(const char *dir, char *buf, int len) {
  int consumed = 0;
  while (1) {
    char *header_end = memmem(buf + consumed, len - consumed, "\r\n\r\n", 4);
    if (!header_end) break;

    char *cl = memmem(buf + consumed, header_end - (buf + consumed),
                      "Content-Length: ", 16);
    if (!cl) {
      // Malformed; skip past header to avoid infinite loop
      consumed = (header_end - buf) + 4;
      continue;
    }
    int content_length = atoi(cl + 16);
    int header_size = (header_end + 4) - (buf + consumed);
    int total_needed = header_size + content_length;

    if (len - consumed < total_needed) break;

    const char *body = buf + consumed + header_size;
    char summary[96];
    extract_summary(body, content_length, summary, sizeof(summary));

    fprintf(logf, "%ld\t%s\t%d\t%s\n",
            now_us() - t0_us, dir, content_length, summary);
    fflush(logf);

    consumed += total_needed;
  }
  return consumed;
}

// State per direction: rolling buffer for parsing while bytes stream through.
typedef struct {
  const char *dir;
  char buf[BUFSZ];
  int len;
} stream_t;

static void stream_init(stream_t *s, const char *dir) {
  s->dir = dir;
  s->len = 0;
}

// Forward `n` bytes from src_fd -> dst_fd, ALSO feed them into `s` for parsing.
// Returns 1 on success, 0 on EOF, -1 on error.
static int pump(int src_fd, int dst_fd, stream_t *s) {
  char tmp[BUFSZ];
  int n = read(src_fd, tmp, sizeof(tmp));
  if (n == 0) return 0;
  if (n < 0) {
    if (errno == EINTR) return 1;
    return -1;
  }

  // Forward untouched
  int written = 0;
  while (written < n) {
    int w = write(dst_fd, tmp + written, n - written);
    if (w <= 0) {
      if (errno == EINTR) continue;
      return -1;
    }
    written += w;
  }

  // Feed to parser buffer
  if (s->len + n > BUFSZ) {
    // Drop old bytes; we only care about parsing fresh frames
    int drop = (s->len + n) - BUFSZ;
    memmove(s->buf, s->buf + drop, s->len - drop);
    s->len -= drop;
  }
  memcpy(s->buf + s->len, tmp, n);
  s->len += n;

  int consumed = log_and_consume(s->dir, s->buf, s->len);
  if (consumed > 0) {
    memmove(s->buf, s->buf + consumed, s->len - consumed);
    s->len -= consumed;
  }
  return 1;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s <lsp-binary> [args...]\n", argv[0]);
    return 2;
  }

  const char *log_path = getenv("VALK_LSP_PROXY_LOG");
  if (!log_path || !*log_path) log_path = "/tmp/valk-lsp-proxy.log";
  logf = fopen(log_path, "w");
  if (!logf) { perror(log_path); return 2; }
  setvbuf(logf, NULL, _IOLBF, 0);

  t0_us = now_us();
  fprintf(logf, "# lsp_proxy log for %s\n", argv[1]);
  fprintf(logf, "# columns: elapsed_us\\tdirection\\tbytes\\tmethod-or-id\n");
  fprintf(logf, "0\tSTART\t0\tproxy_started\n");
  fflush(logf);

  int to_child[2], from_child[2];
  if (pipe(to_child) < 0 || pipe(from_child) < 0) { perror("pipe"); return 2; }

  pid_t pid = fork();
  if (pid < 0) { perror("fork"); return 2; }
  if (pid == 0) {
    dup2(to_child[0], 0);
    dup2(from_child[1], 1);
    close(to_child[0]); close(to_child[1]);
    close(from_child[0]); close(from_child[1]);
    // child inherits stderr — user can still see LSP stderr in nvim's :LspLog
    execvp(argv[1], argv + 1);
    perror("execvp");
    _exit(127);
  }
  close(to_child[0]);
  close(from_child[1]);

  signal(SIGPIPE, SIG_IGN);

  stream_t c2s, s2c;
  stream_init(&c2s, "C2S");
  stream_init(&s2c, "S2C");

  int client_in = 0, client_out = 1;
  int server_in = to_child[1], server_out = from_child[0];

  int client_alive = 1, server_alive = 1;
  while (client_alive || server_alive) {
    struct pollfd pfd[2];
    int nfd = 0;
    if (client_alive) { pfd[nfd].fd = client_in; pfd[nfd].events = POLLIN; nfd++; }
    if (server_alive) { pfd[nfd].fd = server_out; pfd[nfd].events = POLLIN; nfd++; }
    if (nfd == 0) break;

    int r = poll(pfd, nfd, -1);
    if (r < 0) {
      if (errno == EINTR) continue;
      break;
    }

    for (int i = 0; i < nfd; i++) {
      if (!(pfd[i].revents & (POLLIN | POLLHUP | POLLERR))) continue;
      if (pfd[i].fd == client_in) {
        int rc = pump(client_in, server_in, &c2s);
        if (rc <= 0) {
          fprintf(logf, "%ld\tEOF\t0\tclient_closed\n", now_us() - t0_us);
          close(server_in);
          client_alive = 0;
        }
      } else if (pfd[i].fd == server_out) {
        int rc = pump(server_out, client_out, &s2c);
        if (rc <= 0) {
          fprintf(logf, "%ld\tEOF\t0\tserver_closed\n", now_us() - t0_us);
          server_alive = 0;
        }
      }
    }
  }

  int status = 0;
  waitpid(pid, &status, 0);
  fprintf(logf, "%ld\tEND\t0\texit=%d\n", now_us() - t0_us, WEXITSTATUS(status));
  fclose(logf);
  return WIFEXITED(status) ? WEXITSTATUS(status) : 1;
}
