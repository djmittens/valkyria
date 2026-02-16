#include "lsp_doc.h"

#include <dirent.h>
#include <libgen.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

// ---------------------------------------------------------------------------
// Workspace root discovery
// ---------------------------------------------------------------------------

static char g_workspace_root[PATH_MAX] = {0};

const char *lsp_workspace_root(void) {
  return g_workspace_root[0] ? g_workspace_root : nullptr;
}

void lsp_workspace_set_root(const char *root) {
  if (!root) return;
  char resolved[PATH_MAX];
  if (realpath(root, resolved))
    snprintf(g_workspace_root, sizeof(g_workspace_root), "%s", resolved);
  else
    snprintf(g_workspace_root, sizeof(g_workspace_root), "%s", root);
}

char *lsp_workspace_discover_root(const char *file_path) {
  char dir[PATH_MAX];
  snprintf(dir, sizeof(dir), "%s", file_path);

  char *last_slash = strrchr(dir, '/');
  if (last_slash) *last_slash = '\0';
  else return nullptr;

  char probe[PATH_MAX];
  char resolved[PATH_MAX];

  for (;;) {
    snprintf(probe, sizeof(probe), "%s/.git", dir);
    struct stat st;
    if (stat(probe, &st) == 0) {
      if (realpath(dir, resolved))
        snprintf(g_workspace_root, sizeof(g_workspace_root), "%s", resolved);
      else
        snprintf(g_workspace_root, sizeof(g_workspace_root), "%s", dir);
      return g_workspace_root;
    }

    char *slash = strrchr(dir, '/');
    if (!slash) break;
    *slash = '\0';
    if (dir[0] == '\0') break;
  }

  snprintf(dir, sizeof(dir), "%s", file_path);
  last_slash = strrchr(dir, '/');
  if (last_slash) *last_slash = '\0';
  if (realpath(dir, resolved))
    snprintf(g_workspace_root, sizeof(g_workspace_root), "%s", resolved);
  else
    snprintf(g_workspace_root, sizeof(g_workspace_root), "%s", dir);
  return g_workspace_root;
}

// ---------------------------------------------------------------------------
// Recursive file discovery
// ---------------------------------------------------------------------------

typedef struct {
  char **paths;
  size_t count;
  size_t cap;
} file_list_t;

static void file_list_add(file_list_t *fl, const char *path) {
  if (fl->count >= fl->cap) {
    fl->cap = fl->cap == 0 ? 64 : fl->cap * 2;
    fl->paths = realloc(fl->paths, sizeof(char *) * fl->cap);
  }
  fl->paths[fl->count++] = strdup(path);
}

static void file_list_free(file_list_t *fl) {
  for (size_t i = 0; i < fl->count; i++)
    free(fl->paths[i]);
  free(fl->paths);
}

static bool has_prefix(const char *s, const char *prefix) {
  return strncmp(s, prefix, strlen(prefix)) == 0;
}

static bool has_suffix(const char *s, const char *suffix) {
  size_t slen = strlen(s);
  size_t sfxlen = strlen(suffix);
  if (slen < sfxlen) return false;
  return strcmp(s + slen - sfxlen, suffix) == 0;
}

static void scan_dir_recursive(const char *dir_path, file_list_t *out) {
  DIR *d = opendir(dir_path);
  if (!d) return;

  struct dirent *ent;
  while ((ent = readdir(d))) {
    if (ent->d_name[0] == '.') continue;
    if (strcmp(ent->d_name, "build") == 0) continue;
    if (strcmp(ent->d_name, "vendor") == 0) continue;
    if (strcmp(ent->d_name, "node_modules") == 0) continue;

    char full[PATH_MAX];
    snprintf(full, sizeof(full), "%s/%s", dir_path, ent->d_name);

    struct stat st;
    if (stat(full, &st) != 0) continue;

    if (S_ISDIR(st.st_mode)) {
      scan_dir_recursive(full, out);
    } else if (S_ISREG(st.st_mode) && has_suffix(ent->d_name, ".valk")) {
      if (has_prefix(ent->d_name, "test_"))
        file_list_add(out, full);
    }
  }
  closedir(d);
}

// ---------------------------------------------------------------------------
// Read file from disk
// ---------------------------------------------------------------------------

static char *read_file(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) return nullptr;
  fseek(f, 0, SEEK_END);
  long flen = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (flen <= 0 || flen > 10 * 1024 * 1024) { fclose(f); return nullptr; }
  char *buf = calloc(flen + 1, 1);
  fread(buf, 1, flen, f);
  fclose(f);
  return buf;
}

// ---------------------------------------------------------------------------
// Load files transitively referenced by (load ...) from a document
// Uses lsp_for_each_load from lsp_loads.c for shared load-directive parsing.
// ---------------------------------------------------------------------------

static void load_into_store_cb(const char *contents, const char *real_path,
                               void *ctx) {
  lsp_doc_store_t *store = ctx;
  char uri[PATH_MAX + 8];
  snprintf(uri, sizeof(uri), "file://%s", real_path);
  if (doc_store_find(store, uri)) return;
  lsp_document_t *doc = doc_store_open(store, uri, contents, 0);
  doc->is_background = true;
  analyze_document_light(doc);
}

static void load_transitive_files(lsp_doc_store_t *store, const char *text,
                                  const char *base_dir, lsp_symset_t *visited) {
  lsp_for_each_load(text, base_dir, visited, load_into_store_cb, store);
}

// ---------------------------------------------------------------------------
// Workspace scan: find test_*.valk, load them + their transitive deps
// ---------------------------------------------------------------------------

void lsp_workspace_scan(lsp_doc_store_t *store) {
  const char *root = lsp_workspace_root();
  if (!root) return;

  fprintf(stderr, "[valk-lsp] scanning workspace: %s\n", root);

  file_list_t files = {0};
  scan_dir_recursive(root, &files);

  fprintf(stderr, "[valk-lsp] found %zu test files\n", files.count);

  lsp_symset_t visited;
  symset_init(&visited);

  for (size_t i = 0; i < files.count; i++) {
    char resolved[PATH_MAX];
    if (!realpath(files.paths[i], resolved)) continue;
    if (symset_contains(&visited, resolved)) continue;
    symset_add(&visited, resolved);

    char *text = read_file(resolved);
    if (!text) continue;

    char *dir_copy = strdup(resolved);
    char *dir = dirname(dir_copy);
    load_transitive_files(store, text, dir, &visited);
    free(dir_copy);

    char uri[PATH_MAX + 8];
    snprintf(uri, sizeof(uri), "file://%s", resolved);
    if (!doc_store_find(store, uri)) {
      lsp_document_t *doc = doc_store_open(store, uri, text, 0);
      doc->is_background = true;
      analyze_document_light(doc);
    }
    free(text);
  }

  symset_free(&visited);
  file_list_free(&files);

  fprintf(stderr, "[valk-lsp] workspace indexed: %zu documents\n", store->count);
}
