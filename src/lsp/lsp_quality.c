#include "lsp_doc.h"
#include "lsp_db.h"

#include <libgen.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// JSON output helpers
// ---------------------------------------------------------------------------

static void json_str(FILE *f, const char *s) {
  fputc('"', f);
  for (const char *p = s; *p; p++) {
    switch (*p) {
    case '"': fputs("\\\"", f); break;
    case '\\': fputs("\\\\", f); break;
    case '\n': fputs("\\n", f); break;
    case '\t': fputs("\\t", f); break;
    default: fputc(*p, f);
    }
  }
  fputc('"', f);
}

// ---------------------------------------------------------------------------
// Workspace scan + symdb sync (headless, no LSP server)
// ---------------------------------------------------------------------------

static void sync_all_documents(lsp_doc_store_t *store) {
  for (size_t i = 0; i < store->count; i++)
    lsp_db_sync_document(&store->docs[i]);
}

// ---------------------------------------------------------------------------
// Per-file metrics from symdb
// ---------------------------------------------------------------------------

typedef struct {
  char *path;
  int symbol_count;
  int function_count;
  int dead_count;
  int total_fan_in;
  int total_fan_out;
  int max_fan_out;
  char *max_fan_out_fn;
  bool is_test;
  int line_count;
} file_metric_t;

typedef struct {
  file_metric_t *files;
  size_t count;
  size_t cap;
} file_metrics_t;

static void file_metrics_free(file_metrics_t *m) {
  for (size_t i = 0; i < m->count; i++) {
    free(m->files[i].path);
    free(m->files[i].max_fan_out_fn);
  }
  free(m->files);
}

// ---------------------------------------------------------------------------
// Snapshot generation
// ---------------------------------------------------------------------------

static const char *strip_workspace_prefix(const char *path, const char *root) {
  if (!root) return path;
  size_t rlen = strlen(root);
  if (strncmp(path, root, rlen) == 0 && path[rlen] == '/')
    return path + rlen + 1;
  return path;
}

static int count_lines(lsp_doc_store_t *store, const char *uri) {
  lsp_document_t *doc = doc_store_find(store, uri);
  if (!doc || !doc->text) return 0;
  int n = 1;
  for (const char *p = doc->text; *p; p++)
    if (*p == '\n') n++;
  return n;
}

static void emit_snapshot(valk_symdb_t *db, lsp_doc_store_t *store,
                          const char *root) {
  FILE *f = stdout;

  symdb_summary_t sum = valk_symdb_summary(db);
  symdb_stat_result_t dead = valk_symdb_dead_code(db, 500);
  symdb_stat_result_t hotspots = valk_symdb_hotspots(db, 20);
  symdb_stat_result_t fanout = valk_symdb_high_fanout(db, 20);
  symdb_coupling_result_t coupling = valk_symdb_file_coupling(db, 50);

  // Build per-file metrics
  file_metrics_t fm = {0};
  for (size_t i = 0; i < store->count; i++) {
    lsp_document_t *doc = &store->docs[i];
    if (!doc->uri) continue;

    char path[PATH_MAX];
    if (strncmp(doc->uri, "file://", 7) == 0)
      snprintf(path, sizeof(path), "%s", doc->uri + 7);
    else
      snprintf(path, sizeof(path), "%s", doc->uri);

    if (fm.count >= fm.cap) {
      fm.cap = fm.cap == 0 ? 64 : fm.cap * 2;
      fm.files = realloc(fm.files, fm.cap * sizeof(*fm.files));
    }
    file_metric_t *m = &fm.files[fm.count++];
    memset(m, 0, sizeof(*m));
    m->path = strdup(strip_workspace_prefix(path, root));
    m->symbol_count = (int)doc->symbol_count;
    m->line_count = count_lines(store, doc->uri);

    const char *basename = strrchr(m->path, '/');
    basename = basename ? basename + 1 : m->path;
    m->is_test = (strncmp(basename, "test_", 5) == 0);

    for (size_t j = 0; j < doc->symbol_count; j++) {
      if (doc->symbols[j].arity >= 0) m->function_count++;
    }

    // Count dead symbols in this file
    for (size_t j = 0; j < dead.count; j++) {
      const char *dp = strip_workspace_prefix(dead.rows[j].file_path, root);
      if (strcmp(dp, m->path) == 0) m->dead_count++;
    }
  }

  // Compute fan-in per file from hotspots
  for (size_t i = 0; i < hotspots.count; i++) {
    const char *hp = strip_workspace_prefix(hotspots.rows[i].file_path, root);
    for (size_t j = 0; j < fm.count; j++) {
      if (strcmp(fm.files[j].path, hp) == 0) {
        fm.files[j].total_fan_in += (int)hotspots.rows[i].count;
        break;
      }
    }
  }

  // Compute fan-out per file from high-fanout results
  for (size_t i = 0; i < fanout.count; i++) {
    const char *fp = strip_workspace_prefix(fanout.rows[i].file_path, root);
    for (size_t j = 0; j < fm.count; j++) {
      if (strcmp(fm.files[j].path, fp) == 0) {
        fm.files[j].total_fan_out += (int)fanout.rows[i].count;
        if ((int)fanout.rows[i].count > fm.files[j].max_fan_out) {
          fm.files[j].max_fan_out = (int)fanout.rows[i].count;
          free(fm.files[j].max_fan_out_fn);
          fm.files[j].max_fan_out_fn = strdup(fanout.rows[i].name);
        }
        break;
      }
    }
  }

  // Test coverage by reference: which non-test symbols are referenced
  // from test files?
  int tested_symbols = 0;
  int testable_symbols = 0;
  for (size_t i = 0; i < store->count; i++) {
    lsp_document_t *doc = &store->docs[i];
    if (!doc->uri) continue;
    char path[PATH_MAX];
    if (strncmp(doc->uri, "file://", 7) == 0)
      snprintf(path, sizeof(path), "%s", doc->uri + 7);
    else
      snprintf(path, sizeof(path), "%s", doc->uri);
    const char *bn = strrchr(path, '/');
    bn = bn ? bn + 1 : path;
    if (strncmp(bn, "test_", 5) == 0) continue;

    symdb_file_id fid = valk_symdb_file_id(db, path);
    if (fid < 0) continue;

    symdb_sym_result_t *syms = NULL;
    size_t sym_count = valk_symdb_file_symbols(db, fid, &syms);
    for (size_t j = 0; j < sym_count; j++) {
      if (!syms[j].exported) continue;
      testable_symbols++;

      symdb_ref_result_t *refs = NULL;
      size_t ref_count = valk_symdb_find_refs(db, syms[j].id, &refs);
      bool has_test_ref = false;
      for (size_t k = 0; k < ref_count && !has_test_ref; k++) {
        // Check if ref's file is a test file
        // We need the file path for this ref
        for (size_t fi = 0; fi < store->count; fi++) {
          lsp_document_t *rd = &store->docs[fi];
          if (!rd->uri) continue;
          char rp[PATH_MAX];
          if (strncmp(rd->uri, "file://", 7) == 0)
            snprintf(rp, sizeof(rp), "%s", rd->uri + 7);
          else
            snprintf(rp, sizeof(rp), "%s", rd->uri);
          symdb_file_id rfid = valk_symdb_file_id(db, rp);
          if (rfid == refs[k].file_id) {
            const char *rbn = strrchr(rp, '/');
            rbn = rbn ? rbn + 1 : rp;
            if (strncmp(rbn, "test_", 5) == 0) has_test_ref = true;
            break;
          }
        }
      }
      if (has_test_ref) tested_symbols++;
      free(refs);
    }
    for (size_t j = 0; j < sym_count; j++) free(syms[j].name);
    free(syms);
  }

  // --- Emit JSON ---
  fprintf(f, "{\n");

  // Summary
  fprintf(f, "  \"summary\": {\n");
  fprintf(f, "    \"files\": %lld,\n", (long long)sum.file_count);
  fprintf(f, "    \"symbols\": %lld,\n", (long long)sum.symbol_count);
  fprintf(f, "    \"types\": %lld,\n", (long long)sum.type_count);
  fprintf(f, "    \"references\": %lld,\n", (long long)sum.ref_count);
  fprintf(f, "    \"scopes\": %lld,\n", (long long)sum.scope_count);
  fprintf(f, "    \"dead_symbols\": %zu,\n", dead.count);
  fprintf(f, "    \"testable_symbols\": %d,\n", testable_symbols);
  fprintf(f, "    \"tested_symbols\": %d,\n", tested_symbols);
  int pct = testable_symbols > 0 ? (tested_symbols * 100 / testable_symbols) : 0;
  fprintf(f, "    \"test_coverage_pct\": %d\n", pct);
  fprintf(f, "  },\n");

  // Per-file
  fprintf(f, "  \"files\": [\n");
  for (size_t i = 0; i < fm.count; i++) {
    file_metric_t *m = &fm.files[i];
    fprintf(f, "    {");
    fprintf(f, "\"path\": "); json_str(f, m->path);
    fprintf(f, ", \"lines\": %d", m->line_count);
    fprintf(f, ", \"symbols\": %d", m->symbol_count);
    fprintf(f, ", \"functions\": %d", m->function_count);
    fprintf(f, ", \"dead\": %d", m->dead_count);
    fprintf(f, ", \"fan_in\": %d", m->total_fan_in);
    fprintf(f, ", \"fan_out\": %d", m->total_fan_out);
    fprintf(f, ", \"max_fan_out\": %d", m->max_fan_out);
    if (m->max_fan_out_fn) {
      fprintf(f, ", \"max_fan_out_fn\": ");
      json_str(f, m->max_fan_out_fn);
    }
    fprintf(f, ", \"is_test\": %s", m->is_test ? "true" : "false");
    fprintf(f, "}%s\n", i + 1 < fm.count ? "," : "");
  }
  fprintf(f, "  ],\n");

  // Dead symbols
  fprintf(f, "  \"dead_symbols\": [\n");
  for (size_t i = 0; i < dead.count; i++) {
    fprintf(f, "    {\"name\": ");
    json_str(f, dead.rows[i].name);
    fprintf(f, ", \"file\": ");
    json_str(f, strip_workspace_prefix(dead.rows[i].file_path, root));
    fprintf(f, ", \"line\": %d}%s\n", dead.rows[i].line,
            i + 1 < dead.count ? "," : "");
  }
  fprintf(f, "  ],\n");

  // Hotspots (top fan-in)
  fprintf(f, "  \"hotspots\": [\n");
  for (size_t i = 0; i < hotspots.count; i++) {
    fprintf(f, "    {\"name\": ");
    json_str(f, hotspots.rows[i].name);
    fprintf(f, ", \"file\": ");
    json_str(f, strip_workspace_prefix(hotspots.rows[i].file_path, root));
    fprintf(f, ", \"refs\": %lld}%s\n", (long long)hotspots.rows[i].count,
            i + 1 < hotspots.count ? "," : "");
  }
  fprintf(f, "  ],\n");

  // High fan-out functions
  fprintf(f, "  \"high_fan_out\": [\n");
  for (size_t i = 0; i < fanout.count; i++) {
    fprintf(f, "    {\"name\": ");
    json_str(f, fanout.rows[i].name);
    fprintf(f, ", \"file\": ");
    json_str(f, strip_workspace_prefix(fanout.rows[i].file_path, root));
    fprintf(f, ", \"deps\": %lld}%s\n", (long long)fanout.rows[i].count,
            i + 1 < fanout.count ? "," : "");
  }
  fprintf(f, "  ],\n");

  // File coupling
  fprintf(f, "  \"file_coupling\": [\n");
  for (size_t i = 0; i < coupling.count; i++) {
    fprintf(f, "    {\"source\": ");
    json_str(f, strip_workspace_prefix(coupling.rows[i].source_path, root));
    fprintf(f, ", \"target\": ");
    json_str(f, strip_workspace_prefix(coupling.rows[i].target_path, root));
    fprintf(f, ", \"refs\": %lld}%s\n", (long long)coupling.rows[i].ref_count,
            i + 1 < coupling.count ? "," : "");
  }
  fprintf(f, "  ]\n");

  fprintf(f, "}\n");

  symdb_stat_result_free(&dead);
  symdb_stat_result_free(&hotspots);
  symdb_stat_result_free(&fanout);
  symdb_coupling_result_free(&coupling);
  file_metrics_free(&fm);
}

// ---------------------------------------------------------------------------
// Public entry point — called from repl.c via --lsp-check
// Headless diagnostic check: analyze a file and print all diagnostics.
// ---------------------------------------------------------------------------

int valk_lsp_check(const char *file_path) {
  char resolved[PATH_MAX];
  if (!realpath(file_path, resolved)) {
    fprintf(stderr, "lsp-check: cannot resolve path: %s\n", file_path);
    return 1;
  }

  char *dir_copy = strdup(resolved);
  (void)dirname(dir_copy);
  lsp_workspace_discover_root(resolved);

  FILE *f = fopen(resolved, "rb");
  if (!f) {
    fprintf(stderr, "lsp-check: cannot open: %s\n", resolved);
    free(dir_copy);
    return 1;
  }
  fseek(f, 0, SEEK_END);
  long flen = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *text = calloc(flen + 1, 1);
  fread(text, 1, flen, f);
  fclose(f);

  char uri[PATH_MAX + 8];
  snprintf(uri, sizeof(uri), "file://%s", resolved);

  lsp_doc_store_t store = {0};
  lsp_load_builtins_into_store(&store);
  lsp_document_t *doc = doc_store_open(&store, uri, text, 0);

  analyze_document(doc);

  int errors = 0, warnings = 0, infos = 0;
  for (size_t i = 0; i < doc->diag_count; i++) {
    int sev = doc->diag_severities[i];
    const char *sev_str = sev == 1 ? "error" : sev == 2 ? "warning" : "info";
    if (sev == 1) errors++;
    else if (sev == 2) warnings++;
    else infos++;
    fprintf(stdout, "%s:%d:%d: %s: %s\n",
            file_path,
            doc->diag_positions[i].line + 1,
            doc->diag_positions[i].col + 1,
            sev_str, doc->diag_messages[i]);
  }

  fprintf(stdout, "\n%zu diagnostics (%d errors, %d warnings, %d info)\n",
          doc->diag_count, errors, warnings, infos);

  free(text);
  free(dir_copy);
  doc_store_free(&store);
  return errors > 0 ? 1 : 0;
}

// ---------------------------------------------------------------------------
// Public entry point — called from repl.c via --quality-snapshot
// ---------------------------------------------------------------------------

int valk_quality_snapshot(const char *dir) {
  char root[PATH_MAX];
  if (!dir) dir = ".";
  if (!realpath(dir, root)) {
    fprintf(stderr, "quality-snapshot: cannot resolve path: %s\n", dir);
    return 1;
  }

  lsp_workspace_set_root(root);
  lsp_db_init(root);

  valk_symdb_t *db = lsp_db_get();
  if (!db) {
    fprintf(stderr, "quality-snapshot: failed to open symdb\n");
    return 1;
  }

  lsp_doc_store_t store = {0};
  lsp_load_builtins_into_store(&store);
  lsp_workspace_scan(&store);

  sync_all_documents(&store);

  emit_snapshot(db, &store, root);

  lsp_db_shutdown();
  doc_store_free(&store);
  return 0;
}
