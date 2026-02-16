#include "lsp_db.h"
#include "../../vendor/sqlite3/sqlite3.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

sqlite3 *valk_symdb_get_raw_db(valk_symdb_t *db);

static sqlite3 *get_db(valk_symdb_t *sdb) { return valk_symdb_get_raw_db(sdb); }

// ---------------------------------------------------------------------------
// Result helpers
// ---------------------------------------------------------------------------

void symdb_stat_result_free(symdb_stat_result_t *r) {
  if (!r) return;
  for (size_t i = 0; i < r->count; i++) {
    free(r->rows[i].name);
    free(r->rows[i].file_path);
  }
  free(r->rows);
  r->rows = NULL;
  r->count = 0;
}

void symdb_type_stat_result_free(symdb_type_stat_result_t *r) {
  if (!r) return;
  for (size_t i = 0; i < r->count; i++)
    free(r->rows[i].display);
  free(r->rows);
  r->rows = NULL;
  r->count = 0;
}

void symdb_coupling_result_free(symdb_coupling_result_t *r) {
  if (!r) return;
  for (size_t i = 0; i < r->count; i++) {
    free(r->rows[i].source_path);
    free(r->rows[i].target_path);
  }
  free(r->rows);
  r->rows = NULL;
  r->count = 0;
}

static sqlite3_stmt *prep(sqlite3 *db, const char *sql) {
  sqlite3_stmt *s = NULL;
  int rc = sqlite3_prepare_v2(db, sql, -1, &s, NULL);
  if (rc != SQLITE_OK) {
    fprintf(stderr, "symdb stats: %s\n", sqlite3_errmsg(db));
    return NULL;
  }
  return s;
}

// ---------------------------------------------------------------------------
// Hotspots — symbols with the most incoming references
// ---------------------------------------------------------------------------

symdb_stat_result_t valk_symdb_hotspots(valk_symdb_t *db, int limit) {
  symdb_stat_result_t result = {0};
  sqlite3 *raw = get_db(db);

  const char *sql =
    "SELECT s.name, f.path, s.line, COUNT(r.id) AS cnt"
    " FROM symbols s"
    " JOIN refs r ON r.symbol_id = s.id"
    " JOIN files f ON f.id = s.file_id"
    " GROUP BY s.id"
    " ORDER BY cnt DESC"
    " LIMIT ?1";

  sqlite3_stmt *s = prep(raw, sql);
  if (!s) return result;
  sqlite3_bind_int(s, 1, limit);

  size_t cap = 16;
  result.rows = malloc(cap * sizeof(*result.rows));

  while (sqlite3_step(s) == SQLITE_ROW) {
    if (result.count >= cap) {
      cap *= 2;
      result.rows = realloc(result.rows, cap * sizeof(*result.rows));
    }
    symdb_stat_row_t *row = &result.rows[result.count++];
    row->name      = strdup((const char *)sqlite3_column_text(s, 0));
    row->file_path = strdup((const char *)sqlite3_column_text(s, 1));
    row->line      = sqlite3_column_int(s, 2);
    row->count     = sqlite3_column_int64(s, 3);
  }
  sqlite3_finalize(s);
  return result;
}

// ---------------------------------------------------------------------------
// High fanout — symbols whose definitions contain the most outgoing refs
//
// We approximate fanout as: references originating from the same file and
// line range as a function definition.
// ---------------------------------------------------------------------------

symdb_stat_result_t valk_symdb_high_fanout(valk_symdb_t *db, int limit) {
  symdb_stat_result_t result = {0};
  sqlite3 *raw = get_db(db);

  const char *sql =
    "SELECT s.name, f.path, s.line, COUNT(DISTINCT r.symbol_id) AS cnt"
    " FROM symbols s"
    " JOIN files f ON f.id = s.file_id"
    " JOIN refs r ON r.file_id = s.file_id"
    "   AND r.line >= s.line AND r.line <= s.end_line"
    " WHERE s.kind IN (1, 5)"
    " GROUP BY s.id"
    " ORDER BY cnt DESC"
    " LIMIT ?1";

  sqlite3_stmt *s = prep(raw, sql);
  if (!s) return result;
  sqlite3_bind_int(s, 1, limit);

  size_t cap = 16;
  result.rows = malloc(cap * sizeof(*result.rows));

  while (sqlite3_step(s) == SQLITE_ROW) {
    if (result.count >= cap) {
      cap *= 2;
      result.rows = realloc(result.rows, cap * sizeof(*result.rows));
    }
    symdb_stat_row_t *row = &result.rows[result.count++];
    row->name      = strdup((const char *)sqlite3_column_text(s, 0));
    row->file_path = strdup((const char *)sqlite3_column_text(s, 1));
    row->line      = sqlite3_column_int(s, 2);
    row->count     = sqlite3_column_int64(s, 3);
  }
  sqlite3_finalize(s);
  return result;
}

// ---------------------------------------------------------------------------
// Dead code — exported symbols with zero references
// ---------------------------------------------------------------------------

symdb_stat_result_t valk_symdb_dead_code(valk_symdb_t *db, int limit) {
  symdb_stat_result_t result = {0};
  sqlite3 *raw = get_db(db);

  const char *sql =
    "SELECT s.name, f.path, s.line, 0 AS cnt"
    " FROM symbols s"
    " JOIN files f ON f.id = s.file_id"
    " LEFT JOIN refs r ON r.symbol_id = s.id"
    " WHERE s.exported = 1 AND r.id IS NULL"
    " ORDER BY f.path, s.line"
    " LIMIT ?1";

  sqlite3_stmt *s = prep(raw, sql);
  if (!s) return result;
  sqlite3_bind_int(s, 1, limit);

  size_t cap = 16;
  result.rows = malloc(cap * sizeof(*result.rows));

  while (sqlite3_step(s) == SQLITE_ROW) {
    if (result.count >= cap) {
      cap *= 2;
      result.rows = realloc(result.rows, cap * sizeof(*result.rows));
    }
    symdb_stat_row_t *row = &result.rows[result.count++];
    row->name      = strdup((const char *)sqlite3_column_text(s, 0));
    row->file_path = strdup((const char *)sqlite3_column_text(s, 1));
    row->line      = sqlite3_column_int(s, 2);
    row->count     = 0;
  }
  sqlite3_finalize(s);
  return result;
}

// ---------------------------------------------------------------------------
// Type popularity — most frequently used types
// ---------------------------------------------------------------------------

symdb_type_stat_result_t valk_symdb_type_popularity(valk_symdb_t *db, int limit) {
  symdb_type_stat_result_t result = {0};
  sqlite3 *raw = get_db(db);

  const char *sql =
    "SELECT t.display, COUNT(s.id) AS cnt"
    " FROM types t"
    " JOIN symbols s ON s.type_id = t.id"
    " GROUP BY t.id"
    " ORDER BY cnt DESC"
    " LIMIT ?1";

  sqlite3_stmt *s = prep(raw, sql);
  if (!s) return result;
  sqlite3_bind_int(s, 1, limit);

  size_t cap = 16;
  result.rows = malloc(cap * sizeof(*result.rows));

  while (sqlite3_step(s) == SQLITE_ROW) {
    if (result.count >= cap) {
      cap *= 2;
      result.rows = realloc(result.rows, cap * sizeof(*result.rows));
    }
    symdb_type_stat_row_t *row = &result.rows[result.count++];
    row->display = strdup((const char *)sqlite3_column_text(s, 0));
    row->count   = sqlite3_column_int64(s, 1);
  }
  sqlite3_finalize(s);
  return result;
}

// ---------------------------------------------------------------------------
// File coupling — files that reference each other's symbols
// ---------------------------------------------------------------------------

symdb_coupling_result_t valk_symdb_file_coupling(valk_symdb_t *db, int limit) {
  symdb_coupling_result_t result = {0};
  sqlite3 *raw = get_db(db);

  const char *sql =
    "SELECT src.path, dst.path, COUNT(r.id) AS cnt"
    " FROM refs r"
    " JOIN files src ON src.id = r.file_id"
    " JOIN symbols s ON s.id = r.symbol_id"
    " JOIN files dst ON dst.id = s.file_id"
    " WHERE r.file_id != s.file_id"
    " GROUP BY r.file_id, s.file_id"
    " ORDER BY cnt DESC"
    " LIMIT ?1";

  sqlite3_stmt *s = prep(raw, sql);
  if (!s) return result;
  sqlite3_bind_int(s, 1, limit);

  size_t cap = 16;
  result.rows = malloc(cap * sizeof(*result.rows));

  while (sqlite3_step(s) == SQLITE_ROW) {
    if (result.count >= cap) {
      cap *= 2;
      result.rows = realloc(result.rows, cap * sizeof(*result.rows));
    }
    symdb_coupling_row_t *row = &result.rows[result.count++];
    row->source_path = strdup((const char *)sqlite3_column_text(s, 0));
    row->target_path = strdup((const char *)sqlite3_column_text(s, 1));
    row->ref_count   = sqlite3_column_int64(s, 2);
  }
  sqlite3_finalize(s);
  return result;
}

// ---------------------------------------------------------------------------
// Summary — aggregate counts across all tables
// ---------------------------------------------------------------------------

symdb_summary_t valk_symdb_summary(valk_symdb_t *db) {
  symdb_summary_t sum = {0};
  sqlite3 *raw = get_db(db);

  const char *tables[] = {"files", "symbols", "types", "refs", "scopes"};
  int64_t *fields[] = {&sum.file_count, &sum.symbol_count, &sum.type_count,
                       &sum.ref_count, &sum.scope_count};

  for (int i = 0; i < 5; i++) {
    char sql[64];
    snprintf(sql, sizeof(sql), "SELECT COUNT(*) FROM %s", tables[i]);
    sqlite3_stmt *s = prep(raw, sql);
    if (s && sqlite3_step(s) == SQLITE_ROW)
      *fields[i] = sqlite3_column_int64(s, 0);
    sqlite3_finalize(s);
  }
  return sum;
}
