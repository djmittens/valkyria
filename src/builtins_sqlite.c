#include "builtins_internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../vendor/sqlite3/sqlite3.h"

#define SQLITE_REF_TYPE "sqlite_db"
#define SQLITE_STMT_REF_TYPE "sqlite_stmt"

static void sqlite_db_free(void *ptr) {
  sqlite3 *db = ptr;
  if (db) sqlite3_close(db);
}

static void sqlite_stmt_free(void *ptr) {
  sqlite3_stmt *stmt = ptr;
  if (stmt) sqlite3_finalize(stmt);
}

#define LVAL_ASSERT_SQLITE_DB(args, val)                                      \
  do {                                                                        \
    if (LVAL_TYPE(val) != LVAL_REF ||                                         \
        strcmp((val)->ref.type, SQLITE_REF_TYPE) != 0)                        \
      LVAL_RAISE(args, "Expected sqlite_db reference, got %s",               \
                 valk_ltype_name(LVAL_TYPE(val)));                            \
  } while (0)

#define LVAL_ASSERT_SQLITE_STMT(args, val)                                    \
  do {                                                                        \
    if (LVAL_TYPE(val) != LVAL_REF ||                                         \
        strcmp((val)->ref.type, SQLITE_STMT_REF_TYPE) != 0)                   \
      LVAL_RAISE(args, "Expected sqlite_stmt reference, got %s",             \
                 valk_ltype_name(LVAL_TYPE(val)));                            \
  } while (0)

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

static int bind_params(sqlite3_stmt *stmt, valk_lval_t *args, u64 start) {
  u64 count = valk_lval_list_count(args);
  int param_idx = 1;
  for (u64 i = start; i < count; i++, param_idx++) {
    valk_lval_t *v = valk_lval_list_nth(args, i);
    switch (LVAL_TYPE(v)) {
      case LVAL_NUM:
        sqlite3_bind_int64(stmt, param_idx, v->num);
        break;
      case LVAL_STR:
        sqlite3_bind_text(stmt, param_idx, v->str, -1, SQLITE_TRANSIENT);
        break;
      case LVAL_NIL:
        sqlite3_bind_null(stmt, param_idx);
        break;
      default:
        return -1;
    }
  }
  return 0;
}

static valk_lval_t *read_column(sqlite3_stmt *stmt, int i) {
  switch (sqlite3_column_type(stmt, i)) {
    case SQLITE_INTEGER:
      return valk_lval_num(sqlite3_column_int64(stmt, i));
    case SQLITE_TEXT:
      return valk_lval_str((const char *)sqlite3_column_text(stmt, i));
    case SQLITE_FLOAT:
      return valk_lval_num((long)sqlite3_column_double(stmt, i));
    case SQLITE_NULL:
      return valk_lval_nil();
    default: // LCOV_EXCL_LINE
      return valk_lval_nil(); // LCOV_EXCL_LINE
  }
}

static valk_lval_t *build_row_plist(sqlite3_stmt *stmt, int ncols,
                                    char **col_keys) {
  valk_lval_t **fields = malloc(ncols * 2 * sizeof(valk_lval_t *));
  for (int i = 0; i < ncols; i++) {
    fields[i * 2] = valk_lval_sym(col_keys[i]);
    fields[i * 2 + 1] = read_column(stmt, i);
  }
  valk_lval_t *row = valk_lval_qlist(fields, ncols * 2);
  free(fields);
  return row;
}

static char **build_col_keys(sqlite3_stmt *stmt, int ncols) {
  char **keys = malloc(ncols * sizeof(char *));
  for (int i = 0; i < ncols; i++) {
    const char *name = sqlite3_column_name(stmt, i);
    keys[i] = malloc(strlen(name) + 2);
    keys[i][0] = ':';
    strcpy(keys[i] + 1, name);
  }
  return keys;
}

static void free_col_keys(char **keys, int ncols) {
  for (int i = 0; i < ncols; i++) free(keys[i]);
  free(keys);
}

typedef struct {
  sqlite3 *db;
  sqlite3_stmt *stmt;
  int ncols;
  char **col_keys;
} query_ctx_t;

static valk_lval_t *prepare_query(valk_lval_t *a, const char *fn_name,
                                  query_ctx_t *ctx) {
  valk_lval_t *db_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_DB(a, db_ref);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);

  ctx->db = db_ref->ref.ptr;
  if (!ctx->db) LVAL_RAISE(a, "%s: database is closed", fn_name);

  const char *sql = valk_lval_list_nth(a, 1)->str;
  ctx->stmt = nullptr;
  int rc = sqlite3_prepare_v2(ctx->db, sql, -1, &ctx->stmt, nullptr);
  if (rc != SQLITE_OK) {
    LVAL_RAISE(a, "%s: %s", fn_name, sqlite3_errmsg(ctx->db));
  }

  if (bind_params(ctx->stmt, a, 2) < 0) {
    sqlite3_finalize(ctx->stmt);
    LVAL_RAISE(a, "%s: unsupported bind parameter type", fn_name);
  }

  ctx->ncols = sqlite3_column_count(ctx->stmt);
  ctx->col_keys = build_col_keys(ctx->stmt, ctx->ncols);
  return nullptr;
}

static void cleanup_query(query_ctx_t *ctx) {
  free_col_keys(ctx->col_keys, ctx->ncols);
  sqlite3_finalize(ctx->stmt);
}

// ---------------------------------------------------------------------------
// sqlite/open
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_open(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GE(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char *path = valk_lval_list_nth(a, 0)->str;
  sqlite3 *db = nullptr;
  int rc = sqlite3_open(path, &db);
  if (rc != SQLITE_OK) {
    const char *msg = sqlite3_errmsg(db);
    valk_lval_t *err = valk_lval_err("sqlite/open: %s", msg);
    sqlite3_close(db);
    return err;
  }

  sqlite3_busy_timeout(db, 5000);

  return valk_lval_ref(SQLITE_REF_TYPE, db, sqlite_db_free);
}

// ---------------------------------------------------------------------------
// sqlite/close
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_close(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *db_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_DB(a, db_ref);

  sqlite3 *db = db_ref->ref.ptr;
  if (db) {
    sqlite3_close(db);
    db_ref->ref.ptr = nullptr;
  }

  return valk_lval_nil();
}

// ---------------------------------------------------------------------------
// sqlite/exec — execute DML/DDL, return rows changed
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_exec(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GE(a, a, 2);
  valk_lval_t *db_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_DB(a, db_ref);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);

  sqlite3 *db = db_ref->ref.ptr;
  if (!db) LVAL_RAISE(a, "sqlite/exec: database is closed");

  const char *sql = valk_lval_list_nth(a, 1)->str;
  sqlite3_stmt *stmt = nullptr;
  int rc = sqlite3_prepare_v2(db, sql, -1, &stmt, nullptr);
  if (rc != SQLITE_OK) {
    LVAL_RAISE(a, "sqlite/exec: %s", sqlite3_errmsg(db));
  }

  if (bind_params(stmt, a, 2) < 0) {
    sqlite3_finalize(stmt);
    LVAL_RAISE(a, "sqlite/exec: unsupported bind parameter type");
  }

  rc = sqlite3_step(stmt);
  if (rc != SQLITE_DONE && rc != SQLITE_ROW) {
    const char *msg = sqlite3_errmsg(db);
    sqlite3_finalize(stmt);
    LVAL_RAISE(a, "sqlite/exec: %s", msg);
  }

  while (rc == SQLITE_ROW) rc = sqlite3_step(stmt);

  sqlite3_finalize(stmt);
  return valk_lval_num(sqlite3_changes(db));
}

// ---------------------------------------------------------------------------
// sqlite/exec-script — execute multiple statements (schema migrations)
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_exec_script(valk_lenv_t *e,
                                                     valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *db_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_DB(a, db_ref);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);

  sqlite3 *db = db_ref->ref.ptr;
  if (!db) LVAL_RAISE(a, "sqlite/exec-script: database is closed");

  const char *sql = valk_lval_list_nth(a, 1)->str;
  char *errmsg = nullptr;
  int rc = sqlite3_exec(db, sql, nullptr, nullptr, &errmsg);
  if (rc != SQLITE_OK) {
    valk_lval_t *err =
        valk_lval_err("sqlite/exec-script: %s", errmsg ? errmsg : "unknown");
    sqlite3_free(errmsg);
    return err;
  }

  return valk_lval_nil();
}

// ---------------------------------------------------------------------------
// sqlite/query — SELECT returning all rows as list of plists
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_query(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GE(a, a, 2);

  query_ctx_t ctx;
  valk_lval_t *err = prepare_query(a, "sqlite/query", &ctx);
  if (err) return err;

  size_t row_cap = 64;
  size_t row_count = 0;
  valk_lval_t **rows = malloc(row_cap * sizeof(valk_lval_t *));

  int rc;
  while ((rc = sqlite3_step(ctx.stmt)) == SQLITE_ROW) {
    if (row_count >= row_cap) {
      row_cap *= 2;
      rows = realloc(rows, row_cap * sizeof(valk_lval_t *));
    }
    rows[row_count++] = build_row_plist(ctx.stmt, ctx.ncols, ctx.col_keys);
  }

  if (rc != SQLITE_DONE) {
    const char *msg = sqlite3_errmsg(ctx.db);
    free(rows);
    cleanup_query(&ctx);
    LVAL_RAISE(a, "sqlite/query: %s", msg);
  }

  cleanup_query(&ctx);
  valk_lval_t *result = valk_lval_qlist(rows, row_count);
  free(rows);
  return result;
}

// ---------------------------------------------------------------------------
// sqlite/query-row — SELECT returning exactly one row (errors otherwise)
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_query_row(valk_lenv_t *e,
                                                   valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GE(a, a, 2);

  query_ctx_t ctx;
  valk_lval_t *err = prepare_query(a, "sqlite/query-row", &ctx);
  if (err) return err;

  int rc = sqlite3_step(ctx.stmt);
  if (rc != SQLITE_ROW) {
    cleanup_query(&ctx);
    LVAL_RAISE(a, "sqlite/query-row: expected 1 row, got 0");
  }

  valk_lval_t *row = build_row_plist(ctx.stmt, ctx.ncols, ctx.col_keys);

  rc = sqlite3_step(ctx.stmt);
  if (rc == SQLITE_ROW) {
    cleanup_query(&ctx);
    LVAL_RAISE(a, "sqlite/query-row: expected 1 row, got multiple");
  }

  cleanup_query(&ctx);
  return row;
}

// ---------------------------------------------------------------------------
// sqlite/query-maybe — SELECT returning 0 or 1 row (nil if none)
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_query_maybe(valk_lenv_t *e,
                                                     valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GE(a, a, 2);

  query_ctx_t ctx;
  valk_lval_t *err = prepare_query(a, "sqlite/query-maybe", &ctx);
  if (err) return err;

  int rc = sqlite3_step(ctx.stmt);
  if (rc == SQLITE_DONE) {
    cleanup_query(&ctx);
    return valk_lval_nil();
  }
  if (rc != SQLITE_ROW) {
    const char *msg = sqlite3_errmsg(ctx.db);
    cleanup_query(&ctx);
    LVAL_RAISE(a, "sqlite/query-maybe: %s", msg);
  }

  valk_lval_t *row = build_row_plist(ctx.stmt, ctx.ncols, ctx.col_keys);

  rc = sqlite3_step(ctx.stmt);
  if (rc == SQLITE_ROW) {
    cleanup_query(&ctx);
    LVAL_RAISE(a, "sqlite/query-maybe: expected 0 or 1 row, got multiple");
  }

  cleanup_query(&ctx);
  return row;
}

// ---------------------------------------------------------------------------
// sqlite/query-value — SELECT returning a single scalar value
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_query_value(valk_lenv_t *e,
                                                     valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GE(a, a, 2);

  query_ctx_t ctx;
  valk_lval_t *err = prepare_query(a, "sqlite/query-value", &ctx);
  if (err) return err;

  if (ctx.ncols != 1) {
    cleanup_query(&ctx);
    LVAL_RAISE(a, "sqlite/query-value: expected 1 column, got %d", ctx.ncols);
  }

  int rc = sqlite3_step(ctx.stmt);
  if (rc != SQLITE_ROW) {
    cleanup_query(&ctx);
    LVAL_RAISE(a, "sqlite/query-value: expected 1 row, got 0");
  }

  valk_lval_t *val = read_column(ctx.stmt, 0);

  rc = sqlite3_step(ctx.stmt);
  if (rc == SQLITE_ROW) {
    cleanup_query(&ctx);
    LVAL_RAISE(a, "sqlite/query-value: expected 1 row, got multiple");
  }

  cleanup_query(&ctx);
  return val;
}

// ---------------------------------------------------------------------------
// sqlite/prepare, sqlite/bind, sqlite/step, sqlite/finalize
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_prepare(valk_lenv_t *e,
                                                 valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *db_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_DB(a, db_ref);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_STR);

  sqlite3 *db = db_ref->ref.ptr;
  if (!db) LVAL_RAISE(a, "sqlite/prepare: database is closed");

  const char *sql = valk_lval_list_nth(a, 1)->str;
  sqlite3_stmt *stmt = nullptr;
  int rc = sqlite3_prepare_v2(db, sql, -1, &stmt, nullptr);
  if (rc != SQLITE_OK) {
    LVAL_RAISE(a, "sqlite/prepare: %s", sqlite3_errmsg(db));
  }

  return valk_lval_ref(SQLITE_STMT_REF_TYPE, stmt, sqlite_stmt_free);
}

static valk_lval_t *valk_builtin_sqlite_bind(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_GE(a, a, 1);
  valk_lval_t *stmt_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_STMT(a, stmt_ref);

  sqlite3_stmt *stmt = stmt_ref->ref.ptr;
  if (!stmt) LVAL_RAISE(a, "sqlite/bind: statement is finalized");

  sqlite3_reset(stmt);
  sqlite3_clear_bindings(stmt);

  if (bind_params(stmt, a, 1) < 0) {
    LVAL_RAISE(a, "sqlite/bind: unsupported parameter type");
  }

  return stmt_ref;
}

static valk_lval_t *valk_builtin_sqlite_step(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *stmt_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_STMT(a, stmt_ref);

  sqlite3_stmt *stmt = stmt_ref->ref.ptr;
  if (!stmt) LVAL_RAISE(a, "sqlite/step: statement is finalized");

  int rc = sqlite3_step(stmt);
  if (rc == SQLITE_DONE) return valk_lval_nil();
  if (rc != SQLITE_ROW) {
    sqlite3 *db = sqlite3_db_handle(stmt);
    LVAL_RAISE(a, "sqlite/step: %s", sqlite3_errmsg(db));
  }

  int ncols = sqlite3_column_count(stmt);
  char **col_keys = build_col_keys(stmt, ncols);
  valk_lval_t *row = build_row_plist(stmt, ncols, col_keys);
  free_col_keys(col_keys, ncols);
  return row;
}

static valk_lval_t *valk_builtin_sqlite_finalize(valk_lenv_t *e,
                                                  valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *stmt_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_STMT(a, stmt_ref);

  sqlite3_stmt *stmt = stmt_ref->ref.ptr;
  if (stmt) {
    sqlite3_finalize(stmt);
    stmt_ref->ref.ptr = nullptr;
  }

  return valk_lval_nil();
}

// ---------------------------------------------------------------------------
// sqlite/last-insert-id, sqlite/changes, sqlite/busy-timeout
// ---------------------------------------------------------------------------

static valk_lval_t *valk_builtin_sqlite_last_insert_id(valk_lenv_t *e,
                                                        valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *db_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_DB(a, db_ref);

  sqlite3 *db = db_ref->ref.ptr;
  if (!db) LVAL_RAISE(a, "sqlite/last-insert-id: database is closed");

  return valk_lval_num(sqlite3_last_insert_rowid(db));
}

static valk_lval_t *valk_builtin_sqlite_changes(valk_lenv_t *e,
                                                 valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *db_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_DB(a, db_ref);

  sqlite3 *db = db_ref->ref.ptr;
  if (!db) LVAL_RAISE(a, "sqlite/changes: database is closed");

  return valk_lval_num(sqlite3_changes(db));
}

static valk_lval_t *valk_builtin_sqlite_busy_timeout(valk_lenv_t *e,
                                                      valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *db_ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_SQLITE_DB(a, db_ref);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);

  sqlite3 *db = db_ref->ref.ptr;
  if (!db) LVAL_RAISE(a, "sqlite/busy-timeout: database is closed");

  sqlite3_busy_timeout(db, (int)valk_lval_list_nth(a, 1)->num);
  return valk_lval_nil();
}

// ---------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------

void valk_register_sqlite_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "sqlite/open", valk_builtin_sqlite_open);
  valk_lenv_put_builtin(env, "sqlite/close", valk_builtin_sqlite_close);
  valk_lenv_put_builtin(env, "sqlite/exec", valk_builtin_sqlite_exec);
  valk_lenv_put_builtin(env, "sqlite/exec-script", valk_builtin_sqlite_exec_script);
  valk_lenv_put_builtin(env, "sqlite/query", valk_builtin_sqlite_query);
  valk_lenv_put_builtin(env, "sqlite/query-row", valk_builtin_sqlite_query_row);
  valk_lenv_put_builtin(env, "sqlite/query-maybe", valk_builtin_sqlite_query_maybe);
  valk_lenv_put_builtin(env, "sqlite/query-value", valk_builtin_sqlite_query_value);
  valk_lenv_put_builtin(env, "sqlite/prepare", valk_builtin_sqlite_prepare);
  valk_lenv_put_builtin(env, "sqlite/bind", valk_builtin_sqlite_bind);
  valk_lenv_put_builtin(env, "sqlite/step", valk_builtin_sqlite_step);
  valk_lenv_put_builtin(env, "sqlite/finalize", valk_builtin_sqlite_finalize);
  valk_lenv_put_builtin(env, "sqlite/last-insert-id", valk_builtin_sqlite_last_insert_id);
  valk_lenv_put_builtin(env, "sqlite/changes", valk_builtin_sqlite_changes);
  valk_lenv_put_builtin(env, "sqlite/busy-timeout", valk_builtin_sqlite_busy_timeout);
}
