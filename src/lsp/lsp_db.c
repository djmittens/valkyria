#include "lsp_db.h"
#include "lsp_types.h"
#include "../../vendor/sqlite3/sqlite3.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct valk_symdb {
  sqlite3 *db;
  sqlite3_stmt *stmt_upsert_file;
  sqlite3_stmt *stmt_file_stale;
  sqlite3_stmt *stmt_file_id;
  sqlite3_stmt *stmt_insert_type;
  sqlite3_stmt *stmt_find_type;
  sqlite3_stmt *stmt_insert_type_param;
  sqlite3_stmt *stmt_insert_symbol;
  sqlite3_stmt *stmt_find_symbol;
  sqlite3_stmt *stmt_insert_ref;
  sqlite3_stmt *stmt_insert_scope;
  sqlite3_stmt *stmt_invalidate_refs;
  sqlite3_stmt *stmt_invalidate_syms;
  sqlite3_stmt *stmt_invalidate_scopes;
  sqlite3_stmt *stmt_type_display;
  sqlite3_stmt *stmt_type_kind;
  sqlite3_stmt *stmt_find_symbol_any;
};

// ---------------------------------------------------------------------------
// Schema
// ---------------------------------------------------------------------------

static const char *SCHEMA_SQL =
  "PRAGMA journal_mode=WAL;"
  "PRAGMA synchronous=NORMAL;"
  "PRAGMA foreign_keys=ON;"

  "CREATE TABLE IF NOT EXISTS files ("
  "  id INTEGER PRIMARY KEY,"
  "  path TEXT UNIQUE NOT NULL,"
  "  mtime INTEGER NOT NULL,"
  "  size INTEGER NOT NULL,"
  "  content_hash TEXT NOT NULL"
  ");"

  "CREATE TABLE IF NOT EXISTS types ("
  "  id INTEGER PRIMARY KEY,"
  "  kind INTEGER NOT NULL,"
  "  display TEXT NOT NULL,"
  "  hash TEXT UNIQUE NOT NULL"
  ");"

  "CREATE TABLE IF NOT EXISTS type_params ("
  "  type_id INTEGER NOT NULL REFERENCES types(id),"
  "  position INTEGER NOT NULL,"
  "  param_type_id INTEGER NOT NULL REFERENCES types(id),"
  "  PRIMARY KEY (type_id, position)"
  ");"

  "CREATE TABLE IF NOT EXISTS symbols ("
  "  id INTEGER PRIMARY KEY,"
  "  name TEXT NOT NULL,"
  "  file_id INTEGER NOT NULL REFERENCES files(id),"
  "  line INTEGER NOT NULL,"
  "  col INTEGER NOT NULL,"
  "  end_line INTEGER NOT NULL,"
  "  end_col INTEGER NOT NULL,"
  "  kind INTEGER NOT NULL,"
  "  type_id INTEGER REFERENCES types(id),"
  "  scope_id INTEGER REFERENCES scopes(id),"
  "  exported INTEGER NOT NULL DEFAULT 1"
  ");"

  "CREATE TABLE IF NOT EXISTS refs ("
  "  id INTEGER PRIMARY KEY,"
  "  symbol_id INTEGER NOT NULL REFERENCES symbols(id),"
  "  file_id INTEGER NOT NULL REFERENCES files(id),"
  "  line INTEGER NOT NULL,"
  "  col INTEGER NOT NULL,"
  "  kind INTEGER NOT NULL"
  ");"

  "CREATE TABLE IF NOT EXISTS scopes ("
  "  id INTEGER PRIMARY KEY,"
  "  parent_id INTEGER REFERENCES scopes(id),"
  "  file_id INTEGER NOT NULL REFERENCES files(id),"
  "  start_line INTEGER NOT NULL,"
  "  start_col INTEGER NOT NULL,"
  "  end_line INTEGER NOT NULL,"
  "  end_col INTEGER NOT NULL"
  ");"

  "CREATE INDEX IF NOT EXISTS idx_symbols_name ON symbols(name);"
  "CREATE INDEX IF NOT EXISTS idx_symbols_file ON symbols(file_id);"
  "CREATE INDEX IF NOT EXISTS idx_refs_symbol ON refs(symbol_id);"
  "CREATE INDEX IF NOT EXISTS idx_refs_file ON refs(file_id);"
  "CREATE INDEX IF NOT EXISTS idx_scopes_file ON scopes(file_id);"
  "CREATE INDEX IF NOT EXISTS idx_type_params_type ON type_params(type_id);"
  ;

// ---------------------------------------------------------------------------
// Prepared statement SQL
// ---------------------------------------------------------------------------

#define SQL_UPSERT_FILE \
  "INSERT INTO files (path, mtime, size, content_hash) VALUES (?1, ?2, ?3, ?4)" \
  " ON CONFLICT(path) DO UPDATE SET mtime=?2, size=?3, content_hash=?4" \
  " RETURNING id"

#define SQL_FILE_STALE \
  "SELECT content_hash FROM files WHERE path=?1"

#define SQL_FILE_ID \
  "SELECT id FROM files WHERE path=?1"

#define SQL_INSERT_TYPE \
  "INSERT INTO types (kind, display, hash) VALUES (?1, ?2, ?3)" \
  " ON CONFLICT(hash) DO UPDATE SET kind=kind RETURNING id"

#define SQL_FIND_TYPE \
  "SELECT id FROM types WHERE hash=?1"

#define SQL_INSERT_TYPE_PARAM \
  "INSERT OR REPLACE INTO type_params (type_id, position, param_type_id)" \
  " VALUES (?1, ?2, ?3)"

#define SQL_INSERT_SYMBOL \
  "INSERT INTO symbols (name, file_id, line, col, end_line, end_col," \
  " kind, type_id, scope_id, exported)" \
  " VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10)"

#define SQL_FIND_SYMBOL \
  "SELECT id FROM symbols WHERE name=?1 AND file_id=?2 LIMIT 1"

#define SQL_FIND_SYMBOL_ANY \
  "SELECT id FROM symbols WHERE name=?1 AND exported=1 LIMIT 1"

#define SQL_INSERT_REF \
  "INSERT INTO refs (symbol_id, file_id, line, col, kind)" \
  " VALUES (?1, ?2, ?3, ?4, ?5)"

#define SQL_INSERT_SCOPE \
  "INSERT INTO scopes (parent_id, file_id, start_line, start_col," \
  " end_line, end_col)" \
  " VALUES (?1, ?2, ?3, ?4, ?5, ?6)"

#define SQL_INVALIDATE_REFS \
  "DELETE FROM refs WHERE file_id=?1"

#define SQL_INVALIDATE_SYMS \
  "DELETE FROM symbols WHERE file_id=?1"

#define SQL_INVALIDATE_SCOPES \
  "DELETE FROM scopes WHERE file_id=?1"

#define SQL_TYPE_DISPLAY \
  "SELECT display FROM types WHERE id=?1"

#define SQL_TYPE_KIND \
  "SELECT kind FROM types WHERE id=?1"

// ---------------------------------------------------------------------------
// Raw DB access (for stats module)
// ---------------------------------------------------------------------------

sqlite3 *valk_symdb_get_raw_db(valk_symdb_t *sdb) {
  return sdb ? sdb->db : NULL;
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static bool exec(sqlite3 *db, const char *sql) {
  char *err = NULL;
  int rc = sqlite3_exec(db, sql, NULL, NULL, &err);
  if (rc != SQLITE_OK) {
    fprintf(stderr, "symdb: %s\n", err);
    sqlite3_free(err);
    return false;
  }
  return true;
}

static sqlite3_stmt *prepare(sqlite3 *db, const char *sql) {
  sqlite3_stmt *stmt = NULL;
  int rc = sqlite3_prepare_v2(db, sql, -1, &stmt, NULL);
  if (rc != SQLITE_OK) {
    fprintf(stderr, "symdb prepare: %s\n", sqlite3_errmsg(db));
    return NULL;
  }
  return stmt;
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

valk_symdb_t *valk_symdb_open(const char *db_path) {
  sqlite3 *db = NULL;
  int rc = sqlite3_open(db_path, &db);
  if (rc != SQLITE_OK) {
    fprintf(stderr, "symdb: cannot open %s: %s\n", db_path, sqlite3_errmsg(db));
    sqlite3_close(db);
    return NULL;
  }

  if (!exec(db, SCHEMA_SQL)) {
    sqlite3_close(db);
    return NULL;
  }

  valk_symdb_t *sdb = calloc(1, sizeof(valk_symdb_t));
  sdb->db = db;

  sdb->stmt_upsert_file     = prepare(db, SQL_UPSERT_FILE);
  sdb->stmt_file_stale      = prepare(db, SQL_FILE_STALE);
  sdb->stmt_file_id         = prepare(db, SQL_FILE_ID);
  sdb->stmt_insert_type     = prepare(db, SQL_INSERT_TYPE);
  sdb->stmt_find_type       = prepare(db, SQL_FIND_TYPE);
  sdb->stmt_insert_type_param = prepare(db, SQL_INSERT_TYPE_PARAM);
  sdb->stmt_insert_symbol   = prepare(db, SQL_INSERT_SYMBOL);
  sdb->stmt_find_symbol     = prepare(db, SQL_FIND_SYMBOL);
  sdb->stmt_insert_ref      = prepare(db, SQL_INSERT_REF);
  sdb->stmt_insert_scope    = prepare(db, SQL_INSERT_SCOPE);
  sdb->stmt_invalidate_refs = prepare(db, SQL_INVALIDATE_REFS);
  sdb->stmt_invalidate_syms = prepare(db, SQL_INVALIDATE_SYMS);
  sdb->stmt_invalidate_scopes = prepare(db, SQL_INVALIDATE_SCOPES);
  sdb->stmt_type_display    = prepare(db, SQL_TYPE_DISPLAY);
  sdb->stmt_type_kind       = prepare(db, SQL_TYPE_KIND);
  sdb->stmt_find_symbol_any = prepare(db, SQL_FIND_SYMBOL_ANY);

  return sdb;
}

static void finalize_stmt(sqlite3_stmt **s) {
  if (*s) { sqlite3_finalize(*s); *s = NULL; }
}

void valk_symdb_close(valk_symdb_t *db) {
  if (!db) return;
  finalize_stmt(&db->stmt_upsert_file);
  finalize_stmt(&db->stmt_file_stale);
  finalize_stmt(&db->stmt_file_id);
  finalize_stmt(&db->stmt_insert_type);
  finalize_stmt(&db->stmt_find_type);
  finalize_stmt(&db->stmt_insert_type_param);
  finalize_stmt(&db->stmt_insert_symbol);
  finalize_stmt(&db->stmt_find_symbol);
  finalize_stmt(&db->stmt_insert_ref);
  finalize_stmt(&db->stmt_insert_scope);
  finalize_stmt(&db->stmt_invalidate_refs);
  finalize_stmt(&db->stmt_invalidate_syms);
  finalize_stmt(&db->stmt_invalidate_scopes);
  finalize_stmt(&db->stmt_type_display);
  finalize_stmt(&db->stmt_type_kind);
  finalize_stmt(&db->stmt_find_symbol_any);
  sqlite3_close(db->db);
  free(db);
}

// ---------------------------------------------------------------------------
// Transactions
// ---------------------------------------------------------------------------

void valk_symdb_begin(valk_symdb_t *db)    { exec(db->db, "BEGIN"); }
void valk_symdb_commit(valk_symdb_t *db)   { exec(db->db, "COMMIT"); }
void valk_symdb_rollback(valk_symdb_t *db) { exec(db->db, "ROLLBACK"); }

// ---------------------------------------------------------------------------
// Content hash — FNV-1a 64-bit
// ---------------------------------------------------------------------------

void valk_symdb_content_hash(const char *text, size_t len,
                             char *out, size_t out_size) {
  uint64_t h = 0xcbf29ce484222325ULL;
  for (size_t i = 0; i < len; i++) {
    h ^= (uint8_t)text[i];
    h *= 0x100000001b3ULL;
  }
  snprintf(out, out_size, "%016llx", (unsigned long long)h);
}

// ---------------------------------------------------------------------------
// File tracking
// ---------------------------------------------------------------------------

symdb_file_id valk_symdb_upsert_file(valk_symdb_t *db, const char *path,
                                     int64_t mtime, int64_t size,
                                     const char *content_hash) {
  sqlite3_stmt *s = db->stmt_upsert_file;
  sqlite3_reset(s);
  sqlite3_bind_text(s, 1, path, -1, SQLITE_TRANSIENT);
  sqlite3_bind_int64(s, 2, mtime);
  sqlite3_bind_int64(s, 3, size);
  sqlite3_bind_text(s, 4, content_hash, -1, SQLITE_TRANSIENT);
  symdb_file_id result = -1;
  if (sqlite3_step(s) == SQLITE_ROW)
    result = sqlite3_column_int64(s, 0);
  sqlite3_reset(s);
  return result;
}

bool valk_symdb_file_stale(valk_symdb_t *db, const char *path,
                           int64_t mtime, int64_t size,
                           const char *content_hash) {
  (void)mtime; (void)size;
  sqlite3_stmt *s = db->stmt_file_stale;
  sqlite3_reset(s);
  sqlite3_bind_text(s, 1, path, -1, SQLITE_TRANSIENT);
  bool stale = true;
  if (sqlite3_step(s) == SQLITE_ROW) {
    const char *stored = (const char *)sqlite3_column_text(s, 0);
    stale = strcmp(stored, content_hash) != 0;
  }
  sqlite3_reset(s);
  return stale;
}

symdb_file_id valk_symdb_file_id(valk_symdb_t *db, const char *path) {
  sqlite3_stmt *s = db->stmt_file_id;
  sqlite3_reset(s);
  sqlite3_bind_text(s, 1, path, -1, SQLITE_TRANSIENT);
  symdb_file_id result = -1;
  if (sqlite3_step(s) == SQLITE_ROW)
    result = sqlite3_column_int64(s, 0);
  sqlite3_reset(s);
  return result;
}

void valk_symdb_invalidate_file(valk_symdb_t *db, symdb_file_id file_id) {
  sqlite3_stmt *stmts[] = {
    db->stmt_invalidate_refs,
    db->stmt_invalidate_scopes,
    db->stmt_invalidate_syms,
  };
  for (int i = 0; i < 3; i++) {
    sqlite3_reset(stmts[i]);
    sqlite3_bind_int64(stmts[i], 1, file_id);
    sqlite3_step(stmts[i]);
    sqlite3_reset(stmts[i]);
  }
}

// ---------------------------------------------------------------------------
// Type interning — content-addressed via structural hash
//
// Hash is computed recursively from type structure. Type variables are
// normalized to positional names (V0, V1, ...) in encounter order so that
// alpha-equivalent types produce the same hash.
// ---------------------------------------------------------------------------

typedef struct {
  int ids[64];
  int count;
} type_var_norm_t;

static int norm_var(type_var_norm_t *n, int id) {
  for (int i = 0; i < n->count; i++)
    if (n->ids[i] == id) return i;
  if (n->count < 64) n->ids[n->count++] = id;
  return n->count - 1;
}

static void type_hash_str(const valk_type_t *ty, type_var_norm_t *norm,
                          char *buf, size_t buf_size) {
  if (!ty) { snprintf(buf, buf_size, "?"); return; }
  valk_type_t *r = ty_resolve((valk_type_t *)ty);

  int pos = 0;
  char sub[256];

  switch (r->kind) {
  case TY_NUM:   snprintf(buf, buf_size, "N"); return;
  case TY_STR:   snprintf(buf, buf_size, "S"); return;
  case TY_SYM:   snprintf(buf, buf_size, "Y"); return;
  case TY_NIL:   snprintf(buf, buf_size, "0"); return;
  case TY_ERR:   snprintf(buf, buf_size, "E"); return;
  case TY_ANY:   snprintf(buf, buf_size, "*"); return;
  case TY_NEVER: snprintf(buf, buf_size, "!"); return;

  case TY_LIST:
    type_hash_str(r->list.elem, norm, sub, sizeof(sub));
    snprintf(buf, buf_size, "L:%s", sub);
    return;

  case TY_HANDLE:
    type_hash_str(r->handle.inner, norm, sub, sizeof(sub));
    snprintf(buf, buf_size, "H:%s", sub);
    return;

  case TY_REF:
    snprintf(buf, buf_size, "R:%s", r->ref.tag ? r->ref.tag : "");
    return;

  case TY_VAR:
    snprintf(buf, buf_size, "V%d", norm_var(norm, r->var.id));
    return;

  case TY_FUN:
    pos += snprintf(buf + pos, buf_size - pos, "F(");
    for (int i = 0; i < r->fun.param_count; i++) {
      type_hash_str(r->fun.params[i], norm, sub, sizeof(sub));
      pos += snprintf(buf + pos, buf_size - pos, "%s%s",
                      i ? "," : "", sub);
    }
    if (r->fun.variadic) pos += snprintf(buf + pos, buf_size - pos, "...");
    type_hash_str(r->fun.ret, norm, sub, sizeof(sub));
    snprintf(buf + pos, buf_size - pos, "->%s)", sub);
    return;

  case TY_UNION:
    pos += snprintf(buf + pos, buf_size - pos, "U(");
    for (int i = 0; i < r->onion.count; i++) {
      type_hash_str(r->onion.members[i], norm, sub, sizeof(sub));
      pos += snprintf(buf + pos, buf_size - pos, "%s%s",
                      i ? "|" : "", sub);
    }
    snprintf(buf + pos, buf_size - pos, ")");
    return;

  case TY_NAMED:
    pos += snprintf(buf + pos, buf_size - pos, "D:%s(", r->named.name);
    for (int i = 0; i < r->named.param_count; i++) {
      type_hash_str(r->named.params[i], norm, sub, sizeof(sub));
      pos += snprintf(buf + pos, buf_size - pos, "%s%s",
                      i ? "," : "", sub);
    }
    snprintf(buf + pos, buf_size - pos, ")");
    return;

  default:
    snprintf(buf, buf_size, "?");
    return;
  }
}

static void hash_fnv1a(const char *s, char *out, size_t out_size) {
  uint64_t h = 0xcbf29ce484222325ULL;
  for (const char *p = s; *p; p++) {
    h ^= (uint8_t)*p;
    h *= 0x100000001b3ULL;
  }
  snprintf(out, out_size, "%016llx", (unsigned long long)h);
}

static symdb_type_id intern_type_inner(valk_symdb_t *db, const valk_type_t *ty,
                                       type_var_norm_t *norm);

static void insert_type_params(valk_symdb_t *db, symdb_type_id parent_id,
                               const valk_type_t **params, int count,
                               type_var_norm_t *norm) {
  for (int i = 0; i < count; i++) {
    symdb_type_id pid = intern_type_inner(db, params[i], norm);
    sqlite3_stmt *s = db->stmt_insert_type_param;
    sqlite3_reset(s);
    sqlite3_bind_int64(s, 1, parent_id);
    sqlite3_bind_int(s, 2, i);
    sqlite3_bind_int64(s, 3, pid);
    sqlite3_step(s);
    sqlite3_reset(s);
  }
}

static symdb_type_id intern_type_inner(valk_symdb_t *db, const valk_type_t *ty,
                                       type_var_norm_t *norm) {
  char hash_input[512];
  type_hash_str(ty, norm, hash_input, sizeof(hash_input));

  char hash[32];
  hash_fnv1a(hash_input, hash, sizeof(hash));

  sqlite3_stmt *find = db->stmt_find_type;
  sqlite3_reset(find);
  sqlite3_bind_text(find, 1, hash, -1, SQLITE_TRANSIENT);
  if (sqlite3_step(find) == SQLITE_ROW) {
    symdb_type_id existing = sqlite3_column_int64(find, 0);
    sqlite3_reset(find);
    return existing;
  }
  sqlite3_reset(find);

  char *display = valk_type_display_pretty(ty);
  valk_type_t *r = ty_resolve((valk_type_t *)ty);

  sqlite3_stmt *ins = db->stmt_insert_type;
  sqlite3_reset(ins);
  sqlite3_bind_int(ins, 1, r ? r->kind : TY_ANY);
  sqlite3_bind_text(ins, 2, display, -1, SQLITE_TRANSIENT);
  sqlite3_bind_text(ins, 3, hash, -1, SQLITE_TRANSIENT);
  free(display);

  symdb_type_id type_id = -1;
  if (sqlite3_step(ins) == SQLITE_ROW)
    type_id = sqlite3_column_int64(ins, 0);
  sqlite3_reset(ins);

  if (type_id < 0) return -1;

  if (r) {
    switch (r->kind) {
    case TY_LIST:
      insert_type_params(db, type_id,
                         (const valk_type_t *[]){r->list.elem}, 1, norm);
      break;
    case TY_HANDLE:
      insert_type_params(db, type_id,
                         (const valk_type_t *[]){r->handle.inner}, 1, norm);
      break;
    case TY_FUN:
      insert_type_params(db, type_id,
                         (const valk_type_t **)r->fun.params,
                         r->fun.param_count, norm);
      if (r->fun.ret)
        insert_type_params(db, type_id,
                           (const valk_type_t *[]){r->fun.ret}, 1, norm);
      break;
    case TY_UNION:
      insert_type_params(db, type_id,
                         (const valk_type_t **)r->onion.members,
                         r->onion.count, norm);
      break;
    case TY_NAMED:
      insert_type_params(db, type_id,
                         (const valk_type_t **)r->named.params,
                         r->named.param_count, norm);
      break;
    default:
      break;
    }
  }

  return type_id;
}

symdb_type_id valk_symdb_intern_type(valk_symdb_t *db, const valk_type_t *ty) {
  type_var_norm_t norm = {.count = 0};
  return intern_type_inner(db, ty, &norm);
}

char *valk_symdb_type_display(valk_symdb_t *db, symdb_type_id type_id) {
  sqlite3_stmt *s = db->stmt_type_display;
  sqlite3_reset(s);
  sqlite3_bind_int64(s, 1, type_id);
  char *result = NULL;
  if (sqlite3_step(s) == SQLITE_ROW)
    result = strdup((const char *)sqlite3_column_text(s, 0));
  sqlite3_reset(s);
  return result;
}

int valk_symdb_type_kind(valk_symdb_t *db, symdb_type_id type_id) {
  sqlite3_stmt *s = db->stmt_type_kind;
  sqlite3_reset(s);
  sqlite3_bind_int64(s, 1, type_id);
  int result = -1;
  if (sqlite3_step(s) == SQLITE_ROW)
    result = sqlite3_column_int(s, 0);
  sqlite3_reset(s);
  return result;
}

// ---------------------------------------------------------------------------
// Symbols
// ---------------------------------------------------------------------------

symdb_sym_id valk_symdb_add_symbol(valk_symdb_t *db, const char *name,
                                   symdb_file_id file_id,
                                   int line, int col,
                                   int end_line, int end_col,
                                   symdb_sym_kind_e kind,
                                   symdb_type_id type_id,
                                   symdb_scope_id scope_id,
                                   bool exported) {
  sqlite3_stmt *s = db->stmt_insert_symbol;
  sqlite3_reset(s);
  sqlite3_bind_text(s, 1, name, -1, SQLITE_TRANSIENT);
  sqlite3_bind_int64(s, 2, file_id);
  sqlite3_bind_int(s, 3, line);
  sqlite3_bind_int(s, 4, col);
  sqlite3_bind_int(s, 5, end_line);
  sqlite3_bind_int(s, 6, end_col);
  sqlite3_bind_int(s, 7, kind);
  if (type_id >= 0)
    sqlite3_bind_int64(s, 8, type_id);
  else
    sqlite3_bind_null(s, 8);
  if (scope_id >= 0)
    sqlite3_bind_int64(s, 9, scope_id);
  else
    sqlite3_bind_null(s, 9);
  sqlite3_bind_int(s, 10, exported ? 1 : 0);
  sqlite3_step(s);
  symdb_sym_id result = sqlite3_last_insert_rowid(db->db);
  sqlite3_reset(s);
  return result;
}

symdb_sym_id valk_symdb_find_symbol(valk_symdb_t *db, const char *name,
                                    symdb_file_id file_id) {
  sqlite3_stmt *s = db->stmt_find_symbol;
  sqlite3_reset(s);
  sqlite3_bind_text(s, 1, name, -1, SQLITE_TRANSIENT);
  sqlite3_bind_int64(s, 2, file_id);
  symdb_sym_id result = -1;
  if (sqlite3_step(s) == SQLITE_ROW)
    result = sqlite3_column_int64(s, 0);
  sqlite3_reset(s);
  return result;
}

symdb_sym_id valk_symdb_find_symbol_any(valk_symdb_t *db, const char *name) {
  sqlite3_stmt *s = db->stmt_find_symbol_any;
  sqlite3_reset(s);
  sqlite3_bind_text(s, 1, name, -1, SQLITE_TRANSIENT);
  symdb_sym_id result = -1;
  if (sqlite3_step(s) == SQLITE_ROW)
    result = sqlite3_column_int64(s, 0);
  sqlite3_reset(s);
  return result;
}

// ---------------------------------------------------------------------------
// References
// ---------------------------------------------------------------------------

void valk_symdb_add_ref(valk_symdb_t *db, symdb_sym_id symbol_id,
                        symdb_file_id file_id, int line, int col,
                        symdb_ref_kind_e kind) {
  sqlite3_stmt *s = db->stmt_insert_ref;
  sqlite3_reset(s);
  sqlite3_bind_int64(s, 1, symbol_id);
  sqlite3_bind_int64(s, 2, file_id);
  sqlite3_bind_int(s, 3, line);
  sqlite3_bind_int(s, 4, col);
  sqlite3_bind_int(s, 5, kind);
  sqlite3_step(s);
  sqlite3_reset(s);
}

// ---------------------------------------------------------------------------
// Scopes
// ---------------------------------------------------------------------------

symdb_scope_id valk_symdb_add_scope(valk_symdb_t *db, symdb_scope_id parent_id,
                                    symdb_file_id file_id,
                                    int start_line, int start_col,
                                    int end_line, int end_col) {
  sqlite3_stmt *s = db->stmt_insert_scope;
  sqlite3_reset(s);
  if (parent_id >= 0)
    sqlite3_bind_int64(s, 1, parent_id);
  else
    sqlite3_bind_null(s, 1);
  sqlite3_bind_int64(s, 2, file_id);
  sqlite3_bind_int(s, 3, start_line);
  sqlite3_bind_int(s, 4, start_col);
  sqlite3_bind_int(s, 5, end_line);
  sqlite3_bind_int(s, 6, end_col);
  sqlite3_step(s);
  symdb_scope_id result = sqlite3_last_insert_rowid(db->db);
  sqlite3_reset(s);
  return result;
}

// ---------------------------------------------------------------------------
// Queries
// ---------------------------------------------------------------------------

size_t valk_symdb_find_refs(valk_symdb_t *db, symdb_sym_id symbol_id,
                            symdb_ref_result_t **out) {
  const char *sql = "SELECT file_id, line, col, kind FROM refs"
                    " WHERE symbol_id=?1 ORDER BY file_id, line, col";
  sqlite3_stmt *s = prepare(db->db, sql);
  sqlite3_bind_int64(s, 1, symbol_id);

  size_t count = 0, cap = 16;
  symdb_ref_result_t *arr = malloc(cap * sizeof(*arr));

  while (sqlite3_step(s) == SQLITE_ROW) {
    if (count >= cap) { cap *= 2; arr = realloc(arr, cap * sizeof(*arr)); }
    arr[count++] = (symdb_ref_result_t){
      .file_id = sqlite3_column_int64(s, 0),
      .line    = sqlite3_column_int(s, 1),
      .col     = sqlite3_column_int(s, 2),
      .kind    = sqlite3_column_int(s, 3),
    };
  }
  sqlite3_finalize(s);
  *out = arr;
  return count;
}

size_t valk_symdb_file_symbols(valk_symdb_t *db, symdb_file_id file_id,
                               symdb_sym_result_t **out) {
  const char *sql = "SELECT id, name, line, col, kind, type_id, exported"
                    " FROM symbols WHERE file_id=?1 ORDER BY line, col";
  sqlite3_stmt *s = prepare(db->db, sql);
  sqlite3_bind_int64(s, 1, file_id);

  size_t count = 0, cap = 16;
  symdb_sym_result_t *arr = malloc(cap * sizeof(*arr));

  while (sqlite3_step(s) == SQLITE_ROW) {
    if (count >= cap) { cap *= 2; arr = realloc(arr, cap * sizeof(*arr)); }
    arr[count].id       = sqlite3_column_int64(s, 0);
    arr[count].name     = strdup((const char *)sqlite3_column_text(s, 1));
    arr[count].line     = sqlite3_column_int(s, 2);
    arr[count].col      = sqlite3_column_int(s, 3);
    arr[count].kind     = sqlite3_column_int(s, 4);
    arr[count].type_id  = sqlite3_column_type(s, 5) == SQLITE_NULL
                            ? -1 : sqlite3_column_int64(s, 5);
    arr[count].exported = sqlite3_column_int(s, 6) != 0;
    count++;
  }
  sqlite3_finalize(s);
  *out = arr;
  return count;
}
