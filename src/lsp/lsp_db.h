#pragma once
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct valk_type valk_type_t;
typedef struct valk_symdb valk_symdb_t;

// Symbol kinds
typedef enum {
  SYMKIND_FUNCTION = 1,
  SYMKIND_VARIABLE,
  SYMKIND_TYPE,
  SYMKIND_CONSTRUCTOR,
  SYMKIND_MACRO,
  SYMKIND_BUILTIN,
} symdb_sym_kind_e;

// Reference kinds
typedef enum {
  REF_CALL = 1,
  REF_READ,
  REF_WRITE,
  REF_TYPE,
} symdb_ref_kind_e;

// Opaque IDs (SQLite rowids)
typedef int64_t symdb_file_id;
typedef int64_t symdb_type_id;
typedef int64_t symdb_sym_id;
typedef int64_t symdb_scope_id;

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

valk_symdb_t *valk_symdb_open(const char *db_path);
void valk_symdb_close(valk_symdb_t *db);

// ---------------------------------------------------------------------------
// Transaction control — batch file updates for performance
// ---------------------------------------------------------------------------

void valk_symdb_begin(valk_symdb_t *db);
void valk_symdb_commit(valk_symdb_t *db);
void valk_symdb_rollback(valk_symdb_t *db);

// ---------------------------------------------------------------------------
// File tracking — staleness detection via content hash
// ---------------------------------------------------------------------------

symdb_file_id valk_symdb_upsert_file(valk_symdb_t *db, const char *path,
                                     int64_t mtime, int64_t size,
                                     const char *content_hash);
bool valk_symdb_file_stale(valk_symdb_t *db, const char *path,
                           int64_t mtime, int64_t size,
                           const char *content_hash);
symdb_file_id valk_symdb_file_id(valk_symdb_t *db, const char *path);
void valk_symdb_invalidate_file(valk_symdb_t *db, symdb_file_id file_id);

// ---------------------------------------------------------------------------
// Type interning — content-addressed deduplication
//
// Interns a valk_type_t into the DB. Returns the same ID for structurally
// identical types. e.g. List[Str] always returns the same type_id.
// ---------------------------------------------------------------------------

symdb_type_id valk_symdb_intern_type(valk_symdb_t *db, const valk_type_t *ty);

// Lookup a type's display string by id. Caller must free().
char *valk_symdb_type_display(valk_symdb_t *db, symdb_type_id type_id);

// Lookup a type's kind by id. Returns -1 if not found.
int valk_symdb_type_kind(valk_symdb_t *db, symdb_type_id type_id);

// ---------------------------------------------------------------------------
// Symbols — definitions in source files
// ---------------------------------------------------------------------------

symdb_sym_id valk_symdb_add_symbol(valk_symdb_t *db, const char *name,
                                   symdb_file_id file_id,
                                   int line, int col,
                                   int end_line, int end_col,
                                   symdb_sym_kind_e kind,
                                   symdb_type_id type_id,
                                   symdb_scope_id scope_id,
                                   bool exported);

symdb_sym_id valk_symdb_find_symbol(valk_symdb_t *db, const char *name,
                                     symdb_file_id file_id);
symdb_sym_id valk_symdb_find_symbol_any(valk_symdb_t *db, const char *name);

// ---------------------------------------------------------------------------
// References — uses of symbols
// ---------------------------------------------------------------------------

void valk_symdb_add_ref(valk_symdb_t *db, symdb_sym_id symbol_id,
                        symdb_file_id file_id, int line, int col,
                        symdb_ref_kind_e kind);

// ---------------------------------------------------------------------------
// Scopes — lexical scope tree
// ---------------------------------------------------------------------------

symdb_scope_id valk_symdb_add_scope(valk_symdb_t *db, symdb_scope_id parent_id,
                                    symdb_file_id file_id,
                                    int start_line, int start_col,
                                    int end_line, int end_col);

// ---------------------------------------------------------------------------
// Query: find all references to a symbol
// ---------------------------------------------------------------------------

typedef struct {
  symdb_file_id file_id;
  int line;
  int col;
  symdb_ref_kind_e kind;
} symdb_ref_result_t;

size_t valk_symdb_find_refs(valk_symdb_t *db, symdb_sym_id symbol_id,
                            symdb_ref_result_t **out);

// ---------------------------------------------------------------------------
// Query: find all symbols in a file
// ---------------------------------------------------------------------------

typedef struct {
  symdb_sym_id id;
  char *name;
  int line;
  int col;
  symdb_sym_kind_e kind;
  symdb_type_id type_id;
  bool exported;
} symdb_sym_result_t;

size_t valk_symdb_file_symbols(valk_symdb_t *db, symdb_file_id file_id,
                               symdb_sym_result_t **out);

// ---------------------------------------------------------------------------
// Statistics / reporting
// ---------------------------------------------------------------------------

typedef struct {
  char *name;
  char *file_path;
  int line;
  int64_t count;
} symdb_stat_row_t;

typedef struct {
  symdb_stat_row_t *rows;
  size_t count;
} symdb_stat_result_t;

void symdb_stat_result_free(symdb_stat_result_t *r);

// Most referenced symbols (highest fan-in)
symdb_stat_result_t valk_symdb_hotspots(valk_symdb_t *db, int limit);

// Symbols that reference the most others (highest fan-out)
symdb_stat_result_t valk_symdb_high_fanout(valk_symdb_t *db, int limit);

// Exported symbols with zero references (dead code candidates)
symdb_stat_result_t valk_symdb_dead_code(valk_symdb_t *db, int limit);

// Most frequently used types
typedef struct {
  char *display;
  int64_t count;
} symdb_type_stat_row_t;

typedef struct {
  symdb_type_stat_row_t *rows;
  size_t count;
} symdb_type_stat_result_t;

void symdb_type_stat_result_free(symdb_type_stat_result_t *r);

symdb_type_stat_result_t valk_symdb_type_popularity(valk_symdb_t *db, int limit);

// File coupling — files that reference each other
typedef struct {
  char *source_path;
  char *target_path;
  int64_t ref_count;
} symdb_coupling_row_t;

typedef struct {
  symdb_coupling_row_t *rows;
  size_t count;
} symdb_coupling_result_t;

void symdb_coupling_result_free(symdb_coupling_result_t *r);

symdb_coupling_result_t valk_symdb_file_coupling(valk_symdb_t *db, int limit);

// Summary counts
typedef struct {
  int64_t file_count;
  int64_t symbol_count;
  int64_t type_count;
  int64_t ref_count;
  int64_t scope_count;
} symdb_summary_t;

symdb_summary_t valk_symdb_summary(valk_symdb_t *db);

// ---------------------------------------------------------------------------
// Content hash utility
// ---------------------------------------------------------------------------

void valk_symdb_content_hash(const char *text, size_t len, char *out, size_t out_size);
