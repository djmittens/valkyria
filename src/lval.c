#include "parser.h"
#include "dict.h"

#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "builtins_internal.h"
#include "collections.h"
#include "common.h"
#include "gc.h"
#include "memory.h"

#ifdef VALK_COVERAGE
#include "coverage.h"
#endif

static const char* valk_lval_str_escape(char x);

static char* lval_str_escapable = "\a\b\f\n\r\t\v\\\'\"";

// ============================================================================
// Singleton Nil, Small Integer Cache, and Symbol Intern Table
// ============================================================================

#define VALK_NUM_CACHE_MIN (-1)
#define VALK_NUM_CACHE_MAX 256
#define VALK_NUM_CACHE_SIZE (VALK_NUM_CACHE_MAX - VALK_NUM_CACHE_MIN + 1)

static valk_lval_t __valk_nil_singleton;
static valk_lval_t __valk_num_cache[VALK_NUM_CACHE_SIZE];
static bool __valk_singletons_initialized = false;

// Symbol string intern table: open-addressing hash table with FNV-1a
// Stores deduplicated, permanent char* strings for symbol names.
// Each valk_lval_sym() call creates a fresh struct but shares the interned string.
#define SYM_TABLE_INITIAL_CAP 512

static struct {
  const char **strings;
  u64 count;
  u64 capacity;
  pthread_mutex_t lock;
} __sym_table = {.strings = NULL, .count = 0, .capacity = 0,
                 .lock = PTHREAD_MUTEX_INITIALIZER};

static u64 sym_hash(const char *s) {
  u64 h = 14695981039346656037ULL;
  for (; *s; s++) {
    h ^= (u8)*s;
    h *= 1099511628211ULL;
  }
  return h;
}

static void sym_table_grow(void) {
  u64 new_cap = __sym_table.capacity * 2;
  const char **new_strings = calloc(new_cap, sizeof(const char *));
  for (u64 i = 0; i < __sym_table.capacity; i++) {
    if (__sym_table.strings[i] == NULL) continue;
    u64 idx = sym_hash(__sym_table.strings[i]) & (new_cap - 1);
    while (new_strings[idx] != NULL)
      idx = (idx + 1) & (new_cap - 1);
    new_strings[idx] = __sym_table.strings[i];
  }
  free(__sym_table.strings);
  __sym_table.strings = new_strings;
  __sym_table.capacity = new_cap;
}

// The table is statically initialized empty and grown on first use under its
// own lock. It used to be allocated inside valk_lval_init_singletons, which
// forced valk_sym_intern to be a silent pass-through until that ran — and a
// pass-through returns a NON-canonical pointer. Anything keyed on pointer
// identity (the env key arrays, the global concurrent map) degrades silently in
// that window: two distinct strings can end up sharing a pointer. Removing the
// init step makes "interned" an unconditional guarantee.
//
// Deliberately NOT pthread_once: this is reachable from inside singleton setup,
// and a nested pthread_once on the same gate traps with
// _os_once_gate_recursive_abort.
static const char *sym_intern_str(const char *name) {
  pthread_mutex_lock(&__sym_table.lock);
  if (__sym_table.capacity == 0) {
    __sym_table.strings = calloc(SYM_TABLE_INITIAL_CAP, sizeof(const char *));
    // LCOV_EXCL_START - OOM
    if (!__sym_table.strings) {
      pthread_mutex_unlock(&__sym_table.lock);
      return name;
    }
    // LCOV_EXCL_STOP
    __sym_table.capacity = SYM_TABLE_INITIAL_CAP;
  }
  u64 mask = __sym_table.capacity - 1;
  u64 idx = sym_hash(name) & mask;
  while (__sym_table.strings[idx] != NULL) {
    if (strcmp(__sym_table.strings[idx], name) == 0) {
      const char *result = __sym_table.strings[idx];
      pthread_mutex_unlock(&__sym_table.lock);
      return result;
    }
    idx = (idx + 1) & mask;
  }
  u64 slen = strlen(name);
  if (slen > 200) slen = 200;
  char *istr = malloc(slen + 1);
  memcpy(istr, name, slen);
  istr[slen] = '\0';
  __sym_table.strings[idx] = istr;
  __sym_table.count++;
  if (__sym_table.count * 4 > __sym_table.capacity * 3)
    sym_table_grow();
  pthread_mutex_unlock(&__sym_table.lock);
  return istr;
}

u64 valk_sym_intern_count(void) { return __sym_table.count; }

const char *valk_sym_intern(const char *name) {
  return sym_intern_str(name);
}

// Interning is now unconditional (the table initializes lazily), so this is
// always true. Kept as the single place callers ask the question, in case the
// table ever needs a real teardown.
bool valk_sym_intern_active(void) { return true; }


void valk_lval_init_singletons(void) {
  if (__valk_singletons_initialized) return;
  __valk_singletons_initialized = true;

  __valk_nil_singleton.flags = LVAL_NIL | LVAL_ALLOC_HEAP | LVAL_FLAG_IMMORTAL | LVAL_SRC_POS_DEFAULT;
  __valk_nil_singleton.cons.head = nullptr;
  __valk_nil_singleton.cons.tail = nullptr;

  for (int i = 0; i < VALK_NUM_CACHE_SIZE; i++) {
    long val = VALK_NUM_CACHE_MIN + i;
    __valk_num_cache[i].flags = LVAL_NUM | LVAL_ALLOC_HEAP | LVAL_FLAG_IMMORTAL | LVAL_SRC_POS_DEFAULT;
    __valk_num_cache[i].num = val;
  }

}


char* valk_c_err_format(const char* fmt, const char* file, const u64 line,
                        const char* function) {
  u64 len =
      snprintf(nullptr, 0, "%s:%llu:%s || %s", file, (unsigned long long)line, function, fmt);
  char* buf = valk_mem_alloc(len + 1);
  snprintf(buf, len + 1, "%s:%llu:%s || %s", file, (unsigned long long)line, function, fmt);
  return buf;
}

// LCOV_EXCL_BR_START - allocator type switch with unreachable default
u64 valk_alloc_flags_from_allocator(void* allocator) {
  if (allocator == NULL) return LVAL_ALLOC_SCRATCH;
  valk_mem_allocator_t* alloc = (valk_mem_allocator_t*)allocator;
  switch (alloc->type) {
    case VALK_ALLOC_ARENA:
      return LVAL_ALLOC_SCRATCH;
    case VALK_ALLOC_MALLOC:
      return LVAL_ALLOC_GLOBAL;
    case VALK_ALLOC_GC_HEAP:
      return LVAL_ALLOC_HEAP;
    case VALK_ALLOC_REGION: {
      valk_region_t *region = (valk_region_t *)allocator;
      switch (region->lifetime) {
        case VALK_LIFETIME_IMMORTAL: return LVAL_ALLOC_GLOBAL;
        case VALK_LIFETIME_SESSION:  return LVAL_ALLOC_HEAP;
        default:                     return LVAL_ALLOC_SCRATCH;
      }
    }
    // LCOV_EXCL_START - SLAB allocator not used for lval allocation
    case VALK_ALLOC_SLAB:
      return LVAL_ALLOC_GLOBAL;
    default:
      return LVAL_ALLOC_SCRATCH;
    // LCOV_EXCL_STOP
  }
}
// LCOV_EXCL_BR_STOP

char* valk_str_join(const u64 n, const char** strs, const char* sep) {
  u64 res_len = 0;
  u64 sep_len = strlen(sep);
  u64 str_lens[n];
  for (u64 i = 0; i < n; i++) {
    u64 _len = strlen(strs[i]);
    res_len += _len;
    str_lens[i] = _len;
    if (i < n - 1) {
      res_len += sep_len;
    }
  }
  char* res = valk_mem_alloc(res_len + 1);
  u64 offset = 0;
  for (u64 i = 0; i < n; i++) {
    memcpy(&res[offset], strs[i], str_lens[i]);
    offset += str_lens[i];
    if (i < n - 1) {
      memcpy(&res[offset], sep, sep_len);
      offset += sep_len;
    }
  }
  res[offset] = '\0';

  return res;
}

// LCOV_EXCL_BR_START - type name switch covers all cases, Unknown is unreachable
const char* valk_ltype_name(valk_ltype_e type) {
  switch (type) {
    case LVAL_NUM:
      return "Number";
    case LVAL_SYM:
      return "Symbol";
    case LVAL_FUN:
      return "Function";
    case LVAL_NIL:
      return "Nil";
    case LVAL_CONS:
      return "List";
    case LVAL_ERR:
      return "Error";
    case LVAL_STR:
      return "String";
    case LVAL_REF:
      return "Reference";
    case LVAL_HANDLE:
      return "Handle";
    case LVAL_DICT:
      return "Dict";
    case LVAL_UNDEFINED:
      return "UNDEFINED";
  }
  return "Unknown";
}
// LCOV_EXCL_BR_STOP

valk_lval_t* valk_lval_ref(const char* type, void* ptr, void (*free)(void*)) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_REF | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  u64 tlen = strlen(type);
  if (tlen > 100) tlen = 100;
  res->ref.type = valk_mem_alloc(tlen + 1);
  memcpy(res->ref.type, type, tlen);
  res->ref.type[tlen] = '\0';
  res->ref.ptr = ptr;
  res->ref.free = free;
  res->ref.mark = nullptr;
  res->ref.evacuate = nullptr;
  res->ref.retain = nullptr;

  return res;
}

valk_lval_t* valk_lval_dict(valk_dict_t* data) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_DICT | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  res->dict.data = data;
  return res;
}

valk_lval_t* valk_lval_num(long x) {
  if (__valk_singletons_initialized && x >= VALK_NUM_CACHE_MIN && x <= VALK_NUM_CACHE_MAX) {
    return &__valk_num_cache[x - VALK_NUM_CACHE_MIN];
  }
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_NUM | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  res->num = x;
  return res;
}

// TODO(main): look into UTF-8 support
valk_lval_t* valk_lval_err(const char* fmt, ...) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_ERR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  va_list va, va2;
  va_start(va, fmt);
  // NOLINTNEXTLINE(clang-analyzer-valist.Uninitialized) - va_start called above
  va_copy(va2, va);

  u64 len = vsnprintf(nullptr, 0, fmt, va);
  va_end(va);

  // TODO(main): look into making this into a constant
  len = len < 10000 ? len : 511;
  res->str = valk_mem_alloc(len + 1);
  vsnprintf(res->str, len + 1, fmt, va2);
  va_end(va2);
  return res;
}

valk_lval_t* valk_lval_sym(const char* sym) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_SYM | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  res->str = (char *)sym_intern_str(sym);
  res->flags |= LVAL_FLAG_INTERNED;
  return res;
}

valk_lval_t* valk_lval_str(const char* str) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_STR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  u64 slen = strlen(str);
  res->str = valk_mem_alloc(slen + 1);
  memcpy(res->str, str, slen + 1);

  return res;
}

valk_lval_t* valk_lval_str_n(const char* bytes, u64 n) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_STR | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  res->str = valk_mem_alloc(n + 1);
  if (n) memcpy(res->str, bytes, n);
  res->str[n] = '\0';

  return res;
}

// LCOV_EXCL_START - coverage instrumentation code (self-referential - not worth testing)
#ifdef VALK_COVERAGE
static bool is_if_expr(valk_lval_t* lval) {
  if (lval == NULL || LVAL_TYPE(lval) != LVAL_CONS) return false;
  valk_lval_t* head = lval->cons.head;
  if (head == NULL || LVAL_TYPE(head) != LVAL_SYM) return false;
  return strcmp(head->str, "if") == 0;
}

static void mark_if_branches(valk_lval_t* lval) {
  valk_lval_t* args = lval->cons.tail;
  if (args == NULL || LVAL_TYPE(args) != LVAL_CONS) return;

  valk_lval_t* rest = args->cons.tail;
  if (rest == NULL || LVAL_TYPE(rest) != LVAL_CONS) return;

  valk_lval_t* true_branch = rest->cons.head;
  if (true_branch != NULL && true_branch->cov_file_id != 0 && true_branch->cov_line != 0) {
    valk_coverage_mark_expr(true_branch->cov_file_id, true_branch->cov_line,
                            true_branch->cov_column, 0);
  }

  valk_lval_t* rest2 = rest->cons.tail;
  if (rest2 == NULL || LVAL_TYPE(rest2) != LVAL_CONS) return;
  valk_lval_t* false_branch = rest2->cons.head;
  if (false_branch != NULL && false_branch->cov_file_id != 0 && false_branch->cov_line != 0) {
    valk_coverage_mark_expr(false_branch->cov_file_id, false_branch->cov_line,
                            false_branch->cov_column, 0);
  }
}

void valk_coverage_mark_tree(valk_lval_t* lval) {
  if (lval == NULL) return;

  u8 type = LVAL_TYPE(lval);
  bool is_quoted = (lval->flags & LVAL_FLAG_QUOTED) != 0;
  
  if (type == LVAL_CONS) {
    if (!is_quoted) {
      VALK_COVERAGE_MARK_LVAL(lval);
      if (is_if_expr(lval)) {
        mark_if_branches(lval);
      }
    }
    valk_coverage_mark_tree(lval->cons.head);
    valk_coverage_mark_tree(lval->cons.tail);
  }
}
#endif
// LCOV_EXCL_STOP

valk_lval_t* valk_lval_lambda(valk_lenv_t* env, valk_lval_t* formals,
                              valk_lval_t* body) {
  extern valk_eval_metrics_t g_eval_metrics;
  atomic_fetch_add(&g_eval_metrics.closures_created, 1);

  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  INHERIT_SOURCE_LOC(res, body);

  res->fun.builtin = nullptr;

  int arity = 0;
  bool is_variadic = false;
  for (u64 i = 0; i < valk_lval_list_count(formals); i++) {
    valk_lval_t* formal = valk_lval_list_nth(formals, i);
    if (LVAL_TYPE(formal) == LVAL_SYM && strcmp(formal->str, "&") == 0) {
      is_variadic = true;
      break;
    }
    arity++;
  }

  if (is_variadic) {
    arity = -(arity + 1);
  }

  res->fun.arity = arity;
  static const char* lambda_name = "<lambda>";
  u64 name_len = strlen(lambda_name) + 1;
  res->fun.name = valk_mem_alloc(name_len);
  if (res->fun.name) {  // LCOV_EXCL_BR_LINE - memory allocation rarely fails
    memcpy(res->fun.name, lambda_name, name_len);
  }
  res->fun.env = env;
  res->fun.formals = formals;
  res->fun.body = body;
  res->fun.native_fn = nullptr;
  res->fun.native_name = nullptr;

#ifdef VALK_COVERAGE
  valk_coverage_mark_tree(body);
#endif

  return res;
}

valk_lval_t* valk_lval_nil(void) {
  if (__valk_singletons_initialized) return &__valk_nil_singleton;
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_NIL | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  res->cons.head = nullptr;
  res->cons.tail = nullptr;
  return res;
}

valk_lval_t* valk_lval_cons(valk_lval_t* head, valk_lval_t* tail) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_CONS | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  INHERIT_SOURCE_LOC(res, head);
  res->cons.head = valk_region_ensure_safe_ref(res, head);
  res->cons.tail = valk_region_ensure_safe_ref(res, tail);
  return res;
}

valk_lval_t* valk_lval_qcons(valk_lval_t* head, valk_lval_t* tail) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags =
      LVAL_CONS | LVAL_FLAG_QUOTED | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) | LVAL_SRC_POS_DEFAULT;
  LVAL_INIT_SOURCE_LOC(res);
  INHERIT_SOURCE_LOC(res, head);
  res->cons.head = valk_region_ensure_safe_ref(res, head);
  res->cons.tail = valk_region_ensure_safe_ref(res, tail);
  return res;
}

valk_lval_t* valk_lval_list(valk_lval_t* arr[], u64 count) {
  valk_lval_t* res = valk_lval_nil();
  for (u64 i = count; i > 0; i--) {
    res = valk_lval_cons(arr[i - 1], res);
  }
  return res;
}

valk_lval_t* valk_lval_qlist(valk_lval_t* arr[], u64 count) {
  valk_lval_t* res = valk_lval_nil();
  for (u64 i = count; i > 0; i--) {
    res = valk_lval_qcons(arr[i - 1], res);
  }
  return res;
}

#ifdef VALK_COVERAGE
static inline void valk_copy_source_loc(valk_lval_t* dst, valk_lval_t* src) {
  dst->cov_file_id = src->cov_file_id;
  dst->cov_line = src->cov_line;
  dst->cov_column = src->cov_column;
}
#else
#define valk_copy_source_loc(dst, src) ((void)0)
#endif

valk_lval_t* valk_qexpr_to_cons(valk_lval_t* qexpr) {
  if (qexpr == NULL || LVAL_TYPE(qexpr) == LVAL_NIL) {  // LCOV_EXCL_BR_LINE - defensive null check
    return valk_lval_nil();
  }
  VALK_COVERAGE_RECORD_LVAL(qexpr);
  valk_lval_t* res = valk_lval_cons(qexpr->cons.head, valk_qexpr_to_cons(qexpr->cons.tail));
  valk_copy_source_loc(res, qexpr);
  return res;
}

static inline int valk_is_list_type(valk_ltype_e type) {
  return type == LVAL_CONS || type == LVAL_QEXPR || type == LVAL_NIL;  // LCOV_EXCL_BR_LINE - short-circuit eval
}

valk_lval_t* valk_lval_head(valk_lval_t* cons) {
  VALK_ASSERT(valk_is_list_type(LVAL_TYPE(cons)),
              "Expected list (S-Expr, Q-Expr, or Nil), got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.head;
}

valk_lval_t* valk_lval_tail(valk_lval_t* cons) {
  VALK_ASSERT(valk_is_list_type(LVAL_TYPE(cons)),
              "Expected list (S-Expr, Q-Expr, or Nil), got %s",
              valk_ltype_name(LVAL_TYPE(cons)));
  return cons->cons.tail;
}

// LCOV_EXCL_BR_START - helper functions have short-circuit evaluations
int valk_lval_list_is_empty(valk_lval_t* list) {
  if (list == nullptr) return 1;
  if (LVAL_TYPE(list) == LVAL_NIL) return 1;
  if ((LVAL_TYPE(list) == LVAL_CONS || LVAL_TYPE(list) == LVAL_QEXPR) &&
      list->cons.head == nullptr)
    return 1;
  return 0;
}
// LCOV_EXCL_BR_STOP

u64 valk_lval_list_count(valk_lval_t* list) {
  u64 count = 0;
  valk_lval_t* curr = list;
  while (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    count++;
    curr = curr->cons.tail;
  }
  return count;
}

valk_lval_t* valk_lval_list_nth(valk_lval_t* list, u64 n) {
  valk_lval_t* curr = list;
  for (u64 i = 0; i < n && curr != nullptr && !valk_lval_list_is_empty(curr);
       i++) {
    curr = curr->cons.tail;
  }
  if (curr != nullptr && !valk_lval_list_is_empty(curr)) {
    return curr->cons.head;
  }
  return nullptr;
}

valk_lval_t* valk_plist_get(valk_lval_t* plist, const char* key_str) {
  if (!plist || LVAL_TYPE(plist) != LVAL_QEXPR) return NULL;  // LCOV_EXCL_BR_LINE - defensive check
  if (valk_lval_list_is_empty(plist)) return NULL;  // LCOV_EXCL_BR_LINE - defensive check

  valk_lval_t* curr = plist;
  while (curr && (LVAL_TYPE(curr) == LVAL_CONS || LVAL_TYPE(curr) == LVAL_QEXPR)) {  // LCOV_EXCL_BR_LINE - defensive check
    if (valk_lval_list_is_empty(curr)) break;  // LCOV_EXCL_BR_LINE - defensive check

    valk_lval_t* key = curr->cons.head;
    valk_lval_t* rest = curr->cons.tail;

    if (!rest || valk_lval_list_is_empty(rest)) break;  // LCOV_EXCL_BR_LINE - defensive check

    valk_lval_t* val = rest->cons.head;

    if (LVAL_TYPE(key) == LVAL_SYM && strcmp(key->str, key_str) == 0) {
      return val;
    }

    curr = rest->cons.tail;
  }
  return NULL;
}

valk_lval_t* valk_lval_copy(valk_lval_t* lval) {
  if (lval == nullptr) return nullptr;
  if (valk_lval_is_immortal(lval)) return lval;

  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));

  res->flags = (lval->flags & (LVAL_TYPE_MASK | LVAL_FLAG_QUOTED | LVAL_FLAG_INTERNED | LVAL_SRC_POS_MASK)) |
               valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);

#ifdef VALK_COVERAGE
  res->cov_file_id = lval->cov_file_id;
  res->cov_line = lval->cov_line;
  res->cov_column = lval->cov_column;
#endif

  switch (LVAL_TYPE(lval)) {  // LCOV_EXCL_BR_LINE - type dispatch (not all types copied in tests)
    case LVAL_NUM:
      res->num = lval->num;
      break;
    case LVAL_FUN:
      if (lval->fun.builtin) {
        res->fun.builtin = lval->fun.builtin;
        res->fun.env = nullptr;
        res->fun.body = nullptr;
        res->fun.formals = nullptr;
      } else {
        res->fun.builtin = nullptr;
        res->fun.env = lval->fun.env;
        res->fun.body = lval->fun.body;
        res->fun.formals = lval->fun.formals;
      }
      res->fun.native_fn = lval->fun.native_fn;
      res->fun.native_name = lval->fun.native_name;
      break;
    case LVAL_CONS:
      res->cons.head = lval->cons.head;
      res->cons.tail = lval->cons.tail;
      break;
    case LVAL_NIL:
      break;
    case LVAL_SYM: {
      if (lval->flags & LVAL_FLAG_INTERNED) {
        res->str = lval->str;
        res->flags |= LVAL_FLAG_INTERNED;
      } else {
        u64 slen = strlen(lval->str);
        if (slen > 200) slen = 200;
        res->str = valk_mem_alloc(slen + 1);
        memcpy(res->str, lval->str, slen);
        res->str[slen] = '\0';
      }
      break;
    }
    case LVAL_ERR: {
      u64 slen = strlen(lval->str);
      if (slen > 2000) slen = 2000;
      res->str = valk_mem_alloc(slen + 1);
      memcpy(res->str, lval->str, slen);
      res->str[slen] = '\0';
      break;
    }
    case LVAL_STR: {
      u64 slen = strlen(lval->str);
      res->str = valk_mem_alloc(slen + 1);
      memcpy(res->str, lval->str, slen + 1);
      break;
    }
    case LVAL_REF: {
      u64 tlen = strlen(lval->ref.type);
      if (tlen > 100) tlen = 100;
      res->ref.type = valk_mem_alloc(tlen + 1);
      memcpy(res->ref.type, lval->ref.type, tlen);
      res->ref.type[tlen] = '\0';
      res->ref.ptr = lval->ref.ptr;
      res->ref.free = lval->ref.free;
      res->ref.mark = lval->ref.mark;
      res->ref.evacuate = lval->ref.evacuate;
      res->ref.retain = lval->ref.retain;
      if (lval->ref.retain) lval->ref.retain(lval->ref.ptr);
      break;
    }
    // LCOV_EXCL_START - LVAL_UNDEFINED is an invariant violation, should never happen
    case LVAL_UNDEFINED:
      break;
    // LCOV_EXCL_STOP
    case LVAL_HANDLE:
      res->async.handle = lval->async.handle;
      break;
    case LVAL_DICT:
      res->dict.data = lval->dict.data;
      break;
  }
  return res;
}

int valk_lval_eq(valk_lval_t* x, valk_lval_t* y) {
  // LCOV_EXCL_BR_START - null comparison rarely exercised
  if (x == nullptr && y == nullptr) {
    return 1;
  }
  if (x == nullptr || y == nullptr) {
    return 0;
  }
  // LCOV_EXCL_BR_STOP

  if (x == y) return 1;
  if (LVAL_TYPE(x) != LVAL_TYPE(y)) {
    return 0;
  }

  switch (LVAL_TYPE(x)) {  // LCOV_EXCL_BR_LINE - type dispatch (not all types exercised)
    case LVAL_NUM:
      return (x->num == y->num);
    case LVAL_SYM:
      return (x->str == y->str) || (strcmp(x->str, y->str) == 0);
    case LVAL_STR:
    case LVAL_ERR:
      return (strcmp(x->str, y->str) == 0);
    case LVAL_FUN: {
      // LCOV_EXCL_BR_START - function equality comparison rarely used
      if (x->fun.builtin || y->fun.builtin) {
        return x->fun.builtin == y->fun.builtin;
      } else {
        return valk_lval_eq(x->fun.formals, y->fun.formals) &&
               valk_lval_eq(x->fun.body, y->fun.body);
      }
      // LCOV_EXCL_BR_STOP
    }
    case LVAL_NIL:
      return 1;
    case LVAL_CONS:
      return valk_lval_eq(x->cons.head, y->cons.head) &&
             valk_lval_eq(x->cons.tail, y->cons.tail);
    case LVAL_REF:
      return (x->ref.ptr == y->ref.ptr) && (x->ref.free == y->ref.free);
    case LVAL_DICT:
      return x->dict.data == y->dict.data;
    case LVAL_HANDLE:
      return x == y;
    // LCOV_EXCL_START - invariant violation, should never happen
    case LVAL_UNDEFINED:
      VALK_RAISE("LVAL is undefined, something went wrong");
      break;
  }

  return 0;
  // LCOV_EXCL_STOP
}

valk_lval_t* valk_lval_pop(valk_lval_t* lval, u64 i) {
  VALK_ASSERT(lval != nullptr, "valk_lval_pop: lval must not be null");
  u64 count = valk_lval_list_count(lval);
  LVAL_ASSERT(
      (valk_lval_t*)0, i < count,
      "Cant pop from list at invalid position: [%zu] total length: [%zu]", i,
      count);
  LVAL_ASSERT((valk_lval_t*)0, count > 0, "Cant pop from empty");

  if (i == 0) {
    valk_lval_t* cell = lval->cons.head;
    if (lval->cons.tail != nullptr &&
        !valk_lval_list_is_empty(lval->cons.tail)) {
      lval->cons.head = lval->cons.tail->cons.head;
      lval->cons.tail = lval->cons.tail->cons.tail;
    } else {
      lval->cons.head = nullptr;
      lval->cons.tail = nullptr;
    }
    return cell;
  }

  valk_lval_t* prev = lval;
  for (u64 j = 0; j < i - 1; j++) {
    prev = prev->cons.tail;
  }

  valk_lval_t* curr = prev->cons.tail;
  valk_lval_t* cell = curr->cons.head;

  prev->cons.tail = curr->cons.tail;

  return cell;
}

valk_lval_t* valk_lval_join(valk_lval_t* a, valk_lval_t* b) {
  valk_lval_t* orig_a __attribute__((unused)) = a;

  bool is_qexpr = (a->flags & LVAL_FLAG_QUOTED) != 0;

  u64 lena = valk_lval_list_count(a);

  valk_lval_t* res;
  if (LVAL_TYPE(b) != LVAL_CONS && LVAL_TYPE(b) != LVAL_NIL) {
    res = is_qexpr ? valk_lval_qcons(b, valk_lval_nil())
                   : valk_lval_cons(b, valk_lval_nil());
  } else {
    res = b;
  }

  struct {
    valk_lval_t** items;
    u64 count;
    u64 capacity;
  } tmp = {0};

  da_init(&tmp);

  for (u64 i = 0; i < lena; i++) {
    da_add(&tmp, a->cons.head);
    a = a->cons.tail;
  }

  for (u64 i = lena; i > 0; i--) {
    if (is_qexpr) {
      res = valk_lval_qcons(tmp.items[i - 1], res);
    } else {
      res = valk_lval_cons(tmp.items[i - 1], res);
    }
  }

  da_free(&tmp);

  INHERIT_SOURCE_LOC(res, orig_a);
  return res;
}

void valk_lval_print(valk_lval_t* val) {
  if (val == nullptr) {
    printf("NULL");
    return;
  }
  switch (LVAL_TYPE(val)) {  // LCOV_EXCL_BR_LINE - type dispatch (not all types used in tests)
    case LVAL_NUM:
      printf("Num[%li]", val->num);
      break;
    case LVAL_SYM:
      printf("%s", val->str);
      break;
    case LVAL_NIL:
      printf("()");
      break;
    case LVAL_CONS: {
      bool is_quoted = (val->flags & LVAL_FLAG_QUOTED) != 0;
      printf(is_quoted ? "{" : "(");
      valk_lval_t* curr = val;
      int first = 1;
      while (curr != nullptr && LVAL_TYPE(curr) == LVAL_CONS) {
        if (!first) putchar(' ');
        valk_lval_print(curr->cons.head);
        curr = curr->cons.tail;
        first = 0;
      }
      // LCOV_EXCL_START - improper lists (dotted pairs) rarely occur in tests
      if (curr != nullptr && LVAL_TYPE(curr) != LVAL_NIL) {
        printf(" . ");
        valk_lval_print(curr);
      }
      // LCOV_EXCL_STOP
      printf(is_quoted ? "}" : ")");
      break;
    }
    case LVAL_ERR:
      printf("Error[%s]", val->str);
      break;
    case LVAL_FUN:
      if (val->fun.builtin) {
        printf("<builtin>");
      } else {
        printf("(\\ ");
        valk_lval_print(val->fun.formals);
        putchar(' ');
        valk_lval_print(val->fun.body);
        putchar(')');
      }
      break;
    case LVAL_STR: {
      putchar('"');
      for (u64 i = 0; i < strlen(val->str); ++i) {
        if (strchr(lval_str_escapable, val->str[i])) {
          printf("%s", valk_lval_str_escape(val->str[i]));
        } else {
          putchar(val->str[i]);
        }
      }
      putchar('"');
      break;
    }
    case LVAL_REF:
      printf("Reference[%s:%p]", val->ref.type, val->ref.ptr);
      break;
    case LVAL_DICT:
      printf("<dict:%u>", val->dict.data ? val->dict.data->count : 0);
      break;
    case LVAL_HANDLE:
      printf("<handle>");
      break;
    case LVAL_UNDEFINED:
      printf("[Undefined]");
      break;
  }
}

static const char* valk_lval_str_escape(char x) {
  switch (x) {  // LCOV_EXCL_BR_LINE - not all escape sequences tested
    case '\a':
      return "\\a";
    case '\b':
      return "\\b";
    case '\f':
      return "\\f";
    case '\n':
      return "\\n";
    case '\r':
      return "\\r";
    case '\t':
      return "\\t";
    case '\v':
      return "\\v";
    case '\\':
      return "\\\\";
    case '\'':
      return "\\\'";
    case '\"':
      return "\\\"";
  }
  return "";
}

bool valk_lval_is_truthy(valk_lval_t *val) {
  if (val == nullptr) return false;
  valk_ltype_e type = LVAL_TYPE(val);
  if (type == LVAL_NIL) return false;
  if (type == LVAL_NUM) return val->num != 0;
  if (type == LVAL_ERR) return false;
  return true;
}
