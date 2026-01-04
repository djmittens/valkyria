#pragma once

#include <stdio.h>
#include "types.h"

// #define VALK_ARC_DEBUG
#define VALK_ARC_TRACE_DEPTH 10

#define VALK_WITH_CTX(_ctx_)                        \
  for (struct {                                     \
         int exec;                                  \
         valk_thread_context_t old_ctx;             \
       } __ctx = {1, valk_thread_ctx};              \
       __ctx.exec; valk_thread_ctx = __ctx.old_ctx) \
    for (valk_thread_ctx = (_ctx_); __ctx.exec; __ctx.exec = 0)

#define VALK_WITH_ALLOC(_alloc_)                                \
  for (struct {                                                 \
         int exec;                                              \
         void *old_alloc;                                       \
       } __ctx = {1, valk_thread_ctx.allocator};                \
       __ctx.exec; valk_thread_ctx.allocator = __ctx.old_alloc) \
    for (valk_thread_ctx.allocator = (_alloc_); __ctx.exec; __ctx.exec = 0)

#define valk_mem_alloc(__bytes) \
  valk_mem_allocator_alloc(valk_thread_ctx.allocator, (__bytes))

#define valk_mem_realloc(__ptr, __new_size) \
  valk_mem_allocator_realloc(valk_thread_ctx.allocator, (__ptr), (__new_size))

#define valk_mem_calloc(__num, __size) \
  valk_mem_allocator_calloc(valk_thread_ctx.allocator, (__num), (__size))

#define valk_mem_free(__ptr) \
  valk_mem_allocator_free(valk_thread_ctx.allocator, __ptr)

#define valk_retain(ref)                                            \
  ({                                                                \
    if (ref != nullptr) {                                           \
      (ref)->refcount++;                                            \
      valk_capture_trace(VALK_TRACE_ACQUIRE, (ref)->refcount, ref); \
    }                                                               \
    (ref);                                                          \
  })

// This is bootleg arc
#define valk_release(ref)                                               \
  do {                                                                  \
    if (ref == nullptr) break;                                          \
    (ref)->refcount--;                                                  \
    /*char _buf[512];                                                   \
    pthread_getname_np(pthread_self(), _buf, sizeof(_buf));*/           \
    if ((ref)->refcount == 0) {                                         \
      /* printf("[%s] Arc is freeing %d\n", _buf, old); */              \
      /* Only free using the allocator if a custom one is not defined*/ \
      valk_capture_trace(VALK_TRACE_FREE, (ref)->refcount, ref);        \
      if ((ref)->free) {                                                \
        valk_arc_trace_report_print(ref);                               \
        (ref)->free(ref);                                               \
      } else if ((ref)->allocator) {                                    \
        valk_mem_allocator_free((ref)->allocator, (ref));               \
      }                                                                 \
    } else {                                                            \
      /* printf("[%s] Arc is decrementing %d\n", _buf, old); */         \
      valk_capture_trace(VALK_TRACE_RELEASE, (ref)->refcount, ref);     \
    }                                                                   \
  } while (0)

#ifdef VALK_ARC_DEBUG
#include <dlfcn.h>
#include <execinfo.h>
#define VALK_ARC_TRACE_MAX 50

typedef enum {
  VALK_TRACE_NEW,
  VALK_TRACE_ACQUIRE,
  VALK_TRACE_RELEASE,
  VALK_TRACE_FREE
} valk_trace_kind_e;

typedef struct valk_arc_trace_info {
  valk_trace_kind_e kind;
  const char *file;
  const char *function;
  int line;
  u64 refcount;
  void *stack[VALK_ARC_TRACE_DEPTH];
  u64 size;
} valk_arc_trace_info;

#define valk_capture_trace(_kind, _refcount, ref)                             \
  do {                                                                        \
    u64 _old = __atomic_fetch_add(&(ref)->nextTrace, 1, __ATOMIC_RELEASE); \
    VALK_ASSERT(                                                              \
        _old < VALK_ARC_TRACE_MAX,                                            \
        "Cannot keep tracing this variable, please increase the max traces"); \
    (ref)->traces[_old].kind = (_kind);                                       \
    (ref)->traces[_old].file = __FILE__;                                      \
    (ref)->traces[_old].function = __func__;                                  \
    (ref)->traces[_old].line = __LINE__;                                      \
    (ref)->traces[_old].refcount = (_refcount);                               \
    (ref)->traces[_old].size =                                                \
        backtrace((ref)->traces[_old].stack, VALK_ARC_TRACE_DEPTH);           \
  } while (0)

#define valk_arc_trace_report_print(report) \
  __valk_arc_trace_report_print((report)->traces, (report)->nextTrace)

void __valk_arc_trace_report_print(valk_arc_trace_info *traces, u64 num);

#else
#define valk_capture_trace(_kind, _refcount, ref) UNUSED((_refcount));
#define valk_arc_trace_report_print(report)
#endif

/// generic helper, same as Linux kernel’s container_of
/// @return the ptr of the right type
#define valk_container_of(ptr, type, member) \
  ((type *)((u8 *)(ptr) - offsetof(type, member)))

/// @brief efficient way to calculate the next power of 2 for a given size
static inline sz valk_next_pow2(sz x) {
  if (x <= 1) return 1;

#if defined(__clang__) || defined(__GNUC__)
#if SIZE_MAX <= UINT32_MAX
  return 1u << (32 - __builtin_clz((u32)(x - 1)));
#else
  return 1ull << (64 - __builtin_clzll((u64)(x - 1)));
#endif
#else /* portable smear–add-one method */
  x--;
  x |= x >> 1;
  x |= x >> 2;
  x |= x >> 4;
  x |= x >> 8;
  x |= x >> 16;
#if SIZE_MAX > UINT32_MAX
  x |= x >> 32;
#endif
  return x + 1;
#endif
}

typedef enum {
  VALK_ALLOC_NULL,
  VALK_ALLOC_MALLOC,
  VALK_ALLOC_ARENA,
  VALK_ALLOC_SLAB,
  VALK_ALLOC_GC_HEAP,
  VALK_ALLOC_TLAB,
} valk_mem_allocator_e;

char *valk_mem_allocator_e_to_string(valk_mem_allocator_e self);

typedef struct {
  valk_mem_allocator_e type;
} valk_mem_allocator_t;

// Global malloc allocator for use with VALK_WITH_ALLOC
extern valk_mem_allocator_t valk_malloc_allocator;

typedef struct {
  sz capacity;
  sz count;
  void *items;
} valk_buffer_t;

void valk_buffer_alloc(valk_buffer_t *buf, sz capacity);
void valk_buffer_append(valk_buffer_t *buf, void *bytes, sz len);
int valk_buffer_is_full(valk_buffer_t *buf);

typedef struct {
  sz capacity;
  sz offset;
  u64 items[];
} valk_ring_t;

/// @param[out] self buffer to initialize
/// @param[in] capcity capacity of the ring buffer in bytes
void valk_ring_init(valk_ring_t *self, sz capacity);

void valk_ring_write(valk_ring_t *self, u8 *data, sz len);

void valk_ring_rewind(valk_ring_t *self, sz n);

// @brief read the contents of the buffer into a buffer dst
void valk_ring_read(valk_ring_t *self, sz n, void *dst);

// @brief read the contents of the buffer into a file
void valk_ring_fread(valk_ring_t *self, sz n, FILE *f);

// @brief print the contents of the buffer into a file
void valk_ring_print(valk_ring_t *self, FILE *f);

typedef struct valk_slab_item_t {
  sz handle;
  sz next;
  // sz size; // todo(networking): i should add this to the layout if i need
  // it. i dont think this will ever be useful tho, so save a few bytes of
  // overhead
  u8 data[];
} valk_slab_item_t;

typedef struct {  // extends valk_mem_allocator_t;
  valk_mem_allocator_e type;
  sz itemSize;
  sz numItems;
  sz numFree;
  sz peakUsed;  // High water mark: max (numItems - numFree) ever observed
  u64 overflowCount;
  sz head;
  sz mmap_size;  // Size of mmap'd region (0 if not mmap'd)
  // treiber list top

#ifdef VALK_METRICS_ENABLED
  u64 bitmap_version;
  u8 *usage_bitmap;
#endif

  // Memory layout
  // [sizeof(u64) * numSlabs | freeList]
  // [sizeof(valk_slab_t + (u64 * numSlabs)) * capacity | slabs]
  u8 heap[];
} valk_slab_t;

_Static_assert(offsetof(valk_slab_t, heap) % 16 == 0,
               "heap must be 16-byte aligned for AIO handle storage");

valk_slab_t *valk_slab_new(sz itemSize, sz numItems);
void valk_slab_init(valk_slab_t *self, sz itemSize, sz numItems);

void valk_slab_free(valk_slab_t *self);

/// @brief estimate the amount of bytes that are needed to contain the entire
/// slab
/// @return the total size that should be allocated, to initialize slab
sz valk_slab_size(sz itemSize, sz numItems);

/// @brief estimate the the total chunk size in bytes of each item in the array
///
/// this is useful in cases where one would want to iterate over the chunks or
/// perhaps access a chunk at a particular offset
/// @param itemSize the concrete size of item without padding or headers
/// @return the actual size of the the item in memory including padding and
/// headers
sz valk_slab_item_stride(sz itemSize);

valk_slab_item_t *valk_slab_aquire(valk_slab_t *self);

void valk_slab_release(valk_slab_t *self, valk_slab_item_t *item);
void valk_slab_release_ptr(valk_slab_t *self, void *data);

/// @brief Get number of available (free) items in the slab
/// @return Current count of free items (may change due to concurrent access)
static inline sz valk_slab_available(valk_slab_t *self) {
  return __atomic_load_n(&self->numFree, __ATOMIC_ACQUIRE);
}

#ifdef VALK_METRICS_ENABLED
typedef struct {
  u8 *data;
  sz bytes;
  u64 version;
} valk_slab_bitmap_t;

typedef struct {
  sz offset;
  sz count;
  u8 byte;
} valk_bitmap_delta_run_t;

typedef struct {
  valk_bitmap_delta_run_t *runs;
  sz run_count;
  sz run_capacity;
  u64 from_version;
  u64 to_version;
} valk_bitmap_delta_t;

void valk_slab_bitmap_snapshot(valk_slab_t *slab, valk_slab_bitmap_t *out);
void valk_slab_bitmap_free(valk_slab_bitmap_t *bmp);

void valk_bitmap_delta_init(valk_bitmap_delta_t *delta);
void valk_bitmap_delta_free(valk_bitmap_delta_t *delta);
bool valk_bitmap_delta_compute(const valk_slab_bitmap_t *curr,
                                const valk_slab_bitmap_t *prev,
                                valk_bitmap_delta_t *out);
sz valk_bitmap_delta_to_rle(const valk_bitmap_delta_t *delta,
                                 char *buf, sz buf_size);

typedef struct {
  sz used;
  sz free;
} valk_bitmap_bucket_t;

sz valk_slab_bitmap_buckets(valk_slab_t *slab,
                                 sz start_slot, sz end_slot,
                                 sz num_buckets,
                                 valk_bitmap_bucket_t *out_buckets);
#endif

// Arena statistics for telemetry
typedef struct {
  u64 total_allocations;      // Count of alloc calls
  sz total_bytes_allocated;   // Sum of all requested bytes
  sz high_water_mark;         // Maximum offset reached
  u64 num_resets;             // Count of arena_reset calls
  u64 num_checkpoints;        // Count of checkpoint evacuations
  sz bytes_evacuated;         // Total bytes copied to heap
  u64 values_evacuated;       // Count of values copied to heap
  u64 overflow_fallbacks;     // Count of heap fallback allocations due to full arena
  sz overflow_bytes;          // Bytes allocated via heap fallback
} valk_arena_stats_t;

// Process-level memory stats (from OS)
typedef struct {
  sz rss_bytes;             // Resident Set Size (physical RAM)
  sz vms_bytes;             // Virtual Memory Size
  sz system_total_bytes;    // Total system RAM (for memory pressure calc)
  sz shared_bytes;          // Shared memory (Linux only)
  sz data_bytes;            // Data + stack segment (Linux only)
  u64 page_faults_minor;    // Soft page faults
  u64 page_faults_major;    // Hard page faults (disk I/O)
} valk_process_memory_t;

// Detailed memory breakdown from /proc/self/smaps (Linux only)
// Categorizes RSS by region type to identify where untracked memory lives
typedef struct {
  sz heap_rss;        // [heap] - glibc malloc arena
  sz stack_rss;       // [stack] and thread stacks
  sz anon_rss;        // Anonymous mappings (mmap, buffers)
  sz file_rss;        // File-backed mappings (shared libs, etc.)
  sz shmem_rss;       // Shared memory regions
  sz uring_rss;       // io_uring ring buffers
  sz other_rss;       // vdso, vvar, vsyscall, etc.
  sz total_rss;       // Sum of all (should match process RSS)
  u32 anon_regions;   // Count of anonymous regions
  u32 file_regions;   // Count of file-backed regions
} valk_smaps_breakdown_t;

// Collect process-level memory stats from OS
void valk_process_memory_collect(valk_process_memory_t *pm);

// Collect detailed smaps breakdown (Linux only, no-op on other platforms)
void valk_smaps_collect(valk_smaps_breakdown_t *smaps);

typedef struct {  // extends valk_mem_allocator_t;
  valk_mem_allocator_e type;
  sz capacity;
  sz offset;
  bool warned_overflow;          // Reset each checkpoint cycle
  valk_arena_stats_t stats;      // Telemetry statistics
  u8 heap[];
} valk_mem_arena_t;

void valk_mem_arena_init(valk_mem_arena_t *self, sz capacity);
void valk_mem_arena_reset(valk_mem_arena_t *self);
void *valk_mem_arena_alloc(valk_mem_arena_t *self, sz bytes);

// Arena statistics API
void valk_mem_arena_print_stats(valk_mem_arena_t *arena, FILE *out);
void valk_mem_arena_reset_stats(valk_mem_arena_t *arena);
bool valk_ptr_in_arena(valk_mem_arena_t *arena, void *ptr);

// Forward declaration for root environment
struct valk_lenv_t;

// Forward declarations for parallel GC
struct valk_gc_mark_queue;
struct valk_lval_t;

struct valk_gc_tlab;

typedef struct {
  valk_mem_allocator_t *allocator;
  void *heap;                     // Fallback GC heap for arena overflow (valk_gc_malloc_heap_t*)
  valk_mem_arena_t *scratch;      // Scratch arena for temporary allocations
  struct valk_lenv_t *root_env;   // Root environment for checkpoint evacuation
  float checkpoint_threshold;     // Threshold for automatic checkpointing (0.0-1.0)
  bool checkpoint_enabled;        // Whether automatic checkpointing is enabled
  u64 call_depth;              // Current function call depth (for TCO testing/debugging)
  
  // Parallel GC fields (Phase 0)
  u64 gc_thread_id;            // Index in GC coordinator's thread registry
  bool gc_registered;             // Whether registered with parallel GC
  struct valk_lval_t **root_stack;       // Explicit root stack for protecting temps during GC
  sz root_stack_count;
  sz root_stack_capacity;
  
  // TLAB for parallel GC allocations (Phase 7)
  struct valk_gc_tlab *tlab;      // Thread-Local Allocation Buffer
  bool tlab_enabled;              // Whether TLAB allocation is active
  
  // Eval stack for checkpoint evacuation
  void *eval_stack;               // Current valk_eval_stack_t* (forward ref)
  struct valk_lval_t *eval_expr;  // Current expression being evaluated
  struct valk_lval_t *eval_value; // Current value in evaluation
} valk_thread_context_t;

extern __thread valk_thread_context_t valk_thread_ctx;

__attribute__((malloc)) void *valk_mem_allocator_alloc(valk_mem_allocator_t *self, sz bytes);
void *valk_mem_allocator_realloc(valk_mem_allocator_t *self, void *ptr,
                                 sz new_size);
__attribute__((malloc)) void *valk_mem_allocator_calloc(valk_mem_allocator_t *self, sz num,
                                sz size);
void valk_mem_allocator_free(valk_mem_allocator_t *self, void *ptr);

void valk_mem_init_malloc();

typedef struct valk_gc_chunk_t valk_gc_chunk_t;
typedef void(valk_gc_finalize_f)(valk_gc_chunk_t *);
typedef void(valk_gc_mark_f)(valk_gc_chunk_t *);

typedef struct valk_gc_chunk_t {
  bool marked;
  struct valk_gc_chunk_t *next;
  struct valk_gc_chunk_t *prev;
} valk_gc_chunk_t;

typedef struct {
  sz capacity;
  sz free;
  valk_mem_allocator_t *allocator;
  valk_gc_chunk_t sentinel;
  valk_gc_mark_f *mark;
  valk_gc_finalize_f *finalize;
} valk_gc_heap_t;

void valk_gc_init(valk_gc_heap_t *self, sz capacity);
void valk_gc_mark(valk_gc_heap_t *self, void *ptr);
void *valk_gc_alloc(valk_gc_heap_t *heap, sz size);
void *valk_gc_realloc(valk_gc_heap_t *heap, void *ptr, sz size);
void valk_gc_sweep(valk_gc_heap_t *self);

// No extra resize helper; rely on valk_mem_allocator_realloc which now performs
// copy-on-realloc semantics for arena as well as malloc allocators.
