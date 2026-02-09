#pragma once

#include <stdio.h>
#include "types.h"

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

#define VALK_WITH_REQUEST_CTX(_req_ctx_)                              \
  for (struct {                                                       \
         int exec;                                                    \
         struct valk_request_ctx *old_ctx;                            \
       } __rctx = {1, valk_thread_ctx.request_ctx};                   \
       __rctx.exec; valk_thread_ctx.request_ctx = __rctx.old_ctx)     \
    for (valk_thread_ctx.request_ctx = (_req_ctx_); __rctx.exec; __rctx.exec = 0)

#define valk_mem_alloc(__bytes) \
  valk_mem_allocator_alloc(valk_thread_ctx.allocator, (__bytes))

#define valk_mem_realloc(__ptr, __new_size) \
  valk_mem_allocator_realloc(valk_thread_ctx.allocator, (__ptr), (__new_size))

#define valk_mem_calloc(__num, __size) \
  valk_mem_allocator_calloc(valk_thread_ctx.allocator, (__num), (__size))

#define valk_mem_free(__ptr) \
  valk_mem_allocator_free(valk_thread_ctx.allocator, __ptr)

/// generic helper, same as Linux kernel's container_of
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
  VALK_ALLOC_REGION,
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

  u64 bitmap_version;
  u8 *usage_bitmap;

  // Memory layout
  // [sizeof(u64) * numSlabs | freeList]
  // [sizeof(valk_slab_t + (u64 * numSlabs)) * capacity | slabs]
  u8 heap[];
} valk_slab_t;

_Static_assert(offsetof(valk_slab_t, heap) % 16 == 0,
               "heap must be 16-byte aligned for AIO handle storage");

valk_slab_t *valk_slab_new(sz itemSize, sz numItems);

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

// Arena statistics for telemetry (all fields atomic for thread-safe access)
typedef struct {
  _Atomic u64 total_allocations;      // Count of alloc calls
  _Atomic sz total_bytes_allocated;   // Sum of all requested bytes
  _Atomic sz high_water_mark;         // Maximum offset reached
  _Atomic u64 num_resets;             // Count of arena_reset calls
  _Atomic u64 num_checkpoints;        // Count of checkpoint evacuations
  _Atomic sz bytes_evacuated;         // Total bytes copied to heap
  _Atomic u64 values_evacuated;       // Count of values copied to heap
  _Atomic u64 overflow_fallbacks;     // Count of heap fallback allocations due to full arena
  _Atomic sz overflow_bytes;          // Bytes allocated via heap fallback
} valk_arena_stats_t;

typedef struct {
  sz offset;
} valk_arena_checkpoint_t;

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

valk_arena_checkpoint_t valk_arena_checkpoint_save(valk_mem_arena_t *arena);
void valk_arena_checkpoint_restore(valk_mem_arena_t *arena, valk_arena_checkpoint_t cp);

// Arena statistics API
void valk_mem_arena_print_stats(valk_mem_arena_t *arena, FILE *out);
void valk_mem_arena_reset_stats(valk_mem_arena_t *arena);
bool valk_ptr_in_arena(valk_mem_arena_t *arena, void *ptr);

// Forward declaration for root environment
struct valk_lenv_t;

// Forward declarations for parallel GC
struct valk_gc_mark_queue;
struct valk_lval_t;

typedef struct {
  valk_mem_allocator_t *allocator;
  void *heap;                     // Fallback GC heap for arena overflow (valk_gc_heap_t*)
  valk_mem_arena_t *scratch;      // Scratch arena for temporary allocations
  struct valk_lenv_t *root_env;   // Root environment for checkpoint evacuation
  float checkpoint_threshold;     // Threshold for automatic checkpointing (0.0-1.0)
  bool checkpoint_enabled;        // Whether automatic checkpointing is enabled
  u64 call_depth;              // Current function call depth (for TCO testing/debugging)
  
  // Request context (Finagle-style context propagation)
  struct valk_request_ctx *request_ctx;   // Current request context for deadline/tracing
  
  // Parallel GC fields (Phase 0)
  u64 gc_thread_id;            // Index in GC coordinator's thread registry
  bool gc_registered;             // Whether registered with parallel GC
  struct valk_lval_t **root_stack;       // Explicit root stack for protecting temps during GC
  sz root_stack_count;
  sz root_stack_capacity;
  
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

#define VALK_CHUNK_SIZE 8

typedef struct valk_ptr_chunk {
  struct valk_ptr_chunk *next;
  void *items[VALK_CHUNK_SIZE];
} valk_ptr_chunk_t;

typedef struct {
  valk_ptr_chunk_t *head;
  valk_ptr_chunk_t *tail;
  u32 count;
  u32 tail_count;
  bool malloc_chunks;
} valk_chunked_ptrs_t;

void valk_chunked_ptrs_init(valk_chunked_ptrs_t *self);
bool valk_chunked_ptrs_push(valk_chunked_ptrs_t *self, void *ptr, void *alloc_ctx);
void *valk_chunked_ptrs_get(valk_chunked_ptrs_t *self, u32 index);
void valk_chunked_ptrs_free(valk_chunked_ptrs_t *self);

static inline u32 valk_chunked_ptrs_count(valk_chunked_ptrs_t *self) {
  return self->count;
}
