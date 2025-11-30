#pragma once

#include <stdint.h>
#include <stdio.h>
#include <string.h>

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
  size_t refcount;
  void *stack[VALK_ARC_TRACE_DEPTH];
  size_t size;
} valk_arc_trace_info;

#define valk_capture_trace(_kind, _refcount, ref)                             \
  do {                                                                        \
    size_t _old = __atomic_fetch_add(&(ref)->nextTrace, 1, __ATOMIC_RELEASE); \
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

void __valk_arc_trace_report_print(valk_arc_trace_info *traces, size_t num);

#else
#define valk_capture_trace(_kind, _refcount, ref) UNUSED((_refcount));
#define valk_arc_trace_report_print(report)
#endif

/// generic helper, same as Linux kernel’s container_of
/// @return the ptr of the right type
#define valk_container_of(ptr, type, member) \
  ((type *)((uint8_t *)(ptr) - offsetof(type, member)))

/// @brief efficient way to calculate the next pow2 to store this shit
/// chatgpt, cooked up this shit
static inline size_t valk_next_pow2(size_t x) {
  if (x <= 1) return 1;

#if defined(__clang__) || defined(__GNUC__)
#if SIZE_MAX <= UINT32_MAX
  return 1u << (32 - __builtin_clz((uint32_t)(x - 1)));
#else
  return 1ull << (64 - __builtin_clzll((uint64_t)(x - 1)));
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
} valk_mem_allocator_e;

char *valk_mem_allocator_e_to_string(valk_mem_allocator_e self);

typedef struct {
  valk_mem_allocator_e type;
} valk_mem_allocator_t;

typedef struct {
  size_t capacity;
  size_t count;
  void *items;
} valk_buffer_t;

void valk_buffer_alloc(valk_buffer_t *buf, size_t capacity);
void valk_buffer_append(valk_buffer_t *buf, void *bytes, size_t len);
int valk_buffer_is_full(valk_buffer_t *buf);

typedef struct {
  size_t capacity;
  size_t offset;
  uint64_t items[];
} valk_ring_t;

/// @param[out] self buffer to initialize
/// @param[in] capcity capacity of the ring buffer in bytes
void valk_ring_init(valk_ring_t *self, size_t capacity);

void valk_ring_write(valk_ring_t *self, uint8_t *data, size_t len);

void valk_ring_rewind(valk_ring_t *self, size_t n);

// @brief read the contents of the buffer into a buffer dst
void valk_ring_read(valk_ring_t *self, size_t n, void *dst);

// @brief read the contents of the buffer into a file
void valk_ring_fread(valk_ring_t *self, size_t n, FILE *f);

// @brief print the contents of the buffer into a file
void valk_ring_print(valk_ring_t *self, FILE *f);

typedef struct valk_slab_item_t {
  size_t handle;
  uint64_t next;
  // size_t size; // todo(networking): i should add this to the layout if i need
  // it. i dont think this will ever be useful tho, so save a few bytes of
  // overhead
  uint8_t data[];
} valk_slab_item_t;

typedef struct {  // extends valk_mem_allocator_t;
  valk_mem_allocator_e type;
  size_t itemSize;
  size_t numItems;
  size_t numFree;
  uint64_t head;
  // treiber list top
  // Memory layout
  // [sizeof(size_t) * numSlabs | freeList]
  // [sizeof(valk_slab_t + (size_t * numSlabs)) * capacity | slabs]
  uint8_t heap[];
} valk_slab_t;

valk_slab_t *valk_slab_new(size_t itemSize, size_t numItems);
void valk_slab_init(valk_slab_t *self, size_t itemSize, size_t numItems);

void valk_slab_free(valk_slab_t *self);

/// @brief estimate the amount of bytes that are needed to contain the entire
/// slab
/// @return the total size that should be allocated, to initialize slab
size_t valk_slab_size(size_t itemSize, size_t numItems);

/// @brief estimate the the total chunk size in bytes of each item in the array
///
/// this is useful in cases where one would want to iterate over the chunks or
/// perhaps access a chunk at a particular offset
/// @param itemSize the concrete size of item without padding or headers
/// @return the actual size of the the item in memory including padding and
/// headers
size_t valk_slab_item_stride(size_t itemSize);

valk_slab_item_t *valk_slab_aquire(valk_slab_t *self);

void valk_slab_release(valk_slab_t *self, valk_slab_item_t *item);
void valk_slab_release_ptr(valk_slab_t *self, void *data);

// Arena statistics for telemetry
typedef struct {
  size_t total_allocations;      // Count of alloc calls
  size_t total_bytes_allocated;  // Sum of all requested bytes
  size_t high_water_mark;        // Maximum offset reached
  size_t num_resets;             // Count of arena_reset calls
  size_t num_checkpoints;        // Count of checkpoint evacuations
  size_t bytes_evacuated;        // Total bytes copied to heap
  size_t values_evacuated;       // Count of values copied to heap
  size_t overflow_fallbacks;     // Count of heap fallback allocations due to full arena
  size_t overflow_bytes;         // Bytes allocated via heap fallback
} valk_arena_stats_t;

typedef struct {  // extends valk_mem_allocator_t;
  valk_mem_allocator_e type;
  size_t capacity;
  size_t offset;
  bool warned_overflow;          // Reset each checkpoint cycle
  valk_arena_stats_t stats;      // Telemetry statistics
  uint8_t heap[];
} valk_mem_arena_t;

void valk_mem_arena_init(valk_mem_arena_t *self, size_t capacity);
void valk_mem_arena_reset(valk_mem_arena_t *self);
void *valk_mem_arena_alloc(valk_mem_arena_t *self, size_t bytes);

// Arena statistics API
void valk_mem_arena_print_stats(valk_mem_arena_t *arena, FILE *out);
void valk_mem_arena_reset_stats(valk_mem_arena_t *arena);
bool valk_ptr_in_arena(valk_mem_arena_t *arena, void *ptr);

// Forward declaration for root environment
struct valk_lenv_t;

// TODO(networking): Maybe these types should be in thread local context or something
typedef struct {
  valk_mem_allocator_t *allocator;
  void *heap;                     // Fallback GC heap for arena overflow (valk_gc_malloc_heap_t*)
  valk_mem_arena_t *scratch;      // Scratch arena for temporary allocations
  struct valk_lenv_t *root_env;   // Root environment for checkpoint evacuation
  float checkpoint_threshold;     // Threshold for automatic checkpointing (0.0-1.0)
  bool checkpoint_enabled;        // Whether automatic checkpointing is enabled
  size_t call_depth;              // Current function call depth (for TCO testing/debugging)
} valk_thread_context_t;

extern __thread valk_thread_context_t valk_thread_ctx;

void *valk_mem_allocator_alloc(valk_mem_allocator_t *self, size_t bytes);
void *valk_mem_allocator_realloc(valk_mem_allocator_t *self, void *ptr,
                                 size_t new_size);
void *valk_mem_allocator_calloc(valk_mem_allocator_t *self, size_t num,
                                size_t size);
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
  size_t capacity;
  size_t free;
  valk_mem_allocator_t *allocator;
  valk_gc_chunk_t sentinel;
  valk_gc_mark_f *mark;
  valk_gc_finalize_f *finalize;
} valk_gc_heap_t;

void valk_gc_init(valk_gc_heap_t *self, size_t capacity);
void valk_gc_mark(valk_gc_heap_t *self, void *ptr);
void *valk_gc_alloc(valk_gc_heap_t *heap, size_t size);
void *valk_gc_realloc(valk_gc_heap_t *heap, void *ptr, size_t size);
void valk_gc_sweep(valk_gc_heap_t *self);

// No extra resize helper; rely on valk_mem_allocator_realloc which now performs
// copy-on-realloc semantics for arena as well as malloc allocators.
