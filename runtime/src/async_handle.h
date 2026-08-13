#pragma once

#include <stdatomic.h>
#include "memory.h"
#include "aio/aio_types.h"

struct valk_aio_system;
struct valk_lval_t;
struct valk_lenv_t;
struct valk_region;
struct valk_request_ctx;

typedef struct {
  void (*fn)(void *data, void *ctx);
  void *data;
  void *ctx;
} valk_async_cleanup_entry_t;

struct valk_async_handle_t {
  u64 id;
  _Atomic valk_async_status_t status;

  _Atomic int cancel_requested;

  void *uv_handle_ptr;
  struct valk_aio_system *sys;

  struct valk_lval_t *on_complete;
  struct valk_lval_t *on_error;
  struct valk_lval_t *on_cancel;
  struct valk_lenv_t *env;

  _Atomic(struct valk_lval_t *) result;
  _Atomic(struct valk_lval_t *) error;

  struct valk_region *region;

  struct valk_request_ctx *request_ctx;

  _Atomic(valk_async_done_fn) on_done;
  _Atomic(void *) on_done_ctx;

  struct valk_async_handle_t *parent;
  valk_chunked_ptrs_t children;

  struct valk_async_handle_t *prev;
  struct valk_async_handle_t *next;

  _Atomic u32 refcount;

  valk_async_cleanup_fn cleanup_fn;
  void *cleanup_ctx;

  valk_async_cleanup_entry_t *resource_cleanups;
  u16 resource_cleanup_count;
  u16 resource_cleanup_capacity;

  valk_async_on_child_fn on_child_completed;
  valk_async_on_child_fn on_child_failed;

  union {
    struct {
      struct valk_lval_t **results;
      struct valk_async_handle_t **handles;
      u64 total;
      _Atomic(u64) completed;
    } all;
    struct {
      struct valk_async_handle_t **handles;
      u64 total;
    } race;
    struct {
      struct valk_async_handle_t **handles;
      u64 total;
      u64 failed_count;
      struct valk_lval_t *last_error;
    } any;
    struct {
      struct valk_async_handle_t *source_handle;
      struct valk_async_handle_t *timeout_handle;
    } within;
    struct {
      struct valk_async_handle_t *current_attempt;
      struct valk_async_handle_t *backoff_timer;
      struct valk_lval_t *fn;
      u64 max_attempts;
      u64 current_attempt_num;
      u64 base_delay_ms;
      f64 backoff_multiplier;
      struct valk_lval_t *last_error;
    } retry;
  } comb;
};
