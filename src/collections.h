#pragma once
#include "log.h"
#include "memory.h"

#define DA_INIT_CAPACITY 8
#define da_init(arr)                                                           \
  do {                                                                         \
    (arr)->count = 0;                                                          \
    (arr)->capacity = DA_INIT_CAPACITY;                                        \
    if ((arr)->items) {                                                        \
      VALK_WARN("Reinitializing array (items not cleaned up?)");              \
    }                                                                          \
    (arr)->items = valk_mem_alloc(sizeof((arr)->items[0]) * DA_INIT_CAPACITY); \
  } while (0)

#define da_free(arr)                                                           \
  do {                                                                         \
    valk_mem_free((arr)->items);                                               \
  } while (0)

#define da_add(arr, elem)                                                      \
  do {                                                                         \
    if ((arr)->count >= (arr)->capacity) {                                     \
      (arr)->capacity =                                                        \
          (arr)->capacity == 0 ? DA_INIT_CAPACITY : (arr)->capacity * 2;       \
      (arr)->items =                                                           \
          valk_mem_realloc((arr)->items, (arr)->capacity * sizeof(*(arr)->items)); \
      VALK_ASSERT((arr)->items != nullptr, "Buy more ram LUlz %d\n", 0);          \
    }                                                                          \
    (arr)->items[(arr)->count++] = (elem);                                     \
  } while (0)

#define valk_dll_insert_node(target, node)                                    \
  do {                                                                         \
    if ((node) != nullptr) {                                                   \
      if (target == nullptr) {                                                 \
        (node)->prev = nullptr;                                                \
        break;                                                                 \
      }                                                                        \
      node->next = (target)->next;                                            \
      if ((target)->next)                                                      \
        (target)->next->prev = node;                                          \
      (node)->prev = (target);                                                 \
      (target)->next = (node);                                                 \
    }                                                                          \
  } while (0)

#define valk_dll_insert_after(target, head)                                    \
  do {                                                                         \
    if ((head) != nullptr) {                                                   \
      if (target == nullptr) {                                                 \
        (head)->prev = nullptr;                                                \
        break;                                                                 \
      }                                                                        \
      __typeof__(head) __cur = (head);                                         \
      while (__cur->next)                                                      \
        __cur = __cur->next;                                                   \
      __cur->next = (target)->next;                                            \
      if ((target)->next)                                                      \
        (target)->next->prev = __cur;                                          \
      (head)->prev = (target);                                                 \
      (target)->next = (head);                                                 \
    }                                                                          \
  } while (0)

#define valk_dll_pop(node)                                                     \
  do {                                                                         \
    __typeof__(node) __n = (node);                                             \
    if (__n->prev)                                                             \
      __n->prev->next = __n->next;                                             \
    if (__n->next)                                                             \
      __n->next->prev = __n->prev;                                             \
    __n->prev = nullptr;                                                       \
    __n->next = nullptr;                                                       \
  } while (0)

#define valk_dll_foreach(head)                                                 \
  for (__typeof__(head) item = (head); item != nullptr; item = item->next)

#define valk_dll_at(head, n)                                                   \
  ({                                                                           \
    __typeof__(head) __it = (head);                                            \
    u64 __i = (n);                                                          \
    while (__i-- > 0 && __it != nullptr)                                          \
      __it = __it->next;                                                       \
    __it;                                                                      \
  })

#define valk_dll_count(head)                                                   \
  ({                                                                           \
    u64 __count = 0;                                                        \
    valk_dll_foreach(head) { __count++; }                                      \
    __count;                                                                   \
  })
