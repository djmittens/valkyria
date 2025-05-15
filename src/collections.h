#pragma once

#define DA_INIT_CAPACITY 8
#define da_init(arr)                                                           \
  do {                                                                         \
    (arr)->count = 0;                                                          \
    (arr)->capacity = DA_INIT_CAPACITY;                                        \
    if ((arr)->items) {                                                        \
      printf("Reinitializing the array for some stupid reason, probably a "    \
             "memory leak, since items are not cleaned up\n");                 \
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
          realloc((arr)->items, (arr)->capacity * sizeof(*(arr)->items));      \
      VALK_ASSERT((arr)->items != NULL, "Buy more ram LUlz %d\n", 0);          \
    }                                                                          \
    (arr)->items[(arr)->count++] = (elem);                                     \
  } while (0)

/// @brief Swap an element out at idx
/// Put the end element in the place of the specified element, returning it as a
/// result
/// This will mess up the order the array but its more performant than pop
/// as it wont have to copy any other element
///
/// Example:
/// idx = 2
/// [ a b c d e f]
///       ^
/// [ a b d e f] c
/// return c
///
/// @param[in] arr the dynamic array to perform the operation
/// @param[in] idx the id of the element to swap to
/// @return the value swapped out
#define da_xpop(arr, idx)                                                      \
  ({                                                                           \
    VALK_ASSERT(0, "Not implemented yet");                                     \
    VALK_ASSERT((arr)->count > 0, "Cannot pop from empty array %ld",           \
                (arr)->count);                                                 \
    int idx = (arr)->count;                                                    \
    if ((arr)->count == (arr->capacity)) {                                     \
    }                                                                          \
  })

#define valk_pool_init(pool, size)                                             \
  do {                                                                         \
    (pool)->numFree = (size) + 1;                                              \
    (pool)->capacity = (size) + 1;                                             \
    if ((pool)->items) {                                                       \
      printf("Reinitializing the pool for some stupid reason, probably a "     \
             "memory leak, since items are not cleaned up\n");                 \
    }                                                                          \
    (pool)->items = valk_mem_alloc(sizeof((pool)->items[0]) * ((size) + 1));   \
    (pool)->free = valk_mem_alloc(sizeof((pool)->free[0]) * ((size) + 1));     \
    for (size_t i = 0; i < (pool)->capacity; ++i) {                            \
      (pool)->free[i] = i;                                                     \
    }                                                                          \
  } while (0)

#define valk_dll_insert_after(node_a, node_b)                                  \
  do {                                                                         \
    if ((head) != NULL) {                                                      \
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

#define valk_dll_pop(node_a)                                                   \
  do {                                                                         \
    do {                                                                       \
      if ((node)->prev)                                                        \
        (node)->prev->next = (node)->next;                                     \
      if ((node)->next)                                                        \
        (node)->next->prev = (node)->prev;                                     \
      (node)->prev = NULL;                                                     \
      (node)->next = NULL;                                                     \
  } while (0)

// TODO(networking): add dynamic resizing at some point, but its kinda
// complicated with id rebalancing

#define valk_pool_request(pool)                                                \
  ({                                                                           \
    if (pool->numFree == 1) {                                                  \
      printf("Pool is out of shit returning invalid index");                   \
      return 0;                                                                \
    }                                                                          \
    size_t tmp = (pool)->free[0];                                              \
    (pool)->free[1] = (pool)->free[(pool)->numFree];                           \
    (pool)->free[(pool)->numFree] = tmp;                                       \
    (pool)->numFree--;                                                         \
    tmp;                                                                       \
  })

// TODO(networking):  add edge case assertions for missing id's and 0 index
#define valk_pool_release(pool, idx)                                           \
  do {                                                                         \
    for (size_t i = 0; i < (pool)->capacity; ++i) {                            \
      if ((pool)->free[i] == (idx)) {                                          \
        size_t tmp = (pool)->items[(pool)->numFree];                           \
        (pool)->items[(pool)->numFree] = (pool->items[i]);                     \
        (pool)->items[i] = tmp;                                                \
        (pool)->numFree++;                                                     \
        break;                                                                 \
      }                                                                        \
    }                                                                          \
  } while (0)
