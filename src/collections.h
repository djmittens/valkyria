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
    (arr)->items = malloc(sizeof((arr)->items[0]) * DA_INIT_CAPACITY);         \
  } while (0)

#define da_free(arr)                                                           \
  do {                                                                         \
    free((arr)->items);                                                        \
    free((arr));                                                               \
  } while (0)

#define da_add(arr, elem)                                                      \
  do {                                                                         \
    if ((arr)->count >= (arr)->capacity) {                                     \
      (arr)->capacity =                                                        \
          (arr)->capacity == 0 ? DA_INIT_CAPACITY : (arr)->capacity * 2;       \
      (arr)->items =                                                           \
          realloc((arr)->items, (arr)->capacity * sizeof(*(arr)->items));      \
      if ((arr)->items == NULL) {                                              \
        printf("Buy more ram LUlz\n");                                         \
        exit(1);                                                               \
      }                                                                        \
    }                                                                          \
    (arr)->items[(arr)->count++] = (elem);                                     \
  } while (0)

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
