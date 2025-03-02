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
    printf("Malladfsdfsdf %ld bytes\n",                                        \
           sizeof((arr)->items[0]) * DA_INIT_CAPACITY);                        \
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

