/* hashmap.h - Hashmap.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTIL_HASHMAP_H
#define WEAK_COMPILER_UTIL_HASHMAP_H

#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

typedef struct {
    uint64_t key;
    uint64_t val;
    bool     is_occupied;
    bool     is_deleted;
} hashmap_bucket_t;

typedef struct {
    hashmap_bucket_t* buckets;
    uint64_t          capacity;
    uint64_t          size;
} hashmap_t;

void     hashmap_init   (hashmap_t *map, uint64_t size);
void     hashmap_destroy(hashmap_t *map);
void     hashmap_put    (hashmap_t *map, uint64_t key, uint64_t value);
uint64_t hashmap_get    (hashmap_t *map, uint64_t key, bool *success);
bool     hashmap_remove (hashmap_t *map, uint64_t key);

#define hashmap_foreach(map, k, v) \
    for (uint64_t _i = 0, k, v;  k = (map)->buckets[_i].key, \
                                 v = (map)->buckets[_i].val, \
                                _i < (map)->capacity; ++_i)  \
                                /*
                                            ^^^^^^^^
                                     Must be comparison with count of
                                     occupied entries, not with capacity.
                                 */                          \
        if ((map)->buckets[_i].is_occupied && !(map)->buckets[_i].is_deleted)

#endif // WEAK_COMPILER_UTIL_HASHMAP_H