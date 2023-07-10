/* storage.c - Storage for intermediate code variables.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/storage.h"
#include "util/hashmap.h"
#include "util/crc32.h"
#include <assert.h>

static hashmap_t storage;

void ir_storage_init()
{
    hashmap_init(&storage, 512);
}

void ir_storage_reset()
{
    hashmap_destroy(&storage);
}

void ir_storage_push(const char *name, int32_t ir_idx)
{
    hashmap_put(&storage, crc32_string(name), (uint64_t) ir_idx);
}

int32_t ir_storage_get(const char *name)
{
    bool ok = 0;
    int32_t got = (int32_t) hashmap_get(&storage, crc32_string(name), &ok);

    return ok ? got : -1;
}