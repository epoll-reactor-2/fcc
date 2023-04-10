/* ir_storage.c - Storage for intermediate code variables.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_storage.h"
#include "utility/hashmap.h"
#include "utility/crc32.h"
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
    hashmap_put(&storage, crc32_string(name), (size_t)ir_idx);
}

int32_t ir_storage_get(const char *name)
{
    return (int32_t)hashmap_get(&storage, crc32_string(name));
}