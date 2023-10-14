/* storage.c - Storage for intermediate code variables.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/storage.h"
#include "util/alloc.h"
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

void ir_storage_push(
    const char     *name,
    int32_t         sym_idx,
    enum data_type  dt,
    struct ir_node *ir
) {
    struct ir_storage_record *record =
        weak_calloc(1, sizeof (struct ir_storage_record));

    record->sym_idx = sym_idx;
    record->dt = dt;
    record->ir = ir;

    hashmap_put(&storage, crc32_string(name), (uint64_t) record);
}

struct ir_storage_record *ir_storage_get(const char *name)
{
    bool ok = 0;
    struct ir_storage_record *got =
        (struct ir_storage_record *) hashmap_get(&storage, crc32_string(name), &ok);

    return ok ? got : NULL;
}