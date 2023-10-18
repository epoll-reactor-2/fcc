/* meta.c - Extra information about IR nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/meta.h"
#include "util/alloc.h"

void *meta_init(int32_t type)
{
    struct meta *meta = weak_calloc(1, sizeof (struct meta));
    meta->type = type;
    return (void *) meta;
}

void meta_cleanup(void *meta)
{
    weak_free(meta);
}