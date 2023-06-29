/* alloc.c - Safe memory allocation functions.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "util/alloc.h"
#include "util/unreachable.h"
#include <alloca.h>
#include <stdlib.h>

void *weak_malloc(size_t size)
{
    void *addr = malloc(size);
    if (addr == NULL) {
        weak_fatal_error("malloc() failed");
    }

    return addr;
}

void *weak_calloc(size_t nmemb, size_t size)
{
    void *addr = calloc(nmemb, size);
    if (addr == NULL) {
        weak_fatal_error("calloc() failed");
    }

    return addr;
}

void *weak_realloc(void *addr, size_t size)
{
    addr = realloc(addr, size);
    if (addr == NULL) {
        weak_fatal_error("calloc() failed");
    }

    return addr;
}

void weak_free(void *addr)
{
    free(addr);
}